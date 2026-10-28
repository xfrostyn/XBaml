import os
import io
import math
import struct
import shutil
import threading
import queue
import copy
import time
import json
import importlib.util
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
from pathlib import Path


try:
    from PIL import Image, ImageTk
    PIL_OK = True
except Exception:
    PIL_OK = False
PROP_NAMES = {1: 'X position', 2: 'Y position', 3: 'Scale X', 4: 'Scale Y', 5: 'Rotation', 6: 'Opacity'}
TYPE_NAMES = {0: 'Group', 1: 'Image', 2: 'Component', 3: 'Text'}


def read_pstr(data, off):
    if off >= len(data):
        raise EOFError
    n = data[off]
    off += 1
    if off + n > len(data):
        raise EOFError
    return (data[off:off + n].decode('latin1', 'replace'), off + n)


def f32(data, off):
    return struct.unpack_from('<f', data, off)[0]


def u32(data, off):
    return struct.unpack_from('<I', data, off)[0]


def normalize_tex_name(path):
    s = path.replace('\\', '/').split('/')[-1]
    s = os.path.splitext(s)[0].upper()
    for suffix in ('_DX11', '_PC'):
        if s.endswith(suffix):
            s = s[:-len(suffix)]
    return s


def extract_strings(data):
    out = []
    i = 0
    while i < len(data):
        n = data[i]
        if 3 <= n <= 120 and i + 1 + n <= len(data):
            b = data[i + 1:i + 1 + n]
            if all((32 <= c <= 126 for c in b)):
                out.append(b.decode('ascii', 'replace'))
                i += 1 + n
                continue
        i += 1
    return out


def parse_timecode(s):
    try:
        parts = [float(x) for x in s.split(':')]
        if len(parts) == 1:
            return parts[0]
        if len(parts) == 2:
            return parts[0] * 60.0 + parts[1]
        if len(parts) == 3:
            return parts[0] * 3600.0 + parts[1] * 60.0 + parts[2]
    except Exception:
        pass
    try:
        return float(s)
    except Exception:
        return 0.0


def approx_pivot_value(raw):
    if raw <= 0:
        return 0.0
    if abs(raw - 16128) <= 64:
        return 0.5
    if abs(raw - 16256) <= 64:
        return 1.0
    return max(0.0, min(1.0, raw / 32256.0))


def lerp(a, b, t):
    return a + (b - a) * t


def parse_baml(path, data_override=None):
    data = bytes(data_override) if data_override is not None else Path(path).read_bytes()
    result = {'path': path, 'data': data, 'nodes': [], 'animations': [], 'complete': False, 'note': '', 'strings': extract_strings(data), 'structure_dirty': False}
    if len(data) < 4:
        result['note'] = 'Too small / unknown BAML family'
        return result
    header_count = u32(data, 0)
    if header_count < 1 or header_count > 10000:
        result['note'] = 'Context/index or unknown BAML family'
        return result
    off = 4
    complete = True
    expected_slots = 1
    stack = []
    parsed_count = 0
    while expected_slots > 0 and parsed_count < 10000:
        try:
            while stack and stack[-1][1] <= 0:
                stack.pop()
            parent_index = stack[-1][0] if stack else None
            name, off = read_pstr(data, off)
            if off + 42 > len(data):
                raise EOFError
            common_offset = off
            vals = struct.unpack_from('<8f', data, off)
            off += 32
            ntype = u32(data, off)
            off += 4
            pivots = struct.unpack_from('<3H', data, off)
            off += 6
            if ntype not in (0, 1, 2, 3):
                raise ValueError('unsupported node type')
            node = {'name': name, 'type': ntype, 'common_offset': common_offset, 'width': vals[0], 'height': vals[1], 'x': vals[2], 'y': vals[3], 'sx': vals[4], 'sy': vals[5], 'rotation': vals[6], 'opacity': vals[7], 'pivots': pivots, 'texture': '', 'component': '', 'text': '', 'parent_index': parent_index}
            child_count = 0
            if ntype == 0:
                if off + 4 > len(data):
                    raise EOFError
                child_count = u32(data, off)
                off += 4
                if child_count > 10000:
                    raise ValueError('bad child count')
                node['child_count'] = child_count
            elif ntype == 1:
                node['texture_field_start'] = off
                node['texture'], off = read_pstr(data, off)
                node['texture_field_end'] = off
            elif ntype == 2:
                node['component_field_start'] = off
                node['component'], off = read_pstr(data, off)
                node['component_field_end'] = off
            elif ntype == 3:
                node['text_field_start'] = off
                node['text'], off = read_pstr(data, off)
                node['text_field_end'] = off
                if off + 10 > len(data):
                    raise EOFError
                node['text_color_raw'] = u32(data, off)
                off += 4
                node['font_size'] = f32(data, off)
                off += 4
                node['text_style'] = (data[off], data[off + 1])
                off += 2
            node_index = len(result['nodes'])
            result['nodes'].append(node)
            parsed_count += 1
            expected_slots -= 1
            if stack:
                stack[-1][1] -= 1
            if child_count:
                stack.append([node_index, child_count])
                expected_slots += child_count
        except Exception:
            complete = False
            break
    result['tree_complete'] = expected_slots == 0
    result['header_count'] = header_count
    result['original_node_count'] = len(result['nodes'])
    if result['tree_complete'] and off + 4 <= len(data):
        try:
            ac = u32(data, off)
            off += 4
            if ac > 10000:
                raise ValueError
            for _ in range(ac):
                name, off = read_pstr(data, off)
                if off + 6 > len(data):
                    raise EOFError
                flags = (data[off], data[off + 1])
                off += 2
                tc = u32(data, off)
                off += 4
                anim = {'name': name, 'flags': flags, 'tracks': []}
                if tc > 10000:
                    raise ValueError
                for _ in range(tc):
                    if off + 7 > len(data):
                        raise EOFError
                    prop = u32(data, off)
                    off += 4
                    unknown3 = data[off:off + 3]
                    off += 3
                    target, off = read_pstr(data, off)
                    kc = u32(data, off)
                    off += 4
                    if kc > 100000:
                        raise ValueError
                    track = {'property': prop, 'target': target, 'unknown3': unknown3, 'keys': []}
                    for _ in range(kc):
                        tm, off = read_pstr(data, off)
                        if off + 21 > len(data):
                            raise EOFError
                        flag = data[off]
                        off += 1
                        value = f32(data, off)
                        off += 4
                        ease = struct.unpack_from('<4f', data, off)
                        off += 16
                        track['keys'].append({'time': tm, 'value': value, 'flag': flag, 'ease': ease})
                    anim['tracks'].append(track)
                result['animations'].append(anim)
        except Exception:
            complete = False
    result['complete'] = result['tree_complete'] and complete
    if not result['note']:
        if not result['nodes']:
            result['note'] = 'Context/index or unknown BAML family'
        elif not result['tree_complete']:
            result['note'] = 'Partially parsed: visual tree ended unexpectedly'
        elif not result['complete']:
            result['note'] = 'Visual tree parsed; animation section has an unsupported variant'
        elif header_count != len(result['nodes']):
            result['note'] = f"Parsed full hierarchy ({len(result['nodes'])} nodes; header count was {header_count})"
    return result


def pack_pstr(s):
    raw = (s or '').encode('latin1', 'replace')
    if len(raw) > 255:
        raise ValueError('BAML string is too long (max 255 bytes)')
    return bytes([len(raw)]) + raw


def serialize_baml(parsed):
    """Rebuild the known visual BAML family from parsed nodes/animations."""
    nodes = parsed.get('nodes', [])
    if not nodes:
        return bytes(parsed.get('data', b''))
    out = bytearray()
    original_count = int(parsed.get('original_node_count', len(nodes)) or len(nodes))
    original_header = int(parsed.get('header_count', len(nodes)) or len(nodes))
    header = max(1, original_header + (len(nodes) - original_count))
    out += struct.pack('<I', header)
    child_counts = {i: 0 for i in range(len(nodes))}
    for i, n in enumerate(nodes):
        p = n.get('parent_index')
        if p is not None and p in child_counts:
            child_counts[p] += 1
    for i, n in enumerate(nodes):
        out += pack_pstr(n.get('name', ''))
        out += struct.pack('<8f', float(n.get('width', 0)), float(n.get('height', 0)), float(n.get('x', 0)), float(n.get('y', 0)), float(n.get('sx', 1)), float(n.get('sy', 1)), float(n.get('rotation', 0)), float(n.get('opacity', 1)))
        out += struct.pack('<I', int(n.get('type', 0)))
        piv = n.get('pivots', (0, 0, 0))
        piv = (list(piv) + [0, 0, 0])[:3]
        out += struct.pack('<3H', *(int(x) & 65535 for x in piv))
        typ = int(n.get('type', 0))
        if typ == 0:
            out += struct.pack('<I', child_counts.get(i, 0))
        elif typ == 1:
            out += pack_pstr(n.get('texture', ''))
        elif typ == 2:
            out += pack_pstr(n.get('component', ''))
        elif typ == 3:
            out += pack_pstr(n.get('text', ''))
            out += struct.pack('<I', int(n.get('text_color_raw', 4294967295)) & 4294967295)
            out += struct.pack('<f', float(n.get('font_size', 24.0) or 24.0))
            st = n.get('text_style', (0, 0))
            st = (list(st) + [0, 0])[:2]
            out += bytes([int(st[0]) & 255, int(st[1]) & 255])
        else:
            raise ValueError('Cannot rebuild unsupported node type ' + str(typ))
    anims = parsed.get('animations', [])
    out += struct.pack('<I', len(anims))
    valid_names = {n.get('name', '') for n in nodes}
    for a in anims:
        out += pack_pstr(a.get('name', ''))
        flags = a.get('flags', (0, 0))
        flags = (list(flags) + [0, 0])[:2]
        out += bytes([int(flags[0]) & 255, int(flags[1]) & 255])
        tracks = [tr for tr in a.get('tracks', []) if tr.get('target', '') in valid_names]
        out += struct.pack('<I', len(tracks))
        for tr in tracks:
            out += struct.pack('<I', int(tr.get('property', 0)))
            u = bytes(tr.get('unknown3', b'\x00\x00\x00'))[:3].ljust(3, b'\x00')
            out += u
            out += pack_pstr(tr.get('target', ''))
            keys = tr.get('keys', [])
            out += struct.pack('<I', len(keys))
            for k in keys:
                out += pack_pstr(k.get('time', '0'))
                out += bytes([int(k.get('flag', 0)) & 255])
                out += struct.pack('<f', float(k.get('value', 0)))
                ease = (list(k.get('ease', (0, 0, 1, 1))) + [0, 0, 1, 1])[:4]
                out += struct.pack('<4f', *(float(x) for x in ease))
    return bytes(out)


class App:

    def __init__(self, root):
        self.root = root
        root.title('XBAML')
        root.geometry('1480x900')
        root.minsize(1020, 640)
        self.q = queue.Queue()
        self.scan_token = 0
        self.parse_token = 0
        self.root_dir = ''
        self.baml_paths = []
        self.tex_index = {}
        self.current = None
        self.selected_node = None
        self.preview_img = None
        self.preview_texture_path = ''
        self.preview_texture_pil = None
        self.background_path = ''
        self.background_pil = None
        self.nonstandard_background_path = ''
        self.nonstandard_background_pil = None
        self.background_tk = None
        self.selected_baml_paths = []
        self.active_animation_keys = set()
        self.anim_check_vars = {}
        self.overlay_tk = None
        self.anim_names = ['(raw node values)']
        self.baml_index = {}
        self.parsed_cache = {}
        self.texture_pil_cache = {}
        self.preview_scene_tk = None
        self.preview_canvas_image_item = None
        self.visible_node_indices = []
        self.preview_items = []
        self.preview_view_metrics = None
        self.dragging_node = False
        self.drag_node_index = None
        self.drag_mode = None
        self.drag_start = None
        self.preview_render_job = None
        self.fast_preview = False
        self.hidden_nodes_by_path = {}
        self.locked_nodes_by_path = {}
        self.undo_stack = []
        self.max_undo = 50
        self.appearance = 'dark'
        self._drag_undo_pushed = False
        self.playing = False
        self.loop_animation = tk.BooleanVar(value=True)
        self.playback_job = None
        self.playback_last_time = None
        self.playback_start_clock = None
        self.playback_start_value = 0.0
        self.playback_generation = 0
        self.animation_duration = 0.0
        self.updating_time_controls = False
        self.preview_time_numeric = 0.0
        self.playback_target_fps = 60.0
        self.playback_frame_interval = 1.0 / self.playback_target_fps
        self.playback_next_frame_clock = None
        self.playback_ui_last_clock = 0.0
        self.settings_dir = os.path.join(os.environ.get('APPDATA') or os.path.expanduser('~'), 'XBAML')
        os.makedirs(self.settings_dir, exist_ok=True)
        self.settings_path = os.path.join(self.settings_dir, 'settings.json')
        self.plugins_dir = os.path.join(self.settings_dir, 'plugins')
        os.makedirs(self.plugins_dir, exist_ok=True)
        self.settings_data = self._load_settings_file()
        self.restore_baml_name = str(self.settings_data.get('last_baml', 'MAINWINDOW.BAML'))
        self.hud_preview_scale = float(self.settings_data.get('hud_preview_scale', 0.55))
        self._session_save_job = None
        self.confirm_delete = bool(self.settings_data.get('confirm_delete', True))
        self.installed_plugins = set(self.settings_data.get('installed_plugins', ['animation_editor']))
        self.external_plugins = {}
        self.animation_editor_window = None
        self.animation_editor_tab = None
        self.last_notebook_tab = None
        self.resized_texture_cache = {}
        self.resized_texture_cache_order = []
        self.font_cache = {}
        self.background_scaled_cache = {}
        self.preview_dirty = True
        self.last_preview_signature = None
        self._node_select_job = None
        menubar = tk.Menu(root)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label='Open Directory…', command=self.choose_dir)
        file_menu.add_separator()
        file_menu.add_command(label='Save', command=self.save_current, accelerator='Ctrl+S')
        file_menu.add_command(label='Save As…', command=self.save_as)
        file_menu.add_separator()
        file_menu.add_command(label='Exit', command=root.destroy)
        edit_menu = tk.Menu(menubar, tearoff=0)
        edit_menu.add_command(label='Undo', command=self.undo, accelerator='Ctrl+Z')
        view_menu = tk.Menu(menubar, tearoff=0)
        view_menu.add_command(label='Dark Theme', command=lambda: self.set_appearance('dark'))
        view_menu.add_command(label='Light Theme', command=lambda: self.set_appearance('light'))
        view_menu.add_separator()
        view_menu.add_command(label='Show Background', command=lambda: self.show_bg_var.set(True) if hasattr(self, 'show_bg_var') else None)
        render_menu = tk.Menu(menubar, tearoff=0)
        render_menu.add_command(label='Refresh Preview', command=lambda: self.request_preview_render(1))
        render_menu.add_command(label='Communicator HUD Scale…', command=self.change_hud_scale)
        window_menu = tk.Menu(menubar, tearoff=0)
        window_menu.add_command(label='Plugins', command=lambda: self.notebook.select(self.plugins_tab) if hasattr(self, 'plugins_tab') else None)
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label='About XBAML', command=lambda: messagebox.showinfo('XBAML', 'XBAML\nLEGO City Undercover BAML editor'))
        menubar.add_cascade(label='File', menu=file_menu)
        menubar.add_cascade(label='Edit', menu=edit_menu)
        menubar.add_cascade(label='Render', menu=render_menu)
        menubar.add_cascade(label='Window', menu=window_menu)
        menubar.add_cascade(label='Help', menu=help_menu)
        root.config(menu=menubar)
        self.theme_menus = (menubar, file_menu, edit_menu, view_menu, render_menu, window_menu, help_menu)
        header = ttk.Frame(root)
        header.pack(fill='x')
        ttk.Button(header, text='Open', command=self.choose_dir, width=7).pack(side='left', padx=(4, 2), pady=3)
        ttk.Button(header, text='Save', command=self.save_current, width=7).pack(side='left', padx=2, pady=3)
        ttk.Button(header, text='Save As', command=self.save_as, width=8).pack(side='left', padx=2, pady=3)
        self.path_var = tk.StringVar()
        ttk.Entry(header, textvariable=self.path_var, state='readonly').pack(side='left', fill='x', expand=True, padx=6, pady=3)
        self.status = tk.StringVar(value='Ready')
        ttk.Label(header, textvariable=self.status).pack(side='right', padx=8)
        nb = ttk.Notebook(root)
        nb.pack(fill='both', expand=True)
        layout_tab = ttk.Frame(nb)
        plugins_tab = ttk.Frame(nb)
        data_tab = ttk.Frame(nb)
        nb.add(layout_tab, text='Layout')
        nb.add(plugins_tab, text='Plugins')
        nb.add(data_tab, text='Data')
        self.notebook = nb
        self.preview_tab = layout_tab
        self.plugins_tab = plugins_tab
        self.animation_editor_tab = None
        main = ttk.Panedwindow(layout_tab, orient='horizontal')
        main.pack(fill='both', expand=True)
        self.main_panes = main
        left = ttk.Frame(main, width=255)
        centre = ttk.Frame(main)
        right = ttk.Frame(main, width=255)
        # Keep pane contents from increasing their parent pane's requested width.
        left.pack_propagate(False)
        right.pack_propagate(False)
        main.add(left, weight=0)
        main.add(centre, weight=1)
        main.add(right, weight=0)
        left_split = ttk.Panedwindow(left, orient='vertical')
        left_split.pack(fill='both', expand=True)
        files_panel = ttk.Frame(left_split)
        nodes_panel = ttk.Frame(left_split)
        left_split.add(files_panel, weight=1)
        left_split.add(nodes_panel, weight=3)
        ttk.Label(files_panel, text='  BAML FILES').pack(fill='x', pady=(3, 2))
        file_container = ttk.Frame(files_panel)
        file_container.pack(fill='both', expand=True, padx=2, pady=(0, 2))
        self.baml_list = tk.Listbox(file_container, exportselection=False, selectmode=tk.EXTENDED, borderwidth=0, highlightthickness=0)
        file_scroll = ttk.Scrollbar(file_container, orient='vertical', command=self.baml_list.yview)
        self.baml_list.configure(yscrollcommand=file_scroll.set)
        file_scroll.pack(side='right', fill='y')
        self.baml_list.pack(side='left', fill='both', expand=True)
        self.baml_list.bind('<<ListboxSelect>>', self.on_baml)
        self.baml_list.bind('<ButtonRelease-1>', self.on_baml_click_release, add='+')
        ttk.Label(nodes_panel, text='  OUTLINER / NODES').pack(fill='x', pady=(3, 2))
        self.node_list = ttk.Treeview(nodes_panel, columns=('eye', 'lock', 'name', 'type'), show='headings', selectmode='extended')
        self.node_list.heading('eye', text='👁')
        self.node_list.heading('lock', text='🔒')
        self.node_list.heading('name', text='Name')
        self.node_list.heading('type', text='Type')
        self.node_list.column('eye', width=32, stretch=False, anchor='center')
        self.node_list.column('lock', width=32, stretch=False, anchor='center')
        self.node_list.column('name', width=150, stretch=True)
        self.node_list.column('type', width=75, stretch=False)
        node_container = ttk.Frame(nodes_panel)
        node_container.pack(fill='both', expand=True, padx=2)
        node_scroll = ttk.Scrollbar(node_container, orient='vertical', command=self.node_list.yview)
        self.node_list.configure(yscrollcommand=node_scroll.set)
        node_scroll.pack(side='right', fill='y')
        self.node_list.pack(side='left', fill='both', expand=True)
        self.node_list.bind('<<TreeviewSelect>>', self.on_node)
        self.node_list.bind('<Button-1>', self.on_layer_click, add='+')
        layer_tools = ttk.Frame(nodes_panel)
        layer_tools.pack(fill='x', pady=3)
        ttk.Button(layer_tools, text='+', width=4, command=self.add_node).pack(side='left', padx=(2, 2))
        ttk.Button(layer_tools, text='🗑', width=4, command=self.delete_selected_node).pack(side='left', padx=2)
        ttk.Label(layer_tools, text='Ctrl+Z Undo').pack(side='left', padx=8)
        viewport_bar = ttk.Frame(centre)
        viewport_bar.pack(fill='x')
        ttk.Label(viewport_bar, text='Viewport').pack(side='left', padx=(6, 8))
        ttk.Button(viewport_bar, text='Background', command=self.choose_background).pack(side='left', padx=2)
        ttk.Button(viewport_bar, text='Default BG', command=self.load_default_background).pack(side='left', padx=2)
        self.preview_res_var = tk.StringVar(value='Auto (BAML aspect)')
        self.preview_res_combo = ttk.Combobox(viewport_bar, textvariable=self.preview_res_var, values=['Auto (BAML aspect)', '1280x720', '1920x1080', 'Use layout root'], state='readonly', width=18)
        self.preview_res_combo.pack(side='left', padx=6)
        self.preview_res_combo.bind('<<ComboboxSelected>>', lambda e: self.request_preview_render(1))
        self.show_bg_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(viewport_bar, text='BG', variable=self.show_bg_var, command=lambda: self.request_preview_render(1)).pack(side='left')
        self.show_labels_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(viewport_bar, text='Labels', variable=self.show_labels_var, command=self.draw_selection_overlay).pack(side='left')
        self.preview_note = tk.StringVar(value='')
        ttk.Label(viewport_bar, textvariable=self.preview_note).pack(side='right', padx=6)
        self.preview_canvas = tk.Canvas(centre, bg='#101010', highlightthickness=0, borderwidth=0, cursor='fleur')
        self.preview_canvas.pack(fill='both', expand=True)
        self.preview_canvas.bind('<Configure>', lambda e: self.request_preview_render(25))
        self.preview_canvas.bind('<ButtonPress-1>', self.on_preview_press)
        self.preview_canvas.bind('<B1-Motion>', self.on_preview_drag)
        self.preview_canvas.bind('<ButtonRelease-1>', self.on_preview_release)
        timeline = ttk.Frame(centre)
        timeline.pack(fill='x', side='bottom')
        playback = ttk.Frame(timeline)
        playback.pack(fill='x', padx=4, pady=(3, 2))
        self.play_button = ttk.Button(playback, text='▶', command=self.toggle_playback, width=4)
        self.play_button.pack(side='left')
        ttk.Button(playback, text='■', command=self.stop_playback, width=4).pack(side='left', padx=(2, 0))
        ttk.Checkbutton(playback, text='Loop', variable=self.loop_animation).pack(side='left', padx=(6, 5))
        self.playback_slider = tk.Scale(playback, from_=0.0, to=1.0, resolution=0.001, orient='horizontal', showvalue=False, command=self.on_playback_slider, borderwidth=0, highlightthickness=0)
        self.playback_slider.pack(side='left', fill='x', expand=True, padx=4)
        self.preview_time_var = tk.StringVar(value='0')
        self.playback_time_label = tk.StringVar(value='0.000 / 0.000 s')
        ttk.Label(playback, textvariable=self.playback_time_label, width=18).pack(side='right')
        self.animation_editor_frame = ttk.Frame(timeline)
        anim_canvas = tk.Canvas(self.animation_editor_frame, height=28, highlightthickness=0, borderwidth=0)
        anim_scroll = ttk.Scrollbar(self.animation_editor_frame, orient='horizontal', command=anim_canvas.xview)
        anim_canvas.configure(xscrollcommand=anim_scroll.set)
        anim_canvas.pack(fill='x')
        anim_scroll.pack(fill='x')
        ae = ttk.Frame(anim_canvas)
        anim_window = anim_canvas.create_window((0, 0), anchor='nw', window=ae)
        ae.bind('<Configure>', lambda event: anim_canvas.configure(scrollregion=anim_canvas.bbox('all')))
        anim_canvas.bind('<Shift-MouseWheel>', lambda event: self._scroll_horizontal(anim_canvas, event))
        ae.bind('<Shift-MouseWheel>', lambda event: self._scroll_horizontal(anim_canvas, event))
        self.anim_canvas = anim_canvas
        ttk.Label(ae, text='Animation Editor', style='Accent.TLabel').pack(side='left', padx=(2, 8))
        self.ae_anim_var = tk.StringVar()
        self.ae_anim_combo = ttk.Combobox(ae, textvariable=self.ae_anim_var, state='readonly', width=20)
        self.ae_anim_combo.pack(side='left', padx=2)
        self.ae_anim_combo.bind('<<ComboboxSelected>>', lambda e: self._ae_anim_combo_changed())
        self.preview_anim_var = self.ae_anim_var
        self.preview_anim_combo = self.ae_anim_combo
        self.anim_multi_menu = tk.Menu(ae, tearoff=0)
        self.theme_menus += (self.anim_multi_menu,)
        self.anim_multi_button = ttk.Menubutton(ae, text='Animations (0) ▾', width=18)
        self.anim_multi_button['menu'] = self.anim_multi_menu
        self.anim_multi_button.pack(side='left', padx=(4, 2))
        self.ae_target_var = tk.StringVar(value='Select an image')
        ttk.Label(ae, text='Target:').pack(side='left', padx=(8, 2))
        self.ae_target_label = ttk.Label(ae, textvariable=self.ae_target_var, width=18)
        self.ae_target_label.pack(side='left')
        self.ae_duration_var = tk.StringVar(value='1.0')
        ttk.Button(ae, text='+ Anim', command=self._ae_new_animation).pack(side='left', padx=(6, 1))
        ttk.Button(ae, text='− Anim', command=self._ae_delete_animation).pack(side='left', padx=1)
        ttk.Button(ae, text='Fade In', command=self._ae_fade_in).pack(side='left', padx=1)
        ttk.Button(ae, text='Fade Out', command=self._ae_fade_out).pack(side='left', padx=1)
        ttk.Button(ae, text='Rotate', command=self._ae_rotate).pack(side='left', padx=1)
        ttk.Button(ae, text='Scale +', command=lambda: self._ae_scale(1.5)).pack(side='left', padx=1)
        ttk.Button(ae, text='Scale −', command=lambda: self._ae_scale(0.5)).pack(side='left', padx=1)
        ttk.Button(ae, text='Speed', command=self._ae_change_speed).pack(side='left', padx=1)
        ttk.Button(ae, text='Split', command=self._ae_split_scene).pack(side='left', padx=1)
        self.ae_status = tk.StringVar(value='Plugin by xfrostyn')
        ttk.Label(timeline, textvariable=self.ae_status).pack(fill='x', padx=8, pady=(0, 3))
        self.animation_editor_frame.pack_forget()
        ttk.Label(right, text='  PROPERTIES').pack(fill='x', pady=(3, 2))
        props = ttk.Notebook(right)
        props.pack(fill='both', expand=True)
        inspect = ttk.Frame(props)
        anims = ttk.Frame(props)
        raw = ttk.Frame(props)
        props.add(inspect, text='Transform')
        props.add(anims, text='Animations')
        props.add(raw, text='Raw')
        property_canvas = tk.Canvas(inspect, highlightthickness=0, borderwidth=0)
        self.property_canvas = property_canvas
        property_scroll = ttk.Scrollbar(inspect, orient='vertical', command=property_canvas.yview)
        property_canvas.configure(yscrollcommand=property_scroll.set)
        property_scroll.pack(side='right', fill='y')
        property_canvas.pack(side='left', fill='both', expand=True)
        property_body = ttk.Frame(property_canvas)
        property_window = property_canvas.create_window((0, 0), window=property_body, anchor='nw')
        property_body.bind('<Configure>', lambda event: property_canvas.configure(scrollregion=property_canvas.bbox('all')))
        property_canvas.bind('<Configure>', lambda event: property_canvas.itemconfigure(property_window, width=event.width))
        property_canvas.bind('<MouseWheel>', lambda event: self._scroll_vertical(property_canvas, event))
        self.info = tk.Text(property_body, height=7, wrap='word', state='disabled', borderwidth=0)
        self.info.pack(fill='x', padx=4, pady=4)
        form = ttk.Frame(property_body)
        form.pack(fill='x', padx=4, pady=4)
        self.fields = {}
        self.field_entries = {}
        for row, (key, label) in enumerate([('width', 'Width'), ('height', 'Height'), ('x', 'Location X'), ('y', 'Location Y'), ('sx', 'Scale X'), ('sy', 'Scale Y'), ('rotation', 'Rotation'), ('opacity', 'Opacity')]):
            ttk.Label(form, text=label, width=12).grid(row=row, column=0, sticky='w', padx=2, pady=2)
            var = tk.StringVar()
            self.fields[key] = var
            ent = ttk.Entry(form, textvariable=var, width=14)
            ent.grid(row=row, column=1, sticky='ew', padx=2, pady=2)
            self.field_entries[key] = ent
        form.columnconfigure(1, weight=1)
        ttk.Button(form, text='Apply', command=self.apply_node_fields).grid(row=8, column=0, columnspan=2, sticky='ew', padx=2, pady=(8, 2))
        ttk.Button(form, text='Replace Texture…', command=self.replace_texture_reference).grid(row=9, column=0, columnspan=2, sticky='ew', padx=2, pady=2)
        ttk.Button(form, text='Remove Texture', command=self.remove_texture_reference).grid(row=10, column=0, columnspan=2, sticky='ew', padx=2, pady=2)
        self.visibility_button = ttk.Button(form, text='👁 Visible', command=self.toggle_selected_hidden)
        self.visibility_button.grid(row=11, column=0, sticky='ew', padx=2, pady=2)
        self.lock_button = ttk.Button(form, text='🔓 Unlocked', command=self.toggle_selected_locked)
        self.lock_button.grid(row=11, column=1, sticky='ew', padx=2, pady=2)
        ttk.Button(form, text='Show All', command=self.show_all_hidden).grid(row=12, column=0, sticky='ew', padx=2, pady=2)
        ttk.Button(form, text='Unlock All', command=self.unlock_all).grid(row=12, column=1, sticky='ew', padx=2, pady=2)
        ttk.Button(form, text='Set Opacity 0', command=self.set_selected_invisible).grid(row=13, column=0, columnspan=2, sticky='ew', padx=2, pady=2)
        self.anim_text = tk.Text(anims, wrap='none', borderwidth=0)
        self.anim_text.pack(side='left', fill='both', expand=True)
        anim_text_scroll = ttk.Scrollbar(anims, orient='vertical', command=self.anim_text.yview)
        self.anim_text.configure(yscrollcommand=anim_text_scroll.set)
        anim_text_scroll.pack(side='right', fill='y')
        self.raw_text = tk.Text(raw, wrap='none', borderwidth=0)
        self.raw_text.pack(side='left', fill='both', expand=True)
        raw_text_scroll = ttk.Scrollbar(raw, orient='vertical', command=self.raw_text.yview)
        self.raw_text.configure(yscrollcommand=raw_text_scroll.set)
        raw_text_scroll.pack(side='right', fill='y')
        plugin_header = ttk.Frame(plugins_tab)
        plugin_header.pack(fill='x', padx=10, pady=10)
        ttk.Label(plugin_header, text='Plugins', style='Title.TLabel').pack(side='left')
        ttk.Button(plugin_header, text='Install Plugin File…', command=self.install_external_plugin).pack(side='right')
        self.plugin_tree = ttk.Treeview(plugins_tab, columns=('name', 'author', 'status'), show='headings', selectmode='browse')
        self.plugin_tree.heading('name', text='Plugin')
        self.plugin_tree.heading('author', text='Author')
        self.plugin_tree.heading('status', text='Status')
        self.plugin_tree.column('name', width=300)
        self.plugin_tree.column('author', width=180)
        self.plugin_tree.column('status', width=120, stretch=False)
        self.plugin_tree.pack(fill='both', expand=True, padx=10, pady=(0, 8))
        plugin_buttons = ttk.Frame(plugins_tab)
        plugin_buttons.pack(fill='x', padx=10, pady=(0, 10))
        ttk.Button(plugin_buttons, text='Install', command=self.install_selected_plugin).pack(side='left')
        ttk.Button(plugin_buttons, text='Uninstall', command=self.uninstall_selected_plugin).pack(side='left', padx=4)
        ttk.Button(plugin_buttons, text='Refresh', command=self.refresh_plugin_list).pack(side='left')
        ttk.Label(data_tab, text='BAML DATA / DEBUG').pack(anchor='w', padx=8, pady=8)
        data_nb = ttk.Notebook(data_tab)
        data_nb.pack(fill='both', expand=True, padx=8, pady=(0, 8))
        d1 = ttk.Frame(data_nb)
        d2 = ttk.Frame(data_nb)
        data_nb.add(d1, text='Animations')
        data_nb.add(d2, text='Raw Strings')
        ttk.Label(d1, text='Animation tracks are shown in Layout → Properties → Animations.').pack(padx=20, pady=20)
        ttk.Label(d2, text='Raw strings are shown in Layout → Properties → Raw.').pack(padx=20, pady=20)
        self.notebook.bind('<<NotebookTabChanged>>', self.on_notebook_tab_changed)
        for tabs in (self.notebook, props, data_nb):
            tabs.bind('<MouseWheel>', lambda e, book=tabs: self._wheel_tabs(book, e))
            tabs.bind('<Button-4>', lambda e, book=tabs: self._step_tab(book, -1))
            tabs.bind('<Button-5>', lambda e, book=tabs: self._step_tab(book, 1))
        self.root.bind('<Control-Tab>', lambda e: self._step_tab(self.notebook, 1))
        self.root.bind('<Control-Shift-Tab>', lambda e: self._step_tab(self.notebook, -1))
        self.root.bind('<Key-h>', lambda e: self.toggle_selected_hidden())
        self.root.bind('<Key-H>', lambda e: self.toggle_selected_hidden())
        self.root.bind('<Key-l>', lambda e: self.toggle_selected_locked())
        self.root.bind('<Key-L>', lambda e: self.toggle_selected_locked())
        self.root.bind('<Control-z>', self.undo)
        self.root.bind('<Control-Z>', self.undo)
        self.root.bind('<Control-s>', lambda e: self.save_current())
        self.root.after(50, self.poll)
        self.root.after(180, self._set_initial_pane_widths)
        self.load_default_background()
        self.set_appearance('dark')
        self.refresh_plugin_list()
        self._apply_installed_plugins()
        self.root.after(250, self._restore_last_session)
        self.root.after(450, self._maximize_window)

    def _scroll_vertical(self, canvas, event):
        canvas.yview_scroll(-1 if event.delta > 0 else 1, 'units')
        return 'break'

    def _scroll_horizontal(self, canvas, event):
        canvas.xview_scroll(-1 if event.delta > 0 else 1, 'units')
        return 'break'

    def _step_tab(self, notebook, delta):
        tabs = notebook.tabs()
        if tabs:
            notebook.select(tabs[(notebook.index('current') + delta) % len(tabs)])
        return 'break'

    def _wheel_tabs(self, notebook, event):
        try:
            if notebook.identify(event.x, event.y) == '':
                return None
        except Exception:
            return None
        return self._step_tab(notebook, -1 if event.delta > 0 else 1)

    def change_hud_scale(self):
        pct = simpledialog.askinteger('Communicator HUD Size', 'Preview-only HUD size (25–100%):',
                                      initialvalue=round(self.hud_preview_scale * 100), minvalue=25,
                                      maxvalue=100, parent=self.root)
        if pct is None:
            return
        self.hud_preview_scale = pct / 100.0
        self.resized_texture_cache.clear()
        self.resized_texture_cache_order.clear()
        self._save_settings_file()
        self.request_preview_render(1)

    def _maximize_window(self):
        if os.name == 'nt':
            try:
                self.root.state('zoomed')
            except tk.TclError:
                pass

    def _find_communicator(self):
        if os.name != 'nt':
            return ''
        roots = [os.path.join(os.environ.get('PROGRAMFILES(X86)', r'C:\Program Files (x86)'), 'Steam', 'steamapps', 'common', 'LEGO City Undercover')]
        for letter in 'CDEFGHIJKLMNOPQRSTUVWXYZ':
            roots.append(f'{letter}:/steam/steamapps/common/LEGO City Undercover')
            roots.append(f'{letter}:/SteamLibrary/steamapps/common/LEGO City Undercover')
        for root in roots:
            candidate = os.path.join(root, 'GUI', 'BLEND', 'COMMUNICATOR')
            if os.path.isfile(os.path.join(candidate, 'MAINWINDOW.BAML')):
                return candidate
        return ''

    def _restore_last_session(self):
        folder = self.settings_data.get('last_directory', '')
        if not os.path.isdir(folder):
            folder = self._find_communicator()
        if folder:
            self.open_directory(folder)

    def _remember_active_baml(self, path):
        self.restore_baml_name = os.path.basename(path)
        self.settings_data['last_baml'] = self.restore_baml_name
        if self._session_save_job is not None:
            try:
                self.root.after_cancel(self._session_save_job)
            except tk.TclError:
                pass
        self._session_save_job = self.root.after(400, self._save_settings_file)

    def _set_initial_pane_widths(self):
        """Set the initial sidebar widths."""
        try:
            total = max(900, self.main_panes.winfo_width())
            self.main_panes.sashpos(0, 250)
            self.main_panes.sashpos(1, max(600, total - 255))
        except Exception:
            pass

    def _load_settings_file(self):
        try:
            with open(self.settings_path, 'r', encoding='utf-8') as f:
                d = json.load(f)
                return d if isinstance(d, dict) else {}
        except Exception:
            return {}

    def _save_settings_file(self):
        self.settings_data['confirm_delete'] = bool(self.confirm_delete)
        self.settings_data['installed_plugins'] = sorted(self.installed_plugins)
        self.settings_data['hud_preview_scale'] = self.hud_preview_scale
        if self.root_dir:
            self.settings_data['last_directory'] = self.root_dir
        if self.restore_baml_name:
            self.settings_data['last_baml'] = self.restore_baml_name
        try:
            with open(self.settings_path, 'w', encoding='utf-8') as f:
                json.dump(self.settings_data, f, indent=2)
        except Exception:
            pass

    def reset_delete_confirmations(self):
        self.confirm_delete = True
        self._save_settings_file()
        self.status.set('Delete confirmations enabled again.')

    def _external_plugin_meta(self, path):
        name = os.path.splitext(os.path.basename(path))[0]
        author = 'Unknown'
        try:
            raw = open(path, 'r', encoding='utf-8', errors='ignore').read(8192)
            import re
            m = re.search('^PLUGIN_NAME\\s*=\\s*[\\\'\\"]([^\\\'\\"]+)', raw, re.M)
            if m:
                name = m.group(1)
            m = re.search('^PLUGIN_AUTHOR\\s*=\\s*[\\\'\\"]([^\\\'\\"]+)', raw, re.M)
            if m:
                author = m.group(1)
        except Exception:
            pass
        return {'id': 'external:' + os.path.abspath(path), 'name': name, 'author': author, 'path': path, 'builtin': False}

    def discover_plugins(self):
        plugins = [{'id': 'animation_editor', 'name': 'Animation Editor', 'author': 'xfrostyn', 'builtin': True}]
        self.external_plugins = {}
        try:
            for fn in os.listdir(self.plugins_dir):
                if fn.lower().endswith('.py'):
                    meta = self._external_plugin_meta(os.path.join(self.plugins_dir, fn))
                    plugins.append(meta)
                    self.external_plugins[meta['id']] = meta
        except Exception:
            pass
        return plugins

    def refresh_plugin_list(self):
        if not hasattr(self, 'plugin_tree'):
            return
        for i in self.plugin_tree.get_children():
            self.plugin_tree.delete(i)
        for meta in self.discover_plugins():
            status = 'Installed' if meta['id'] in self.installed_plugins else 'Not installed'
            self.plugin_tree.insert('', 'end', iid=meta['id'], values=(meta['name'], meta['author'], status))

    def install_external_plugin(self):
        path = filedialog.askopenfilename(title='Install XBAML plugin', filetypes=[('Python plugin', '*.py'), ('All files', '*.*')])
        if not path:
            return
        try:
            dst = os.path.join(self.plugins_dir, os.path.basename(path))
            shutil.copy2(path, dst)
            meta = self._external_plugin_meta(dst)
            self.installed_plugins.add(meta['id'])
            self._load_external_plugin(meta)
            self._save_settings_file()
            self.refresh_plugin_list()
            self.status.set('Installed plugin: ' + meta['name'])
        except Exception as e:
            messagebox.showerror('XBAML', 'Could not install plugin:\n' + str(e))

    def _load_external_plugin(self, meta):
        try:
            spec = importlib.util.spec_from_file_location('xbaml_plugin_' + str(abs(hash(meta['id']))), meta['path'])
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
            if hasattr(mod, 'register'):
                mod.register(self)
        except Exception as e:
            self.status.set('Plugin load failed: ' + str(e))

    def install_selected_plugin(self):
        sel = self.plugin_tree.selection()
        if not sel:
            return
        pid = sel[0]
        self.installed_plugins.add(pid)
        if pid == 'animation_editor':
            self._enable_animation_editor_plugin()
        elif pid in self.external_plugins:
            self._load_external_plugin(self.external_plugins[pid])
        self._save_settings_file()
        self.refresh_plugin_list()

    def uninstall_selected_plugin(self):
        sel = self.plugin_tree.selection()
        if not sel:
            return
        pid = sel[0]
        self.installed_plugins.discard(pid)
        if pid == 'animation_editor':
            self._disable_animation_editor_plugin()
        elif pid.startswith('external:'):
            meta = self.external_plugins.get(pid)
            if meta:
                try:
                    os.remove(meta['path'])
                except Exception:
                    pass
        self._save_settings_file()
        self.refresh_plugin_list()

    def _apply_installed_plugins(self):
        if 'animation_editor' in self.installed_plugins:
            self._enable_animation_editor_plugin()
        for pid in list(self.installed_plugins):
            if pid.startswith('external:') and pid in self.external_plugins:
                self._load_external_plugin(self.external_plugins[pid])

    def _enable_animation_editor_plugin(self):
        try:
            self.animation_editor_frame.pack(fill='x', padx=4, pady=(0, 4))
        except Exception:
            pass
        self.animation_editor_tab = True
        self._ae_refresh_all()

    def _disable_animation_editor_plugin(self):
        try:
            self.animation_editor_frame.pack_forget()
        except Exception:
            pass
        self.animation_editor_tab = None

    def on_notebook_tab_changed(self, event=None):
        if self._preview_is_visible():
            self.request_preview_render(5)
        elif self.playing:
            self.pause_playback()

    def _preview_is_visible(self):
        try:
            return self.notebook.nametowidget(self.notebook.select()) is self.preview_tab
        except Exception:
            return True

    def request_preview_render(self, delay=20):
        self.preview_dirty = True
        if not self._preview_is_visible():
            return
        self.schedule_preview_render(delay)

    def open_animation_editor(self):
        try:
            self.notebook.select(self.preview_tab)
            self.animation_editor_frame.pack(fill='x', padx=4, pady=(0, 4))
            self.ae_anim_combo.focus_set()
        except Exception:
            pass
        self._ae_refresh_all()

    def _close_animation_editor(self):
        return

    def _ae_anim_combo_changed(self):
        self._ae_refresh_detail()
        a = self._ae_current_anim()
        if a:
            self.preview_anim_var.set(a.get('name', ''))
            self._enable_animation_for_parsed(self.current, a.get('name', ''), True, exclusive_if_empty=False)
            self._refresh_multi_animation_menu()
            self.update_playback_controls()
            self.request_preview_render(5)

    def _anim_key(self, parsed, name):
        return (parsed.get('path', '') if parsed else '') + '\x00' + str(name)

    def _enable_animation_for_parsed(self, parsed, name, enabled=True, exclusive_if_empty=False):
        if not parsed or not name or name == '(raw node values)':
            return
        key = self._anim_key(parsed, name)
        if enabled:
            self.active_animation_keys.add(key)
        else:
            self.active_animation_keys.discard(key)

    def _active_animation_names_for(self, parsed):
        if not parsed:
            return []
        names = []
        for a in parsed.get('animations', []):
            name = a.get('name', '')
            if self._anim_key(parsed, name) in self.active_animation_keys:
                names.append(name)
        return names

    def _toggle_multi_animation(self, key, var):
        if bool(var.get()):
            self.active_animation_keys.add(key)
        else:
            self.active_animation_keys.discard(key)
        self._refresh_multi_animation_menu(rebuild=False)
        self.update_playback_controls()
        self.request_preview_render(1)

    def _refresh_multi_animation_menu(self, rebuild=True):
        if not hasattr(self, 'anim_multi_menu'):
            return
        parsed_files = self._selected_parsed_files()
        valid = set()
        if rebuild:
            self.anim_multi_menu.delete(0, 'end')
            self.anim_check_vars = {}
            total_anims = sum((len(p.get('animations', [])) for p in parsed_files))
            if total_anims == 0:
                self.anim_multi_menu.add_command(label='No animations', state='disabled')
            for p in parsed_files:
                base = os.path.basename(p.get('path', 'BAML'))
                for a in p.get('animations', []):
                    name = a.get('name', '')
                    key = self._anim_key(p, name)
                    valid.add(key)
                    v = tk.BooleanVar(value=key in self.active_animation_keys)
                    self.anim_check_vars[key] = v
                    label = f'{base}  ::  {name}' if len(parsed_files) > 1 else name
                    self.anim_multi_menu.add_checkbutton(label=label, variable=v, command=lambda k=key, vv=v: self._toggle_multi_animation(k, vv))
            self.active_animation_keys.intersection_update(valid)
        count = len(self.active_animation_keys)
        self.anim_multi_button.configure(text=f'Animations ({count}) ▾')

    def _ae_refresh_all(self):
        if not hasattr(self, 'ae_anim_combo'):
            return
        names = ['(raw node values)']
        if self.current:
            names += [a.get('name', 'Animation') for a in self.current.get('animations', [])]
        self.ae_anim_combo.configure(values=names)
        cur = self.preview_anim_var.get() if hasattr(self, 'preview_anim_var') else '(raw node values)'
        if cur in names:
            self.ae_anim_var.set(cur)
        else:
            self.ae_anim_var.set(names[0])
        if self.current is not None and self.selected_node is not None and (self.selected_node < len(self.current.get('nodes', []))):
            node = self.current['nodes'][self.selected_node]
            self.ae_target_var.set(node.get('name', ''))
            typ = TYPE_NAMES.get(node.get('type'), 'Node')
            self.ae_status.set(f"Plugin by xfrostyn · selected {typ}: {node.get('name', '')}")
        else:
            self.ae_target_var.set('Select an image')
            self.ae_status.set('Plugin by xfrostyn · select an image/node to animate')
        self._ae_refresh_detail()

    def _ae_current_anim_index(self):
        if not hasattr(self, 'ae_anim_combo'):
            return None
        try:
            i = self.ae_anim_combo.current()
            return i - 1 if i > 0 else None
        except Exception:
            return None

    def _ae_current_anim(self):
        i = self._ae_current_anim_index()
        if self.current is None or i is None or i >= len(self.current.get('animations', [])):
            return None
        return self.current['animations'][i]

    def _animation_max_time(self, anim):
        mx = 0.0
        for tr in anim.get('tracks', []):
            for k in tr.get('keys', []):
                mx = max(mx, parse_timecode(k.get('time', '0')))
        return mx

    def _fmt_timecode(self, sec):
        sec = max(0.0, float(sec))
        return '0:0:' + '{:.4f}'.format(sec).rstrip('0').rstrip('.') if sec else '0'

    def _ae_refresh_detail(self):
        if not hasattr(self, 'ae_status'):
            return
        a = self._ae_current_anim()
        if not a:
            self.ae_duration_var.set('1.0')
            return
        dur = self._animation_max_time(a)
        self.ae_duration_var.set(str(round(max(0.001, dur), 4)))

    def _ae_new_animation(self):
        if self.current is None:
            return
        name = simpledialog.askstring('New animation', 'Animation name:', initialvalue='NewAnimation', parent=self.root)
        if not name:
            return
        self.push_undo('New animation')
        self.current.setdefault('animations', []).append({'name': name, 'flags': (1, 0), 'tracks': []})
        self.current['structure_dirty'] = True
        self._ae_refresh_all()
        self.ae_anim_combo.current(len(self.current.get('animations', [])))
        self.ae_anim_var.set(name)
        self._ae_refresh_detail()
        self._refresh_animation_combo()

    def _ae_delete_animation(self):
        if self.current is None:
            return
        i = self._ae_current_anim_index()
        if i is None:
            return
        self.push_undo('Delete animation')
        del self.current['animations'][i]
        self.current['structure_dirty'] = True
        self._ae_refresh_all()
        self._refresh_animation_combo()

    def _ae_duration(self):
        try:
            return max(0.001, float(self.ae_duration_var.get()))
        except Exception:
            return 1.0

    def _ae_add_track(self, prop, start, end):
        a = self._ae_current_anim()
        target = self.ae_target_var.get()
        dur = self._ae_duration()
        if not a or not target:
            return
        self.push_undo('Animation effect')
        a['tracks'] = [tr for tr in a.get('tracks', []) if not (tr.get('target') == target and tr.get('property') == prop)]
        a['tracks'].append({'property': prop, 'target': target, 'unknown3': b'\x00\x00\x00', 'keys': [{'time': '0', 'value': float(start), 'flag': 0, 'ease': (0.0, 0.0, 1.0, 1.0)}, {'time': self._fmt_timecode(dur), 'value': float(end), 'flag': 0, 'ease': (0.0, 0.0, 1.0, 1.0)}]})
        self.current['structure_dirty'] = True
        self._ae_refresh_detail()
        self._refresh_animation_combo()
        self.request_preview_render()

    def _ae_fade_in(self):
        self._ae_add_track(6, 0, 1)

    def _ae_fade_out(self):
        self._ae_add_track(6, 1, 0)

    def _ae_rotate(self):
        self._ae_add_track(5, 0, 360)

    def _ae_scale(self, end):
        self._ae_add_track(3, 1, end)
        self._ae_add_track(4, 1, end)

    def _ae_change_speed(self):
        a = self._ae_current_anim()
        if not a:
            return
        speed = simpledialog.askfloat('Change speed', 'Speed multiplier (2 = twice as fast, 0.5 = half speed):', initialvalue=2.0, minvalue=0.01, parent=self.root)
        if not speed:
            return
        self.push_undo('Animation speed')
        for tr in a.get('tracks', []):
            for k in tr.get('keys', []):
                k['time'] = self._fmt_timecode(parse_timecode(k.get('time', '0')) / speed)
        self.current['structure_dirty'] = True
        self._ae_refresh_detail()
        self._refresh_animation_combo()
        self.request_preview_render()

    def _interpolate_track_at(self, tr, t):
        return self.evaluate_track_value(tr, t)

    def _ae_split_scene(self):
        a = self._ae_current_anim()
        idx = self._ae_current_anim_index()
        if not a or idx is None:
            return
        split = float(self.get_preview_time())
        dur = self._animation_max_time(a)
        if split <= 0 or split >= dur:
            messagebox.showinfo('Split scene', 'Move the playhead somewhere inside the animation first.', parent=self.root)
            return
        self.push_undo('Split animation')
        a1 = copy.deepcopy(a)
        a2 = copy.deepcopy(a)
        a1['name'] = a['name'] + '_Part1'
        a2['name'] = a['name'] + '_Part2'
        for source, dest, second in [(a, a1, False), (a, a2, True)]:
            dest['tracks'] = []
            for tr in source.get('tracks', []):
                val = self._interpolate_track_at(tr, split)
                nt = copy.deepcopy(tr)
                keys = []
                if second:
                    keys.append({'time': '0', 'value': float(val), 'flag': 0, 'ease': (0.0, 0.0, 1.0, 1.0)})
                    for k in tr.get('keys', []):
                        tt = parse_timecode(k.get('time', '0'))
                        if tt > split:
                            kk = copy.deepcopy(k)
                            kk['time'] = self._fmt_timecode(tt - split)
                            keys.append(kk)
                else:
                    for k in tr.get('keys', []):
                        tt = parse_timecode(k.get('time', '0'))
                        if tt < split:
                            keys.append(copy.deepcopy(k))
                    keys.append({'time': self._fmt_timecode(split), 'value': float(val), 'flag': 0, 'ease': (0.0, 0.0, 1.0, 1.0)})
                nt['keys'] = keys
                dest['tracks'].append(nt)
        self.current['animations'][idx:idx + 1] = [a1, a2]
        self.current['structure_dirty'] = True
        self._ae_refresh_all()
        self._refresh_animation_combo()

    def _refresh_animation_combo(self):
        if not self.current:
            return
        self.anim_names = ['(raw node values)'] + [a.get('name', '') for a in self.current.get('animations', [])]
        self.preview_anim_combo.configure(values=self.anim_names)
        if self.preview_anim_var.get() not in self.anim_names:
            self.preview_anim_var.set(self.anim_names[0])
        self.update_playback_controls()
        self._ae_refresh_all()
        self._refresh_multi_animation_menu()

    def _ae_apply_preview(self):
        a = self._ae_current_anim()
        if not a:
            return
        self.preview_anim_var.set(a.get('name', ''))
        self._enable_animation_for_parsed(self.current, a.get('name', ''), True)
        self._refresh_multi_animation_menu()
        self.notebook.select(self.preview_tab)
        self.request_preview_render(5)

    def choose_dir(self):
        d = filedialog.askdirectory(title='Select LCU UI/BAML directory', initialdir=self.root_dir or None)
        if d:
            self.open_directory(d)

    def open_directory(self, d):
        self.root_dir = d
        self._save_settings_file()
        self.path_var.set(d)
        self.scan_token += 1
        token = self.scan_token
        self.baml_paths = []
        self.tex_index = {}
        self.baml_list.delete(0, 'end')
        [self.node_list.delete(i) for i in self.node_list.get_children()]
        self.status.set('Scanning in background…')
        threading.Thread(target=self.scan_worker, args=(d, token), daemon=True).start()

    def scan_worker(self, d, token):
        bamls = []
        tex = {}
        seen = 0
        try:
            for base, dirs, files in os.walk(d):
                dirs[:] = [x for x in dirs if x not in ('.git', '__pycache__')]
                for fn in files:
                    path = os.path.join(base, fn)
                    ext = os.path.splitext(fn)[1].upper()
                    if ext == '.BAML':
                        bamls.append(path)
                    elif ext in ('.TEX', '.DDS'):
                        tex.setdefault(normalize_tex_name(path), []).append(path)
                    seen += 1
                    if seen % 500 == 0:
                        self.q.put(('scan_progress', token, len(bamls), len(tex)))
            bamls.sort(key=lambda p: p.lower())
            self.q.put(('scan_done', token, bamls, tex))
        except Exception as e:
            self.q.put(('error', f'Scan failed: {e}'))

    def _active_baml_index(self):
        sel = self.baml_list.curselection()
        if not sel:
            return None
        try:
            active = int(self.baml_list.index(tk.ACTIVE))
            if active in sel:
                return active
        except Exception:
            pass
        return sel[-1]

    def on_baml_click_release(self, event=None):
        try:
            idx = self.baml_list.nearest(event.y) if event is not None else None
            if idx is not None and idx in self.baml_list.curselection():
                self.baml_list.activate(idx)
        except Exception:
            pass
        self.on_baml()

    def on_baml(self, _=None):
        sel = self.baml_list.curselection()
        if not sel:
            return
        self.selected_baml_paths = [self.baml_paths[i] for i in sel if 0 <= i < len(self.baml_paths)]
        idx = self._active_baml_index()
        if idx is None or idx >= len(self.baml_paths):
            return
        path = self.baml_paths[idx]
        self.parse_token += 1
        token = self.parse_token
        selected_count = len(self.selected_baml_paths)
        self._remember_active_baml(path)
        self.status.set(f'Parsing BAML… ({selected_count} selected)' if selected_count > 1 else 'Parsing BAML…')
        [self.node_list.delete(i) for i in self.node_list.get_children()]
        threading.Thread(target=self.parse_worker, args=(path, token), daemon=True).start()

    def parse_worker(self, path, token):
        try:
            self.q.put(('parse_done', token, parse_baml(path)))
        except Exception as e:
            self.q.put(('error', f'Parse failed: {e}'))

    def _selected_node_indices(self):
        out = []
        try:
            for row in self.node_list.selection():
                try:
                    out.append(int(row))
                except Exception:
                    pass
        except Exception:
            pass
        return sorted(set(out))

    def on_node(self, _=None):
        if not self.current:
            return
        sels = self._selected_node_indices()
        if not sels:
            return
        try:
            focus = self.node_list.focus()
            i = int(focus) if focus else sels[-1]
            if i not in sels:
                i = sels[-1]
        except Exception:
            i = sels[-1]
        if i >= len(self.current['nodes']):
            return
        self.selected_node = i
        n = self.current['nodes'][i]
        for k in self.fields:
            self.fields[k].set(str(n[k]))
        pivx = approx_pivot_value(n['pivots'][0])
        pivy = approx_pivot_value(n['pivots'][2] if len(n['pivots']) > 2 else 0)
        is_hidden = self._node_hidden_in_preview(self.current, i)
        is_locked = self._node_locked(self.current, i)
        self.visibility_button.configure(text='👁̸ Hidden' if is_hidden else '👁 Visible')
        self.lock_button.configure(text='🔒 Locked' if is_locked else '🔓 Unlocked')
        for key, ent in self.field_entries.items():
            ent.configure(state='disabled' if is_locked and key in ('width', 'height', 'x', 'y', 'sx', 'sy', 'rotation') else 'normal')
        lines = [f"Name: {n['name']}", f"Type: {TYPE_NAMES.get(n['type'], n['type'])}", f'Selected nodes: {len(sels)}', f"Size: {n['width']} × {n['height']}", f'Approx pivot: ({pivx:.3f}, {pivy:.3f})']
        if n['texture']:
            lines.append('Texture ref: ' + n['texture'])
        if n['component']:
            lines.append('Component: ' + n['component'])
        if n['text']:
            lines.append('Text: ' + n['text'])
        self.set_text(self.info, '\n'.join(lines))
        if hasattr(self, 'ae_target_var'):
            self.ae_target_var.set(n.get('name', ''))
            self.ae_status.set(f"Plugin by xfrostyn · selected {TYPE_NAMES.get(n.get('type'), 'Node')}: {n.get('name', '')}")
        self.draw_selection_overlay()

    def draw_selection_overlay(self):
        canvas = getattr(self, 'preview_canvas', None)
        if canvas is None:
            return
        try:
            canvas.delete('selection_overlay')
        except Exception:
            return
        if self.current is None or self.selected_node is None or self.selected_node >= len(self.current.get('nodes', [])):
            return
        if self._node_hidden_in_preview(self.current, self.selected_node):
            return
        pts = self._selected_preview_corners()
        if not pts:
            return
        flat = [v for pt in pts for v in pt]
        canvas.create_polygon(*flat, outline='#ff8a00', fill='', width=2, tags='selection_overlay')
        hx, hy = pts[2]
        hs = 6
        canvas.create_rectangle(hx - hs, hy - hs, hx + hs, hy + hs, fill='#ff8a00', outline='#f0f0f0', width=1, tags='selection_overlay')
        if getattr(self, 'show_labels_var', None) is not None and self.show_labels_var.get():
            x1 = min((x for x, y in pts))
            y1 = min((y for x, y in pts))
            n = self.current['nodes'][self.selected_node]
            canvas.create_text(x1 + 5, y1 - 12, text=n.get('name', ''), anchor='w', fill='#ff8a00', font=('Segoe UI', 9, 'bold'), tags='selection_overlay')

    def _apply_dark_titlebar(self, dark):
        if os.name != 'nt':
            return
        try:
            import ctypes
            from ctypes import wintypes
            hwnd = self.root.winfo_id()
            parent = ctypes.windll.user32.GetParent(hwnd)
            if parent:
                hwnd = parent
            dwm = ctypes.windll.dwmapi.DwmSetWindowAttribute
            enabled = ctypes.c_int(1 if dark else 0)
            for attribute in (20, 19):
                if dwm(wintypes.HWND(hwnd), attribute,
                       ctypes.byref(enabled), ctypes.sizeof(enabled)) == 0:
                    break
        except (AttributeError, OSError, ValueError):
            pass

    def set_appearance(self, mode):
        self.appearance = mode
        dark = mode == 'dark'
        bg = '#303030' if dark else '#e8e8e8'
        panel = '#252525' if dark else '#f4f4f4'
        field = '#1d1d1d' if dark else '#ffffff'
        header = '#1f1f1f' if dark else '#d8d8d8'
        fg = '#d8d8d8' if dark else '#151515'
        muted = '#a7a7a7' if dark else '#555555'
        accent = '#e87921'
        active = '#3b3b3b' if dark else '#d5d5d5'
        border = '#4a4a4a' if dark else '#b5b5b5'
        arrow = '#d1d1d1' if dark else '#333333'
        style = ttk.Style(self.root)
        try:
            style.theme_use('clam')
        except tk.TclError:
            pass

        style.configure('.', background=bg, foreground=fg, fieldbackground=field,
                        font=('Segoe UI', 9))
        style.configure('TFrame', background=bg)
        style.configure('TLabel', background=bg, foreground=fg)
        style.configure('Accent.TLabel', background=bg, foreground=accent,
                        font=('Segoe UI', 9, 'bold'))
        style.configure('Title.TLabel', background=bg, foreground=fg,
                        font=('Segoe UI', 12, 'bold'))
        style.configure('TPanedwindow', background=bg)
        style.configure('Sash', background=border)

        style.configure('TButton', background=panel, foreground=fg, borderwidth=0,
                        relief='flat', padding=(7, 4))
        style.map('TButton', background=[('pressed', active), ('active', active)],
                  foreground=[('disabled', muted)])

        # Read-only fields need an explicit state map; their default state
        # colours otherwise come from the operating system's light palette.
        style.configure('TEntry', fieldbackground=field, background=field,
                        foreground=fg, insertcolor=fg, bordercolor=border,
                        lightcolor=border, darkcolor=border, padding=2)
        style.map('TEntry', fieldbackground=[('disabled', field),
                                            ('readonly', field)],
                  foreground=[('disabled', muted), ('readonly', fg)],
                  bordercolor=[('focus', accent)])
        style.configure('TCombobox', background=panel, fieldbackground=field,
                        foreground=fg, arrowcolor=arrow, arrowsize=12,
                        bordercolor=border, lightcolor=border, darkcolor=border,
                        selectbackground=accent, selectforeground='#ffffff')
        style.map('TCombobox', fieldbackground=[('readonly', field),
                                               ('disabled', field)],
                  background=[('active', active), ('readonly', panel)],
                  foreground=[('readonly', fg), ('disabled', muted)],
                  arrowcolor=[('disabled', muted), ('active', fg)],
                  selectbackground=[('readonly', field)],
                  selectforeground=[('readonly', fg)])
        style.configure('TMenubutton', background=panel, foreground=fg,
                        arrowcolor=arrow, padding=(6, 3), borderwidth=0)
        style.map('TMenubutton', background=[('active', active), ('pressed', active)],
                  arrowcolor=[('active', fg)])
        style.configure('TCheckbutton', background=bg, foreground=fg,
                        indicatorcolor=field, bordercolor=border)
        style.map('TCheckbutton', background=[('active', bg)],
                  foreground=[('disabled', muted)],
                  indicatorcolor=[('selected', accent), ('!selected', field)])

        style.configure('Treeview', background=field, fieldbackground=field,
                        foreground=fg, rowheight=22, borderwidth=0)
        style.map('Treeview', background=[('selected', accent)],
                  foreground=[('selected', '#ffffff')])
        style.configure('Treeview.Heading', background=header, foreground=muted,
                        relief='flat', padding=(4, 3))
        style.map('Treeview.Heading', background=[('active', active)])
        style.configure('TNotebook', background=header, borderwidth=0)
        style.configure('TNotebook.Tab', background=header, foreground=muted,
                        padding=(12, 5), borderwidth=0)
        style.map('TNotebook.Tab', background=[('selected', active), ('active', panel)],
                  foreground=[('selected', fg), ('active', fg)])

        for orientation in ('Vertical', 'Horizontal'):
            name = orientation + '.TScrollbar'
            style.configure(name, background=panel, troughcolor=field,
                            arrowcolor=arrow, bordercolor=bg,
                            lightcolor=panel, darkcolor=panel,
                            gripcount=0, arrowsize=11, relief='flat')
            style.map(name, background=[('pressed', active), ('active', active)],
                      arrowcolor=[('active', fg)])
        style.configure('TScrollbar', background=panel, troughcolor=field,
                        arrowcolor=arrow, bordercolor=bg, gripcount=0,
                        relief='flat')

        self.root.option_add('*TCombobox*Listbox.background', field)
        self.root.option_add('*TCombobox*Listbox.foreground', fg)
        self.root.option_add('*TCombobox*Listbox.selectBackground', accent)
        self.root.option_add('*TCombobox*Listbox.selectForeground', '#ffffff')
        self.root.option_add('*Menu.background', panel)
        self.root.option_add('*Menu.foreground', fg)
        self.root.option_add('*Menu.activeBackground', accent)
        self.root.option_add('*Menu.activeForeground', '#ffffff')

        for menu in getattr(self, 'theme_menus', ()):
            try:
                menu.configure(bg=panel, fg=fg, activebackground=accent,
                               activeforeground='#ffffff', selectcolor=accent,
                               borderwidth=0, relief='flat')
            except tk.TclError:
                pass

        for widget in (getattr(self, 'info', None),
                       getattr(self, 'anim_text', None),
                       getattr(self, 'raw_text', None)):
            if widget is not None:
                widget.configure(bg=field, fg=fg, insertbackground=fg,
                                 selectbackground=accent, selectforeground='#ffffff',
                                 relief='flat', highlightthickness=0)
        self.baml_list.configure(bg=field, fg=fg, selectbackground=accent,
                                 selectforeground='#ffffff', activestyle='none')
        for canvas in (getattr(self, 'property_canvas', None),
                       getattr(self, 'anim_canvas', None)):
            if canvas is not None:
                canvas.configure(bg=bg)
        # The central preview retains its own near-black backdrop.
        self.preview_canvas.configure(bg='#101010')
        self.playback_slider.configure(bg=panel, fg=fg, troughcolor=field,
                                       activebackground=active,
                                       highlightbackground=bg, relief='flat',
                                       sliderrelief='flat', bd=0, showvalue=False)
        self.root.configure(bg=bg)
        self._apply_dark_titlebar(dark)
        self._save_settings_file()
        self.status.set(('Dark' if dark else 'Light') + ' theme')

    def push_undo(self, label='Edit'):
        if self.current is None:
            return
        path = self.current.get('path', '')
        snap = {'label': label, 'current': copy.deepcopy(self.current), 'hidden': set(self.hidden_nodes_by_path.get(path, set())), 'locked': set(self.locked_nodes_by_path.get(path, set())), 'selected': self.selected_node}
        self.undo_stack.append(snap)
        if len(self.undo_stack) > self.max_undo:
            self.undo_stack.pop(0)

    def undo(self, event=None):
        if not self.undo_stack:
            return 'break'
        snap = self.undo_stack.pop()
        self.current = snap['current']
        path = self.current.get('path', '')
        self.hidden_nodes_by_path[path] = set(snap['hidden'])
        self.locked_nodes_by_path[path] = set(snap['locked'])
        self.selected_node = snap['selected'] if snap['selected'] is None or snap['selected'] < len(self.current.get('nodes', [])) else None
        self.refresh_current_ui(select_index=self.selected_node)
        self.status.set('Undid: ' + snap['label'])
        return 'break'

    def on_layer_click(self, event):
        row = self.node_list.identify_row(event.y)
        col = self.node_list.identify_column(event.x)
        if not row:
            return
        try:
            idx = int(row)
        except Exception:
            return
        ctrl = bool(event.state & 4)
        shift = bool(event.state & 1)
        if col in ('#1', '#2'):
            if row not in self.node_list.selection():
                self.node_list.selection_set(row)
            self.node_list.focus(row)
            self.selected_node = idx
            if col == '#1':
                self.toggle_selected_hidden()
                return 'break'
            if col == '#2':
                self.toggle_selected_locked()
                return 'break'
        return None

    def _subtree_end(self, idx):
        nodes = self.current.get('nodes', [])
        end = idx + 1
        while end < len(nodes):
            p = nodes[end].get('parent_index')
            cur = p
            inside = False
            while cur is not None:
                if cur == idx:
                    inside = True
                    break
                cur = nodes[cur].get('parent_index') if 0 <= cur < len(nodes) else None
            if not inside:
                break
            end += 1
        return end

    def add_node(self):
        if self.current is None:
            return
        typ = simpledialog.askstring('Add node', 'Type: image, group, text, or component', initialvalue='image', parent=self.root)
        if not typ:
            return
        typ = typ.strip().lower()
        mapping = {'group': 0, 'image': 1, 'component': 2, 'text': 3}
        if typ not in mapping:
            messagebox.showerror('Add node', 'Use image, group, text, or component.')
            return
        name = simpledialog.askstring('Add node', 'Node name:', initialvalue='NewImage' if typ == 'image' else 'New' + typ.title(), parent=self.root)
        if not name:
            return
        self.push_undo('Add node')
        parent = 0
        insert_at = len(self.current['nodes'])
        if self.selected_node is not None:
            sn = self.current['nodes'][self.selected_node]
            if sn.get('type') == 0:
                parent = self.selected_node
                insert_at = self._subtree_end(self.selected_node)
            else:
                parent = sn.get('parent_index')
                parent = 0 if parent is None else parent
                insert_at = self._subtree_end(self.selected_node)
        n = {'name': name, 'type': mapping[typ], 'width': 128.0, 'height': 128.0, 'x': 0.0, 'y': 0.0, 'sx': 1.0, 'sy': 1.0, 'rotation': 0.0, 'opacity': 1.0, 'pivots': (0, 0, 0), 'texture': '', 'component': '', 'text': '', 'parent_index': parent}
        if typ == 'text':
            n.update({'text': 'New Text', 'text_color_raw': 4294967295, 'font_size': 24.0, 'text_style': (0, 0)})
        if typ == 'component':
            n['component'] = ''
        self.current['nodes'].insert(insert_at, n)
        for j, node in enumerate(self.current['nodes']):
            if j == insert_at:
                continue
            p = node.get('parent_index')
            if p is not None and p >= insert_at:
                node['parent_index'] = p + 1
        self.current['structure_dirty'] = True
        self.selected_node = insert_at
        self.refresh_current_ui(select_index=insert_at)
        self.status.set('Added ' + typ + ' node in memory. Save to write the rebuilt BAML.')

    def _confirm_delete_nodes(self, count):
        if not self.confirm_delete:
            return True
        result = {'ok': False}
        dlg = tk.Toplevel(self.root)
        dlg.title('Delete')
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)
        ttk.Label(dlg, text=f'Delete {count} selected node' + ('s' if count != 1 else '') + ' and their children?', font=('Segoe UI', 10, 'bold')).pack(padx=22, pady=(18, 10))
        row = ttk.Frame(dlg)
        row.pack(padx=18, pady=(0, 18))

        def close(ok, never=False):
            result['ok'] = ok
            if never:
                self.confirm_delete = False
                self._save_settings_file()
            dlg.destroy()
        ttk.Button(row, text='Delete', command=lambda: close(True)).pack(side='left')
        ttk.Button(row, text='Delete + Never show again', command=lambda: close(True, True)).pack(side='left', padx=6)
        ttk.Button(row, text='Cancel', command=lambda: close(False)).pack(side='left')
        dlg.protocol('WM_DELETE_WINDOW', lambda: close(False))
        self.root.wait_window(dlg)
        return result['ok']

    def delete_selected_node(self):
        if self.current is None:
            return
        roots = [i for i in self._selected_node_indices() if i < len(self.current['nodes']) and self.current['nodes'][i].get('name') != 'LayoutRoot']
        if not roots:
            return
        if not self._confirm_delete_nodes(len(roots)):
            return
        self.push_undo('Delete nodes')
        nodes = self.current['nodes']
        delete = set()
        for root in roots:
            for i in range(root, self._subtree_end(root)):
                delete.add(i)
        deleted_names = {nodes[i].get('name', '') for i in delete}
        mapping = {}
        new_nodes = []
        for old, n in enumerate(nodes):
            if old in delete:
                continue
            mapping[old] = len(new_nodes)
            new_nodes.append(n)
        for old, n in zip([i for i in range(len(nodes)) if i not in delete], new_nodes):
            p = n.get('parent_index')
            n['parent_index'] = mapping.get(p) if p is not None else None
        self.current['nodes'] = new_nodes
        for a in self.current.get('animations', []):
            a['tracks'] = [tr for tr in a.get('tracks', []) if tr.get('target') not in deleted_names]
        self.current['structure_dirty'] = True
        self.selected_node = None
        self.refresh_current_ui()
        self.status.set(f'Deleted {len(delete)} node(s) in memory. Ctrl+Z restores them; Save writes changes.')

    def _hidden_set_for(self, parsed=None):
        parsed = parsed or self.current
        if not parsed:
            return set()
        path = parsed.get('path', '')
        return self.hidden_nodes_by_path.setdefault(path, set())

    def _node_hidden_in_preview(self, parsed, idx):
        if not parsed or idx < 0 or idx >= len(parsed.get('nodes', [])):
            return False
        hidden = self._hidden_set_for(parsed)
        cur = idx
        seen = set()
        while cur is not None and cur not in seen:
            seen.add(cur)
            if cur in hidden:
                return True
            node = parsed['nodes'][cur]
            cur = node.get('parent_index')
        return False

    def toggle_selected_hidden(self):
        if self.current is None:
            return
        inds = [i for i in self._selected_node_indices() if self.current['nodes'][i].get('name') != 'LayoutRoot']
        if not inds and self.selected_node is not None:
            inds = [self.selected_node]
        if not inds:
            return
        self.push_undo('Visibility')
        hidden = self._hidden_set_for(self.current)
        hide = any((i not in hidden for i in inds))
        for i in inds:
            if hide:
                hidden.add(i)
            else:
                hidden.discard(i)
        self.status.set(('Hidden ' if hide else 'Shown ') + f'{len(inds)} node(s) in preview.')
        self.refresh_current_ui(select_indices=inds)
        self.request_preview_render()

    def show_all_hidden(self):
        if self.current is None:
            return
        self._hidden_set_for(self.current).clear()
        self.status.set('All editor-hidden nodes are visible again.')
        self.refresh_current_ui(select_index=self.selected_node)

    def _locked_set_for(self, parsed=None):
        parsed = parsed or self.current
        if not parsed:
            return set()
        path = parsed.get('path', '')
        return self.locked_nodes_by_path.setdefault(path, set())

    def _node_locked(self, parsed, idx):
        if not parsed or idx is None:
            return False
        return idx in self._locked_set_for(parsed)

    def toggle_selected_locked(self):
        if self.current is None:
            return
        inds = [i for i in self._selected_node_indices() if self.current['nodes'][i].get('name') != 'LayoutRoot']
        if not inds and self.selected_node is not None:
            inds = [self.selected_node]
        if not inds:
            return
        self.push_undo('Lock')
        locked = self._locked_set_for(self.current)
        do_lock = any((i not in locked for i in inds))
        for i in inds:
            if do_lock:
                locked.add(i)
            else:
                locked.discard(i)
        self.status.set(('Locked ' if do_lock else 'Unlocked ') + f'{len(inds)} node(s).')
        self.refresh_current_ui(select_indices=inds)

    def unlock_all(self):
        if self.current is None:
            return
        self._locked_set_for(self.current).clear()
        self.status.set('All nodes unlocked.')
        self.refresh_current_ui(select_index=self.selected_node)

    def set_selected_invisible(self):
        if self.current is None:
            return
        inds = self._selected_node_indices() or ([self.selected_node] if self.selected_node is not None else [])
        if not inds:
            return
        self.push_undo('Set invisible')
        for i in inds:
            self.current['nodes'][i]['opacity'] = 0.0
        if self.selected_node is not None:
            self.fields['opacity'].set('0.0')
        self.status.set(f'Opacity set to 0 for {len(inds)} node(s). Save to write it into the BAML.')
        self.request_preview_render()

    def load_default_background(self):
        candidate = Path(__file__).with_name('preview_background.png')
        special = Path(__file__).with_name('MAINFRAME_SCREENBG_CENT_DX11.TEX')
        if PIL_OK and special.exists():
            try:
                self.nonstandard_background_pil = Image.open(str(special)).convert('RGBA')
                self.nonstandard_background_pil.load()
                self.nonstandard_background_path = str(special)
            except Exception:
                self.nonstandard_background_pil = None
                self.nonstandard_background_path = ''
        if candidate.exists():
            self.set_background_path(str(candidate))
        else:
            self.preview_note.set('No preview background loaded')
            self.render_layout_preview()

    def choose_background(self):
        path = filedialog.askopenfilename(title='Select preview background image', filetypes=[('Image files', '*.png;*.jpg;*.jpeg;*.bmp;*.webp'), ('All files', '*.*')])
        if path:
            self.set_background_path(path)

    def set_background_path(self, path):
        self.background_path = path
        if not PIL_OK:
            self.preview_note.set('Background chosen, but Pillow is required for preview')
            self.render_layout_preview()
            return
        try:
            im = Image.open(path).convert('RGBA')
            self.background_pil = im
            self.preview_note.set('Background: ' + os.path.basename(path))
        except Exception as e:
            self.background_pil = None
            self.preview_note.set('Failed to load background: ' + str(e))
        self.render_layout_preview()

    def _parsed_layout_size(self, parsed):
        if parsed and parsed.get('nodes'):
            root = parsed['nodes'][0]
            w = float(root.get('width', 0) or 0)
            h = float(root.get('height', 0) or 0)
            if w > 0 and h > 0:
                return (w, h)
        return (0.0, 0.0)

    def _selected_parsed_files(self):
        paths = list(self.selected_baml_paths or [])
        if not paths and self.current and self.current.get('path'):
            paths = [self.current['path']]
        out = []
        curpath = self.current.get('path') if self.current else None
        for path in paths:
            parsed = None
            if curpath and os.path.normcase(path) == os.path.normcase(curpath):
                parsed = self.current
            else:
                parsed = self.parsed_cache.get(path)
            if parsed is None:
                try:
                    parsed = parse_baml(path)
                    self.parsed_cache[path] = parsed
                except Exception:
                    parsed = None
            if parsed is not None:
                out.append(parsed)
        return out

    def get_layout_size(self):
        selected = self._selected_parsed_files()
        sizes = [self._parsed_layout_size(p) for p in selected]
        sizes = [x for x in sizes if x[0] > 0 and x[1] > 0]
        if sizes:
            return (max((x[0] for x in sizes)), max((x[1] for x in sizes)))
        if self.background_pil is not None:
            return self.background_pil.size
        return (1280.0, 720.0)

    def _active_layout_size(self):
        sz = self._parsed_layout_size(self.current)
        return sz if sz[0] > 0 and sz[1] > 0 else self.get_layout_size()

    def _is_standard_layout(self, size):
        w, h = size
        return abs(w - 1280.0) < 0.5 and abs(h - 720.0) < 0.5 or (abs(w - 1920.0) < 0.5 and abs(h - 1080.0) < 0.5)

    def _context_background(self):
        if not self._is_standard_layout(self.get_layout_size()) and self.nonstandard_background_pil is not None:
            return (self.nonstandard_background_pil, self.nonstandard_background_path)
        return (self.background_pil, self.background_path)

    def get_preview_resolution(self):
        sel = self.preview_res_var.get() if hasattr(self, 'preview_res_var') else 'Auto (BAML aspect)'
        if sel in ('Use layout root', 'Auto (BAML aspect)'):
            return self.get_layout_size()
        try:
            w, h = sel.lower().split('x', 1)
            return (float(w), float(h))
        except Exception:
            return (1920.0, 1080.0)

    def get_logical_resolution(self):
        return self.get_layout_size()

    def resolve_texture_path(self, ref, parsed_path=None):
        if not ref:
            return None
        base_path = parsed_path or (self.current.get('path') if self.current else None)
        if base_path:
            folder = os.path.dirname(base_path)
            ref_name = os.path.splitext(os.path.basename(ref.replace('\\', '/')))[0]
            candidates = [os.path.join(folder, ref.replace('\\', os.sep).replace('/', os.sep)), os.path.join(folder, 'IMAGES', ref_name + '_DX11.TEX'), os.path.join(folder, 'Images', ref_name + '_DX11.TEX'), os.path.join(folder, 'IMAGES', ref_name + '.TEX'), os.path.join(folder, 'Images', ref_name + '.TEX'), os.path.join(folder, 'IMAGES', ref_name + '.DDS'), os.path.join(folder, 'Images', ref_name + '.DDS')]
            for c in candidates:
                if os.path.isfile(c):
                    return c
        matches = self.tex_index.get(normalize_tex_name(ref), [])
        return matches[0] if matches else None

    def load_texture_pil(self, ref, parsed_path=None):
        path = self.resolve_texture_path(ref, parsed_path)
        if not path or not PIL_OK:
            return None
        if path in self.texture_pil_cache:
            return self.texture_pil_cache[path]
        try:
            raw = open(path, 'rb').read()
            im = Image.open(io.BytesIO(raw)).convert('RGBA')
            im.load()
            self.texture_pil_cache[path] = im
            return im
        except Exception:
            return None

    def resolve_component_baml(self, name):
        if not name:
            return None
        key = os.path.splitext(os.path.basename(name))[0].upper()
        return self.baml_index.get(key)

    def load_component_baml(self, name):
        path = self.resolve_component_baml(name)
        if not path:
            return None
        if path in self.parsed_cache:
            return self.parsed_cache[path]
        try:
            r = parse_baml(path)
            self.parsed_cache[path] = r
            return r
        except Exception:
            return None

    def get_animation_duration(self, anim=None):
        if anim is None:
            anim = self.get_selected_animation()
        if not anim:
            return 0.0
        mx = 0.0
        for tr in anim.get('tracks', []):
            for k in tr.get('keys', []):
                mx = max(mx, parse_timecode(k.get('time', '0')))
        return mx

    def update_playback_controls(self):
        active = []
        for p in self._selected_parsed_files():
            names = set(self._active_animation_names_for(p))
            active.extend((a for a in p.get('animations', []) if a.get('name') in names))
        anim = self.get_selected_animation()
        if not active and anim:
            active = [anim]
        self.animation_duration = max([self.get_animation_duration(a) for a in active] or [0.0])
        try:
            cur = max(0.0, float(self.preview_time_var.get()))
        except Exception:
            cur = 0.0
        if self.animation_duration > 0:
            cur = min(cur, self.animation_duration)
            self.playback_slider.configure(from_=0.0, to=self.animation_duration, resolution=max(0.001, self.animation_duration / 5000.0))
        else:
            cur = 0.0
            self.playback_slider.configure(from_=0.0, to=1.0, resolution=0.001)
        self.updating_time_controls = True
        try:
            self._set_slider_programmatic(cur)
        finally:
            self.updating_time_controls = False
        self.preview_time_numeric = cur
        self.playback_time_label.set(f'{cur:.3f} / {self.animation_duration:.3f} s')
        state = 'normal' if self.animation_duration > 0 else 'disabled'
        try:
            self.play_button.configure(state=state)
        except Exception:
            pass

    def _set_slider_programmatic(self, value):
        try:
            self.playback_slider.configure(command='')
            self.playback_slider.set(value)
        except Exception:
            pass
        finally:
            try:
                self.playback_slider.configure(command=self.on_playback_slider)
            except Exception:
                pass

    def set_preview_time(self, value, render=True):
        try:
            value = float(value)
        except Exception:
            value = 0.0
        if self.animation_duration > 0:
            value = max(0.0, min(value, self.animation_duration))
        else:
            value = max(0.0, value)
        self.preview_time_numeric = value
        self.updating_time_controls = True
        try:
            self.preview_time_var.set(f'{value:.4f}'.rstrip('0').rstrip('.') if value else '0')
            try:
                self._set_slider_programmatic(value)
            except Exception:
                pass
        finally:
            self.updating_time_controls = False
        self.playback_time_label.set(f'{value:.3f} / {self.animation_duration:.3f} s')
        if render:
            self.render_layout_preview()

    def _set_playback_time_fast(self, value, now=None, force_ui=False):
        """Advance the render clock without making Tk redraw the slider 60 times/sec.

        The scene still renders at the target FPS; the comparatively expensive
        Scale/StringVar widgets are refreshed at ~30 Hz.
        """
        try:
            value = float(value)
        except Exception:
            value = 0.0
        if self.animation_duration > 0:
            value = max(0.0, min(value, self.animation_duration))
        else:
            value = max(0.0, value)
        self.preview_time_numeric = value
        if now is None:
            now = time.perf_counter()
        if force_ui or now - self.playback_ui_last_clock >= 1.0 / 30.0:
            self.playback_ui_last_clock = now
            self.updating_time_controls = True
            try:
                self.preview_time_var.set(f'{value:.4f}'.rstrip('0').rstrip('.') if value else '0')
                try:
                    self._set_slider_programmatic(value)
                except Exception:
                    pass
            finally:
                self.updating_time_controls = False
            self.playback_time_label.set(f'{value:.3f} / {self.animation_duration:.3f} s')

    def on_animation_selected(self, event=None):
        self.pause_playback()
        a = self.get_selected_animation()
        if a:
            self._enable_animation_for_parsed(self.current, a.get('name', ''), True)
        self._refresh_multi_animation_menu()
        self.update_playback_controls()
        self.set_preview_time(0.0, render=True)

    def on_time_entry_changed(self, event=None):
        if self.updating_time_controls:
            return
        try:
            value = float(self.preview_time_var.get())
        except Exception:
            return
        if self.animation_duration <= 0:
            self.animation_duration = self.get_animation_duration()
        self.set_preview_time(value, render=True)
        if self.playing:
            self.playback_start_value = self.get_preview_time()
            self.playback_start_clock = time.perf_counter()

    def on_playback_slider(self, value):
        if self.updating_time_controls:
            return
        try:
            v = float(value)
        except Exception:
            return
        self.set_preview_time(v, render=True)
        if self.playing:
            self.playback_start_value = v
            self.playback_start_clock = time.perf_counter()

    def toggle_playback(self):
        if self.playing:
            self.pause_playback()
        else:
            self.start_playback()

    def start_playback(self):
        self.update_playback_controls()
        if self.animation_duration <= 0:
            return
        cur = self.get_preview_time()
        if cur >= self.animation_duration - 1e-06:
            cur = 0.0
            self.set_preview_time(cur, render=False)
        self.playing = True
        self.fast_preview = True
        self.playback_generation += 1
        self.playback_start_clock = time.perf_counter()
        self.playback_start_value = cur
        self.playback_last_time = self.playback_start_clock
        self.playback_next_frame_clock = self.playback_start_clock
        self.playback_ui_last_clock = 0.0
        self.play_button.configure(text='⏸ Pause')
        self._playback_tick(self.playback_generation)

    def pause_playback(self):
        if not self.playing:
            return
        if self.playback_start_clock is not None and self.animation_duration > 0:
            elapsed = max(0.0, time.perf_counter() - self.playback_start_clock)
            cur = self.playback_start_value + elapsed
            if self.loop_animation.get():
                cur = cur % self.animation_duration
            else:
                cur = min(cur, self.animation_duration)
            self.set_preview_time(cur, render=False)
        self.playing = False
        self.playback_generation += 1
        if self.playback_job is not None:
            try:
                self.root.after_cancel(self.playback_job)
            except Exception:
                pass
            self.playback_job = None
        self.playback_last_time = None
        self.playback_start_clock = None
        self.playback_next_frame_clock = None
        self.fast_preview = False
        self.play_button.configure(text='▶ Play')
        self.render_layout_preview()

    def stop_playback(self):
        self.playing = False
        self.playback_generation += 1
        if self.playback_job is not None:
            try:
                self.root.after_cancel(self.playback_job)
            except Exception:
                pass
            self.playback_job = None
        self.playback_last_time = None
        self.playback_start_clock = None
        self.playback_next_frame_clock = None
        self.fast_preview = False
        self.play_button.configure(text='▶ Play')
        self.set_preview_time(0.0, render=True)

    def _playback_tick(self, generation=None):
        if generation is None:
            generation = self.playback_generation
        if not self.playing or generation != self.playback_generation:
            return
        if self.animation_duration <= 0 or self.playback_start_clock is None:
            self.stop_playback()
            return
        elapsed = max(0.0, time.perf_counter() - self.playback_start_clock)
        absolute_time = self.playback_start_value + elapsed
        if self.loop_animation.get():
            cur = absolute_time % self.animation_duration
        else:
            if absolute_time >= self.animation_duration:
                self._set_playback_time_fast(self.animation_duration, now=time.perf_counter(), force_ui=True)
                self.playing = False
                self.playback_generation += 1
                self.playback_job = None
                self.playback_start_clock = None
                self.fast_preview = False
                self.play_button.configure(text='▶ Play')
                self.render_layout_preview()
                return
            cur = absolute_time
        self._set_playback_time_fast(cur, now=time.perf_counter())
        self.render_layout_preview()
        now = time.perf_counter()
        interval = self.playback_frame_interval
        deadline = (self.playback_next_frame_clock or now) + interval
        if deadline <= now:
            missed = int((now - deadline) // interval) + 1
            deadline += missed * interval
        self.playback_next_frame_clock = deadline
        delay_ms = max(1, int(round((deadline - now) * 1000.0)))
        self.playback_job = self.root.after(delay_ms, lambda: self._playback_tick(generation))

    def get_selected_animation(self):
        if not self.current:
            return None
        name = self.preview_anim_var.get() if hasattr(self, 'preview_anim_var') else '(raw node values)'
        for anim in self.current.get('animations', []):
            if anim.get('name') == name:
                return anim
        return None

    def get_preview_time(self):
        try:
            return float(self.preview_time_numeric)
        except Exception:
            try:
                return float(self.preview_time_var.get())
            except Exception:
                return 0.0

    def evaluate_track_value(self, track, t):
        keys = track.get('keys', [])
        if not keys:
            return None
        pts = [(parse_timecode(k['time']), float(k['value'])) for k in keys]
        pts.sort(key=lambda kv: kv[0])
        if t <= pts[0][0]:
            return pts[0][1]
        for i in range(len(pts) - 1):
            t0, v0 = pts[i]
            t1, v1 = pts[i + 1]
            if t0 <= t <= t1:
                if abs(t1 - t0) < 1e-08:
                    return v1
                u = (t - t0) / (t1 - t0)
                return lerp(v0, v1, u)
        return pts[-1][1]

    def get_node_preview_state(self, node):
        state = {'x': float(node.get('x', 0) or 0), 'y': float(node.get('y', 0) or 0), 'sx': float(node.get('sx', 1) or 1), 'sy': float(node.get('sy', 1) or 1), 'rotation': float(node.get('rotation', 0) or 0), 'opacity': float(node.get('opacity', 1) or 1)}
        anim = self.get_selected_animation()
        if not anim:
            return state
        t = self.get_preview_time()
        for tr in anim.get('tracks', []):
            if tr.get('target') != node.get('name'):
                continue
            val = self.evaluate_track_value(tr, t)
            if val is None:
                continue
            prop = tr.get('property')
            if prop == 1:
                state['x'] = val
            elif prop == 2:
                state['y'] = val
            elif prop == 3:
                state['sx'] = val
            elif prop == 4:
                state['sy'] = val
            elif prop == 5:
                state['rotation'] = val
            elif prop == 6:
                state['opacity'] = val
        return state

    def get_selected_node_parent_state(self):
        if self.current is None or self.selected_node is None:
            return None
        node = self.current['nodes'][self.selected_node]
        parent = node.get('parent_index')
        if parent is None:
            return {'x': 0.0, 'y': 0.0, 'sx': 1.0, 'sy': 1.0, 'rotation': 0.0, 'opacity': 1.0}
        cache = {}
        anims = self._active_animation_names_for(self.current) or ([self.preview_anim_var.get()] if self.preview_anim_var.get() != '(raw node values)' else [])
        return self._node_global_state(self.current, parent, anims, self.get_preview_time(), cache)

    def get_selected_node_anim_offsets(self):
        offsets = {'x': 0.0, 'y': 0.0}
        if self.current is None or self.selected_node is None:
            return offsets
        names = set(self._active_animation_names_for(self.current))
        if not names:
            a = self.get_selected_animation()
            names = {a.get('name')} if a else set()
        if not names:
            return offsets
        node = self.current['nodes'][self.selected_node]
        t = self.get_preview_time()
        for anim in self.current.get('animations', []):
            if anim.get('name') not in names:
                continue
            for tr in anim.get('tracks', []):
                if tr.get('target') != node.get('name'):
                    continue
                val = self.evaluate_track_value(tr, t)
                if val is None:
                    continue
                if tr.get('property') == 1:
                    offsets['x'] += val
                elif tr.get('property') == 2:
                    offsets['y'] += val
        return offsets

    def preview_canvas_to_logical(self, event_x, event_y):
        m = self.preview_view_metrics
        if not m:
            return None
        ox, oy, dw, dh, out_w, out_h = m
        logical_w, logical_h = self.get_logical_resolution()
        ex = min(max(event_x, ox), ox + dw)
        ey = min(max(event_y, oy), oy + dh)
        gx = (ex - ox) * (logical_w / dw)
        gy = (ey - oy) * (logical_h / dh)
        return (gx, gy)

    def _selected_preview_corners(self):
        if self.current is None or self.selected_node is None or (not self.preview_view_metrics):
            return None
        ox, oy, dw, dh, out_w, out_h = self.preview_view_metrics
        logical_w, logical_h = self.get_logical_resolution()
        if logical_w <= 0 or logical_h <= 0:
            return None
        cache = {}
        n = self.current['nodes'][self.selected_node]
        anims = self._active_animation_names_for(self.current) or ([self.preview_anim_var.get()] if self.preview_anim_var.get() != '(raw node values)' else [])
        gm, op = self._node_global_matrix(self.current, self.selected_node, anims, self.get_preview_time(), cache)
        sx = dw / logical_w
        sy = dh / logical_h
        pts = []
        for x, y in ((0, 0), (float(n.get('width', 0)), 0), (float(n.get('width', 0)), float(n.get('height', 0))), (0, float(n.get('height', 0)))):
            gx, gy = self._m_apply(gm, x, y)
            pts.append((ox + gx * sx, oy + gy * sy))
        return pts

    def _selected_preview_bbox(self):
        pts = self._selected_preview_corners()
        if not pts:
            return None
        return (min((x for x, y in pts)), min((y for x, y in pts)), max((x for x, y in pts)), max((y for x, y in pts)))

    def schedule_preview_render(self, delay=35):
        if self.preview_render_job is not None:
            try:
                self.root.after_cancel(self.preview_render_job)
            except Exception:
                pass
        self.preview_render_job = self.root.after(delay, self._scheduled_preview_render)

    def _scheduled_preview_render(self):
        self.preview_render_job = None
        self.render_layout_preview()

    def on_preview_press(self, event):
        if self.current is None or self.selected_node is None:
            return
        if self._node_locked(self.current, self.selected_node):
            self.status.set('🔒 This node is locked. Unlock it before moving or resizing.')
            return
        bbox = self._selected_preview_bbox()
        if not bbox:
            return
        x1, y1, x2, y2 = bbox
        handle = 14
        pts = self._selected_preview_corners() or []
        hx, hy = pts[2] if len(pts) >= 3 else (x2, y2)
        if abs(event.x - hx) <= handle and abs(event.y - hy) <= handle:
            self.drag_mode = 'resize'
        elif x1 - 4 <= event.x <= x2 + 4 and y1 - 4 <= event.y <= y2 + 4:
            self.drag_mode = 'move'
        else:
            return
        self.push_undo('Resize node' if self.drag_mode == 'resize' else 'Move node')
        self.dragging_node = True
        self.drag_node_index = self.selected_node
        self.fast_preview = True
        node = self.current['nodes'][self.selected_node]
        self.drag_start = {'mouse': self.preview_canvas_to_logical(event.x, event.y), 'x': float(node.get('x', 0)), 'y': float(node.get('y', 0)), 'sx': float(node.get('sx', 1)), 'sy': float(node.get('sy', 1)), 'bbox': bbox}

    def on_preview_drag(self, event):
        if not self.dragging_node or self.current is None or self.drag_node_index is None or (not self.drag_start):
            return
        pos = self.preview_canvas_to_logical(event.x, event.y)
        if pos is None or self.drag_start['mouse'] is None:
            return
        gx, gy = pos
        sx0, sy0 = self.drag_start['mouse']
        node = self.current['nodes'][self.drag_node_index]
        if self.drag_mode == 'move':
            parent = node.get('parent_index')
            if parent is not None:
                cache = {}
                anims = self._active_animation_names_for(self.current) or ([self.preview_anim_var.get()] if self.preview_anim_var.get() != '(raw node values)' else [])
                pm, _ = self._node_global_matrix(self.current, parent, anims, self.get_preview_time(), cache)
                a, b, c, d, tx, ty = self._m_inverse(pm)
                dx = gx - sx0
                dy = gy - sy0
                ldx = a * dx + c * dy
                ldy = b * dx + d * dy
            else:
                ldx = gx - sx0
                ldy = gy - sy0
            new_x = self.drag_start['x'] + ldx
            new_y = self.drag_start['y'] + ldy
            node['x'] = float(new_x)
            node['y'] = float(new_y)
            self.fields['x'].set(f'{new_x:.6g}')
            self.fields['y'].set(f'{new_y:.6g}')
        elif self.drag_mode == 'resize':
            parent_state = self.get_selected_node_parent_state() or {'sx': 1.0, 'sy': 1.0}
            psx = abs(parent_state.get('sx', 1.0) or 1.0)
            psy = abs(parent_state.get('sy', 1.0) or 1.0)
            local_sx = max(abs(float(node.get('sx', 1.0) or 1.0)), 1e-06)
            local_sy = max(abs(float(node.get('sy', 1.0) or 1.0)), 1e-06)
            start_w = max(1.0, abs(float(node.get('width', 1.0))) * local_sx * psx)
            start_h = max(1.0, abs(float(node.get('height', 1.0))) * local_sy * psy)
            new_global_w = max(1.0, start_w + (gx - sx0))
            new_global_h = max(1.0, start_h + (gy - sy0))
            new_w = max(1.0, new_global_w / (local_sx * psx))
            new_h = max(1.0, new_global_h / (local_sy * psy))
            node['width'] = float(new_w)
            node['height'] = float(new_h)
            self.fields['width'].set(f'{new_w:.6g}')
            self.fields['height'].set(f'{new_h:.6g}')
        self.schedule_preview_render(45)

    def on_preview_release(self, event):
        if self.dragging_node:
            self.dragging_node = False
            mode = self.drag_mode
            self.drag_node_index = None
            self.drag_mode = None
            self.drag_start = None
            self.fast_preview = False
            self.render_layout_preview()
            self.status.set(('Resized' if mode == 'resize' else 'Moved') + ' selected node. Use Save or Save As when finished.')

    def show_texture(self, ref):
        self.preview_texture_path = ''
        self.preview_texture_pil = None
        if not ref:
            self.render_layout_preview()
            return
        matches = self.tex_index.get(normalize_tex_name(ref), [])
        if not matches:
            self.preview_note.set('Background: ' + (os.path.basename(self.background_path) if self.background_path else 'none') + '  |  Texture not found automatically')
            self.render_layout_preview()
            return
        path = matches[0]
        self.preview_texture_path = path
        if not PIL_OK:
            self.preview_note.set('Found texture, but Pillow is required for preview')
            self.render_layout_preview()
            return

        def worker():
            try:
                raw = open(path, 'rb').read()
                im = Image.open(io.BytesIO(raw)).convert('RGBA')
                im.load()
                self.q.put(('preview_texture', path, im.copy()))
            except Exception as e:
                self.q.put(('preview_error', path, str(e)))
        threading.Thread(target=worker, daemon=True).start()

    def _m_identity(self):
        return (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)

    def _m_mul(self, A, B):
        a, b, c, d, tx, ty = A
        e, f, g, h, ux, uy = B
        return (a * e + c * f, b * e + d * f, a * g + c * h, b * g + d * h, a * ux + c * uy + tx, b * ux + d * uy + ty)

    def _m_apply(self, M, x, y):
        a, b, c, d, tx, ty = M
        return (a * x + c * y + tx, b * x + d * y + ty)

    def _m_inverse(self, M):
        a, b, c, d, tx, ty = M
        det = a * d - b * c
        if abs(det) < 1e-12:
            return self._m_identity()
        ia = d / det
        ib = -b / det
        ic = -c / det
        id = a / det
        return (ia, ib, ic, id, -ia * tx - ic * ty, -ib * tx - id * ty)

    def _node_local_matrix(self, node, parsed, animation_name, t):
        st = self._local_node_state(node, parsed, animation_name, t)
        w = float(node.get('width', 0) or 0)
        h = float(node.get('height', 0) or 0)
        piv = node.get('pivots', (0, 0, 0))
        px = approx_pivot_value(piv[0])
        py = approx_pivot_value(piv[2] if len(piv) > 2 else 0)
        ox = w * px
        oy = h * py
        ang = math.radians(float(st.get('rotation', 0) or 0))
        cs = math.cos(ang)
        sn = math.sin(ang)
        sx = float(st.get('sx', 1) or 0)
        sy = float(st.get('sy', 1) or 0)
        rs = (cs * sx, sn * sx, -sn * sy, cs * sy, 0.0, 0.0)
        pre = (1.0, 0.0, 0.0, 1.0, -ox, -oy)
        post = (1.0, 0.0, 0.0, 1.0, float(st.get('x', 0)) + ox, float(st.get('y', 0)) + oy)
        return (self._m_mul(post, self._m_mul(rs, pre)), float(st.get('opacity', 1) or 0))

    def _node_global_matrix(self, parsed, idx, animation_name, t, cache):
        if idx in cache:
            return cache[idx]
        node = parsed['nodes'][idx]
        local, op = self._node_local_matrix(node, parsed, animation_name, t)
        parent = node.get('parent_index')
        if parent is None:
            out = (local, op)
        else:
            pm, pop = self._node_global_matrix(parsed, parent, animation_name, t, cache)
            out = (self._m_mul(pm, local), pop * op)
        cache[idx] = out
        return out

    def _affine_texture(self, tex, node, matrix, scale_x, scale_y, opacity, fast=False):
        """Warp a texture through the complete BAML transform matrix.
        This keeps rotation on the real BAML pivot and also handles rotating/scaled parents.
        Returns (image, paste_x, paste_y).
        """
        if tex is None or tex.width < 1 or tex.height < 1:
            return None
        nw = float(node.get('width', 0) or tex.width)
        nh = float(node.get('height', 0) or tex.height)
        if abs(nw) < 1e-09 or abs(nh) < 1e-09:
            return None
        src_to_node = (nw / tex.width, 0.0, 0.0, nh / tex.height, 0.0, 0.0)
        logical_to_scene = (scale_x, 0.0, 0.0, scale_y, 0.0, 0.0)
        F = self._m_mul(logical_to_scene, self._m_mul(matrix, src_to_node))
        corners = [self._m_apply(F, 0, 0), self._m_apply(F, tex.width, 0), self._m_apply(F, 0, tex.height), self._m_apply(F, tex.width, tex.height)]
        minx = math.floor(min((x for x, y in corners)))
        miny = math.floor(min((y for x, y in corners)))
        maxx = math.ceil(max((x for x, y in corners)))
        maxy = math.ceil(max((y for x, y in corners)))
        ow = max(1, int(maxx - minx))
        oh = max(1, int(maxy - miny))
        if ow > 8192 or oh > 8192:
            return None
        inv = self._m_inverse(F)
        a, b, c, d, tx, ty = inv
        coeff = (a, c, a * minx + c * miny + tx, b, d, b * minx + d * miny + ty)
        resample = Image.BILINEAR if fast else Image.BICUBIC
        try:
            affine_enum = Image.Transform.AFFINE
        except Exception:
            affine_enum = Image.AFFINE
        out = tex.transform((ow, oh), affine_enum, coeff, resample=resample)
        opacity = max(0.0, min(1.0, float(opacity)))
        if opacity < 0.999:
            alpha = out.getchannel('A').point(lambda v: int(v * opacity))
            out.putalpha(alpha)
        return (out, int(minx), int(miny))

    def _local_node_state(self, node, parsed, animation_name=None, t=0.0):
        state = {'x': float(node.get('x', 0) or 0), 'y': float(node.get('y', 0) or 0), 'sx': float(node.get('sx', 1) or 1), 'sy': float(node.get('sy', 1) or 1), 'rotation': float(node.get('rotation', 0) or 0), 'opacity': float(node.get('opacity', 1) or 1)}
        if isinstance(animation_name, (list, tuple, set)):
            names = [n for n in animation_name if n and n != '(raw node values)']
        elif animation_name and animation_name != '(raw node values)':
            names = [animation_name]
        else:
            names = []
        if not names:
            return state
        wanted = set(names)
        xoff = 0.0
        yoff = 0.0
        for anim in parsed.get('animations', []):
            if anim.get('name') not in wanted:
                continue
            for tr in anim.get('tracks', []):
                if tr.get('target') != node.get('name'):
                    continue
                val = self.evaluate_track_value(tr, t)
                if val is None:
                    continue
                prop = tr.get('property')
                if prop == 1:
                    xoff += val
                elif prop == 2:
                    yoff += val
                elif prop == 3:
                    state['sx'] = val
                elif prop == 4:
                    state['sy'] = val
                elif prop == 5:
                    state['rotation'] = val
                elif prop == 6:
                    state['opacity'] = val
        state['x'] = float(node.get('x', 0) or 0) + xoff
        state['y'] = float(node.get('y', 0) or 0) + yoff
        return state

    def _node_global_state(self, parsed, idx, animation_name, t, cache):
        if idx in cache:
            return cache[idx]
        node = parsed['nodes'][idx]
        loc = self._local_node_state(node, parsed, animation_name, t)
        parent = node.get('parent_index')
        if parent is None:
            out = loc.copy()
        else:
            ps = self._node_global_state(parsed, parent, animation_name, t, cache)
            out = {'x': ps['x'] + loc['x'] * ps['sx'], 'y': ps['y'] + loc['y'] * ps['sy'], 'sx': ps['sx'] * loc['sx'], 'sy': ps['sy'] * loc['sy'], 'rotation': ps['rotation'] + loc['rotation'], 'opacity': ps['opacity'] * loc['opacity']}
        cache[idx] = out
        return out

    def _draw_text_on_scene(self, scene, node, gs, scale_x, scale_y, offset_x=0, offset_y=0):
        if not PIL_OK or not node.get('text') or gs['opacity'] <= 0.005:
            return
        try:
            from PIL import ImageDraw, ImageFont
            draw = ImageDraw.Draw(scene)
            x = int((offset_x + gs['x']) * scale_x)
            y = int((offset_y + gs['y']) * scale_y)
            fs = max(10, int(float(node.get('font_size', 24) or 24) * scale_y))
            font = self.font_cache.get(fs)
            if font is None:
                try:
                    font = ImageFont.truetype('arial.ttf', fs)
                except Exception:
                    font = ImageFont.load_default()
                self.font_cache[fs] = font
            raw = int(node.get('text_color_raw', 4294967295))
            r = raw >> 0 & 255
            g = raw >> 8 & 255
            b = raw >> 16 & 255
            a = raw >> 24 & 255
            if a == 0:
                a = 255
            a = int(a * max(0, min(1, gs['opacity'])))
            if r + g + b < 20:
                r = g = b = 255
            draw.text((x, y), node['text'], font=font, fill=(r, g, b, a))
        except Exception:
            pass

    def _draw_parsed_scene(self, scene, parsed, scale_x, scale_y, animation_name, t, base_matrix=None, base_opacity=1.0, depth=0):
        if depth > 4:
            return
        if base_matrix is None:
            base_matrix = self._m_identity()
        cache = {}
        for idx, node in enumerate(parsed.get('nodes', [])):
            if idx == 0 and depth > 0:
                continue
            if self._node_hidden_in_preview(parsed, idx):
                continue
            gm, opacity = self._node_global_matrix(parsed, idx, animation_name, t, cache)
            gm = self._m_mul(base_matrix, gm)
            opacity *= base_opacity
            if opacity <= 0.005:
                continue
            if node.get('type') == 1 and node.get('texture'):
                tex = self.load_texture_pil(node['texture'], parsed.get('path'))
                if tex is not None:
                    try:
                        fast = bool(getattr(self, 'fast_preview', False))
                        mk = tuple((round(float(v), 5) for v in gm))
                        key = (id(tex), round(float(node.get('width', 0)), 4), round(float(node.get('height', 0)), 4), mk, round(opacity, 3), round(scale_x, 5), round(scale_y, 5), fast)
                        cached = self.resized_texture_cache.get(key)
                        if cached is None:
                            rendered = self._affine_texture(tex, node, gm, scale_x, scale_y, opacity, fast)
                            if rendered is None:
                                continue
                            self.resized_texture_cache[key] = rendered
                            self.resized_texture_cache_order.append(key)
                            if len(self.resized_texture_cache_order) > 96:
                                oldk = self.resized_texture_cache_order.pop(0)
                                self.resized_texture_cache.pop(oldk, None)
                        else:
                            rendered = cached
                        im, x, y = rendered
                        scene.alpha_composite(im, (x, y))
                    except Exception:
                        pass
            elif node.get('type') == 3:
                try:
                    x, y = self._m_apply(gm, 0, 0)
                    fake = {'x': x, 'y': y, 'sx': 1.0, 'sy': 1.0, 'rotation': 0.0, 'opacity': opacity}
                    self._draw_text_on_scene(scene, node, fake, scale_x, scale_y)
                except Exception:
                    pass
            elif node.get('type') == 2 and node.get('component'):
                # Communicator corner overlays can be reduced for preview without editing the BAML.
                if os.path.basename(parsed.get('path', '')).upper() == 'MAINWINDOW.BAML' and os.path.basename(os.path.dirname(parsed.get('path', ''))).upper() == 'COMMUNICATOR' and node['component'].upper().startswith('UI_CORNER_HUB'):
                    factor = max(0.25, min(1.0, self.hud_preview_scale))
                    cx = float(node.get('width') or 256.0)
                    cy = float(node.get('height') or 256.0)
                    anchor_x = cx if node['component'].upper().endswith('_P2') else 0.0
                    anchor_y = cy
                    shrink = self._m_mul((1.0, 0.0, 0.0, 1.0, anchor_x, anchor_y), self._m_mul((factor, 0.0, 0.0, factor, 0.0, 0.0), (1.0, 0.0, 0.0, 1.0, -anchor_x, -anchor_y)))
                    gm = self._m_mul(gm, shrink)
                comp = self.load_component_baml(node['component'])
                if comp and comp.get('nodes'):
                    self._draw_parsed_scene(scene, comp, scale_x, scale_y, None, t, base_matrix=gm, base_opacity=opacity, depth=depth + 1)

    def render_layout_preview(self):
        canvas = getattr(self, 'preview_canvas', None)
        if canvas is None or not self._preview_is_visible():
            self.preview_dirty = True
            return
        self.preview_dirty = False
        self.preview_items = []
        if self.playing:
            try:
                canvas.delete('selection_overlay')
            except Exception:
                pass
        else:
            canvas.delete('all')
            self.preview_canvas_image_item = None
        cw = max(canvas.winfo_width(), 50)
        ch = max(canvas.winfo_height(), 50)
        out_w, out_h = self.get_preview_resolution()
        logical_w, logical_h = self.get_logical_resolution()
        if out_w <= 0 or out_h <= 0:
            out_w, out_h = (1920.0, 1080.0)
        if logical_w <= 0 or logical_h <= 0:
            logical_w, logical_h = (1280.0, 720.0)
        fit = min(cw / out_w, ch / out_h)
        dw = max(1, int(out_w * fit))
        dh = max(1, int(out_h * fit))
        ox = (cw - dw) // 2
        oy = (ch - dh) // 2
        self.preview_view_metrics = (ox, oy, dw, dh, out_w, out_h)
        if PIL_OK:
            bg, bg_path = self._context_background()
            if bg is not None and bool(self.show_bg_var.get()):
                resample = Image.BILINEAR if self.fast_preview else Image.LANCZOS
                bkey = (id(bg), dw, dh, bool(self.fast_preview))
                scene = self.background_scaled_cache.get(bkey)
                if scene is None:
                    scene = bg.copy().resize((dw, dh), resample).convert('RGBA')
                    self.background_scaled_cache = {bkey: scene}
                scene = scene.copy()
            else:
                scene = Image.new('RGBA', (dw, dh), (0, 0, 0, 255))
            parsed_files = self._selected_parsed_files()
            if not parsed_files and self.current:
                parsed_files = [self.current]
            for parsed in parsed_files:
                anims = self._active_animation_names_for(parsed)
                if not anims and parsed is self.current:
                    cur = self.preview_anim_var.get() if hasattr(self, 'preview_anim_var') else '(raw node values)'
                    if cur and cur != '(raw node values)':
                        anims = [cur]
                self._draw_parsed_scene(scene, parsed, dw / logical_w, dh / logical_h, anims, self.get_preview_time())
            self.preview_scene_tk = ImageTk.PhotoImage(scene)
            if self.playing and self.preview_canvas_image_item is not None:
                try:
                    canvas.itemconfigure(self.preview_canvas_image_item, image=self.preview_scene_tk)
                    canvas.coords(self.preview_canvas_image_item, ox, oy)
                except Exception:
                    self.preview_canvas_image_item = canvas.create_image(ox, oy, image=self.preview_scene_tk, anchor='nw')
            else:
                self.preview_canvas_image_item = canvas.create_image(ox, oy, image=self.preview_scene_tk, anchor='nw')
            if not self.playing:
                self.draw_selection_overlay()
            sizes = []
            for p in parsed_files:
                w, h = self._parsed_layout_size(p)
                sizes.append(f'{int(w)}×{int(h)}')
            bg_name = os.path.basename(bg_path) if bg_path else 'none'
            multi = f'{len(parsed_files)} BAMLs' if len(parsed_files) > 1 else sizes[0] if sizes else ''
            note = f'{multi}  |  Background: {bg_name}'
            if self.preview_note.get() != note:
                self.preview_note.set(note)
        else:
            canvas.create_text(cw // 2, ch // 2, text='Install Pillow for visual preview', fill='white')

    def apply_node_fields(self):
        if self.current is None or self.selected_node is None:
            return
        n = self.current['nodes'][self.selected_node]
        locked = self._node_locked(self.current, self.selected_node)
        try:
            vals = [float(self.fields[k].get()) for k in ('width', 'height', 'x', 'y', 'sx', 'sy', 'rotation', 'opacity')]
        except ValueError:
            messagebox.showerror('Invalid value', 'One of the values is not a number.')
            return
        self.push_undo('Apply node values')
        for key, val in zip(('width', 'height', 'x', 'y', 'sx', 'sy', 'rotation', 'opacity'), vals):
            if locked and key in ('width', 'height', 'x', 'y', 'sx', 'sy', 'rotation'):
                continue
            n[key] = val
        self.status.set(('Locked transform fields were left unchanged. ' if locked else '') + 'Node values applied in memory. Use Save or Save As to write the BAML.')
        self.render_layout_preview()

    def build_current_bytes(self):
        if self.current is None:
            return None
        if self.current.get('structure_dirty'):
            return bytearray(serialize_baml(self.current))
        data = bytearray(self.current['data'])
        for n in self.current.get('nodes', []):
            off = n.get('common_offset')
            if off is None or off + 32 > len(data):
                continue
            vals = (float(n.get('width', 0)), float(n.get('height', 0)), float(n.get('x', 0)), float(n.get('y', 0)), float(n.get('sx', 1)), float(n.get('sy', 1)), float(n.get('rotation', 0)), float(n.get('opacity', 1)))
            struct.pack_into('<8f', data, off, *vals)
        return data

    def save_current(self):
        if self.current is None:
            return
        path = self.current['path']
        data = self.build_current_bytes()
        if data is None:
            return
        try:
            bak = path + '.bak'
            if os.path.exists(path) and (not os.path.exists(bak)):
                shutil.copy2(path, bak)
            with open(path, 'wb') as f:
                f.write(data)
            self.current = parse_baml(path)
            self.parsed_cache[path] = self.current
            self.status.set('Saved ' + os.path.basename(path) + '  |  backup: ' + os.path.basename(bak))
            self.refresh_current_ui()
        except Exception as e:
            messagebox.showerror('Save failed', str(e))

    def save_as(self):
        if self.current is None:
            return
        initial = os.path.basename(self.current.get('path', 'Edited.BAML'))
        path = filedialog.asksaveasfilename(title='Save BAML As', defaultextension='.BAML', initialfile=initial, filetypes=[('BAML files', '*.BAML'), ('All files', '*.*')])
        if not path:
            return
        data = self.build_current_bytes()
        try:
            with open(path, 'wb') as f:
                f.write(data)
            self.current = parse_baml(path)
            self.status.set('Saved As ' + path)
            self.refresh_current_ui()
        except Exception as e:
            messagebox.showerror('Save As failed', str(e))

    def _replace_texture_string_in_memory(self, new_ref):
        if self.current is None or self.selected_node is None:
            return False
        node = self.current['nodes'][self.selected_node]
        if node.get('type') != 1:
            messagebox.showinfo('Texture', 'The selected node is not an image node.')
            return False
        if self.current.get('structure_dirty') or 'texture_field_start' not in node:
            self.push_undo('Replace texture')
            node['texture'] = new_ref
            self.refresh_current_ui(select_index=self.selected_node)
            return True
        try:
            raw = new_ref.encode('latin1')
        except Exception:
            messagebox.showerror('Texture', 'Texture reference contains unsupported characters.')
            return False
        if len(raw) > 255:
            messagebox.showerror('Texture', 'Texture reference is too long for this BAML string field.')
            return False
        self.push_undo('Replace texture')
        start = node['texture_field_start']
        end = node['texture_field_end']
        data = bytearray(self.build_current_bytes())
        data[start:end] = bytes([len(raw)]) + raw
        old_index = self.selected_node
        self.current = parse_baml(self.current['path'], data)
        self.selected_node = min(old_index, len(self.current['nodes']) - 1) if self.current['nodes'] else None
        self.refresh_current_ui(select_index=self.selected_node)
        return True

    def replace_texture_reference(self):
        if self.current is None or self.selected_node is None:
            return
        node = self.current['nodes'][self.selected_node]
        if node.get('type') != 1:
            messagebox.showinfo('Replace texture', 'Select an Image node first.')
            return
        path = filedialog.askopenfilename(title='Choose replacement TEX/DDS', filetypes=[('LCU textures', '*.TEX *.DDS'), ('TEX files', '*.TEX'), ('DDS files', '*.DDS'), ('All files', '*.*')])
        if not path:
            return
        base = os.path.splitext(os.path.basename(path))[0]
        for suffix in ('_DX11', '_PC'):
            if base.upper().endswith(suffix):
                base = base[:-len(suffix)]
        old = node.get('texture', '')
        prefix = ''
        if '\\' in old:
            prefix = old.rsplit('\\', 1)[0] + '\\'
        elif '/' in old:
            prefix = old.rsplit('/', 1)[0] + '\\'
        else:
            prefix = 'Images\\'
        new_ref = prefix + base + '.dds'
        if self._replace_texture_string_in_memory(new_ref):
            self.tex_index.setdefault(normalize_tex_name(new_ref), [])
            if path not in self.tex_index[normalize_tex_name(new_ref)]:
                self.tex_index[normalize_tex_name(new_ref)].insert(0, path)
            self.texture_pil_cache.pop(path, None)
            self.status.set('Texture reference changed to ' + new_ref + '. Use Save or Save As to write it.')
            self.request_preview_render()

    def remove_texture_reference(self):
        if self.current is None or self.selected_node is None:
            return
        node = self.current['nodes'][self.selected_node]
        if node.get('type') != 1:
            messagebox.showinfo('Remove texture', 'Select an Image node first.')
            return
        if not messagebox.askyesno('Remove texture', 'Remove the texture reference from this image node?'):
            return
        if self._replace_texture_string_in_memory(''):
            self.status.set('Texture reference removed in memory. Use Save or Save As to write it.')
            self.request_preview_render()

    def refresh_current_ui(self, select_index=None, select_indices=None):
        if self.current is None:
            return
        oldsel = select_indices if select_indices is not None else self._selected_node_indices()
        for iid in self.node_list.get_children():
            self.node_list.delete(iid)
        self.visible_node_indices = []
        for idx, n in enumerate(self.current['nodes']):
            if n.get('name') == 'LayoutRoot':
                continue
            self.visible_node_indices.append(idx)
            eye = '👁' if not self._node_hidden_in_preview(self.current, idx) else '👁̸'
            lock = '🔒' if self._node_locked(self.current, idx) else '🔓'
            self.node_list.insert('', 'end', iid=str(idx), values=(eye, lock, n['name'], TYPE_NAMES.get(n['type'], n['type'])))
        targets = []
        if select_indices is not None:
            targets = [i for i in select_indices if i in self.visible_node_indices]
        elif select_index is not None and select_index in self.visible_node_indices:
            targets = [select_index]
        else:
            targets = [i for i in oldsel if i in self.visible_node_indices]
        if targets:
            self.node_list.selection_set(tuple((str(i) for i in targets)))
            self.node_list.focus(str(targets[-1]))
            self.node_list.see(str(targets[-1]))
            self.selected_node = targets[-1]
            self.on_node()
        else:
            self.selected_node = None
        self.preview_dirty = True
        if self._preview_is_visible():
            self.request_preview_render(30)

    def on_node_refresh(self, i):
        if str(i) in self.node_list.get_children():
            self.node_list.selection_set(str(i))
            self.node_list.see(str(i))
            self.on_node()

    def set_text(self, w, s):
        state = str(w.cget('state')) if 'state' in w.keys() else 'normal'
        if state == 'disabled':
            w.configure(state='normal')
        w.delete('1.0', 'end')
        w.insert('1.0', s)
        if state == 'disabled':
            w.configure(state='disabled')

    def poll(self):
        try:
            while True:
                item = self.q.get_nowait()
                kind = item[0]
                if kind == 'scan_progress':
                    _, token, b, t = item
                    if token == self.scan_token:
                        self.status.set(f'Scanning… {b} BAML / {t} texture names')
                elif kind == 'scan_done':
                    _, token, bamls, tex = item
                    if token != self.scan_token:
                        continue
                    self.baml_paths = bamls
                    self.tex_index = tex
                    self.selected_baml_paths = []
                    self.active_animation_keys.clear()
                    self.baml_index = {os.path.splitext(os.path.basename(p))[0].upper(): p for p in bamls}
                    self.parsed_cache = {}
                    self.texture_pil_cache = {}
                    self.baml_list.delete(0, 'end')
                    for p in bamls:
                        self.baml_list.insert('end', os.path.relpath(p, self.root_dir))
                    self.status.set(f'Ready: {len(bamls)} BAML / {len(tex)} texture names')
                    wanted = self.restore_baml_name.upper()
                    match = next((i for i, p in enumerate(bamls) if os.path.basename(p).upper() == wanted), None)
                    if match is None:
                        match = next((i for i, p in enumerate(bamls) if os.path.basename(p).upper() == 'MAINWINDOW.BAML'), None)
                    if match is not None:
                        self.baml_list.selection_set(match)
                        self.baml_list.activate(match)
                        self.baml_list.see(match)
                        self.on_baml()
                elif kind == 'parse_done':
                    _, token, res = item
                    if token != self.parse_token:
                        continue
                    self.current = res
                    self.root.after_idle(self._set_initial_pane_widths)
                    self.parsed_cache[res.get('path', '')] = res
                    self.selected_node = None
                    for iid in self.node_list.get_children():
                        self.node_list.delete(iid)
                    self.visible_node_indices = []
                    for idx, n in enumerate(res['nodes']):
                        if n.get('name') == 'LayoutRoot':
                            continue
                        self.visible_node_indices.append(idx)
                        eye = '👁' if not self._node_hidden_in_preview(res, idx) else '👁̸'
                        lock = '🔒' if self._node_locked(res, idx) else '🔓'
                        self.node_list.insert('', 'end', iid=str(idx), values=(eye, lock, n['name'], TYPE_NAMES.get(n['type'], n['type'])))
                    a = []
                    for anim in res['animations']:
                        visible_tracks = [tr for tr in anim['tracks'] if tr.get('target') != 'LayoutRoot']
                        if not visible_tracks:
                            continue
                        a.append(f"Animation: {anim['name']}  flags={anim['flags']}")
                        for tr in visible_tracks:
                            a.append(f"  {tr['target']} :: {PROP_NAMES.get(tr['property'], 'Property ' + str(tr['property']))}")
                            for k in tr['keys']:
                                a.append(f"    {k['time']:>10} = {k['value']:.6g}   ease={tuple((round(x, 4) for x in k['ease']))}")
                    self.anim_text.delete('1.0', 'end')
                    self.anim_text.insert('1.0', '\n'.join(a) or 'No parsed animations')
                    visible_strings = [s for s in res['strings'] if s != 'LayoutRoot']
                    self.raw_text.delete('1.0', 'end')
                    self.raw_text.insert('1.0', '\n'.join(visible_strings))
                    self.anim_names = ['(raw node values)'] + [anim.get('name', '') for anim in res.get('animations', [])]
                    self.preview_anim_combo.configure(values=self.anim_names)
                    if len(self.anim_names) > 1:
                        self.preview_anim_var.set(self.anim_names[1])
                        self._enable_animation_for_parsed(res, self.anim_names[1], True)
                        mx = 0.0
                        for tr in res.get('animations', [{}])[0].get('tracks', []):
                            for k in tr.get('keys', []):
                                mx = max(mx, parse_timecode(k.get('time', '0')))
                        self.preview_time_var.set(str(round(mx, 3)))
                    else:
                        self.preview_anim_var.set('(raw node values)')
                    self.pause_playback()
                    self.update_playback_controls()
                    self._ae_refresh_all()
                    self._refresh_multi_animation_menu()
                    bg_name = os.path.basename(self._context_background()[1]) if self._context_background()[1] else 'none'
                    self.preview_note.set(f'Background: {bg_name}')
                    self.status.set(('Parsed' if res['complete'] else 'Partial parse') + (': ' + res['note'] if res['note'] else ''))
                    self.render_layout_preview()
                elif kind == 'preview_texture':
                    _, path, im = item
                    self.preview_texture_path = path
                    self.preview_texture_pil = im
                    bgp = self._context_background()[1]
                    bg_name = os.path.basename(bgp) if bgp else 'none'
                    self.preview_note.set(f'Background: {bg_name}  |  Texture: {os.path.basename(path)}')
                    self.render_layout_preview()
                elif kind == 'preview_error':
                    _, path, e = item
                    self.preview_texture_pil = None
                    bgp = self._context_background()[1]
                    bg_name = os.path.basename(bgp) if bgp else 'none'
                    self.preview_note.set(f'Background: {bg_name}  |  Found {os.path.basename(path)} but preview failed: {e}')
                    self.render_layout_preview()
                elif kind == 'error':
                    self.status.set(item[1])
                    messagebox.showerror('XBAML', item[1])
        except queue.Empty:
            pass
        self.root.after(50, self.poll)
if __name__ == '__main__':
    root = tk.Tk()
    App(root)
    root.mainloop()
