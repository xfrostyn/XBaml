package main

import (
    "embed"
    "errors"
    "fmt"
    "io/fs"
    "os"
    "os/exec"
    "path/filepath"
    "syscall"
    "unsafe"
)

//go:embed xbaml.py preview_background.png MAINFRAME_SCREENBG_CENT_DX11.TEX
var resources embed.FS

func alert(message string) {
    dll := syscall.NewLazyDLL("user32.dll")
    box := dll.NewProc("MessageBoxW")
    body, _ := syscall.UTF16PtrFromString(message)
    caption, _ := syscall.UTF16PtrFromString("XBAML")
    box.Call(0, uintptr(unsafe.Pointer(body)), uintptr(unsafe.Pointer(caption)), 0x10)
}

func unpack(target string) error {
    names := []string{"xbaml.py", "preview_background.png", "MAINFRAME_SCREENBG_CENT_DX11.TEX"}
    for _, name := range names {
        b, err := fs.ReadFile(resources, name)
        if err != nil { return err }
        if err := os.WriteFile(filepath.Join(target, name), b, 0600); err != nil { return err }
    }
    return nil
}

func run(target string) error {
    path := filepath.Join(target, "xbaml.py")
    interpreters := []struct {name string; args []string} {
        {"pythonw.exe", []string{path}},
        {"pyw.exe", []string{"-3", path}},
        {"python.exe", []string{path}},
        {"py.exe", []string{"-3", path}},
    }
    for _, item := range interpreters {
        exe, err := exec.LookPath(item.name)
        if err != nil { continue }
        logPath := filepath.Join(target, "xbaml-error.log")
        log, logErr := os.Create(logPath)
        if logErr != nil { return logErr }
        cmd := exec.Command(exe, item.args...)
        cmd.Dir = target
        cmd.SysProcAttr = &syscall.SysProcAttr{HideWindow:true}
        cmd.Stdout = log
        cmd.Stderr = log
        err = cmd.Run()
        log.Close()
        if err != nil {
            b, _ := os.ReadFile(logPath)
            report := fmt.Sprintf("XBAML could not start using %s.\n\n%s\n\n", item.name, err)
            if len(b)>0 {
                if len(b)>1300 { b=b[len(b)-1300:] }
                report += string(b)
            } else { report += "Check that Pillow is installed for this Python version." }
            alert(report)
            return err
        }
        return nil
    }
    return errors.New("Python 3 with Tkinter and Pillow is required to run the original XBAML5 interface. Install Python 3 and Pillow, then try again.")
}

func main() {
    target, err := os.MkdirTemp("", "XBAML14-")
    if err != nil { alert(err.Error()); return }
    defer os.RemoveAll(target)
    if err = unpack(target); err != nil { alert(err.Error()); return }
    if err = run(target); err != nil {
        if err.Error() == "Python 3 with Tkinter and Pillow is required to run the original XBAML5 interface. Install Python 3 and Pillow, then try again." {
            alert(err.Error())
        }
    }
}
