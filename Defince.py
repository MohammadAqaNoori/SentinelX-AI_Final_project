import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import threading
import random
import math
import time
import numpy as np
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib.pyplot as plt
from queue import PriorityQueue

# ===================== Utility Vector Class =====================

class Vector3D:
    __slots__ = ('x', 'y', 'z')
    def __init__(self, x=0.0, y=0.0, z=0.0):
        self.x = float(x)
        self.y = float(y)
        self.z = float(z)
    def __add__(self, other):
        return Vector3D(self.x + other.x, self.y + other.y, self.z + other.z)
    def __sub__(self, other):
        return Vector3D(self.x - other.x, self.y - other.y, self.z - other.z)
    def __mul__(self, scalar):
        return Vector3D(self.x * scalar, self.y * scalar, self.z * scalar)
    def __truediv__(self, scalar):
        return Vector3D(self.x / scalar, self.y / scalar, self.z / scalar) if scalar else Vector3D(self.x, self.y, self.z)
    def magnitude(self):
        return math.sqrt(self.x**2 + self.y**2 + self.z**2)
    def normalize(self):
        mag = self.magnitude()
        return Vector3D(self.x/mag, self.y/mag, self.z/mag) if mag else Vector3D(0.0,0.0,0.0)
    def dot(self, other):
        return self.x*other.x + self.y*other.y + self.z*other.z
    def to_array(self):
        return [self.x, self.y, self.z]
    def __repr__(self):
        return f"Vector3D({self.x:.1f}, {self.y:.1f}, {self.z:.1f})"

# ===================== Threat Classes =====================

class Threat:
    __slots__ = ('position','velocity','name','destroyed','trail','targeted','hit_ground')
    def __init__(self, position: Vector3D, velocity: Vector3D, name: str):
        self.position = position
        self.velocity = velocity
        self.name = name
        self.destroyed = False
        self.trail = []
        self.targeted = False
        self.hit_ground = False
    def update(self, dt: float):
        if self.destroyed or self.hit_ground:
            return
        self.trail.append(self.position.to_array())
        if len(self.trail) > 200:
            self.trail.pop(0)
        self.position = self.position + self.velocity * dt
    def info(self) -> str:
        status = "Destroyed" if self.destroyed else ("Hit Ground" if self.hit_ground else "Active")
        return f"Name: {self.name}\nStatus: {status}\nPos: {self.position}\nVel: {self.velocity}"

class Missile(Threat):
    __slots__ = ('gravity',)
    def __init__(self, position: Vector3D, velocity: Vector3D, name: str):
        super().__init__(position, velocity, name)
        self.gravity = Vector3D(0.0, 0.0, -9.8)
    def update(self, dt: float):
        if self.destroyed or self.hit_ground:
            return
        self.velocity = self.velocity + self.gravity * dt
        super().update(dt)

class Jet(Threat):
    __slots__ = ('evasion_strength',)
    def __init__(self, position: Vector3D, velocity: Vector3D, name: str):
        super().__init__(position, velocity, name)
        self.evasion_strength = 100.0
    def update(self, dt: float):
        if self.destroyed or self.hit_ground:
            return
        ev = Vector3D(random.uniform(-1,1), random.uniform(-1,1), random.uniform(-0.3,0.3)).normalize() * (self.evasion_strength * dt)
        self.velocity = self.velocity + ev
        speed = self.velocity.magnitude()
        if speed > 800.0:
            self.velocity = self.velocity.normalize() * 800.0
        elif speed < 200.0:
            self.velocity = self.velocity.normalize() * 200.0
        super().update(dt)

# ===================== Interceptor Class =====================

class Interceptor:
    __slots__ = ('position','velocity','name','destroyed','trail','target','lifetime','elapsed')
    def __init__(self, position: Vector3D, velocity: Vector3D, name: str, target, lifetime: float):
        self.position = position
        self.velocity = velocity
        self.name = name
        self.destroyed = False
        self.trail = []
        self.target = target
        self.lifetime = lifetime
        self.elapsed = 0.0
    def update(self, dt: float):
        if self.destroyed:
            return
        self.elapsed += dt
        if self.elapsed > self.lifetime:
            self.destroyed = True
            if self.target and not self.target.destroyed and not self.target.hit_ground:
                self.target.targeted = False
            return
        self.trail.append(self.position.to_array())
        if len(self.trail) > 200:
            self.trail.pop(0)
        self.position = self.position + self.velocity * dt

# ===================== Defense System =====================

class DefenseSystem:
    __slots__ = ('position','radar_range','interceptor_speed','max_interceptors','alert_callback','interceptors','destruction_messages','total_launches','total_intercepted','total_missed')
    def __init__(self, position: Vector3D,
                 radar_range=30000.0,
                 interceptor_speed=10000.0,
                 max_interceptors=30,
                 alert_callback=None):
        self.position = position
        self.radar_range = radar_range
        self.interceptor_speed = interceptor_speed
        self.max_interceptors = max_interceptors
        self.alert_callback = alert_callback
        self.interceptors = []
        self.destruction_messages = []
        self.total_launches = 0
        self.total_intercepted = 0
        self.total_missed = 0
    def detect_and_launch(self, threats: list):
        detectable = []
        for threat in threats:
            if threat.destroyed or threat.targeted or threat.hit_ground:
                continue
            dist = (threat.position - self.position).magnitude()
            if dist <= self.radar_range:
                t_est = self._estimate_intercept_time(threat)
                if t_est and t_est > 0:
                    detectable.append((threat, t_est))
        if not detectable:
            return
        # Sort by t_est ascending for variable ordering (smallest t_est first, like MRV heuristic for urgency)
        detectable.sort(key=lambda x: x[1])
        threat_list = [t for t, _ in detectable]
        available_slots = self.max_interceptors - len(self.interceptors)
        selected_threats = self._assign_interceptors_csp(threat_list, available_slots)
        for threat in selected_threats:
            t_est = next(te for tr, te in detectable if tr == threat)
            interceptor = self.launch_interceptor(threat, t_est)
            if interceptor:
                self.interceptors.append(interceptor)
                threat.targeted = True
                self.total_launches += 1
                msg = f"Interceptor {interceptor.name} launched for {threat.name}"
                self.destruction_messages.append(msg)
                if self.alert_callback:
                    self.alert_callback(msg, alert_type="launch")

    def _assign_interceptors_csp(self, threats, available_slots):
        assignment = {}
        def is_consistent(assignment):
            count = sum(1 for v in assignment.values() if v == 'target')
            return count <= available_slots
        def backtrack(var_index):
            if var_index == len(threats):
                return assignment.copy()  # Return a copy of the valid assignment
            variable = threats[var_index]
            for value in ['target', 'not_target']:  # Prefer 'target' first to maximize interceptions
                assignment[variable] = value
                if is_consistent(assignment):
                    result = backtrack(var_index + 1)
                    if result:
                        return result
                del assignment[variable]
            return None
        result = backtrack(0)
        if result:
            return [threat for threat in threats if result.get(threat) == 'target']
        return []

    def _estimate_intercept_time(self, threat: Threat):
        r = threat.position - self.position
        v = threat.velocity
        s = self.interceptor_speed
        a = v.dot(v) - s*s
        b = 2 * r.dot(v)
        c = r.dot(r)
        disc = b*b - 4*a*c
        if disc < 0:
            return None
        if abs(a) < 1e-6:
            if abs(b) < 1e-6:
                return None
            t = -c / b
            return t if t > 0 else None
        sqrt_disc = math.sqrt(disc)
        t1 = (-b + sqrt_disc) / (2*a)
        t2 = (-b - sqrt_disc) / (2*a)
        times = [t for t in (t1, t2) if t > 0]
        return min(times) if times else None
    def launch_interceptor(self, threat: Threat, t_est: float):
        intercept_point = threat.position + threat.velocity * t_est
        direction = (intercept_point - self.position).normalize()
        velocity = direction * self.interceptor_speed
        name = f"I{len(self.interceptors) + 1}"
        lifetime = t_est * 2.0 + 1.0
        return Interceptor(Vector3D(self.position.x, self.position.y, self.position.z),
                           velocity, name, threat, lifetime)
    def update(self, dt: float, threats: list):
        for interceptor in list(self.interceptors):
            interceptor.update(dt)
        for threat in threats:
            if threat.destroyed or threat.hit_ground:
                continue
            for interceptor in list(self.interceptors):
                if interceptor.destroyed:
                    continue
                dist = (threat.position - interceptor.position).magnitude()
                if dist < 200:
                    threat.destroyed = True
                    interceptor.destroyed = True
                    self.total_intercepted += 1
                    msg = f"{threat.name} intercepted by {interceptor.name}"
                    self.destruction_messages.append(msg)
                    if self.alert_callback:
                        self.alert_callback(msg, alert_type="intercept")
        self.interceptors = [i for i in self.interceptors if not i.destroyed]
    def record_misses(self, threats: list):
        for threat in threats:
            if not threat.destroyed and not threat.hit_ground and threat.position.z <= 0:
                threat.hit_ground = True
                self.total_missed += 1
                threat.targeted = False
                msg = f"{threat.name} hit ground!"
                self.destruction_messages.append(msg)
                if self.alert_callback:
                    self.alert_callback(msg, alert_type="hit")

# ===================== Main GUI Application =====================

class FinalAirDefenseApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("SentinelX: Next-Gen Air Defense Simulator")
        self.geometry("1400x900")
        self.bg_color = '#1e1e2e'
        self.fg_color = '#ffffff'
        self.accent_color = '#00ffff'
        self.configure(bg=self.bg_color)
        style = ttk.Style(self)
        style.theme_use('clam')
        style.configure('TFrame', background=self.bg_color)
        style.configure('TLabel', background=self.bg_color, foreground=self.fg_color, font=('Helvetica', 10))
        style.configure('Header.TLabel', background=self.bg_color, foreground=self.accent_color, font=('Helvetica', 16, 'bold'))
        style.configure('Alert.TLabel', background=self.bg_color, font=('Helvetica', 12, 'bold'))
        style.configure('TButton', font=('Helvetica', 10, 'bold'), padding=5)
        style.configure('TSpinbox', font=('Helvetica', 10))
        style.configure('TEntry', font=('Helvetica', 10))
        self.num_missiles = tk.IntVar(value=20)
        self.num_jets = tk.IntVar(value=8)
        self.radar_range = tk.DoubleVar(value=30000.0)
        self.interceptor_speed = tk.DoubleVar(value=10000.0)
        self.max_interceptors = tk.IntVar(value=30)
        self.simulation_running = False
        self.threats = []
        self.defense = None
        self.sim_thread = None
        self.dt = 0.01
        self.start_time = None
        self.stats_history = {'time': [], 'launched': [], 'intercepted': [], 'missed': []}
        self.setup_ui()

    def setup_ui(self):
        notebook = ttk.Notebook(self)
        notebook.pack(expand=True, fill='both')
        sim_frame = ttk.Frame(notebook)
        log_frame = ttk.Frame(notebook)
        stats_frame = ttk.Frame(notebook)
        notebook.add(sim_frame, text="Simulation")
        notebook.add(log_frame, text="Logs")
        notebook.add(stats_frame, text="Statistics")
        control_frame = tk.Frame(sim_frame, bg=self.bg_color, bd=2, relief=tk.RIDGE)
        control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        ttk.Label(control_frame, text="SentinelX Controls", style='Header.TLabel').pack(pady=10)
        self.alert_label = ttk.Label(control_frame, text="", style='Alert.TLabel')
        self.alert_label.pack(pady=(0, 10))
        ttk.Label(control_frame, text="Number of Missiles:").pack(anchor=tk.W, padx=10)
        ttk.Spinbox(control_frame, from_=1, to=200, textvariable=self.num_missiles).pack(fill=tk.X, padx=10, pady=2)
        ttk.Label(control_frame, text="Number of Jets:").pack(anchor=tk.W, padx=10, pady=(10, 0))
        ttk.Spinbox(control_frame, from_=0, to=100, textvariable=self.num_jets).pack(fill=tk.X, padx=10, pady=2)
        ttk.Label(control_frame, text="Radar Range:").pack(anchor=tk.W, padx=10, pady=(10, 0))
        ttk.Entry(control_frame, textvariable=self.radar_range).pack(fill=tk.X, padx=10, pady=2)
        ttk.Label(control_frame, text="Interceptor Speed:").pack(anchor=tk.W, padx=10, pady=(10, 0))
        ttk.Entry(control_frame, textvariable=self.interceptor_speed).pack(fill=tk.X, padx=10, pady=2)
        ttk.Label(control_frame, text="Max Interceptors:").pack(anchor=tk.W, padx=10, pady=(10, 0))
        ttk.Spinbox(control_frame, from_=1, to=100, textvariable=self.max_interceptors).pack(fill=tk.X, padx=10, pady=2)
        ttk.Button(control_frame, text="Start Simulation", command=self.start_simulation).pack(fill=tk.X, padx=10, pady=(20, 5))
        ttk.Button(control_frame, text="Stop Simulation", command=self.stop_simulation).pack(fill=tk.X, padx=10)
        self.status_label = ttk.Label(control_frame, text="Status: Idle", foreground=self.accent_color)
        self.status_label.pack(pady=10)
        ttk.Label(control_frame, text="Active Threats:").pack(anchor=tk.W, padx=10, pady=(20, 0))
        self.threat_listbox = tk.Listbox(control_frame, height=15, bg=self.bg_color, fg=self.fg_color)
        self.threat_listbox.pack(fill=tk.X, padx=10, pady=2)
        self.threat_listbox.bind("<<ListboxSelect>>", self.on_threat_select)
        self.threat_info_label = ttk.Label(control_frame, text="Select a threat to see details.", wraplength=200)
        self.threat_info_label.pack(padx=10, pady=5)
        ttk.Button(control_frame, text="Manual Intercept", command=self.manual_intercept).pack(fill=tk.X, padx=10, pady=(10, 5))
        self.fig = plt.Figure(figsize=(8, 6))
        self.ax = self.fig.add_subplot(111, projection='3d', facecolor='black')
        self.canvas = FigureCanvasTkAgg(self.fig, master=sim_frame)
        self.canvas.get_tk_widget().pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        ttk.Label(log_frame, text="Simulation Logs", style='Header.TLabel').pack(pady=10)
        self.log_text = scrolledtext.ScrolledText(log_frame, wrap=tk.WORD, height=30, bg=self.bg_color, fg=self.fg_color)
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        ttk.Label(stats_frame, text="Simulation Statistics", style='Header.TLabel').pack(pady=10)
        stats_plot_frame = tk.Frame(stats_frame, bg=self.bg_color)
        stats_plot_frame.pack(fill=tk.BOTH, expand=True)
        self.stats_fig = plt.Figure(figsize=(6, 4), facecolor='black')
        self.stats_ax = self.stats_fig.add_subplot(111)
        self.stats_canvas = FigureCanvasTkAgg(self.stats_fig, master=stats_plot_frame)
        self.stats_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def show_alert(self, message: str, alert_type="info"):
        colors = {"launch":"#00ff00","intercept":"#00ff88","hit":"#ff4444","info":"#88ccff"}
        color = colors.get(alert_type, "#88ccff")
        self.alert_label.config(text=message, foreground=color)
        timestamp = time.strftime("%H:%M:%S", time.localtime())
        self.log_text.insert(tk.END, f"[{timestamp}] {message}\n")
        self.log_text.see(tk.END)
        if hasattr(self, 'alert_after_id'):
            self.after_cancel(self.alert_after_id)
        self.alert_after_id = self.after(1500, lambda: self.alert_label.config(text=""))

    def on_threat_select(self, event):
        sel = self.threat_listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        if idx < len(self.threats):
            threat = self.threats[idx]
            status = "Destroyed" if threat.destroyed else ("Hit Ground" if threat.hit_ground else "Active")
            dist = math.floor((threat.position - self.defense.position).magnitude()) if not threat.destroyed else 0
            info = (f"Name: {threat.name}\nType: {'Jet' if isinstance(threat, Jet) else 'Missile'}\n"
                    f"Status: {status}\nPos: {threat.position}\nVel: {threat.velocity}\nDistance: {dist}")
            self.threat_info_label.config(text=info)

    def manual_intercept(self):
        sel = self.threat_listbox.curselection()
        if not sel:
            messagebox.showinfo("No Selection","Select a threat to intercept manually.")
            return
        idx = sel[0]
        if idx < len(self.threats):
            threat = self.threats[idx]
            if threat.destroyed or threat.hit_ground:
                messagebox.showinfo("Invalid","Threat already neutralized.")
                return
            t_est = self.defense._estimate_intercept_time(threat)
            if t_est is None or t_est <= 0:
                messagebox.showwarning("Cannot Intercept","No feasible intercept trajectory.")
                return
            interceptor = self.defense.launch_interceptor(threat, t_est)
            if interceptor:
                self.defense.interceptors.append(interceptor)
                threat.targeted = True
                self.defense.total_launches += 1
                msg = f"Manual interceptor {interceptor.name} launched for {threat.name}"
                self.defense.destruction_messages.append(msg)
                self.show_alert(msg, alert_type="launch")

    def start_simulation(self):
        if self.simulation_running:
            return
        self.simulation_running = True
        self.status_label.config(text="Status: Running", foreground=self.accent_color)
        self.threats = []
        self.defense = DefenseSystem(
            Vector3D(0,0,0),
            radar_range=self.radar_range.get(),
            interceptor_speed=self.interceptor_speed.get(),
            max_interceptors=self.max_interceptors.get(),
            alert_callback=self.show_alert
        )
        for i in range(self.num_missiles.get()):
            pos = Vector3D(random.uniform(-30000,30000), random.uniform(-30000,30000), random.uniform(25000,40000))
            vel = Vector3D(random.uniform(-2000,2000), random.uniform(-2000,2000), random.uniform(-1500,-800))
            self.threats.append(Missile(pos, vel, f"M{i+1}"))
        for j in range(self.num_jets.get()):
            pos = Vector3D(random.uniform(-30000,30000), -30000, random.uniform(20000,30000))
            vel = Vector3D(random.uniform(-2500,2500), random.uniform(800,1200), random.uniform(-400,400))
            self.threats.append(Jet(pos, vel, f"J{j+1}"))
        self.start_time = time.time()
        self.stats_history = {'time':[],'launched':[],'intercepted':[],'missed':[]}
        self.log_text.delete(1.0, tk.END)
        self.defense.detect_and_launch(self.threats)
        self.sim_thread = threading.Thread(target=self.simulation_loop, daemon=True)
        self.sim_thread.start()
        self.after(0, self.update_threat_list)

    def stop_simulation(self):
        if not self.simulation_running:
            return
        self.simulation_running = False
        self.status_label.config(text="Status: Stopped", foreground='#ff4444')

    def simulation_loop(self):
        while self.simulation_running:
            for threat in list(self.threats):
                threat.update(self.dt)
                if not threat.destroyed and not threat.hit_ground and threat.position.z <= 0:
                    self.defense.record_misses(self.threats)
            self.defense.radar_range = self.radar_range.get()
            self.defense.interceptor_speed = self.interceptor_speed.get()
            self.defense.max_interceptors = self.max_interceptors.get()
            self.defense.detect_and_launch(self.threats)
            self.defense.update(self.dt, self.threats)
            self.after(0, self.redraw_plot)
            self.after(0, self.update_threat_list)
            self.after(0, self.update_statistics)
            time.sleep(self.dt)
        self.status_label.config(text="Status: Idle", foreground=self.accent_color)

    def update_threat_list(self):
        self.threat_listbox.delete(0, tk.END)
        for threat in self.threats:
            status = ("Destroyed" if threat.destroyed else ("Hit Ground" if threat.hit_ground else "Active"))
            self.threat_listbox.insert(tk.END, f"{threat.name}: {status}")

    def redraw_plot(self):
        self.ax.clear()
        limit = 35000
        self.ax.set_xlim([-limit, limit])
        self.ax.set_ylim([-limit, limit])
        self.ax.set_zlim([0, limit])
        self.ax.set_facecolor('black')
        self.ax.set_title("SentinelX Simulator", color=self.accent_color, fontsize=14)
        try:
            u = np.linspace(0, 2*np.pi, 30)
            v = np.linspace(0, np.pi, 30)
            x = self.defense.radar_range * np.outer(np.cos(u), np.sin(v))
            y = self.defense.radar_range * np.outer(np.sin(u), np.sin(v))
            z = self.defense.radar_range * np.outer(np.ones_like(u), np.cos(v))
            self.ax.plot_wireframe(x, y, z, color=self.accent_color, alpha=0.03)
        except Exception:
            pass
        dp = self.defense.position.to_array()
        self.ax.scatter(dp[0], dp[1], dp[2], c=self.accent_color, s=200, label="Base")
        self.ax.text(dp[0], dp[1], dp[2], "Base", color=self.fg_color)
        for threat in self.threats:
            if threat.destroyed or threat.hit_ground:
                continue
            if isinstance(threat, Missile):
                color = 'red'; marker='o'
            else:
                color = 'orange'; marker='^'
            p = threat.position.to_array()
            self.ax.scatter(p[0], p[1], p[2], c=color, s=80, marker=marker)
            self.ax.text(p[0], p[1], p[2], threat.name, color=self.fg_color, fontsize=8)
            if threat.trail:
                trail = np.array(threat.trail)
                self.ax.plot(trail[:,0], trail[:,1], trail[:,2], c=color, alpha=0.3)
        for interceptor in self.defense.interceptors:
            if interceptor.destroyed: continue
            p = interceptor.position.to_array()
            self.ax.scatter(p[0], p[1], p[2], c='lime', s=80, marker='x')
            self.ax.text(p[0], p[1], p[2], interceptor.name, color=self.fg_color, fontsize=8)
            if interceptor.trail:
                trail = np.array(interceptor.trail)
                self.ax.plot(trail[:,0], trail[:,1], trail[:,2], c='lime', alpha=0.3)
        msgs = self.defense.destruction_messages[-5:]
        for i, msg in enumerate(msgs):
            self.ax.text2D(0.02, 0.95 - i*0.05, msg, transform=self.ax.transAxes, color=self.fg_color, fontsize=9)
        self.canvas.draw()

    def update_statistics(self):
        elapsed = time.time() - self.start_time if self.start_time else 0
        self.stats_history['time'].append(elapsed)
        self.stats_history['launched'].append(self.defense.total_launches)
        self.stats_history['intercepted'].append(self.defense.total_intercepted)
        self.stats_history['missed'].append(self.defense.total_missed)
        self.stats_ax.clear()
        self.stats_ax.set_facecolor('black')
        self.stats_ax.plot(self.stats_history['time'], self.stats_history['launched'], label='Launched', color='cyan')
        self.stats_ax.plot(self.stats_history['time'], self.stats_history['intercepted'], label='Intercepted', color='lime')
        self.stats_ax.plot(self.stats_history['time'], self.stats_history['missed'], label='Missed', color='red')
        self.stats_ax.set_xlabel("Time (s)", color=self.fg_color)
        self.stats_ax.set_ylabel("Count", color=self.fg_color)
        self.stats_ax.set_title("Defense System Stats Over Time", color=self.fg_color)
        self.stats_ax.legend(facecolor='black', edgecolor='white')
        self.stats_ax.tick_params(colors=self.fg_color)
        self.stats_canvas.draw()

if __name__ == "__main__":
    app = FinalAirDefenseApp()
    app.mainloop()