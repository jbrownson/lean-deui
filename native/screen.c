// deui's screen, native (SDL3, WebGPU and ThorVG)
// =================================================
//
// The effects in Deui/Screen.lean. SDL3 gives the window and its events,
// wgpu-native gives WebGPU on Vulkan (or Metal, or DirectX), and ThorVG's
// WebGPU engine draws onto the window's surface, its labels in a TrueType
// font. The three are opened with dlopen on first use; their headers only
// supply the types.
//
// One window at a time. Events cross into Lean as words; the scene and its
// edits are read as Lean values, laid out as lean.h says: a constructor's
// object fields first, then its scalars, Int32 and UInt32 as 4 bytes each.
//
// Lean's coordinates are the window's, as SDL reports the mouse in. The
// window has the display's full resolution, and the kept scene is drawn
// scaled by its pixel density, so everything, text included, is drawn at
// full resolution.
//
// The screen keeps a copy of the scene, set once and then changed only by
// the scene's edits, as SceneEdit.apply makes them, and ThorVG keeps a paint
// for each part of it that's drawn. A frame only asks ThorVG to draw what it
// keeps.

#include <lean/lean.h>
#include <dlfcn.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <SDL3/SDL.h>
#include <webgpu/webgpu.h>
#include <thorvg-1/thorvg_capi.h>

typedef uint32_t u32;
typedef uint64_t u64;

// The libraries, opened
// ---------------------

static __typeof__(SDL_Init)* ds_SDL_Init;
static __typeof__(SDL_Quit)* ds_SDL_Quit;
static __typeof__(SDL_GetError)* ds_SDL_GetError;
static __typeof__(SDL_CreateWindow)* ds_SDL_CreateWindow;
static __typeof__(SDL_DestroyWindow)* ds_SDL_DestroyWindow;
static __typeof__(SDL_GetWindowProperties)* ds_SDL_GetWindowProperties;
static __typeof__(SDL_GetPointerProperty)* ds_SDL_GetPointerProperty;
static __typeof__(SDL_GetNumberProperty)* ds_SDL_GetNumberProperty;
static __typeof__(SDL_GetCurrentVideoDriver)* ds_SDL_GetCurrentVideoDriver;
static __typeof__(SDL_GetWindowSizeInPixels)* ds_SDL_GetWindowSizeInPixels;
static __typeof__(SDL_GetWindowPixelDensity)* ds_SDL_GetWindowPixelDensity;
static __typeof__(SDL_StartTextInput)* ds_SDL_StartTextInput;
static __typeof__(SDL_WaitEventTimeout)* ds_SDL_WaitEventTimeout;
static __typeof__(SDL_PollEvent)* ds_SDL_PollEvent;
static __typeof__(SDL_LoadFile)* ds_SDL_LoadFile;
static __typeof__(SDL_free)* ds_SDL_free;
static __typeof__(SDL_SetClipboardText)* ds_SDL_SetClipboardText;
static __typeof__(SDL_GetClipboardText)* ds_SDL_GetClipboardText;
static __typeof__(wgpuCreateInstance)* ds_wgpuCreateInstance;
static __typeof__(wgpuInstanceCreateSurface)* ds_wgpuInstanceCreateSurface;
static __typeof__(wgpuInstanceRequestAdapter)* ds_wgpuInstanceRequestAdapter;
static __typeof__(wgpuAdapterRequestDevice)* ds_wgpuAdapterRequestDevice;
static __typeof__(wgpuInstanceProcessEvents)* ds_wgpuInstanceProcessEvents;
static __typeof__(wgpuSurfacePresent)* ds_wgpuSurfacePresent;
static __typeof__(wgpuSurfaceRelease)* ds_wgpuSurfaceRelease;
static __typeof__(wgpuDeviceRelease)* ds_wgpuDeviceRelease;
static __typeof__(wgpuAdapterRelease)* ds_wgpuAdapterRelease;
static __typeof__(wgpuInstanceRelease)* ds_wgpuInstanceRelease;
static __typeof__(tvg_engine_init)* ds_tvg_engine_init;
static __typeof__(tvg_engine_term)* ds_tvg_engine_term;
static __typeof__(tvg_wgcanvas_create)* ds_tvg_wgcanvas_create;
static __typeof__(tvg_wgcanvas_set_target_with_context)* ds_tvg_wgcanvas_set_target_with_context;
static __typeof__(tvg_canvas_destroy)* ds_tvg_canvas_destroy;
static __typeof__(tvg_canvas_add)* ds_tvg_canvas_add;
static __typeof__(tvg_canvas_remove)* ds_tvg_canvas_remove;
static __typeof__(tvg_paint_rel)* ds_tvg_paint_rel;
static __typeof__(tvg_shape_reset)* ds_tvg_shape_reset;
static __typeof__(tvg_canvas_update)* ds_tvg_canvas_update;
static __typeof__(tvg_paint_scale)* ds_tvg_paint_scale;
static __typeof__(tvg_scene_remove)* ds_tvg_scene_remove;
static __typeof__(tvg_scene_insert)* ds_tvg_scene_insert;
static __typeof__(tvg_scene_add)* ds_tvg_scene_add;
static __typeof__(tvg_scene_new)* ds_tvg_scene_new;
static __typeof__(tvg_canvas_draw)* ds_tvg_canvas_draw;
static __typeof__(tvg_canvas_sync)* ds_tvg_canvas_sync;
static __typeof__(tvg_shape_new)* ds_tvg_shape_new;
static __typeof__(tvg_shape_append_rect)* ds_tvg_shape_append_rect;
static __typeof__(tvg_shape_set_fill_color)* ds_tvg_shape_set_fill_color;
static __typeof__(tvg_text_new)* ds_tvg_text_new;
static __typeof__(tvg_text_set_font)* ds_tvg_text_set_font;
static __typeof__(tvg_text_set_size)* ds_tvg_text_set_size;
static __typeof__(tvg_text_set_text)* ds_tvg_text_set_text;
static __typeof__(tvg_text_set_color)* ds_tvg_text_set_color;
static __typeof__(tvg_paint_translate)* ds_tvg_paint_translate;
static __typeof__(tvg_font_load_data)* ds_tvg_font_load_data;
static __typeof__(tvg_font_unload)* ds_tvg_font_unload;

// Opens the libraries and finds every function, once; false if any is
// missing.
static bool ds_load(void) {
  static int state = 0;
  if (state != 0) {
    return state == 1;
  }
  void* libsdl = dlopen("libSDL3.so.0", RTLD_NOW | RTLD_GLOBAL);
  void* libwgpu = dlopen("libwgpu_native.so", RTLD_NOW | RTLD_GLOBAL);
  void* libtvg = dlopen("libthorvg-1.so.1", RTLD_NOW | RTLD_GLOBAL);
  bool ok = libsdl != NULL && libwgpu != NULL && libtvg != NULL;
  ok = ok && (ds_SDL_Init = (__typeof__(SDL_Init)*)dlsym(libsdl, "SDL_Init"));
  ok = ok && (ds_SDL_Quit = (__typeof__(SDL_Quit)*)dlsym(libsdl, "SDL_Quit"));
  ok = ok && (ds_SDL_GetError = (__typeof__(SDL_GetError)*)dlsym(libsdl, "SDL_GetError"));
  ok = ok && (ds_SDL_CreateWindow = (__typeof__(SDL_CreateWindow)*)dlsym(libsdl, "SDL_CreateWindow"));
  ok = ok && (ds_SDL_DestroyWindow = (__typeof__(SDL_DestroyWindow)*)dlsym(libsdl, "SDL_DestroyWindow"));
  ok = ok && (ds_SDL_GetWindowProperties = (__typeof__(SDL_GetWindowProperties)*)dlsym(libsdl, "SDL_GetWindowProperties"));
  ok = ok && (ds_SDL_GetPointerProperty = (__typeof__(SDL_GetPointerProperty)*)dlsym(libsdl, "SDL_GetPointerProperty"));
  ok = ok && (ds_SDL_GetNumberProperty = (__typeof__(SDL_GetNumberProperty)*)dlsym(libsdl, "SDL_GetNumberProperty"));
  ok = ok && (ds_SDL_GetCurrentVideoDriver = (__typeof__(SDL_GetCurrentVideoDriver)*)dlsym(libsdl, "SDL_GetCurrentVideoDriver"));
  ok = ok && (ds_SDL_GetWindowSizeInPixels = (__typeof__(SDL_GetWindowSizeInPixels)*)dlsym(libsdl, "SDL_GetWindowSizeInPixels"));
  ok = ok && (ds_SDL_GetWindowPixelDensity = (__typeof__(SDL_GetWindowPixelDensity)*)dlsym(libsdl, "SDL_GetWindowPixelDensity"));
  ok = ok && (ds_SDL_StartTextInput = (__typeof__(SDL_StartTextInput)*)dlsym(libsdl, "SDL_StartTextInput"));
  ok = ok && (ds_SDL_WaitEventTimeout = (__typeof__(SDL_WaitEventTimeout)*)dlsym(libsdl, "SDL_WaitEventTimeout"));
  ok = ok && (ds_SDL_PollEvent = (__typeof__(SDL_PollEvent)*)dlsym(libsdl, "SDL_PollEvent"));
  ok = ok && (ds_SDL_LoadFile = (__typeof__(SDL_LoadFile)*)dlsym(libsdl, "SDL_LoadFile"));
  ok = ok && (ds_SDL_free = (__typeof__(SDL_free)*)dlsym(libsdl, "SDL_free"));
  ok = ok && (ds_SDL_SetClipboardText = (__typeof__(SDL_SetClipboardText)*)dlsym(libsdl, "SDL_SetClipboardText"));
  ok = ok && (ds_SDL_GetClipboardText = (__typeof__(SDL_GetClipboardText)*)dlsym(libsdl, "SDL_GetClipboardText"));
  ok = ok && (ds_wgpuCreateInstance = (__typeof__(wgpuCreateInstance)*)dlsym(libwgpu, "wgpuCreateInstance"));
  ok = ok && (ds_wgpuInstanceCreateSurface = (__typeof__(wgpuInstanceCreateSurface)*)dlsym(libwgpu, "wgpuInstanceCreateSurface"));
  ok = ok && (ds_wgpuInstanceRequestAdapter = (__typeof__(wgpuInstanceRequestAdapter)*)dlsym(libwgpu, "wgpuInstanceRequestAdapter"));
  ok = ok && (ds_wgpuAdapterRequestDevice = (__typeof__(wgpuAdapterRequestDevice)*)dlsym(libwgpu, "wgpuAdapterRequestDevice"));
  ok = ok && (ds_wgpuInstanceProcessEvents = (__typeof__(wgpuInstanceProcessEvents)*)dlsym(libwgpu, "wgpuInstanceProcessEvents"));
  ok = ok && (ds_wgpuSurfacePresent = (__typeof__(wgpuSurfacePresent)*)dlsym(libwgpu, "wgpuSurfacePresent"));
  ok = ok && (ds_wgpuSurfaceRelease = (__typeof__(wgpuSurfaceRelease)*)dlsym(libwgpu, "wgpuSurfaceRelease"));
  ok = ok && (ds_wgpuDeviceRelease = (__typeof__(wgpuDeviceRelease)*)dlsym(libwgpu, "wgpuDeviceRelease"));
  ok = ok && (ds_wgpuAdapterRelease = (__typeof__(wgpuAdapterRelease)*)dlsym(libwgpu, "wgpuAdapterRelease"));
  ok = ok && (ds_wgpuInstanceRelease = (__typeof__(wgpuInstanceRelease)*)dlsym(libwgpu, "wgpuInstanceRelease"));
  ok = ok && (ds_tvg_engine_init = (__typeof__(tvg_engine_init)*)dlsym(libtvg, "tvg_engine_init"));
  ok = ok && (ds_tvg_engine_term = (__typeof__(tvg_engine_term)*)dlsym(libtvg, "tvg_engine_term"));
  ok = ok && (ds_tvg_wgcanvas_create = (__typeof__(tvg_wgcanvas_create)*)dlsym(libtvg, "tvg_wgcanvas_create"));
  ok = ok && (ds_tvg_wgcanvas_set_target_with_context = (__typeof__(tvg_wgcanvas_set_target_with_context)*)dlsym(libtvg, "tvg_wgcanvas_set_target_with_context"));
  ok = ok && (ds_tvg_canvas_destroy = (__typeof__(tvg_canvas_destroy)*)dlsym(libtvg, "tvg_canvas_destroy"));
  ok = ok && (ds_tvg_canvas_add = (__typeof__(tvg_canvas_add)*)dlsym(libtvg, "tvg_canvas_add"));
  ok = ok && (ds_tvg_canvas_remove = (__typeof__(tvg_canvas_remove)*)dlsym(libtvg, "tvg_canvas_remove"));
  ok = ok && (ds_tvg_paint_rel = (__typeof__(tvg_paint_rel)*)dlsym(libtvg, "tvg_paint_rel"));
  ok = ok && (ds_tvg_shape_reset = (__typeof__(tvg_shape_reset)*)dlsym(libtvg, "tvg_shape_reset"));
  ok = ok && (ds_tvg_canvas_update = (__typeof__(tvg_canvas_update)*)dlsym(libtvg, "tvg_canvas_update"));
  ok = ok && (ds_tvg_paint_scale = (__typeof__(tvg_paint_scale)*)dlsym(libtvg, "tvg_paint_scale"));
  ok = ok && (ds_tvg_scene_remove = (__typeof__(tvg_scene_remove)*)dlsym(libtvg, "tvg_scene_remove"));
  ok = ok && (ds_tvg_scene_insert = (__typeof__(tvg_scene_insert)*)dlsym(libtvg, "tvg_scene_insert"));
  ok = ok && (ds_tvg_scene_add = (__typeof__(tvg_scene_add)*)dlsym(libtvg, "tvg_scene_add"));
  ok = ok && (ds_tvg_scene_new = (__typeof__(tvg_scene_new)*)dlsym(libtvg, "tvg_scene_new"));
  ok = ok && (ds_tvg_canvas_draw = (__typeof__(tvg_canvas_draw)*)dlsym(libtvg, "tvg_canvas_draw"));
  ok = ok && (ds_tvg_canvas_sync = (__typeof__(tvg_canvas_sync)*)dlsym(libtvg, "tvg_canvas_sync"));
  ok = ok && (ds_tvg_shape_new = (__typeof__(tvg_shape_new)*)dlsym(libtvg, "tvg_shape_new"));
  ok = ok && (ds_tvg_shape_append_rect = (__typeof__(tvg_shape_append_rect)*)dlsym(libtvg, "tvg_shape_append_rect"));
  ok = ok && (ds_tvg_shape_set_fill_color = (__typeof__(tvg_shape_set_fill_color)*)dlsym(libtvg, "tvg_shape_set_fill_color"));
  ok = ok && (ds_tvg_text_new = (__typeof__(tvg_text_new)*)dlsym(libtvg, "tvg_text_new"));
  ok = ok && (ds_tvg_text_set_font = (__typeof__(tvg_text_set_font)*)dlsym(libtvg, "tvg_text_set_font"));
  ok = ok && (ds_tvg_text_set_size = (__typeof__(tvg_text_set_size)*)dlsym(libtvg, "tvg_text_set_size"));
  ok = ok && (ds_tvg_text_set_text = (__typeof__(tvg_text_set_text)*)dlsym(libtvg, "tvg_text_set_text"));
  ok = ok && (ds_tvg_text_set_color = (__typeof__(tvg_text_set_color)*)dlsym(libtvg, "tvg_text_set_color"));
  ok = ok && (ds_tvg_paint_translate = (__typeof__(tvg_paint_translate)*)dlsym(libtvg, "tvg_paint_translate"));
  ok = ok && (ds_tvg_font_load_data = (__typeof__(tvg_font_load_data)*)dlsym(libtvg, "tvg_font_load_data"));
  ok = ok && (ds_tvg_font_unload = (__typeof__(tvg_font_unload)*)dlsym(libtvg, "tvg_font_unload"));
  state = ok ? 1 : 2;
  return ok;
}



// The window
// ----------

struct DsNode;

static struct {
  bool           open;
  SDL_Window*    window;
  WGPUInstance   instance;
  WGPUSurface    surface;
  WGPUAdapter    adapter;
  WGPUDevice     device;
  Tvg_Canvas     canvas;
  Tvg_Paint      background;  // a shape filling the window, below the scene
  Tvg_Paint      base;        // a scene holding the kept scene's paint,
                              // scaled by the pixel density
  float          density;
  struct DsNode* root;        // the kept scene
  int            width;       // the canvas's target, in pixels
  int            height;
  bool           font;        // whether a font is loaded, as "deui"
} ds;

static lean_obj_res ds_fail(const char* msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res ds_sdl_fail(const char* what) {
  char msg[512];
  snprintf(msg, sizeof msg, "screen: %s: %s", what, ds_SDL_GetError());
  return ds_fail(msg);
}

static lean_obj_res ds_unit(void) {
  return lean_io_result_mk_ok(lean_box(0));
}

static void* ds_mem(void* p) {
  if (p == NULL) {
    fprintf(stderr, "screen: out of memory\n");
    abort();
  }
  return p;
}

// The window's WebGPU surface, from its Wayland or X11 handles.
static WGPUSurface ds_surface(void) {
  SDL_PropertiesID props = ds_SDL_GetWindowProperties(ds.window);
  const char* driver = ds_SDL_GetCurrentVideoDriver();
  WGPUSurfaceDescriptor desc = { 0 };
  WGPUSurfaceSourceWaylandSurface wayland = { 0 };
  WGPUSurfaceSourceXlibWindow xlib = { 0 };
  if (driver && strcmp(driver, "wayland") == 0) {
    wayland.chain.sType = WGPUSType_SurfaceSourceWaylandSurface;
    wayland.display = ds_SDL_GetPointerProperty(props, SDL_PROP_WINDOW_WAYLAND_DISPLAY_POINTER, NULL);
    wayland.surface = ds_SDL_GetPointerProperty(props, SDL_PROP_WINDOW_WAYLAND_SURFACE_POINTER, NULL);
    desc.nextInChain = &wayland.chain;
  } else if (driver && strcmp(driver, "x11") == 0) {
    xlib.chain.sType = WGPUSType_SurfaceSourceXlibWindow;
    xlib.display = ds_SDL_GetPointerProperty(props, SDL_PROP_WINDOW_X11_DISPLAY_POINTER, NULL);
    xlib.window = (uint64_t)ds_SDL_GetNumberProperty(props, SDL_PROP_WINDOW_X11_WINDOW_NUMBER, 0);
    desc.nextInChain = &xlib.chain;
  } else {
    return NULL;
  }
  return ds_wgpuInstanceCreateSurface(ds.instance, &desc);
}

static void ds_adapter_got(WGPURequestAdapterStatus status, WGPUAdapter adapter,
  WGPUStringView message, void* out, void* unused) {
  *(WGPUAdapter*)out = status == WGPURequestAdapterStatus_Success ? adapter : NULL;
}

static void ds_device_got(WGPURequestDeviceStatus status, WGPUDevice device,
  WGPUStringView message, void* out, void* unused) {
  *(WGPUDevice*)out = status == WGPURequestDeviceStatus_Success ? device : NULL;
}

// The GPU for the window's surface, and a device on it. wgpu-native answers
// these requests at once; the events are processed in case it doesn't.
static const char* ds_gpu(void) {
  ds.instance = ds_wgpuCreateInstance(NULL);
  if (ds.instance == NULL) {
    return "wgpuCreateInstance";
  }
  ds.surface = ds_surface();
  if (ds.surface == NULL) {
    return "the window's surface (Wayland or X11 only)";
  }
  WGPURequestAdapterOptions options = { 0 };
  options.compatibleSurface = ds.surface;
  options.powerPreference = WGPUPowerPreference_HighPerformance;
  WGPURequestAdapterCallbackInfo on_adapter = { 0 };
  on_adapter.mode = WGPUCallbackMode_AllowSpontaneous;
  on_adapter.callback = ds_adapter_got;
  on_adapter.userdata1 = &ds.adapter;
  ds_wgpuInstanceRequestAdapter(ds.instance, &options, on_adapter);
  for (int i = 0; i < 100 && ds.adapter == NULL; i += 1) {
    ds_wgpuInstanceProcessEvents(ds.instance);
  }
  if (ds.adapter == NULL) {
    return "a WebGPU adapter";
  }
  WGPURequestDeviceCallbackInfo on_device = { 0 };
  on_device.mode = WGPUCallbackMode_AllowSpontaneous;
  on_device.callback = ds_device_got;
  on_device.userdata1 = &ds.device;
  ds_wgpuAdapterRequestDevice(ds.adapter, NULL, on_device);
  for (int i = 0; i < 100 && ds.device == NULL; i += 1) {
    ds_wgpuInstanceProcessEvents(ds.instance);
  }
  return ds.device == NULL ? "a WebGPU device" : NULL;
}

static void ds_gpu_release(void) {
  if (ds.device) ds_wgpuDeviceRelease(ds.device);
  if (ds.adapter) ds_wgpuAdapterRelease(ds.adapter);
  if (ds.surface) ds_wgpuSurfaceRelease(ds.surface);
  if (ds.instance) ds_wgpuInstanceRelease(ds.instance);
  ds.device = NULL;
  ds.adapter = NULL;
  ds.surface = NULL;
  ds.instance = NULL;
}



static void ds_close(void);

// A window is a Lean object whose finalizer closes it, if it's still open.
static lean_external_class* ds_window_class = NULL;

static void ds_window_finalize(void* p) {
  if (ds.open) {
    ds_close();
  }
}

static void ds_no_foreach(void* p, b_lean_obj_arg f) {
}

// A window of the given size, taking text input, with a WebGPU device for
// its surface and a ThorVG canvas drawing onto it.
lean_obj_res deui_window_open(b_lean_obj_arg title, uint32_t width, uint32_t height, lean_obj_arg world) {
  if (!ds_load()) {
    return ds_fail("screen: SDL3, wgpu-native and ThorVG (libSDL3.so.0, libwgpu_native.so, libthorvg-1.so.1) not all found");
  }
  if (ds.open || width < 1 || height < 1 || width > 16384 || height > 16384) {
    return ds_fail("screen: one window at a time, and of a sensible size");
  }
  if (!ds_SDL_Init(SDL_INIT_VIDEO)) {
    return ds_sdl_fail("SDL_Init");
  }
  ds.window = ds_SDL_CreateWindow(lean_string_cstr(title), (int)width, (int)height,
    SDL_WINDOW_RESIZABLE | SDL_WINDOW_HIGH_PIXEL_DENSITY);
  if (ds.window == NULL) {
    return ds_sdl_fail("SDL_CreateWindow");
  }
  const char* missing = ds_gpu();
  if (missing != NULL) {
    char msg[256];
    snprintf(msg, sizeof msg, "screen: no %s", missing);
    ds_gpu_release();
    ds_SDL_DestroyWindow(ds.window);
    return ds_fail(msg);
  }
  if (ds_tvg_engine_init(0) != TVG_RESULT_SUCCESS
    || (ds.canvas = ds_tvg_wgcanvas_create(TVG_ENGINE_OPTION_DEFAULT)) == NULL) {
    ds_gpu_release();
    ds_SDL_DestroyWindow(ds.window);
    return ds_fail("screen: ThorVG's WebGPU engine didn't start");
  }
  ds.background = ds_tvg_shape_new();
  ds.base = ds_tvg_scene_new();
  ds_tvg_canvas_add(ds.canvas, ds.background);
  ds_tvg_canvas_add(ds.canvas, ds.base);
  ds.density = 0;
  ds.root = NULL;
  ds_SDL_StartTextInput(ds.window);
  ds.width = 0;
  ds.height = 0;
  ds.open = true;
  if (ds_window_class == NULL) {
    ds_window_class = lean_register_external_class(ds_window_finalize, ds_no_foreach);
  }
  return lean_io_result_mk_ok(lean_alloc_external(ds_window_class, NULL));
}

// The TrueType font labels are drawn in, from its path.
lean_obj_res deui_window_font(b_lean_obj_arg w, b_lean_obj_arg path, lean_obj_arg world) {
  if (!ds.open) {
    return ds_fail("screen: the window is closed");
  }
  size_t size = 0;
  void* data = ds_SDL_LoadFile(lean_string_cstr(path), &size);
  if (data == NULL) {
    return ds_sdl_fail("the font");
  }
  if (ds.font) {
    ds_tvg_font_unload("deui");
  }
  ds.font = ds_tvg_font_load_data("deui", data, (uint32_t)size, "ttf", true) == TVG_RESULT_SUCCESS;
  ds_SDL_free(data);
  return ds.font ? ds_unit() : ds_fail("screen: ThorVG couldn't read the font");
}

// The clipboard
// -------------

// Puts text on the clipboard.
lean_obj_res deui_clipboard_set(b_lean_obj_arg text, lean_obj_arg world) {
  if (!ds.open) {
    return ds_fail("screen: the window is closed");
  }
  if (!ds_SDL_SetClipboardText(lean_string_cstr(text))) {
    return ds_sdl_fail("the clipboard");
  }
  return ds_unit();
}

// The clipboard's text: empty when it holds none.
lean_obj_res deui_clipboard_get(lean_obj_arg world) {
  if (!ds.open) {
    return ds_fail("screen: the window is closed");
  }
  char* text = ds_SDL_GetClipboardText();
  lean_obj_res s = lean_mk_string(text != NULL ? text : "");
  if (text != NULL) {
    ds_SDL_free(text);
  }
  return lean_io_result_mk_ok(s);
}

// Events
// ------

typedef struct {
  u32* w;
  u32  n;
  u32  cap;
} DsWords;

static void ds_put(DsWords* b, u32 x) {
  if (b->n == b->cap) {
    b->cap = b->cap ? b->cap * 2 : 256;
    b->w = ds_mem(realloc(b->w, b->cap * sizeof(u32)));
  }
  b->w[b->n++] = x;
}

// A coordinate, as a Float's 64 bits, high word first.
static void ds_float(DsWords* b, double x) {
  u64 u;
  memcpy(&u, &x, 8);
  ds_put(b, (u32)(u >> 32));
  ds_put(b, (u32)u);
}

// SDL's key as Base's Key code: a key's character in lower case (Return 13,
// Tab 9, Escape 27, Space 32), Backspace 127, the arrows from 63232, the
// function keys from 63236, Insert, Delete, Home, End and the Page keys in
// the private-use area, the modifiers as 65536 + their Mac key code; any
// other key, 131072 + its SDL scancode.
static u32 ds_key(SDL_Keycode k, SDL_Scancode sc) {
  switch (k) {
    case SDLK_BACKSPACE: return 127;
    case SDLK_UP: return 63232;
    case SDLK_DOWN: return 63233;
    case SDLK_LEFT: return 63234;
    case SDLK_RIGHT: return 63235;
    case SDLK_INSERT: return 63271;
    case SDLK_DELETE: return 63272;
    case SDLK_HOME: return 63273;
    case SDLK_END: return 63275;
    case SDLK_PAGEUP: return 63276;
    case SDLK_PAGEDOWN: return 63277;
    case SDLK_RGUI: return 65590;
    case SDLK_LGUI: return 65591;
    case SDLK_LSHIFT: return 65592;
    case SDLK_CAPSLOCK: return 65593;
    case SDLK_LALT: return 65594;
    case SDLK_LCTRL: return 65595;
    case SDLK_RSHIFT: return 65596;
    case SDLK_RALT: return 65597;
    case SDLK_RCTRL: return 65598;
  }
  if (k >= SDLK_F1 && k <= SDLK_F12) {
    return 63236 + (u32)(k - SDLK_F1);
  }
  if (k < 0x40000000u) {
    return (u32)k;
  }
  return 131072 + (u32)sc;
}

// SDL's mouse button as W3C's: 0 the main one, 1 the middle, 2 the right,
// 3 back, 4 forward.
static u32 ds_button(Uint8 b) {
  switch (b) {
    case SDL_BUTTON_LEFT: return 0;
    case SDL_BUTTON_MIDDLE: return 1;
    case SDL_BUTTON_RIGHT: return 2;
    case SDL_BUTTON_X1: return 3;
    case SDL_BUTTON_X2: return 4;
  }
  return b;
}

// UTF-8 as code points, each put as a word.
static void ds_text(DsWords* b, const char* s) {
  const unsigned char* p = (const unsigned char*)s;
  while (*p) {
    u32 c = *p;
    int k = c < 0x80 ? 0 : c < 0xE0 ? 1 : c < 0xF0 ? 2 : 3;
    c = k == 0 ? c : c & (0x3F >> k);
    p += 1;
    for (int i = 0; i < k && (*p & 0xC0) == 0x80; i += 1, p += 1) {
      c = (c << 6) | (*p & 0x3F);
    }
    ds_put(b, c);
  }
}


// One event's words, after a word for their count, as Screen.lean reads
// them; nothing for the rest.
static void ds_event(DsWords* b, SDL_Event* ev) {
  u32 at = b->n;
  ds_put(b, 0);
  switch (ev->type) {
    case SDL_EVENT_MOUSE_BUTTON_DOWN:
    case SDL_EVENT_MOUSE_BUTTON_UP:
      ds_put(b, 1);
      ds_float(b, ev->button.x);
      ds_float(b, ev->button.y);
      ds_put(b, ds_button(ev->button.button));
      ds_put(b, ev->button.down ? 1 : 0);
      break;
    case SDL_EVENT_MOUSE_MOTION:
      ds_put(b, 2);
      ds_float(b, ev->motion.x);
      ds_float(b, ev->motion.y);
      break;
    case SDL_EVENT_KEY_DOWN:
    case SDL_EVENT_KEY_UP:
      ds_put(b, 3);
      ds_put(b, ds_key(ev->key.key, ev->key.scancode));
      ds_put(b, ev->key.down ? 1 : 0);
      ds_put(b, ((ev->key.mod & SDL_KMOD_SHIFT) ? 1 : 0) | ((ev->key.mod & SDL_KMOD_CTRL) ? 2 : 0)
        | ((ev->key.mod & SDL_KMOD_ALT) ? 4 : 0) | ((ev->key.mod & SDL_KMOD_GUI) ? 8 : 0));
      break;
    case SDL_EVENT_TEXT_INPUT:
      ds_put(b, 4);
      ds_text(b, ev->text.text);
      break;
    case SDL_EVENT_MOUSE_WHEEL:
      ds_put(b, 5);
      ds_float(b, ev->wheel.mouse_x);
      ds_float(b, ev->wheel.mouse_y);
      ds_float(b, -ev->wheel.x);
      ds_float(b, ev->wheel.y);
      break;
    case SDL_EVENT_WINDOW_CLOSE_REQUESTED:
    case SDL_EVENT_QUIT:
      ds_put(b, 6);
      break;
    case SDL_EVENT_WINDOW_MOUSE_LEAVE:
      ds_put(b, 7);
      break;
    case SDL_EVENT_WINDOW_FOCUS_GAINED:
    case SDL_EVENT_WINDOW_FOCUS_LOST:
      ds_put(b, 8);
      ds_put(b, ev->type == SDL_EVENT_WINDOW_FOCUS_GAINED ? 1 : 0);
      break;
    case SDL_EVENT_WINDOW_RESIZED:
      ds_put(b, 9);
      ds_put(b, (u32)ev->window.data1);
      ds_put(b, (u32)ev->window.data2);
      break;
    default:
      b->n = at;
      return;
  }
  b->w[at] = b->n - at - 1;
}

// Waits up to ms milliseconds (4294967295: for as long as it takes) for an
// event, then takes every event waiting.
lean_obj_res deui_window_wait(b_lean_obj_arg w, uint32_t ms, lean_obj_arg world) {
  if (!ds.open) {
    return ds_fail("screen: the window is closed");
  }
  DsWords b = { 0 };
  SDL_Event ev;
  bool any = ds_SDL_WaitEventTimeout(&ev, ms == 4294967295u ? -1 : (Sint32)ms);
  while (any) {
    ds_event(&b, &ev);
    any = ds_SDL_PollEvent(&ev);
  }
  lean_object* arr = lean_alloc_array(b.n, b.n);
  for (u32 i = 0; i < b.n; i += 1) {
    lean_array_set_core(arr, i, lean_box_uint32(b.w[i]));
  }
  free(b.w);
  return lean_io_result_mk_ok(arr);
}

// The kept scene
// --------------

// A part of the scene, at (x, y) in its group. A fill, a label or a group
// has a paint, in its group's; a target has none. A group's paint is a
// ThorVG scene holding its children's, in order.
enum { DS_FILL = 0, DS_LABEL = 1, DS_TARGET = 2, DS_GROUP = 3 };

typedef struct DsNode {
  int             kind;
  float           x, y;
  Tvg_Paint       paint;
  struct DsNode** kids;
  u32             len, cap;
} DsNode;

// Frees a part and everything in it; its paints are ThorVG's to free.
static void ds_free(DsNode* n) {
  if (n == NULL) {
    return;
  }
  for (u32 i = 0; i < n->len; i += 1) {
    ds_free(n->kids[i]);
  }
  free(n->kids);
  free(n);
}

static void ds_place(DsNode* n) {
  if (n->paint) {
    ds_tvg_paint_translate(n->paint, n->x, n->y);
  }
}

// A constructor's scalar field: a UInt32's or an Int32's bits, the k-th
// 4-byte scalar after its `objs` object fields.
static u32 ds_u32(b_lean_obj_arg o, unsigned objs, unsigned k) {
  return lean_ctor_get_uint32(o, objs * sizeof(void*) + 4 * k);
}

static float ds_i32(b_lean_obj_arg o, unsigned objs, unsigned k) {
  return (float)(int32_t)ds_u32(o, objs, k);
}

// A Nat, as a position: past what a u32 holds, past every end.
static u32 ds_nat(b_lean_obj_arg n) {
  if (lean_is_scalar(n)) {
    size_t v = lean_unbox(n);
    return v > 0xFFFFFFFFu ? 0xFFFFFFFFu : (u32)v;
  }
  return 0xFFFFFFFFu;
}

static void ds_rgb(u32 rgb, uint8_t* r, uint8_t* g, uint8_t* b) {
  *r = (uint8_t)(rgb >> 16);
  *g = (uint8_t)(rgb >> 8);
  *b = (uint8_t)rgb;
}

static void ds_kid_put(DsNode* g, u32 i, DsNode* kid);

// A scene, read from its Lean value:
//   fill (x y w h : Int32) (color : UInt32)            no objects; 5 scalars
//   label (x y : Int32) (size color : UInt32) text     1 object; 4 scalars
//   target (x y w h : Int32) (tag : UInt32)            no objects; 5 scalars
//   group (x y : Int32) (children : List Scene)        1 object; 2 scalars
static DsNode* ds_read(b_lean_obj_arg s) {
  DsNode* n = ds_mem(calloc(1, sizeof(DsNode)));
  n->kind = lean_ptr_tag(s);
  uint8_t r, g, b;
  if (n->kind == DS_FILL) {
    n->x = ds_i32(s, 0, 0);
    n->y = ds_i32(s, 0, 1);
    n->paint = ds_tvg_shape_new();
    ds_tvg_shape_append_rect(n->paint, 0, 0, ds_i32(s, 0, 2), ds_i32(s, 0, 3), 0, 0, true);
    ds_rgb(ds_u32(s, 0, 4), &r, &g, &b);
    ds_tvg_shape_set_fill_color(n->paint, r, g, b, 255);
  } else if (n->kind == DS_LABEL) {
    n->x = ds_i32(s, 1, 0);
    n->y = ds_i32(s, 1, 1);
    n->paint = ds_tvg_text_new();
    // ThorVG takes sizes in points at 96 per inch, 4/3 of a pixel each.
    ds_tvg_text_set_font(n->paint, "deui");
    ds_tvg_text_set_size(n->paint, (float)ds_u32(s, 1, 2) * 0.75f);
    ds_tvg_text_set_text(n->paint, ds.font ? lean_string_cstr(lean_ctor_get(s, 0)) : "");
    ds_rgb(ds_u32(s, 1, 3), &r, &g, &b);
    ds_tvg_text_set_color(n->paint, r, g, b);
  } else if (n->kind == DS_TARGET) {
    n->x = ds_i32(s, 0, 0);
    n->y = ds_i32(s, 0, 1);
  } else {
    n->kind = DS_GROUP;
    n->x = ds_i32(s, 1, 0);
    n->y = ds_i32(s, 1, 1);
    n->paint = ds_tvg_scene_new();
    for (b_lean_obj_arg cs = lean_ctor_get(s, 0); !lean_is_scalar(cs); cs = lean_ctor_get(cs, 1)) {
      ds_kid_put(n, n->len, ds_read(lean_ctor_get(cs, 0)));
    }
  }
  ds_place(n);
  return n;
}

// Puts kid at position i among a group's children, its paint before the
// next paint after it.
static void ds_kid_put(DsNode* g, u32 i, DsNode* kid) {
  if (g->len == g->cap) {
    g->cap = g->cap ? g->cap * 2 : 8;
    g->kids = ds_mem(realloc(g->kids, g->cap * sizeof(DsNode*)));
  }
  memmove(g->kids + i + 1, g->kids + i, (g->len - i) * sizeof(DsNode*));
  g->kids[i] = kid;
  g->len += 1;
  if (kid->paint) {
    Tvg_Paint before = NULL;
    for (u32 j = i + 1; j < g->len && before == NULL; j += 1) {
      before = g->kids[j]->paint;
    }
    if (before) {
      ds_tvg_scene_insert(g->paint, kid->paint, before);
    } else {
      ds_tvg_scene_add(g->paint, kid->paint);
    }
  }
}

static void ds_translate(DsNode* n, float dx, float dy) {
  n->x += dx;
  n->y += dy;
  ds_place(n);
}

// An edit, read from its Lean value, applied to n as SceneEdit.apply does,
// which leaves a part an edit doesn't fit as it is:
//   translate (dx dy : Int32)              no objects; 2 scalars
//   insert (i : Nat) (child : Scene)       2 objects
//   delete (i : Nat)                       1 object
//   update (i : Nat) (e : SceneEdit)       2 objects
//   shift (i : Nat) (dx dy : Int32)        1 object; 2 scalars
static void ds_apply(DsNode* n, b_lean_obj_arg e) {
  unsigned tag = lean_ptr_tag(e);
  if (tag == 0) {
    ds_translate(n, ds_i32(e, 0, 0), ds_i32(e, 0, 1));
    return;
  }
  if (n->kind != DS_GROUP) {
    return;
  }
  u32 i = ds_nat(lean_ctor_get(e, 0));
  if (tag == 1) {
    ds_kid_put(n, i < n->len ? i : n->len, ds_read(lean_ctor_get(e, 1)));
  } else if (tag == 2) {
    if (i < n->len) {
      DsNode* kid = n->kids[i];
      memmove(n->kids + i, n->kids + i + 1, (n->len - i - 1) * sizeof(DsNode*));
      n->len -= 1;
      if (kid->paint) {
        ds_tvg_scene_remove(n->paint, kid->paint);
      }
      ds_free(kid);
    }
  } else if (tag == 3) {
    if (i < n->len) {
      ds_apply(n->kids[i], lean_ctor_get(e, 1));
    }
  } else if (tag == 4) {
    float dx = ds_i32(e, 1, 0), dy = ds_i32(e, 1, 1);
    for (u32 j = i; j < n->len; j += 1) {
      ds_translate(n->kids[j], dx, dy);
    }
  }
}

// Sets the kept scene, replacing the one before.
lean_obj_res deui_window_set_scene(b_lean_obj_arg w, b_lean_obj_arg s, lean_obj_arg world) {
  if (!ds.open) {
    return ds_fail("screen: the window is closed");
  }
  if (ds.root) {
    if (ds.root->paint) {
      ds_tvg_scene_remove(ds.base, ds.root->paint);
    }
    ds_free(ds.root);
  }
  ds.root = ds_read(s);
  if (ds.root->paint) {
    ds_tvg_scene_add(ds.base, ds.root->paint);
  }
  return ds_unit();
}

// Applies a run of edits to the kept scene, in order.
lean_obj_res deui_window_edit(b_lean_obj_arg w, b_lean_obj_arg es, lean_obj_arg world) {
  if (!ds.open || ds.root == NULL) {
    return ds_fail("screen: the window is closed, or has no scene");
  }
  for (; !lean_is_scalar(es); es = lean_ctor_get(es, 1)) {
    ds_apply(ds.root, lean_ctor_get(es, 0));
  }
  return ds_unit();
}

// Draws the kept scene on a background of 0xRRGGBB, at the window's size
// and pixel density, and presents it.
lean_obj_res deui_window_draw(b_lean_obj_arg w, uint32_t rgb, lean_obj_arg world) {
  if (!ds.open) {
    return ds_fail("screen: the window is closed");
  }
  int pw = 0, ph = 0;
  ds_SDL_GetWindowSizeInPixels(ds.window, &pw, &ph);
  if (pw != ds.width || ph != ds.height) {
    Tvg_WgContext ctx = { ds.instance, ds.adapter, ds.device };
    ds_tvg_wgcanvas_set_target_with_context(ds.canvas, &ctx, ds.surface, (uint32_t)pw,
      (uint32_t)ph, TVG_COLORSPACE_ABGR8888S, 0);
    ds.width = pw;
    ds.height = ph;
  }
  uint8_t r, g, b;
  ds_rgb(rgb, &r, &g, &b);
  ds_tvg_shape_reset(ds.background);
  ds_tvg_shape_append_rect(ds.background, 0, 0, (float)pw, (float)ph, 0, 0, true);
  ds_tvg_shape_set_fill_color(ds.background, r, g, b, 255);
  float d = ds_SDL_GetWindowPixelDensity(ds.window);
  d = d > 0.0f ? d : 1.0f;
  if (d != ds.density) {
    ds_tvg_paint_scale(ds.base, d);
    ds.density = d;
  }
  ds_tvg_canvas_update(ds.canvas);
  ds_tvg_canvas_draw(ds.canvas, true);
  ds_tvg_canvas_sync(ds.canvas);
  ds_wgpuSurfacePresent(ds.surface);
  return ds_unit();
}

static void ds_close(void) {
  ds_free(ds.root);
  ds.root = NULL;
  ds_tvg_canvas_destroy(ds.canvas);
  if (ds.font) {
    ds_tvg_font_unload("deui");
  }
  ds_tvg_engine_term();
  ds_gpu_release();
  ds_SDL_DestroyWindow(ds.window);
  ds_SDL_Quit();
  ds.open = false;
  ds.font = false;
}

lean_obj_res deui_window_close(b_lean_obj_arg w, lean_obj_arg world) {
  if (ds.open) {
    ds_close();
  }
  return ds_unit();
}
