"""Regenerate the README figure with ReportLab and Poppler (pdftoppm)."""
from math import sqrt
from pathlib import Path
from reportlab.graphics.shapes import Drawing, String, Line, PolyLine, Polygon, Rect
from reportlab.graphics import renderSVG, renderPDF
from tempfile import TemporaryDirectory
import subprocess
from reportlab.lib.colors import HexColor, white

d0 = (9 + sqrt(33)) / 12
d1 = (5 + sqrt(97)) / 12

def upper(d):
    return ((2*d-1)**2+sqrt((2*d-1)**4+8*d))/4

def old(d):
    return 2*d-1 if d <= d0 else 3*d*d-2.5*d if d <= d1 else upper(d)

def root_between(f, lo, hi):
    flo = f(lo)
    for _ in range(80):
        mid = (lo+hi)/2
        if f(mid)*flo > 0:
            lo = mid
        else:
            hi = mid
    return (lo+hi)/2

def adaptive_components(a, b, theta):
    k = 2*b-a
    q = b/k
    h = (1+q)/2-theta*a/(4*k)
    r = theta/(4*b)
    lam = (1-2*b)/(4*b)
    l0 = (1-2*a)/4
    a0 = (1-a-3*b)/3
    gamma = (6*b-1-2*a)/(3*a)
    mt = a*h/(1-a*r)
    early = min(a0+gamma*mt, (gamma*l0+lam*a0)/(gamma+lam))
    zero = min((1-q)/3, (1-a)*(b-a)/(4*k*(1-b)))
    av = (1-a)/3-(1-b)*h/2
    sv = (1-a)/(6*a)-(1-b)*r/2
    al = (1-a)/3-h
    sl = (a+2)/(3*a)-r
    late = min(av+sv*a, (sv*l0+lam*av)/(sv+lam),
               al+sl*a, (sl*l0+lam*al)/(sl+lam))
    return zero, early, late

def adaptive_cost(a, b):
    # The early bound is nondecreasing in theta; the late bound is decreasing.
    z, e, l = adaptive_components(a, b, 0)
    if e >= l:
        return max(z, e, l)
    z, e, l = adaptive_components(a, b, 1)
    if e <= l:
        return max(z, e, l)
    lo, hi = 0., 1.
    for _ in range(42):
        mid = (lo+hi)/2
        z, e, l = adaptive_components(a, b, mid)
        if e < l:
            lo = mid
        else:
            hi = mid
    return max(adaptive_components(a, b, (lo+hi)/2))

def adaptive_bound(d):
    if d <= 1.1:
        return 2*d-1
    if d >= 7/6:
        return 1/(3-2*d)
    a = d-1
    return 1+root_between(lambda b: adaptive_cost(a,b)-a, 2*a, .5)


def current(d):
    if d <= (7 - sqrt(7)) / 4:
        return 2 * d - 1
    if d >= (2 + sqrt(6)) / 4:
        return 1 / (3 - 2 * d)
    a = d - 1
    return 1 + 6 * a / (8 * a*a - a + 2 + sqrt(64*a**4 + 32*a**3 - 63*a*a - 28*a + 4))


if __name__ == "__main__":
    drawing = Drawing(960, 560)
    drawing.add(Rect(0, 0, 960, 560, fillColor=white, strokeColor=None))
    ink, teal, blue, gray, shade = map(HexColor,
        ["#27313b", "#007d78", "#416d9d", "#78808b", "#bae6df"])
    def text(x, y, value, size=12, color=ink, anchor="start", bold=False):
        drawing.add(String(x, y, value, fontSize=size, fillColor=color,
            textAnchor=anchor, fontName="Helvetica-Bold" if bold else "Helvetica"))
    text(85, 524, "Improvement in the packing-dimension cutoff", 22, bold=True)
    for x, color, dash, label in [(85, teal, None, "Current bound B_H(d)"),
        (350, blue, [7,3], "Earlier adaptive bound"),
        (630, gray, [2,4], "Originally quoted bound")]:
        drawing.add(Line(x, 490, x+30, 490, strokeColor=color, strokeWidth=2.5,
                         strokeDashArray=dash))
        text(x+40, 486, label)
    drawing.add(Rect(85, 459, 22, 11, fillColor=shade, strokeColor=None))
    text(125, 459, "Gain over the earlier adaptive bound")
    x, y, w, h = 85, 87, 825, 340
    X = lambda d: x + w*(d-1)/.25
    Y = lambda b: y + h*(b-1)/1.04
    xs = sorted({1+.25*j/1200 for j in range(1201)} |
                {(7-sqrt(7))/4, (2+sqrt(6))/4, 1.1, 7/6, d0, d1})
    latest = {d: current(d) for d in xs}
    previous = {d: adaptive_bound(d) for d in xs}
    extra = [d for d in xs if (7-sqrt(7))/4 <= d <= 7/6]
    points = [v for d in extra for v in (X(d), Y(latest[d]))]
    points += [v for d in reversed(extra) for v in (X(d), Y(previous[d]))]
    drawing.add(Polygon(points, fillColor=shade, strokeColor=None))
    for d in [1,1.05,1.1,1.15,1.2,1.25]:
        drawing.add(Line(X(d), y, X(d), y+h, strokeColor=HexColor("#e6e9ed"), strokeWidth=.7))
        text(X(d), y-22, f"{d:.2f}", anchor="middle")
    for b in [1,1.2,1.4,1.6,1.8,2]:
        drawing.add(Line(x, Y(b), x+w, Y(b), strokeColor=HexColor("#e6e9ed"), strokeWidth=.7))
        text(x-12, Y(b)-4, f"{b:.2f}", anchor="end")
    for f, color, width, dash in [(old, gray, 1.8, [2,4]),
        (previous.__getitem__, blue, 2, [7,3]), (latest.__getitem__, teal, 3, None)]:
        drawing.add(PolyLine([v for d in xs for v in (X(d), Y(f(d)))],
            strokeColor=color, strokeWidth=width, strokeDashArray=dash))
    drawing.add(Line(x,y,x+w,y,strokeColor=gray,strokeWidth=.8))
    drawing.add(Line(x,y,x,y+h,strokeColor=gray,strokeWidth=.8))
    text(x, y+h-15, "Packing-dimension cutoff", 11, gray)
    text(x+w/2, 35, "Hausdorff dimension d", 13, anchor="middle")
    text(85, 9, "Strictly below a curve is sufficient; the optimal condition is not known.", 11, gray)
    out = Path(__file__).resolve().parent
    renderSVG.drawToFile(drawing, str(out / "packing-unforced.svg"))
    with TemporaryDirectory() as temp:
        pdf = str(Path(temp) / "figure.pdf")
        renderPDF.drawToFile(drawing, pdf)
        subprocess.run(["pdftoppm", "-singlefile", "-png", "-r", "150", pdf,
                        str(out / "packing-unforced")], check=True)
