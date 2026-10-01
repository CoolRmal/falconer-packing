"""Regenerate the README figure with ReportLab and Poppler (pdftoppm)."""
from math import sqrt
from pathlib import Path
from reportlab.graphics.shapes import Drawing, String, Line, PolyLine, Rect
from reportlab.graphics import renderSVG, renderPDF
from tempfile import TemporaryDirectory
import subprocess
from reportlab.lib.colors import HexColor, white

def current(d):
    if d <= (7 - sqrt(7)) / 4:
        return 2 * d - 1
    if d >= (2 + sqrt(6)) / 4:
        return 1 / (3 - 2 * d)
    a = d - 1
    return 1 + 6 * a / (8 * a*a - a + 2 + sqrt(64*a**4 + 32*a**3 - 63*a*a - 28*a + 4))


if __name__ == "__main__":
    drawing = Drawing(960, 480)
    drawing.add(Rect(0, 0, 960, 480, fillColor=white, strokeColor=None))
    ink, teal, gray = map(HexColor, ["#27313b", "#007d78", "#78808b"])
    def text(x, y, value, size=12, color=ink, anchor="start", bold=False):
        drawing.add(String(x, y, value, fontSize=size, fillColor=color,
            textAnchor=anchor, fontName="Helvetica-Bold" if bold else "Helvetica"))
    text(85, 444, "Current packing-dimension bound", 22, bold=True)
    x, y, w, h = 85, 77, 825, 335
    X = lambda d: x + w*(d-1)/.25
    Y = lambda b: y + h*(b-1)/1.04
    xs = sorted({1+.25*j/1200 for j in range(1201)} |
                {(7-sqrt(7))/4, (2+sqrt(6))/4})
    for d in [1,1.05,1.1,1.15,1.2,1.25]:
        drawing.add(Line(X(d), y, X(d), y+h, strokeColor=HexColor("#e6e9ed"), strokeWidth=.7))
        text(X(d), y-22, f"{d:.2f}", anchor="middle")
    for b in [1,1.2,1.4,1.6,1.8,2]:
        drawing.add(Line(x, Y(b), x+w, Y(b), strokeColor=HexColor("#e6e9ed"), strokeWidth=.7))
        text(x-12, Y(b)-4, f"{b:.2f}", anchor="end")
    drawing.add(PolyLine([v for d in xs for v in (X(d), Y(current(d)))],
        strokeColor=teal, strokeWidth=3))
    drawing.add(Line(x,y,x+w,y,strokeColor=gray,strokeWidth=.8))
    drawing.add(Line(x,y,x,y+h,strokeColor=gray,strokeWidth=.8))
    text(x, y+h-15, "Packing-dimension cutoff", 11, gray)
    text(x+w/2, 25, "Hausdorff dimension d", 13, anchor="middle")
    out = Path(__file__).resolve().parent
    renderSVG.drawToFile(drawing, str(out / "packing-unforced.svg"))
    with TemporaryDirectory() as temp:
        pdf = str(Path(temp) / "figure.pdf")
        renderPDF.drawToFile(drawing, pdf)
        subprocess.run(["pdftoppm", "-singlefile", "-png", "-r", "150", pdf,
                        str(out / "packing-unforced")], check=True)
