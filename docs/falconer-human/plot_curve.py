from math import sqrt
from pathlib import Path
from reportlab.graphics.shapes import Drawing, String, Line, PolyLine, Polygon, Rect, Circle
from reportlab.graphics import renderPDF, renderSVG
from reportlab.lib.colors import HexColor, white

out=Path(__file__).resolve().parent.parent/'figures'
d0=(7-sqrt(7))/4; d1=(2+sqrt(6))/4
def bound(d):
    if d<=d0: return 2*d-1
    if d>=d1: return 1/(3-2*d)
    a=d-1
    return 1+6*a/(2-a+8*a*a+sqrt(4-28*a-63*a*a+32*a**3+64*a**4))

w,h=740,340
left,right,bottom,top=72,695,52,292
X=lambda d:left+(d-1)/.25*(right-left)
Y=lambda D:bottom+(D-1)*(top-bottom)
ink=HexColor('#223544'); blue=HexColor('#136b93'); pale=HexColor('#dbeef4')
gray=HexColor('#8c979d'); grid=HexColor('#e7ecef')
dr=Drawing(w,h)
dr.add(Rect(0,0,w,h,fillColor=white,strokeColor=None))
def label(x,y,s,size=12,color=ink,anchor='start'):
    dr.add(String(x,y,s,fontName='Helvetica',fontSize=size,fillColor=color,textAnchor=anchor))
for D in [1,1.2,1.4,1.6,1.8,2]:
    dr.add(Line(left,Y(D),right,Y(D),strokeColor=grid,strokeWidth=.7))
    label(left-12,Y(D)-4,f'{D:.1f}',anchor='end')
for d in [1,1.05,1.10,1.15,1.20,1.25]:
    dr.add(Line(X(d),bottom,X(d),top,strokeColor=grid,strokeWidth=.7))
    label(X(d),bottom-19,f'{d:.2f}',anchor='middle')
xs=[1+.25*i/600 for i in range(601)]
poly=[]
for d in xs: poly.extend([X(d),Y(bound(d))])
for d in reversed(xs): poly.extend([X(d),Y(d)])
dr.add(Polygon(poly,fillColor=pale,strokeColor=None))
points=[]
for d in xs: points.extend([X(d),Y(bound(d))])
dr.add(PolyLine(points,strokeColor=blue,strokeWidth=2.5,fillColor=None))
dr.add(Line(X(1),Y(1),X(1.25),Y(1.5),strokeColor=gray,strokeWidth=1.5,strokeDashArray=[5,4]))
dr.add(Line(X(1),Y(1),X(1.25),Y(1.25),strokeColor=gray,strokeWidth=.8))
for d in [d0,d1]:
    dr.add(Circle(X(d),Y(bound(d)),2.8,fillColor=white,strokeColor=blue,strokeWidth=1.3))
dr.add(Line(left,bottom,right,bottom,strokeColor=ink,strokeWidth=1))
dr.add(Line(left,bottom,left,top,strokeColor=ink,strokeWidth=1))
label(72,316,'Packing dimension D',14)
label((left+right)/2,12,'Hausdorff dimension d',14,anchor='middle')
label(X(1.207),Y(bound(1.207))+15,'B_H(d)',14,color=blue)
label(X(1.178),Y(1.355)-22,'D < B_H(d)',15,color=blue)
label(X(1.18),Y(1.36)+11,'2d - 1',12,color=gray)
label(X(1.105),Y(1.09)-16,'D < d is impossible',10,color=gray)
renderPDF.drawToFile(dr,str(out/'falconer-human-curve.pdf'))
renderSVG.drawToFile(dr,str(out/'falconer-human-curve.svg'))
print('Plot created. Transitions:',d0,d1)
for d in [1.05,1.1,1.15,1.2,1.24,1.25]: print(d,bound(d))
