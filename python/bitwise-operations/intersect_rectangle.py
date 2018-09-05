class Interval:
    def __init__(self, start, end):
        self.start = start
        self.end   = end

    def __str__(self):
        return "(" + str(self.start) + "," + str(self.end) + ")"

    def __repr__(self):
        return self.__str__()

    def is_intersect(self, other):
        return (self.start <= other.end and
                self.end   >= other.start)

    def intersect(self, other):
        if is_intersect(self, other):
            return Interval(max(self.start, other.start),
                            min(self.end,   other.end))
        else:
            return False

class Rectangle:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def __str__(self):
        return "[" + str(self.x) + "," + str(self.y) + "]"

    def __repr__(self):
        return self.__str__()

    def is_intersect(self, other):
        return (self.x.is_intersect(other.x) and
                self.y.is_intersect(other.y))

    def intersect(self, other):
        if self.is_intersect(other):
            return Rectangle(self.x.intersect(other.x),
                             self.y.intersect(other.y))
        else:
            return False
