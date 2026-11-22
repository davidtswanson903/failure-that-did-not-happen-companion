"""How every figure is finished, to the series' guides: labels at 9pt in a sans-serif, each with an initial capital, fonts embedded. A figure is
drawn at the width of the text, 6.27 inches, so that its labels print at the size they are set."""

import matplotlib.pyplot as plt
from matplotlib.text import Text

fonts = {"font.size": 9, "axes.titlesize": 9, "font.family": "sans-serif", "font.sans-serif": ["Arial", "Helvetica", "DejaVu Sans"], "pdf.fonttype": 42}


def capital(words):
    return words[:1].upper() + words[1:]


def finish(fig, stem):
    """Capitalizes the labels, lays the figure out, and writes its two files."""
    fig.canvas.draw()
    for ax in fig.axes:
        for axis in (ax.xaxis, ax.yaxis):
            labels = [label.get_text() for label in axis.get_ticklabels()]
            if any(words[:1].islower() for words in labels):
                axis.set_ticks(axis.get_ticklocs(), [capital(words) for words in labels])
    for text in fig.findobj(Text):
        text.set_text(capital(text.get_text()))
    fig.tight_layout()
    fig.savefig(stem.with_suffix(".pdf"), metadata={"CreationDate": None, "Creator": None, "Producer": None})
    fig.savefig(stem.with_suffix(".png"), dpi=300, metadata={"Software": None})
    plt.close(fig)
