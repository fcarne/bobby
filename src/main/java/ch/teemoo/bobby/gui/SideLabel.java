package ch.teemoo.bobby.gui;

import javax.swing.*;
import java.awt.*;


class SideLabel extends JLabel {

    private static final long serialVersionUID = 8590128739177353193L;

	SideLabel(String label) {
        super(label);
        setFont(new Font("Sans Serif", Font.PLAIN, 16));
        setOpaque(true);
        setHorizontalAlignment(CENTER);
    }
}
