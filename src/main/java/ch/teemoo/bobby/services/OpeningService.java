package ch.teemoo.bobby.services;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import ch.teemoo.bobby.models.games.Game;
import ch.teemoo.bobby.models.moves.Move;
import ch.teemoo.bobby.models.openings.Node;

public class OpeningService {
	private static final Logger LOGGER = LoggerFactory.getLogger(OpeningService.class);
	private static final List<String> OPENINGS_PGN_FILES = Arrays.asList("bogoindiandefense.pgn", "englishopening.pgn",
			"friedliverattack.pgn", "grunfelddefense.pgn", "italiangame.pgn", "kingsgambit.pgn", "londonsystem.pgn",
			"nimzoindiandefense.pgn", "queensgambit.pgn", "retiopening.pgn", "ruylopezopening.pgn", "scotchgame.pgn",
			"siciliandefense.pgn", "slavdefense.pgn", "trompowskyattack.pgn");

	private final PortableGameNotationService portableGameNotationService;
	private final FileService fileService;
	private final Node openingsTree;

	public OpeningService(PortableGameNotationService portableGameNotationService, FileService fileService) {
		this.portableGameNotationService = portableGameNotationService;
		this.fileService = fileService;
		this.openingsTree = buildTree();
	}

	public List<Move> findPossibleMovesForHistory(List<Move> history) {
		Node currentNode = openingsTree;
		for (Move move : history) {
			Optional<Node> nodeOpt = currentNode.getNodeForMove(move);
			if (nodeOpt.isPresent()) {
				currentNode = nodeOpt.get();
			} else {
				return Collections.emptyList();
			}
		}
		return currentNode.getChildren().stream().map(Node::getMove).collect(Collectors.toList());
	}

	public String prettyPrintTree() {
		return prettyPrintNode(openingsTree, 0).trim();
	}

	private Node buildTree() {
		List<Game> games = new ArrayList<>();
		for (String fileName : OPENINGS_PGN_FILES) {
			try {
				games.add(portableGameNotationService
						.readPgnFile(fileService.readFileFromResourceFolder("openings", fileName)));
			} catch (IOException e) {
				LOGGER.error("Opening could not be read from file {}", fileName, e);
			}
		}

		Node root = new Node(null);

		for (Game game : games) {
			Node currentNode = root;
			List<Move> moves = game.getHistory();
			for (Move move : moves) {
				Optional<Node> nextNodeOpt = currentNode.getNodeForMove(move);
				if (nextNodeOpt.isPresent()) {
					currentNode = nextNodeOpt.get();
				} else {
					Node node = new Node(move);
					currentNode.addNode(node);
					currentNode = node;
				}
				if (move.equals(moves.get(moves.size() - 1))) {
					// last move
					currentNode.setOpeningName(game.getOpening());
				}
			}
		}
		LOGGER.info("{} openings loaded", games.size());

		return root;
	}

	private String prettyPrintNode(Node node, int level) {
		String result = "";
		for (int i = 0; i < level; i++) {
			result += "\t";
		}
		if (level == 0) {
			result += "<START>";
		} else {
			result += node.getMove();
		}
		if (node.getOpeningName() != null) {
			result += " [" + node.getOpeningName() + "]";
		}
		result += "\n";
		List<String> subTrees = node.getChildren().stream().map(child -> prettyPrintNode(child, level + 1))
				.collect(Collectors.toList());
		for (String subTree : subTrees) {
			result += subTree;
		}
		return result;
	}

}
