package org.swrlapi.builtins.aspectswrl;

import de.fuberlin.csw.aspectowl.owlapi.model.OWLAspectAssertionAxiom;
import de.fuberlin.csw.aspectowl.owlapi.model.OWLJoinPointAxiomPointcut;
import de.fuberlin.csw.aspectowl.owlapi.model.OWLOntologyAspectManager;
import de.fuberlin.csw.aspectowl.owlapi.protege.AspectOWLEditorKitHook;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.semanticweb.owlapi.model.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.swrlapi.builtins.AbstractSWRLBuiltInLibrary;
import org.swrlapi.builtins.arguments.SWRLBuiltInArgument;
import org.swrlapi.builtins.arguments.SWRLBuiltInArgumentType;
import org.swrlapi.builtins.arguments.SWRLMultiValueVariableBuiltInArgument;
import org.swrlapi.exceptions.SWRLBuiltInException;
import org.swrlapi.exceptions.SWRLBuiltInLibraryException;

import java.util.*;

import static org.swrlapi.builtins.arguments.SWRLBuiltInArgumentType.*;


/**
 * @author ralph
 * 
 */
public class SWRLBuiltInLibraryImpl extends AbstractSWRLBuiltInLibrary {

    private static final Logger log = LoggerFactory.getLogger(SWRLBuiltInLibraryImpl.class);

    public static final String PREFIX = "aspectswrl";

    public static final String NAMESPACE = "https://ontology.aspectowl.xyz/built-ins/5.2.0/AspectSWRLBuiltinsLibrary.owl#";

    private static final String[] BUILT_IN_NAMES = { "opa", "createOPA" };


    public SWRLBuiltInLibraryImpl() {
        super(PREFIX, NAMESPACE, new HashSet<>(Arrays.asList(BUILT_IN_NAMES)));
    }

    /**
     * Satisfied iff the first argument is an OWL object property r, the second argument is an individual i1, the
     * third argument is an individual i2 connected to i1 by r, and the fourth argument is an AspectOWL aspect name, in
     * which the object property assertion r(i1, i2) holds.
     *
     * @param arguments
     * @return
     * @throws SWRLBuiltInException
     */
    public boolean opa(List<SWRLBuiltInArgument> arguments) throws SWRLBuiltInException {
        // argument 1: aspect a such that aspect(a, op(i1, i2))
        // argument 2: object property op
        // argument 3: individual i1
        // argument 4: individual i2
        checkNumberOfArgumentsEqualTo(4, arguments.size());
        SWRLBuiltInArgument aspectArg = arguments.get(0);
        SWRLBuiltInArgument opArg = arguments.get(1);
        SWRLBuiltInArgument i1Arg = arguments.get(2);
        SWRLBuiltInArgument i2Arg = arguments.get(3);

        final OWLObjectProperty op = getOWLObjectProperty(opArg, 2);
        final OWLNamedIndividual i1 = getOWLNamedIndividual(i1Arg, 3);
        final OWLNamedIndividual i2 = getOWLNamedIndividual(i2Arg, 4);

        OWLOntology onto = getBuiltInBridge().getOWLOntology();

        var axiomOptional = onto.getObjectPropertyAssertionAxioms(i1).stream().filter(ax -> ax.getProperty().equals(op) && ax.getObject().equals(i2)).findFirst();
        if (!axiomOptional.isPresent()) {
            // this axiom does not exist, so there cannot be a contextualized version of it.
            return false;
        }

        // the OPA axiom
        OWLObjectPropertyAssertionAxiom joinPointAxiom = axiomOptional.get();

        OWLOntologyAspectManager aspectManager = AspectOWLEditorKitHook.getAspectManager(onto.getOWLOntologyManager());

        if (aspectArg.isVariable() && aspectArg.asVariable().isUnbound()) {
            // aspect variable is unbound, we have to find all aspects for the given axiom

            final Map<@NonNull Integer, @NonNull SWRLMultiValueVariableBuiltInArgument> outputMultiValueArguments = createOutputMultiValueArguments(arguments);

            aspectManager.getAssertedAspects(onto, joinPointAxiom).stream().filter(aspect -> !aspect.isAnonymous()).forEach(aspect -> outputMultiValueArguments.get(0).addArgument(createClassBuiltInArgument(aspect.asClassExpression().asOWLClass())));

            return processResultMultiValueArguments(arguments, outputMultiValueArguments);
        } else {
            // aspect is given (directly or via bound variable), we just have to check if the given axiom has the given aspect
            final OWLClass aspect = getOWLClass(aspectArg, 1);

            return aspectManager.getAssertedAspects(onto, joinPointAxiom).stream().anyMatch(as -> as.asClassExpression().equals(aspect));
        }
    }

    /**
     * Satisfied iff the first argument is an OWL object property r, the second argument is an individual i1, the
     * third argument is an individual i2 connected to i1 by r, and the fourth argument is an newly created AspectOWL
     * aspect name, in which the object property assertion r(i1, i2) holds.
     *
     * @param arguments
     * @return
     * @throws SWRLBuiltInException
     */
    public boolean createOPA(List<SWRLBuiltInArgument> arguments) throws SWRLBuiltInException {
        // argument 1: object property op
        // argument 2: individual i1
        // argument 3: individual i2
        // argument 4: aspect a such that aspect(a, op(i1, i2))
        checkNumberOfArgumentsEqualTo(4, arguments.size());
        SWRLBuiltInArgument opArg = arguments.get(0);
        SWRLBuiltInArgument i1Arg = arguments.get(1);
        SWRLBuiltInArgument i2Arg = arguments.get(2);
        SWRLBuiltInArgument aspectArg = arguments.get(3);

        if (aspectArg.isVariable()) {
            var aspectVar = aspectArg.asVariable();
            if (aspectVar.isUnbound()) {
                // opArg can either be variable or concrete value
                // if variable, must be bound
                // either way, value must be an OWLObjectProperty
                final OWLObjectProperty op = getOWLObjectProperty(opArg, 1);
                final OWLNamedIndividual i1 = getOWLNamedIndividual(i1Arg, 2);
                final OWLNamedIndividual i2 = getOWLNamedIndividual(i2Arg, 3);

                OWLOntology onto = getBuiltInBridge().getOWLOntology();

                var joinPointAxiomOptional = onto.getObjectPropertyAssertionAxioms(i1).stream().filter(ax -> ax.getProperty().equals(op) && ax.getObject().equals(i2)).findFirst();

                if (joinPointAxiomOptional.isPresent()) {
                    // axiom exists, we cannot contextualize it
                    return false;
                }

                OWLOntologyManager man = onto.getOWLOntologyManager();
                OWLDataFactory df = man.getOWLDataFactory();

                ArrayList<OWLAxiomChange> changes = new ArrayList<>();

                OWLObjectPropertyAssertionAxiom joinPointAxiom = df.getOWLObjectPropertyAssertionAxiom(op, i1, i2);
                changes.add(new AddAxiom(onto, joinPointAxiom));

                OWLClass aspectClass = df.getOWLClass(IRI.create(onto.getOntologyID().getOntologyIRI().get().toString() + "#" + UUID.randomUUID().toString()));
                OWLDeclarationAxiom aspectClassDeclarationAxiom = df.getOWLDeclarationAxiom(aspectClass);
                changes.add(new AddAxiom(onto, aspectClassDeclarationAxiom));

                man.applyChanges(changes);

                OWLOntologyAspectManager aspectManager = AspectOWLEditorKitHook.getAspectManager(man);
                OWLAspectAssertionAxiom aspectAssertionAxiom = aspectManager.getAspectAssertionAxiom(onto, new OWLJoinPointAxiomPointcut(joinPointAxiom), aspectManager.getAspect(aspectClass, Collections.EMPTY_SET, Collections.EMPTY_SET));
                aspectManager.addAspect(onto, aspectAssertionAxiom);

                aspectVar.setBuiltInResult(createClassBuiltInArgument(aspectClass));

                return true;

            } else {
                // must be unbound
                return false;
            }
        } else {
            // must be variable
            return false;
        }

    }

    private OWLNamedIndividual getOWLNamedIndividual(SWRLBuiltInArgument arg, int argPos) throws SWRLBuiltInException {
        return checkAndGetActualArgument(arg, NAMED_INDIVIDUAL, argPos).asSWRLNamedIndividualBuiltInArgument().getOWLNamedIndividual();
    }

    private OWLClass getOWLClass(SWRLBuiltInArgument arg, int argPos) throws SWRLBuiltInException {
        return checkAndGetActualArgument(arg, CLASS, argPos).asSWRLClassBuiltInArgument().getOWLClass();
    }

    private OWLObjectProperty getOWLObjectProperty(SWRLBuiltInArgument arg, int argPos) throws SWRLBuiltInException {
        return checkAndGetActualArgument(arg, OBJECT_PROPERTY, argPos).asSWRLObjectPropertyBuiltInArgument().getOWLObjectProperty();
    }

    private SWRLBuiltInArgument checkAndGetActualArgument(SWRLBuiltInArgument arg, SWRLBuiltInArgumentType expectedType, int argPos) throws SWRLBuiltInException {
        if (arg.isVariable()) {
            var opVar = arg.asVariable();
            if (opVar.isUnbound()) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound but is unbound.", NAMESPACE, getInvokingRuleName(), opVar.getVariableName()));
            }
            SWRLBuiltInArgument actualArg = opVar.getBuiltInResult().get(); // we checked above that it's bound, so must have a value
            if (actualArg.getSWRLBuiltInArgumentType() != expectedType) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound to a value of type %s but is %s.", NAMESPACE, getInvokingRuleName(), opVar.getVariableName(), expectedType, actualArg.getSWRLBuiltInArgumentType()));
            }
            return actualArg;
        } else {
            if (arg.getSWRLBuiltInArgumentType() != expectedType) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Argument at position %d must be of type %s but is %s.", NAMESPACE, getInvokingRuleName(), argPos, expectedType, arg.getSWRLBuiltInArgumentType()));
            }
            return arg;
        }

    }



    @Override
    public void reset() throws SWRLBuiltInLibraryException {

    }



}
