package org.swrlapi.builtins.aspectswrl;

import org.semanticweb.owlapi.model.parameters.Imports;
import xyz.aspectowl.owlapi.model.OWLAspectAssertionAxiom;
import xyz.aspectowl.owlapi.model.AspectOWLJoinPointAxiomPointcut;
import xyz.aspectowl.owlapi.model.OWLAspectManager;
import xyz.aspectowl.owlapi.protege.AspectOWLEditorKitHook;
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

    private static final String[] BUILT_IN_NAMES = { "opa", "createOPA", "temporal", "deontic" };


    public SWRLBuiltInLibraryImpl() {
        super(PREFIX, NAMESPACE, new HashSet<>(Arrays.asList(BUILT_IN_NAMES)));
    }

    /**
     * Satisfied iff the first argument is an OWL object property r, the second argument is an individual i1, the
     * third argument is an individual i2 connected to i1 by r, and the fourth argument is an AspectOWL aspect name, in
     * which the object property assertion r(i1, i2) holds.
     *
     * If the AspectOWL name variable is bound to a valid aspect name, then the expression will evaluate to true if
     * the given OPA holds in it.
     *
     * If the AspectOWL name variable is unbound, then all aspects for the given OPA will be found and bound to it as
     * a multi-value argument.
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
//        SWRLBuiltInArgument opArg = arguments.get(1);
//        SWRLBuiltInArgument i1Arg = arguments.get(2);
//        SWRLBuiltInArgument i2Arg = arguments.get(3);

        final OWLObjectProperty op = getOWLObjectProperty(arguments, 2);
        final OWLNamedIndividual i1 = getOWLNamedIndividual(arguments, 3);
        final OWLNamedIndividual i2 = getOWLNamedIndividual(arguments, 4);

        OWLOntology onto = getBuiltInBridge().getOWLOntology();

        var axiomOptional = onto.getObjectPropertyAssertionAxioms(i1).stream().filter(ax -> ax.getProperty().equals(op) && ax.getObject().equals(i2)).findFirst();
        if (!axiomOptional.isPresent()) {
            // this axiom does not exist, so there cannot be a contextualized version of it.
            return false;
        }

        // the OPA axiom
        OWLObjectPropertyAssertionAxiom joinPointAxiom = axiomOptional.get();

        OWLAspectManager aspectManager = AspectOWLEditorKitHook.getAspectManager(onto.getOWLOntologyManager());

        if (aspectArg.isVariable() && aspectArg.asVariable().isUnbound()) {
            // aspect variable is unbound, we have to find all aspects for the given axiom

            final Map<@NonNull Integer, @NonNull SWRLMultiValueVariableBuiltInArgument> outputMultiValueArguments = createOutputMultiValueArguments(arguments);

            aspectManager.getAssertedAspects(onto, joinPointAxiom).stream().filter(aspect -> !aspect.isAnonymous()).forEach(aspect -> outputMultiValueArguments.get(0).addArgument(createClassBuiltInArgument(aspect.asClassExpression().asOWLClass())));

            return processResultMultiValueArguments(arguments, outputMultiValueArguments);
        } else {
            // aspect is given (directly or via bound variable), we just have to check if the given axiom has the given aspect
            final OWLClass aspect = getOWLClass(arguments, 1);

            return aspectManager.getAssertedAspects(onto, joinPointAxiom).stream().anyMatch(as -> as.asClassExpression().equals(aspect));
        }
    }

    /**
     * Satisfied iff the first argument is an OWL object property r, the second argument is an individual i1, the
     * third argument is an individual i2 connected to i1 by r, and the fourth argument is a newly created AspectOWL
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
//        SWRLBuiltInArgument opArg = arguments.get(0);
//        SWRLBuiltInArgument i1Arg = arguments.get(1);
//        SWRLBuiltInArgument i2Arg = arguments.get(2);
        SWRLBuiltInArgument aspectArg = arguments.get(3);

        OWLOntology onto = getBuiltInBridge().getOWLOntology();
        OWLOntologyManager man = onto.getOWLOntologyManager();
        OWLDataFactory df = man.getOWLDataFactory();

        ArrayList<OWLAxiomChange> changes = new ArrayList<>();

        OWLClass aspectClass = null;
        if (aspectArg.isVariable()) {
            var aspectVar = aspectArg.asVariable();
            if (aspectVar.isBound()) {
                aspectClass = getOWLClass(arguments, 1); // throws exception if not a class
            } else {
                // variable arg but not bound - create new and bind to variable
                aspectClass = df.getOWLClass(IRI.create(onto.getOntologyID().getOntologyIRI().get().toString() + "#" + UUID.randomUUID().toString()));
                OWLDeclarationAxiom aspectClassDeclarationAxiom = df.getOWLDeclarationAxiom(aspectClass);
                changes.add(new AddAxiom(onto, aspectClassDeclarationAxiom));
                aspectVar.setBuiltInResult(createClassBuiltInArgument(aspectClass));
            }
        } else {
            aspectClass = getOWLClass(arguments, 1); // throws exception if not a class
        }

        // opArg can either be variable or concrete value
        // if variable, must be bound
        // either way, value must be an OWLObjectProperty
        final OWLObjectProperty op = getOWLObjectProperty(arguments, 1);
        final OWLNamedIndividual i1 = getOWLNamedIndividual(arguments, 2);
        final OWLNamedIndividual i2 = getOWLNamedIndividual(arguments, 3);


        var joinPointAxiomOptional = onto.getObjectPropertyAssertionAxioms(i1).stream().filter(ax -> ax.getProperty().equals(op) && ax.getObject().equals(i2)).findFirst();
        OWLObjectPropertyAssertionAxiom joinPointAxiom = null;
        if (joinPointAxiomOptional.isPresent()) {
            joinPointAxiom = joinPointAxiomOptional.get();
        } else {
            joinPointAxiom = df.getOWLObjectPropertyAssertionAxiom(op, i1, i2);
        }
        changes.add(new AddAxiom(onto, joinPointAxiom));

        man.applyChanges(changes);

        OWLAspectManager aspectManager = AspectOWLEditorKitHook.getAspectManager(man);
        OWLAspectAssertionAxiom aspectAssertionAxiom = aspectManager.getAspectAssertionAxiom(onto, new AspectOWLJoinPointAxiomPointcut(joinPointAxiom), aspectManager.getAspect(aspectClass, Collections.EMPTY_SET, Collections.EMPTY_SET));
        aspectManager.addAspect(onto, aspectAssertionAxiom);

        return true;
    }

    public boolean createNegativeOPA(List<SWRLBuiltInArgument> arguments) throws SWRLBuiltInException {
        // argument 1: object property op
        // argument 2: individual i1
        // argument 3: individual i2
        // argument 4: aspect a such that aspect(a, op(i1, i2))
        checkNumberOfArgumentsEqualTo(4, arguments.size());
//        SWRLBuiltInArgument opArg = arguments.get(0);
//        SWRLBuiltInArgument i1Arg = arguments.get(1);
//        SWRLBuiltInArgument i2Arg = arguments.get(2);
        SWRLBuiltInArgument aspectArg = arguments.get(3);

        OWLOntology onto = getBuiltInBridge().getOWLOntology();
        OWLOntologyManager man = onto.getOWLOntologyManager();
        OWLDataFactory df = man.getOWLDataFactory();

        ArrayList<OWLAxiomChange> changes = new ArrayList<>();

        OWLClass aspectClass = null;
        if (aspectArg.isVariable()) {
            var aspectVar = aspectArg.asVariable();
            if (aspectVar.isBound()) {
                aspectClass = getOWLClass(arguments, 1); // throws exception if not a class
            } else {
                // variable arg but not bound - create new and bind to variable
                aspectClass = df.getOWLClass(IRI.create(onto.getOntologyID().getOntologyIRI().get().toString() + "#" + UUID.randomUUID().toString()));
                OWLDeclarationAxiom aspectClassDeclarationAxiom = df.getOWLDeclarationAxiom(aspectClass);
                changes.add(new AddAxiom(onto, aspectClassDeclarationAxiom));
                aspectVar.setBuiltInResult(createClassBuiltInArgument(aspectClass));
            }
        } else {
            aspectClass = getOWLClass(arguments, 1); // throws exception if not a class
        }

        // opArg can either be variable or concrete value
        // if variable, must be bound
        // either way, value must be an OWLObjectProperty
        final OWLObjectProperty op = getOWLObjectProperty(arguments, 1);
        final OWLNamedIndividual i1 = getOWLNamedIndividual(arguments, 2);
        final OWLNamedIndividual i2 = getOWLNamedIndividual(arguments, 3);


        var joinPointAxiomOptional = onto.getNegativeObjectPropertyAssertionAxioms(i1).stream().filter(ax -> ax.getProperty().equals(op) && ax.getObject().equals(i2)).findFirst();
        OWLNegativeObjectPropertyAssertionAxiom joinPointAxiom = null;
        if (joinPointAxiomOptional.isPresent()) {
            joinPointAxiom = joinPointAxiomOptional.get();
        } else {
            joinPointAxiom = df.getOWLNegativeObjectPropertyAssertionAxiom(op, i1, i2);
        }
        changes.add(new AddAxiom(onto, joinPointAxiom));

        man.applyChanges(changes);

        OWLAspectManager aspectManager = AspectOWLEditorKitHook.getAspectManager(man);
        OWLAspectAssertionAxiom aspectAssertionAxiom = aspectManager.getAspectAssertionAxiom(onto, new AspectOWLJoinPointAxiomPointcut(joinPointAxiom), aspectManager.getAspect(aspectClass, Collections.EMPTY_SET, Collections.EMPTY_SET));
        aspectManager.addAspect(onto, aspectAssertionAxiom);

        return true;
    }
    /**
     * Satisfied iff
     * - the first argument is an OWLAspect name A (if unbound, a new aspect will be created and bound to it),
     * - the second argument is an OP, which serves as one of the temporal ("before" or "after") accessibility relation (must be bound),
     * - the third argument is an individual, which serves as the start/end time instance (if unbound and the 2nd arg is bound, a new one will be created),
     * - the fourth argument is a boolean indicating whether the individual bound to the 3rd arg should be included in the interval (false: A ≡ op.{T1}, true: A ≡ op.{T1} ⊔ {T1}))
     */
    public boolean temporal(List<SWRLBuiltInArgument> arguments) throws SWRLBuiltInException {
        checkNumberOfArgumentsEqualTo(4, arguments.size());
        var aspectArg = arguments.get(0);
//        var opArg = arguments.get(1);
        var indArg = arguments.get(2);
//        var includeIndArg = arguments.get(3);

        var op = getOWLObjectProperty(arguments, 2);
        var includeArg = getBoolean(arguments, 4);

        OWLOntology onto = getBuiltInBridge().getOWLOntology();
        OWLOntologyManager man = onto.getOWLOntologyManager();
        OWLDataFactory df = man.getOWLDataFactory();
        ArrayList<OWLAxiomChange> changes = new ArrayList<>();


        OWLClass aspectClass = null;
        if (aspectArg.isVariable()) {
            var aspectVar = aspectArg.asVariable();
            if (aspectVar.isBound()) {
                aspectClass = getOWLClass(arguments, 1); // throws exception if not a class
            } else {
                // variable arg but not bound - create new and bind to variable
                aspectClass = df.getOWLClass(IRI.create(onto.getOntologyID().getOntologyIRI().get().toString() + "#" + UUID.randomUUID().toString()));
                OWLDeclarationAxiom aspectClassDeclarationAxiom = df.getOWLDeclarationAxiom(aspectClass);
                changes.add(new AddAxiom(onto, aspectClassDeclarationAxiom));
                aspectVar.setBuiltInResult(createClassBuiltInArgument(aspectClass));
            }
        } else {
            aspectClass = getOWLClass(arguments, 1); // throws exception if not a class
        }

        OWLNamedIndividual ind = null;
        if (indArg.isVariable()) {
            var indVar = indArg.asVariable();
            if (indVar.isBound()) {
                ind = getOWLNamedIndividual(arguments, 3); // throws exception if not a class
            } else {
                // variable arg but not bound - create new and bind to variable
                ind = df.getOWLNamedIndividual(IRI.create(onto.getOntologyID().getOntologyIRI().get().toString() + "#" + UUID.randomUUID().toString()));
                OWLDeclarationAxiom indDeclarationAxiom = df.getOWLDeclarationAxiom(ind);
                changes.add(new AddAxiom(onto, indDeclarationAxiom));
                indVar.setBuiltInResult(createNamedIndividualBuiltInArgument(ind));
            }
        } else {
            ind = getOWLNamedIndividual(arguments, 3); // throws exception if not a class
        }

        // A ≡ op.{T1} ⊔ {T1}

        OWLClassExpression hasValueCE = df.getOWLObjectHasValue(op, ind); // op.{T1}
        OWLClassExpression equivalenceCE = includeArg ? df.getOWLObjectUnionOf(df.getOWLObjectOneOf(ind), hasValueCE) : hasValueCE;

        changes.add(new AddAxiom(onto, df.getOWLEquivalentClassesAxiom(aspectClass, equivalenceCE)));

        man.applyChanges(changes);

        return true;
    }

    public boolean deontic(List<SWRLBuiltInArgument> arguments) throws SWRLBuiltInException {
        // TODO implement
        return false;
    }

    public boolean nest(List<SWRLBuiltInArgument> arguments) throws SWRLBuiltInException {
        // TODO implement
        return false;
    }

//    /**
//     * Gathers known instances of an OWL class (second arg) in a list (which will then be bound to the first arg)
//     * @param arguments
//     * @return
//     * @throws SWRLBuiltInException
//     */
//    public boolean knownDirectInstances(List<SWRLBuiltInArgument> arguments) throws SWRLBuiltInException {
//        OWLClass clazz = getOWLClass(arguments, 1);
//
//        OWLOntology onto = getBuiltInBridge().getOWLOntology();
//        OWLOntologyManager man = onto.getOWLOntologyManager();
//        OWLDataFactory df = man.getOWLDataFactory();
//
//        onto.getIndividualsInSignature(Imports.INCLUDED).stream().filter(ind -> ind.)
//        return true;
//    }

    private OWLNamedIndividual getOWLNamedIndividual(List<SWRLBuiltInArgument> arguments, int argPos) throws SWRLBuiltInException {
        return checkAndGetActualArgument(arguments, NAMED_INDIVIDUAL, argPos).asSWRLNamedIndividualBuiltInArgument().getOWLNamedIndividual();
    }

    private OWLClass getOWLClass(List<SWRLBuiltInArgument> arguments, int argPos) throws SWRLBuiltInException {
        return checkAndGetActualArgument(arguments, CLASS, argPos).asSWRLClassBuiltInArgument().getOWLClass();
    }

    private OWLObjectProperty getOWLObjectProperty(List<SWRLBuiltInArgument> arguments, int argPos) throws SWRLBuiltInException {
        return checkAndGetActualArgument(arguments, OBJECT_PROPERTY, argPos).asSWRLObjectPropertyBuiltInArgument().getOWLObjectProperty();
    }

    private Boolean getBoolean(List<SWRLBuiltInArgument> arguments, int argPos) throws SWRLBuiltInException {
        OWLLiteral literal = checkAndGetActualArgument(arguments, LITERAL, argPos).asSWRLLiteralBuiltInArgument().getLiteral();
        try {
            return literal.parseBoolean();
        } catch (NumberFormatException e) {
            throw new SWRLBuiltInException(String.format("Could not parse boolean from argument %d (argument type is %s, argument value is %s)", argPos, literal.getDatatype(), literal.getLiteral()));
        }
    }

    /**
     * argPos: natural argument position (count starts from 1)!
     * @param arguments
     * @param expectedType
     * @param argPos
     * @return
     * @throws SWRLBuiltInException
     */
    private SWRLBuiltInArgument checkAndGetActualArgument(List<SWRLBuiltInArgument> arguments, SWRLBuiltInArgumentType expectedType, int argPos) throws SWRLBuiltInException {
        SWRLBuiltInArgument arg = arguments.get(argPos - 1);
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
