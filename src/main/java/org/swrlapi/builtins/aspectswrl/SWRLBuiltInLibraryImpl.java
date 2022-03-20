package org.swrlapi.builtins.aspectswrl;

import de.fuberlin.csw.aspectowl.owlapi.model.OWLOntologyAspectManager;
import de.fuberlin.csw.aspectowl.owlapi.protege.AspectOWLEditorKitHook;
import org.semanticweb.owlapi.model.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.swrlapi.builtins.AbstractSWRLBuiltInLibrary;
import org.swrlapi.builtins.arguments.SWRLBuiltInArgument;
import org.swrlapi.exceptions.SWRLBuiltInException;
import org.swrlapi.exceptions.SWRLBuiltInLibraryException;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;

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
        // argument 1: object property op
        // argument 2: individual i1
        // argument 3: individual i2
        // argument 4: aspect a such that aspect(a, op(i1, i2))
        checkNumberOfArgumentsEqualTo(4, arguments.size());
        SWRLBuiltInArgument opArg = arguments.get(0);
        SWRLBuiltInArgument i1Arg = arguments.get(1);
        SWRLBuiltInArgument i2Arg = arguments.get(2);
        SWRLBuiltInArgument aspectArg = arguments.get(3);

        // opArg can either be variable or concrete value
        // if variable, must be bound
        // either way, value must be an OWLObjectProperty
        final OWLObjectProperty op;
        if (opArg.isVariable()) {
            var opVar = opArg.asVariable();
            if (opVar.isUnbound()) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound but is unbound.", NAMESPACE, getInvokingRuleName(), opVar.getVariableName()));
            }
            opArg = opVar.getBuiltInResult().get(); // we checked above that it's bound, so must have a value
            if (opArg.getSWRLBuiltInArgumentType() != OBJECT_PROPERTY) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound to a value of type %s but is %s.", NAMESPACE, getInvokingRuleName(), opVar.getVariableName(), OBJECT_PROPERTY, opArg.getSWRLBuiltInArgumentType()));
            }
            op = opArg.asSWRLObjectPropertyBuiltInArgument().getOWLObjectProperty();
        } else {
            if (opArg.getSWRLBuiltInArgumentType() != OBJECT_PROPERTY) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: First argument must be of type %s but is %s.", NAMESPACE, getInvokingRuleName(), OBJECT_PROPERTY, opArg.getSWRLBuiltInArgumentType()));
            }
            op = opArg.asSWRLObjectPropertyBuiltInArgument().getOWLObjectProperty();
        }

        final OWLNamedIndividual i1;
        if (i1Arg.isVariable()) {
            var i1Var = i1Arg.asVariable();
            if (i1Var.isUnbound()) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound but is unbound.", NAMESPACE, getInvokingRuleName(), i1Var.getVariableName()));
            }
            i1Arg = i1Var.getBuiltInResult().get(); // we checked above that it's bound, so must have a value
            if (i1Arg.getSWRLBuiltInArgumentType() != NAMED_INDIVIDUAL) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound to a value of type %s but is %s.", NAMESPACE, getInvokingRuleName(), i1Var.getVariableName(), NAMED_INDIVIDUAL, i1Arg.getSWRLBuiltInArgumentType()));
            }
            i1 = i1Arg.asSWRLNamedIndividualBuiltInArgument().getOWLNamedIndividual();
        } else {
            if (i1Arg.getSWRLBuiltInArgumentType() != NAMED_INDIVIDUAL) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Second argument must be of type %s but is %s.", NAMESPACE, getInvokingRuleName(), NAMED_INDIVIDUAL, i1Arg.getSWRLBuiltInArgumentType()));
            }
            i1 = i1Arg.asSWRLNamedIndividualBuiltInArgument().getOWLNamedIndividual();
        }

        final OWLNamedIndividual i2;
        if (i2Arg.isVariable()) {
            var i2Var = i2Arg.asVariable();
            if (i2Var.isUnbound()) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound but is unbound.", NAMESPACE, getInvokingRuleName(), i2Var.getVariableName()));
            }
            i2Arg = i2Var.getBuiltInResult().get(); // we checked above that it's bound, so must have a value
            if (i2Arg.getSWRLBuiltInArgumentType() != NAMED_INDIVIDUAL) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound to a value of type %s but is %s.", NAMESPACE, getInvokingRuleName(), i2Var.getVariableName(), NAMED_INDIVIDUAL, i2Arg.getSWRLBuiltInArgumentType()));
            }
            i2 = i2Arg.asSWRLNamedIndividualBuiltInArgument().getOWLNamedIndividual();
        } else {
            if (i2Arg.getSWRLBuiltInArgumentType() != NAMED_INDIVIDUAL) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Third argument must be of type %s but is %s.", NAMESPACE, getInvokingRuleName(), NAMED_INDIVIDUAL, i2Arg.getSWRLBuiltInArgumentType()));
            }
            i2 = i2Arg.asSWRLNamedIndividualBuiltInArgument().getOWLNamedIndividual();
        }

        final OWLClass aspect;
        if (aspectArg.isVariable()) {
            var aspectVar = aspectArg.asVariable();
            if (aspectVar.isUnbound()) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound but is unbound.", NAMESPACE, getInvokingRuleName(), aspectVar.getVariableName()));
            }
            aspectArg = aspectVar.getBuiltInResult().get(); // we checked above that it's bound, so must have a value
            if (aspectArg.getSWRLBuiltInArgumentType() != CLASS) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Variable %s must be bound to a value of type %s but is %s.", NAMESPACE, getInvokingRuleName(), aspectVar.getVariableName(), CLASS, aspectArg.getSWRLBuiltInArgumentType()));
            }
            aspect = aspectArg.asSWRLClassBuiltInArgument().getOWLClass();
        } else {
            if (aspectArg.getSWRLBuiltInArgumentType() != CLASS) {
                throw new SWRLBuiltInException(String.format("Built-in %sopa in rule %s: Second argument must be of type %s but is %s.", NAMESPACE, getInvokingRuleName(), CLASS, aspectArg.getSWRLBuiltInArgumentType()));
            }
            aspect = aspectArg.asSWRLClassBuiltInArgument().getOWLClass();
        }

        OWLOntology onto = getBuiltInBridge().getOWLOntology();

        OWLOntologyAspectManager aspectManager = AspectOWLEditorKitHook.getAspectManager(onto.getOWLOntologyManager());

        var axiomOptional = onto.getObjectPropertyAssertionAxioms(i1).stream().filter(ax -> ax.getProperty().equals(op) && ax.getObject().equals(i2)).findFirst();

        if (axiomOptional.isPresent()) {
            return aspectManager.getAssertedAspects(onto, axiomOptional.get()).stream().anyMatch(as -> as.asClassExpression().equals(aspect));
        }

        return false;

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
    public boolean createOPA(List<SWRLBuiltInArgument> arguments) throws SWRLBuiltInException {
        return false;
    }

        @Override
    public void reset() throws SWRLBuiltInLibraryException {

    }



}
