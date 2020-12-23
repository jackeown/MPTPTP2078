%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:58 EST 2020

% Result     : Theorem 55.75s
% Output     : CNFRefutation 55.75s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 189 expanded)
%              Number of clauses        :   42 (  53 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 247 expanded)
%              Number of equality atoms :  100 ( 202 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f41])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f31,f42])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f42,f42])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f40,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f50,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(definition_unfolding,[],[f40,f31,f26,f43,f43])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f39,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_7,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_341,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_1110,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,X2))))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_4,c_341])).

cnf(c_5,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_334,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_15189,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_1110,c_334])).

cnf(c_15201,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,X2))))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k3_xboole_0(k5_xboole_0(X1,X2),X0)) ),
    inference(light_normalisation,[status(thm)],[c_15189,c_4])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_460,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(superposition,[status(thm)],[c_4,c_8])).

cnf(c_137601,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_15201,c_460])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_192,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_472,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_192])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_191,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_719,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1)) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_472,c_191])).

cnf(c_15863,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_719])).

cnf(c_16414,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_15863])).

cnf(c_17174,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_16414,c_4])).

cnf(c_137602,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != sK1 ),
    inference(demodulation,[status(thm)],[c_137601,c_17174])).

cnf(c_67,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_300,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_537,plain,
    ( X0 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | X0 = sK1
    | sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_3108,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) = sK1
    | sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_66,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1586,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_555,plain,
    ( X0 != X1
    | X0 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_825,plain,
    ( X0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))
    | X0 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_555])).

cnf(c_1585,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))
    | k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_826,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_295,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_323,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_416,plain,
    ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1
    | sK1 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_297,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_66])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_286,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_264,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_137602,c_3108,c_1586,c_1585,c_826,c_416,c_297,c_286,c_264,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.75/7.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.75/7.47  
% 55.75/7.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.75/7.47  
% 55.75/7.47  ------  iProver source info
% 55.75/7.47  
% 55.75/7.47  git: date: 2020-06-30 10:37:57 +0100
% 55.75/7.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.75/7.47  git: non_committed_changes: false
% 55.75/7.47  git: last_make_outside_of_git: false
% 55.75/7.47  
% 55.75/7.47  ------ 
% 55.75/7.47  
% 55.75/7.47  ------ Input Options
% 55.75/7.47  
% 55.75/7.47  --out_options                           all
% 55.75/7.47  --tptp_safe_out                         true
% 55.75/7.47  --problem_path                          ""
% 55.75/7.47  --include_path                          ""
% 55.75/7.47  --clausifier                            res/vclausify_rel
% 55.75/7.47  --clausifier_options                    --mode clausify
% 55.75/7.47  --stdin                                 false
% 55.75/7.47  --stats_out                             sel
% 55.75/7.47  
% 55.75/7.47  ------ General Options
% 55.75/7.47  
% 55.75/7.47  --fof                                   false
% 55.75/7.47  --time_out_real                         604.99
% 55.75/7.47  --time_out_virtual                      -1.
% 55.75/7.47  --symbol_type_check                     false
% 55.75/7.47  --clausify_out                          false
% 55.75/7.47  --sig_cnt_out                           false
% 55.75/7.47  --trig_cnt_out                          false
% 55.75/7.47  --trig_cnt_out_tolerance                1.
% 55.75/7.47  --trig_cnt_out_sk_spl                   false
% 55.75/7.47  --abstr_cl_out                          false
% 55.75/7.47  
% 55.75/7.47  ------ Global Options
% 55.75/7.47  
% 55.75/7.47  --schedule                              none
% 55.75/7.47  --add_important_lit                     false
% 55.75/7.47  --prop_solver_per_cl                    1000
% 55.75/7.47  --min_unsat_core                        false
% 55.75/7.47  --soft_assumptions                      false
% 55.75/7.47  --soft_lemma_size                       3
% 55.75/7.47  --prop_impl_unit_size                   0
% 55.75/7.47  --prop_impl_unit                        []
% 55.75/7.47  --share_sel_clauses                     true
% 55.75/7.47  --reset_solvers                         false
% 55.75/7.47  --bc_imp_inh                            [conj_cone]
% 55.75/7.47  --conj_cone_tolerance                   3.
% 55.75/7.47  --extra_neg_conj                        none
% 55.75/7.47  --large_theory_mode                     true
% 55.75/7.47  --prolific_symb_bound                   200
% 55.75/7.47  --lt_threshold                          2000
% 55.75/7.47  --clause_weak_htbl                      true
% 55.75/7.47  --gc_record_bc_elim                     false
% 55.75/7.47  
% 55.75/7.47  ------ Preprocessing Options
% 55.75/7.47  
% 55.75/7.47  --preprocessing_flag                    true
% 55.75/7.47  --time_out_prep_mult                    0.1
% 55.75/7.47  --splitting_mode                        input
% 55.75/7.47  --splitting_grd                         true
% 55.75/7.47  --splitting_cvd                         false
% 55.75/7.47  --splitting_cvd_svl                     false
% 55.75/7.47  --splitting_nvd                         32
% 55.75/7.47  --sub_typing                            true
% 55.75/7.47  --prep_gs_sim                           false
% 55.75/7.47  --prep_unflatten                        true
% 55.75/7.47  --prep_res_sim                          true
% 55.75/7.47  --prep_upred                            true
% 55.75/7.47  --prep_sem_filter                       exhaustive
% 55.75/7.47  --prep_sem_filter_out                   false
% 55.75/7.47  --pred_elim                             false
% 55.75/7.47  --res_sim_input                         true
% 55.75/7.47  --eq_ax_congr_red                       true
% 55.75/7.47  --pure_diseq_elim                       true
% 55.75/7.47  --brand_transform                       false
% 55.75/7.47  --non_eq_to_eq                          false
% 55.75/7.47  --prep_def_merge                        true
% 55.75/7.47  --prep_def_merge_prop_impl              false
% 55.75/7.47  --prep_def_merge_mbd                    true
% 55.75/7.47  --prep_def_merge_tr_red                 false
% 55.75/7.47  --prep_def_merge_tr_cl                  false
% 55.75/7.47  --smt_preprocessing                     true
% 55.75/7.47  --smt_ac_axioms                         fast
% 55.75/7.47  --preprocessed_out                      false
% 55.75/7.47  --preprocessed_stats                    false
% 55.75/7.47  
% 55.75/7.47  ------ Abstraction refinement Options
% 55.75/7.47  
% 55.75/7.47  --abstr_ref                             []
% 55.75/7.47  --abstr_ref_prep                        false
% 55.75/7.47  --abstr_ref_until_sat                   false
% 55.75/7.47  --abstr_ref_sig_restrict                funpre
% 55.75/7.47  --abstr_ref_af_restrict_to_split_sk     false
% 55.75/7.47  --abstr_ref_under                       []
% 55.75/7.47  
% 55.75/7.47  ------ SAT Options
% 55.75/7.47  
% 55.75/7.47  --sat_mode                              false
% 55.75/7.47  --sat_fm_restart_options                ""
% 55.75/7.47  --sat_gr_def                            false
% 55.75/7.47  --sat_epr_types                         true
% 55.75/7.47  --sat_non_cyclic_types                  false
% 55.75/7.47  --sat_finite_models                     false
% 55.75/7.47  --sat_fm_lemmas                         false
% 55.75/7.47  --sat_fm_prep                           false
% 55.75/7.47  --sat_fm_uc_incr                        true
% 55.75/7.47  --sat_out_model                         small
% 55.75/7.47  --sat_out_clauses                       false
% 55.75/7.47  
% 55.75/7.47  ------ QBF Options
% 55.75/7.47  
% 55.75/7.47  --qbf_mode                              false
% 55.75/7.47  --qbf_elim_univ                         false
% 55.75/7.47  --qbf_dom_inst                          none
% 55.75/7.47  --qbf_dom_pre_inst                      false
% 55.75/7.47  --qbf_sk_in                             false
% 55.75/7.47  --qbf_pred_elim                         true
% 55.75/7.47  --qbf_split                             512
% 55.75/7.47  
% 55.75/7.47  ------ BMC1 Options
% 55.75/7.47  
% 55.75/7.47  --bmc1_incremental                      false
% 55.75/7.47  --bmc1_axioms                           reachable_all
% 55.75/7.47  --bmc1_min_bound                        0
% 55.75/7.47  --bmc1_max_bound                        -1
% 55.75/7.47  --bmc1_max_bound_default                -1
% 55.75/7.47  --bmc1_symbol_reachability              true
% 55.75/7.47  --bmc1_property_lemmas                  false
% 55.75/7.47  --bmc1_k_induction                      false
% 55.75/7.47  --bmc1_non_equiv_states                 false
% 55.75/7.47  --bmc1_deadlock                         false
% 55.75/7.47  --bmc1_ucm                              false
% 55.75/7.47  --bmc1_add_unsat_core                   none
% 55.75/7.47  --bmc1_unsat_core_children              false
% 55.75/7.47  --bmc1_unsat_core_extrapolate_axioms    false
% 55.75/7.47  --bmc1_out_stat                         full
% 55.75/7.47  --bmc1_ground_init                      false
% 55.75/7.47  --bmc1_pre_inst_next_state              false
% 55.75/7.47  --bmc1_pre_inst_state                   false
% 55.75/7.47  --bmc1_pre_inst_reach_state             false
% 55.75/7.47  --bmc1_out_unsat_core                   false
% 55.75/7.47  --bmc1_aig_witness_out                  false
% 55.75/7.47  --bmc1_verbose                          false
% 55.75/7.47  --bmc1_dump_clauses_tptp                false
% 55.75/7.47  --bmc1_dump_unsat_core_tptp             false
% 55.75/7.47  --bmc1_dump_file                        -
% 55.75/7.47  --bmc1_ucm_expand_uc_limit              128
% 55.75/7.47  --bmc1_ucm_n_expand_iterations          6
% 55.75/7.47  --bmc1_ucm_extend_mode                  1
% 55.75/7.47  --bmc1_ucm_init_mode                    2
% 55.75/7.47  --bmc1_ucm_cone_mode                    none
% 55.75/7.47  --bmc1_ucm_reduced_relation_type        0
% 55.75/7.47  --bmc1_ucm_relax_model                  4
% 55.75/7.47  --bmc1_ucm_full_tr_after_sat            true
% 55.75/7.47  --bmc1_ucm_expand_neg_assumptions       false
% 55.75/7.47  --bmc1_ucm_layered_model                none
% 55.75/7.47  --bmc1_ucm_max_lemma_size               10
% 55.75/7.47  
% 55.75/7.47  ------ AIG Options
% 55.75/7.47  
% 55.75/7.47  --aig_mode                              false
% 55.75/7.47  
% 55.75/7.47  ------ Instantiation Options
% 55.75/7.47  
% 55.75/7.47  --instantiation_flag                    true
% 55.75/7.47  --inst_sos_flag                         false
% 55.75/7.47  --inst_sos_phase                        true
% 55.75/7.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.75/7.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.75/7.47  --inst_lit_sel_side                     num_symb
% 55.75/7.47  --inst_solver_per_active                1400
% 55.75/7.47  --inst_solver_calls_frac                1.
% 55.75/7.47  --inst_passive_queue_type               priority_queues
% 55.75/7.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.75/7.47  --inst_passive_queues_freq              [25;2]
% 55.75/7.47  --inst_dismatching                      true
% 55.75/7.47  --inst_eager_unprocessed_to_passive     true
% 55.75/7.47  --inst_prop_sim_given                   true
% 55.75/7.47  --inst_prop_sim_new                     false
% 55.75/7.47  --inst_subs_new                         false
% 55.75/7.47  --inst_eq_res_simp                      false
% 55.75/7.47  --inst_subs_given                       false
% 55.75/7.47  --inst_orphan_elimination               true
% 55.75/7.47  --inst_learning_loop_flag               true
% 55.75/7.47  --inst_learning_start                   3000
% 55.75/7.47  --inst_learning_factor                  2
% 55.75/7.47  --inst_start_prop_sim_after_learn       3
% 55.75/7.47  --inst_sel_renew                        solver
% 55.75/7.47  --inst_lit_activity_flag                true
% 55.75/7.47  --inst_restr_to_given                   false
% 55.75/7.47  --inst_activity_threshold               500
% 55.75/7.47  --inst_out_proof                        true
% 55.75/7.47  
% 55.75/7.47  ------ Resolution Options
% 55.75/7.47  
% 55.75/7.47  --resolution_flag                       true
% 55.75/7.47  --res_lit_sel                           adaptive
% 55.75/7.47  --res_lit_sel_side                      none
% 55.75/7.47  --res_ordering                          kbo
% 55.75/7.47  --res_to_prop_solver                    active
% 55.75/7.47  --res_prop_simpl_new                    false
% 55.75/7.47  --res_prop_simpl_given                  true
% 55.75/7.47  --res_passive_queue_type                priority_queues
% 55.75/7.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.75/7.47  --res_passive_queues_freq               [15;5]
% 55.75/7.47  --res_forward_subs                      full
% 55.75/7.47  --res_backward_subs                     full
% 55.75/7.47  --res_forward_subs_resolution           true
% 55.75/7.47  --res_backward_subs_resolution          true
% 55.75/7.47  --res_orphan_elimination                true
% 55.75/7.47  --res_time_limit                        2.
% 55.75/7.47  --res_out_proof                         true
% 55.75/7.47  
% 55.75/7.47  ------ Superposition Options
% 55.75/7.47  
% 55.75/7.47  --superposition_flag                    true
% 55.75/7.47  --sup_passive_queue_type                priority_queues
% 55.75/7.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.75/7.47  --sup_passive_queues_freq               [1;4]
% 55.75/7.47  --demod_completeness_check              fast
% 55.75/7.47  --demod_use_ground                      true
% 55.75/7.47  --sup_to_prop_solver                    passive
% 55.75/7.47  --sup_prop_simpl_new                    true
% 55.75/7.47  --sup_prop_simpl_given                  true
% 55.75/7.47  --sup_fun_splitting                     false
% 55.75/7.47  --sup_smt_interval                      50000
% 55.75/7.47  
% 55.75/7.47  ------ Superposition Simplification Setup
% 55.75/7.47  
% 55.75/7.47  --sup_indices_passive                   []
% 55.75/7.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.75/7.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.75/7.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.75/7.47  --sup_full_triv                         [TrivRules;PropSubs]
% 55.75/7.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.75/7.47  --sup_full_bw                           [BwDemod]
% 55.75/7.47  --sup_immed_triv                        [TrivRules]
% 55.75/7.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.75/7.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.75/7.47  --sup_immed_bw_main                     []
% 55.75/7.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.75/7.47  --sup_input_triv                        [Unflattening;TrivRules]
% 55.75/7.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.75/7.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.75/7.47  
% 55.75/7.47  ------ Combination Options
% 55.75/7.47  
% 55.75/7.47  --comb_res_mult                         3
% 55.75/7.47  --comb_sup_mult                         2
% 55.75/7.47  --comb_inst_mult                        10
% 55.75/7.47  
% 55.75/7.47  ------ Debug Options
% 55.75/7.47  
% 55.75/7.47  --dbg_backtrace                         false
% 55.75/7.47  --dbg_dump_prop_clauses                 false
% 55.75/7.47  --dbg_dump_prop_clauses_file            -
% 55.75/7.47  --dbg_out_stat                          false
% 55.75/7.47  ------ Parsing...
% 55.75/7.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.75/7.47  
% 55.75/7.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 55.75/7.47  
% 55.75/7.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.75/7.47  
% 55.75/7.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.75/7.47  ------ Proving...
% 55.75/7.47  ------ Problem Properties 
% 55.75/7.47  
% 55.75/7.47  
% 55.75/7.47  clauses                                 10
% 55.75/7.47  conjectures                             2
% 55.75/7.47  EPR                                     1
% 55.75/7.47  Horn                                    10
% 55.75/7.47  unary                                   7
% 55.75/7.47  binary                                  3
% 55.75/7.47  lits                                    13
% 55.75/7.47  lits eq                                 7
% 55.75/7.47  fd_pure                                 0
% 55.75/7.47  fd_pseudo                               0
% 55.75/7.47  fd_cond                                 0
% 55.75/7.47  fd_pseudo_cond                          0
% 55.75/7.47  AC symbols                              0
% 55.75/7.47  
% 55.75/7.47  ------ Input Options Time Limit: Unbounded
% 55.75/7.47  
% 55.75/7.47  
% 55.75/7.47  ------ 
% 55.75/7.47  Current options:
% 55.75/7.47  ------ 
% 55.75/7.47  
% 55.75/7.47  ------ Input Options
% 55.75/7.47  
% 55.75/7.47  --out_options                           all
% 55.75/7.47  --tptp_safe_out                         true
% 55.75/7.47  --problem_path                          ""
% 55.75/7.47  --include_path                          ""
% 55.75/7.47  --clausifier                            res/vclausify_rel
% 55.75/7.47  --clausifier_options                    --mode clausify
% 55.75/7.47  --stdin                                 false
% 55.75/7.47  --stats_out                             sel
% 55.75/7.47  
% 55.75/7.47  ------ General Options
% 55.75/7.47  
% 55.75/7.47  --fof                                   false
% 55.75/7.47  --time_out_real                         604.99
% 55.75/7.47  --time_out_virtual                      -1.
% 55.75/7.47  --symbol_type_check                     false
% 55.75/7.47  --clausify_out                          false
% 55.75/7.47  --sig_cnt_out                           false
% 55.75/7.47  --trig_cnt_out                          false
% 55.75/7.47  --trig_cnt_out_tolerance                1.
% 55.75/7.47  --trig_cnt_out_sk_spl                   false
% 55.75/7.47  --abstr_cl_out                          false
% 55.75/7.47  
% 55.75/7.47  ------ Global Options
% 55.75/7.47  
% 55.75/7.47  --schedule                              none
% 55.75/7.47  --add_important_lit                     false
% 55.75/7.47  --prop_solver_per_cl                    1000
% 55.75/7.47  --min_unsat_core                        false
% 55.75/7.47  --soft_assumptions                      false
% 55.75/7.47  --soft_lemma_size                       3
% 55.75/7.47  --prop_impl_unit_size                   0
% 55.75/7.47  --prop_impl_unit                        []
% 55.75/7.47  --share_sel_clauses                     true
% 55.75/7.47  --reset_solvers                         false
% 55.75/7.47  --bc_imp_inh                            [conj_cone]
% 55.75/7.47  --conj_cone_tolerance                   3.
% 55.75/7.47  --extra_neg_conj                        none
% 55.75/7.47  --large_theory_mode                     true
% 55.75/7.47  --prolific_symb_bound                   200
% 55.75/7.47  --lt_threshold                          2000
% 55.75/7.47  --clause_weak_htbl                      true
% 55.75/7.47  --gc_record_bc_elim                     false
% 55.75/7.47  
% 55.75/7.47  ------ Preprocessing Options
% 55.75/7.47  
% 55.75/7.47  --preprocessing_flag                    true
% 55.75/7.47  --time_out_prep_mult                    0.1
% 55.75/7.47  --splitting_mode                        input
% 55.75/7.47  --splitting_grd                         true
% 55.75/7.47  --splitting_cvd                         false
% 55.75/7.47  --splitting_cvd_svl                     false
% 55.75/7.47  --splitting_nvd                         32
% 55.75/7.47  --sub_typing                            true
% 55.75/7.47  --prep_gs_sim                           false
% 55.75/7.47  --prep_unflatten                        true
% 55.75/7.47  --prep_res_sim                          true
% 55.75/7.47  --prep_upred                            true
% 55.75/7.47  --prep_sem_filter                       exhaustive
% 55.75/7.47  --prep_sem_filter_out                   false
% 55.75/7.47  --pred_elim                             false
% 55.75/7.47  --res_sim_input                         true
% 55.75/7.47  --eq_ax_congr_red                       true
% 55.75/7.47  --pure_diseq_elim                       true
% 55.75/7.47  --brand_transform                       false
% 55.75/7.47  --non_eq_to_eq                          false
% 55.75/7.47  --prep_def_merge                        true
% 55.75/7.47  --prep_def_merge_prop_impl              false
% 55.75/7.47  --prep_def_merge_mbd                    true
% 55.75/7.47  --prep_def_merge_tr_red                 false
% 55.75/7.47  --prep_def_merge_tr_cl                  false
% 55.75/7.47  --smt_preprocessing                     true
% 55.75/7.47  --smt_ac_axioms                         fast
% 55.75/7.47  --preprocessed_out                      false
% 55.75/7.47  --preprocessed_stats                    false
% 55.75/7.47  
% 55.75/7.47  ------ Abstraction refinement Options
% 55.75/7.47  
% 55.75/7.47  --abstr_ref                             []
% 55.75/7.47  --abstr_ref_prep                        false
% 55.75/7.47  --abstr_ref_until_sat                   false
% 55.75/7.47  --abstr_ref_sig_restrict                funpre
% 55.75/7.47  --abstr_ref_af_restrict_to_split_sk     false
% 55.75/7.47  --abstr_ref_under                       []
% 55.75/7.47  
% 55.75/7.47  ------ SAT Options
% 55.75/7.47  
% 55.75/7.47  --sat_mode                              false
% 55.75/7.47  --sat_fm_restart_options                ""
% 55.75/7.47  --sat_gr_def                            false
% 55.75/7.47  --sat_epr_types                         true
% 55.75/7.47  --sat_non_cyclic_types                  false
% 55.75/7.47  --sat_finite_models                     false
% 55.75/7.47  --sat_fm_lemmas                         false
% 55.75/7.47  --sat_fm_prep                           false
% 55.75/7.47  --sat_fm_uc_incr                        true
% 55.75/7.47  --sat_out_model                         small
% 55.75/7.47  --sat_out_clauses                       false
% 55.75/7.47  
% 55.75/7.47  ------ QBF Options
% 55.75/7.47  
% 55.75/7.47  --qbf_mode                              false
% 55.75/7.47  --qbf_elim_univ                         false
% 55.75/7.47  --qbf_dom_inst                          none
% 55.75/7.47  --qbf_dom_pre_inst                      false
% 55.75/7.47  --qbf_sk_in                             false
% 55.75/7.47  --qbf_pred_elim                         true
% 55.75/7.47  --qbf_split                             512
% 55.75/7.47  
% 55.75/7.47  ------ BMC1 Options
% 55.75/7.47  
% 55.75/7.47  --bmc1_incremental                      false
% 55.75/7.47  --bmc1_axioms                           reachable_all
% 55.75/7.47  --bmc1_min_bound                        0
% 55.75/7.47  --bmc1_max_bound                        -1
% 55.75/7.47  --bmc1_max_bound_default                -1
% 55.75/7.47  --bmc1_symbol_reachability              true
% 55.75/7.47  --bmc1_property_lemmas                  false
% 55.75/7.47  --bmc1_k_induction                      false
% 55.75/7.47  --bmc1_non_equiv_states                 false
% 55.75/7.47  --bmc1_deadlock                         false
% 55.75/7.47  --bmc1_ucm                              false
% 55.75/7.47  --bmc1_add_unsat_core                   none
% 55.75/7.47  --bmc1_unsat_core_children              false
% 55.75/7.47  --bmc1_unsat_core_extrapolate_axioms    false
% 55.75/7.47  --bmc1_out_stat                         full
% 55.75/7.47  --bmc1_ground_init                      false
% 55.75/7.47  --bmc1_pre_inst_next_state              false
% 55.75/7.47  --bmc1_pre_inst_state                   false
% 55.75/7.47  --bmc1_pre_inst_reach_state             false
% 55.75/7.47  --bmc1_out_unsat_core                   false
% 55.75/7.47  --bmc1_aig_witness_out                  false
% 55.75/7.47  --bmc1_verbose                          false
% 55.75/7.47  --bmc1_dump_clauses_tptp                false
% 55.75/7.47  --bmc1_dump_unsat_core_tptp             false
% 55.75/7.47  --bmc1_dump_file                        -
% 55.75/7.47  --bmc1_ucm_expand_uc_limit              128
% 55.75/7.47  --bmc1_ucm_n_expand_iterations          6
% 55.75/7.47  --bmc1_ucm_extend_mode                  1
% 55.75/7.47  --bmc1_ucm_init_mode                    2
% 55.75/7.47  --bmc1_ucm_cone_mode                    none
% 55.75/7.47  --bmc1_ucm_reduced_relation_type        0
% 55.75/7.47  --bmc1_ucm_relax_model                  4
% 55.75/7.47  --bmc1_ucm_full_tr_after_sat            true
% 55.75/7.47  --bmc1_ucm_expand_neg_assumptions       false
% 55.75/7.47  --bmc1_ucm_layered_model                none
% 55.75/7.47  --bmc1_ucm_max_lemma_size               10
% 55.75/7.47  
% 55.75/7.47  ------ AIG Options
% 55.75/7.47  
% 55.75/7.47  --aig_mode                              false
% 55.75/7.47  
% 55.75/7.47  ------ Instantiation Options
% 55.75/7.47  
% 55.75/7.47  --instantiation_flag                    true
% 55.75/7.47  --inst_sos_flag                         false
% 55.75/7.47  --inst_sos_phase                        true
% 55.75/7.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.75/7.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.75/7.47  --inst_lit_sel_side                     num_symb
% 55.75/7.47  --inst_solver_per_active                1400
% 55.75/7.47  --inst_solver_calls_frac                1.
% 55.75/7.47  --inst_passive_queue_type               priority_queues
% 55.75/7.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.75/7.47  --inst_passive_queues_freq              [25;2]
% 55.75/7.47  --inst_dismatching                      true
% 55.75/7.47  --inst_eager_unprocessed_to_passive     true
% 55.75/7.47  --inst_prop_sim_given                   true
% 55.75/7.47  --inst_prop_sim_new                     false
% 55.75/7.47  --inst_subs_new                         false
% 55.75/7.47  --inst_eq_res_simp                      false
% 55.75/7.47  --inst_subs_given                       false
% 55.75/7.47  --inst_orphan_elimination               true
% 55.75/7.47  --inst_learning_loop_flag               true
% 55.75/7.47  --inst_learning_start                   3000
% 55.75/7.47  --inst_learning_factor                  2
% 55.75/7.47  --inst_start_prop_sim_after_learn       3
% 55.75/7.47  --inst_sel_renew                        solver
% 55.75/7.47  --inst_lit_activity_flag                true
% 55.75/7.47  --inst_restr_to_given                   false
% 55.75/7.47  --inst_activity_threshold               500
% 55.75/7.47  --inst_out_proof                        true
% 55.75/7.47  
% 55.75/7.47  ------ Resolution Options
% 55.75/7.47  
% 55.75/7.47  --resolution_flag                       true
% 55.75/7.47  --res_lit_sel                           adaptive
% 55.75/7.47  --res_lit_sel_side                      none
% 55.75/7.47  --res_ordering                          kbo
% 55.75/7.47  --res_to_prop_solver                    active
% 55.75/7.47  --res_prop_simpl_new                    false
% 55.75/7.47  --res_prop_simpl_given                  true
% 55.75/7.47  --res_passive_queue_type                priority_queues
% 55.75/7.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.75/7.47  --res_passive_queues_freq               [15;5]
% 55.75/7.47  --res_forward_subs                      full
% 55.75/7.47  --res_backward_subs                     full
% 55.75/7.47  --res_forward_subs_resolution           true
% 55.75/7.47  --res_backward_subs_resolution          true
% 55.75/7.47  --res_orphan_elimination                true
% 55.75/7.47  --res_time_limit                        2.
% 55.75/7.47  --res_out_proof                         true
% 55.75/7.47  
% 55.75/7.47  ------ Superposition Options
% 55.75/7.47  
% 55.75/7.47  --superposition_flag                    true
% 55.75/7.47  --sup_passive_queue_type                priority_queues
% 55.75/7.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.75/7.47  --sup_passive_queues_freq               [1;4]
% 55.75/7.47  --demod_completeness_check              fast
% 55.75/7.47  --demod_use_ground                      true
% 55.75/7.47  --sup_to_prop_solver                    passive
% 55.75/7.47  --sup_prop_simpl_new                    true
% 55.75/7.47  --sup_prop_simpl_given                  true
% 55.75/7.47  --sup_fun_splitting                     false
% 55.75/7.47  --sup_smt_interval                      50000
% 55.75/7.47  
% 55.75/7.47  ------ Superposition Simplification Setup
% 55.75/7.47  
% 55.75/7.47  --sup_indices_passive                   []
% 55.75/7.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.75/7.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.75/7.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.75/7.47  --sup_full_triv                         [TrivRules;PropSubs]
% 55.75/7.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.75/7.47  --sup_full_bw                           [BwDemod]
% 55.75/7.47  --sup_immed_triv                        [TrivRules]
% 55.75/7.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.75/7.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.75/7.47  --sup_immed_bw_main                     []
% 55.75/7.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.75/7.47  --sup_input_triv                        [Unflattening;TrivRules]
% 55.75/7.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.75/7.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.75/7.47  
% 55.75/7.47  ------ Combination Options
% 55.75/7.47  
% 55.75/7.47  --comb_res_mult                         3
% 55.75/7.47  --comb_sup_mult                         2
% 55.75/7.47  --comb_inst_mult                        10
% 55.75/7.47  
% 55.75/7.47  ------ Debug Options
% 55.75/7.47  
% 55.75/7.47  --dbg_backtrace                         false
% 55.75/7.47  --dbg_dump_prop_clauses                 false
% 55.75/7.47  --dbg_dump_prop_clauses_file            -
% 55.75/7.47  --dbg_out_stat                          false
% 55.75/7.47  
% 55.75/7.47  
% 55.75/7.47  
% 55.75/7.47  
% 55.75/7.47  ------ Proving...
% 55.75/7.47  
% 55.75/7.47  
% 55.75/7.47  % SZS status Theorem for theBenchmark.p
% 55.75/7.47  
% 55.75/7.47  % SZS output start CNFRefutation for theBenchmark.p
% 55.75/7.47  
% 55.75/7.47  fof(f6,axiom,(
% 55.75/7.47    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 55.75/7.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.47  
% 55.75/7.47  fof(f30,plain,(
% 55.75/7.47    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 55.75/7.47    inference(cnf_transformation,[],[f6])).
% 55.75/7.47  
% 55.75/7.47  fof(f14,axiom,(
% 55.75/7.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 55.75/7.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.47  
% 55.75/7.47  fof(f38,plain,(
% 55.75/7.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 55.75/7.47    inference(cnf_transformation,[],[f14])).
% 55.75/7.47  
% 55.75/7.47  fof(f7,axiom,(
% 55.75/7.47    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 55.75/7.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.47  
% 55.75/7.47  fof(f31,plain,(
% 55.75/7.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 55.75/7.47    inference(cnf_transformation,[],[f7])).
% 55.75/7.47  
% 55.75/7.47  fof(f10,axiom,(
% 55.75/7.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 55.75/7.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.47  
% 55.75/7.47  fof(f34,plain,(
% 55.75/7.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 55.75/7.47    inference(cnf_transformation,[],[f10])).
% 55.75/7.47  
% 55.75/7.47  fof(f11,axiom,(
% 55.75/7.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 55.75/7.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.47  
% 55.75/7.47  fof(f35,plain,(
% 55.75/7.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 55.75/7.47    inference(cnf_transformation,[],[f11])).
% 55.75/7.47  
% 55.75/7.47  fof(f12,axiom,(
% 55.75/7.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 55.75/7.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.47  
% 55.75/7.47  fof(f36,plain,(
% 55.75/7.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 55.75/7.47    inference(cnf_transformation,[],[f12])).
% 55.75/7.47  
% 55.75/7.47  fof(f41,plain,(
% 55.75/7.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 55.75/7.47    inference(definition_unfolding,[],[f35,f36])).
% 55.75/7.47  
% 55.75/7.47  fof(f42,plain,(
% 55.75/7.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 55.75/7.47    inference(definition_unfolding,[],[f34,f41])).
% 55.75/7.47  
% 55.75/7.47  fof(f49,plain,(
% 55.75/7.47    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 55.75/7.47    inference(definition_unfolding,[],[f38,f31,f42])).
% 55.75/7.47  
% 55.75/7.47  fof(f8,axiom,(
% 55.75/7.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 55.75/7.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.47  
% 55.75/7.47  fof(f32,plain,(
% 55.75/7.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 55.75/7.47    inference(cnf_transformation,[],[f8])).
% 55.75/7.47  
% 55.75/7.47  fof(f47,plain,(
% 55.75/7.47    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 55.75/7.47    inference(definition_unfolding,[],[f32,f42,f42])).
% 55.75/7.47  
% 55.75/7.47  fof(f15,conjecture,(
% 55.75/7.47    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 55.75/7.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.47  
% 55.75/7.47  fof(f16,negated_conjecture,(
% 55.75/7.47    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 55.75/7.47    inference(negated_conjecture,[],[f15])).
% 55.75/7.47  
% 55.75/7.47  fof(f22,plain,(
% 55.75/7.47    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 55.75/7.47    inference(ennf_transformation,[],[f16])).
% 55.75/7.47  
% 55.75/7.47  fof(f23,plain,(
% 55.75/7.47    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 55.75/7.48    introduced(choice_axiom,[])).
% 55.75/7.48  
% 55.75/7.48  fof(f24,plain,(
% 55.75/7.48    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 55.75/7.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 55.75/7.48  
% 55.75/7.48  fof(f40,plain,(
% 55.75/7.48    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 55.75/7.48    inference(cnf_transformation,[],[f24])).
% 55.75/7.48  
% 55.75/7.48  fof(f2,axiom,(
% 55.75/7.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.75/7.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.48  
% 55.75/7.48  fof(f26,plain,(
% 55.75/7.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.75/7.48    inference(cnf_transformation,[],[f2])).
% 55.75/7.48  
% 55.75/7.48  fof(f9,axiom,(
% 55.75/7.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 55.75/7.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.48  
% 55.75/7.48  fof(f33,plain,(
% 55.75/7.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 55.75/7.48    inference(cnf_transformation,[],[f9])).
% 55.75/7.48  
% 55.75/7.48  fof(f43,plain,(
% 55.75/7.48    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 55.75/7.48    inference(definition_unfolding,[],[f33,f42])).
% 55.75/7.48  
% 55.75/7.48  fof(f50,plain,(
% 55.75/7.48    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1),
% 55.75/7.48    inference(definition_unfolding,[],[f40,f31,f26,f43,f43])).
% 55.75/7.48  
% 55.75/7.48  fof(f1,axiom,(
% 55.75/7.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 55.75/7.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.48  
% 55.75/7.48  fof(f25,plain,(
% 55.75/7.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 55.75/7.48    inference(cnf_transformation,[],[f1])).
% 55.75/7.48  
% 55.75/7.48  fof(f4,axiom,(
% 55.75/7.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 55.75/7.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.48  
% 55.75/7.48  fof(f28,plain,(
% 55.75/7.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 55.75/7.48    inference(cnf_transformation,[],[f4])).
% 55.75/7.48  
% 55.75/7.48  fof(f45,plain,(
% 55.75/7.48    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 55.75/7.48    inference(definition_unfolding,[],[f28,f26])).
% 55.75/7.48  
% 55.75/7.48  fof(f5,axiom,(
% 55.75/7.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 55.75/7.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.48  
% 55.75/7.48  fof(f18,plain,(
% 55.75/7.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 55.75/7.48    inference(unused_predicate_definition_removal,[],[f5])).
% 55.75/7.48  
% 55.75/7.48  fof(f20,plain,(
% 55.75/7.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 55.75/7.48    inference(ennf_transformation,[],[f18])).
% 55.75/7.48  
% 55.75/7.48  fof(f29,plain,(
% 55.75/7.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 55.75/7.48    inference(cnf_transformation,[],[f20])).
% 55.75/7.48  
% 55.75/7.48  fof(f46,plain,(
% 55.75/7.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 55.75/7.48    inference(definition_unfolding,[],[f29,f26])).
% 55.75/7.48  
% 55.75/7.48  fof(f3,axiom,(
% 55.75/7.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 55.75/7.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.48  
% 55.75/7.48  fof(f19,plain,(
% 55.75/7.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 55.75/7.48    inference(ennf_transformation,[],[f3])).
% 55.75/7.48  
% 55.75/7.48  fof(f27,plain,(
% 55.75/7.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 55.75/7.48    inference(cnf_transformation,[],[f19])).
% 55.75/7.48  
% 55.75/7.48  fof(f44,plain,(
% 55.75/7.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 55.75/7.48    inference(definition_unfolding,[],[f27,f31])).
% 55.75/7.48  
% 55.75/7.48  fof(f13,axiom,(
% 55.75/7.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 55.75/7.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.75/7.48  
% 55.75/7.48  fof(f17,plain,(
% 55.75/7.48    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 55.75/7.48    inference(unused_predicate_definition_removal,[],[f13])).
% 55.75/7.48  
% 55.75/7.48  fof(f21,plain,(
% 55.75/7.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 55.75/7.48    inference(ennf_transformation,[],[f17])).
% 55.75/7.48  
% 55.75/7.48  fof(f37,plain,(
% 55.75/7.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 55.75/7.48    inference(cnf_transformation,[],[f21])).
% 55.75/7.48  
% 55.75/7.48  fof(f48,plain,(
% 55.75/7.48    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 55.75/7.48    inference(definition_unfolding,[],[f37,f43])).
% 55.75/7.48  
% 55.75/7.48  fof(f39,plain,(
% 55.75/7.48    r2_hidden(sK0,sK1)),
% 55.75/7.48    inference(cnf_transformation,[],[f24])).
% 55.75/7.48  
% 55.75/7.48  cnf(c_4,plain,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 55.75/7.48      inference(cnf_transformation,[],[f30]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_7,plain,
% 55.75/7.48      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 55.75/7.48      inference(cnf_transformation,[],[f49]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_341,plain,
% 55.75/7.48      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_1110,plain,
% 55.75/7.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,X2))))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,X2))) ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_4,c_341]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_5,plain,
% 55.75/7.48      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 55.75/7.48      inference(cnf_transformation,[],[f47]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_334,plain,
% 55.75/7.48      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_15189,plain,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X2),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,k5_xboole_0(X0,X1))))) ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_1110,c_334]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_15201,plain,
% 55.75/7.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,X2))))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k3_xboole_0(k5_xboole_0(X1,X2),X0)) ),
% 55.75/7.48      inference(light_normalisation,[status(thm)],[c_15189,c_4]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_8,negated_conjecture,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 55.75/7.48      inference(cnf_transformation,[],[f50]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_460,plain,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_4,c_8]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_137601,plain,
% 55.75/7.48      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))))) != sK1 ),
% 55.75/7.48      inference(demodulation,[status(thm)],[c_15201,c_460]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_0,plain,
% 55.75/7.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 55.75/7.48      inference(cnf_transformation,[],[f25]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_2,plain,
% 55.75/7.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 55.75/7.48      inference(cnf_transformation,[],[f45]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_192,plain,
% 55.75/7.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 55.75/7.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_472,plain,
% 55.75/7.48      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_0,c_192]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_3,plain,
% 55.75/7.48      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 55.75/7.48      inference(cnf_transformation,[],[f46]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_191,plain,
% 55.75/7.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 55.75/7.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 55.75/7.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_719,plain,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1)) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_472,c_191]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_15863,plain,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_0,c_719]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_16414,plain,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_0,c_15863]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_17174,plain,
% 55.75/7.48      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 55.75/7.48      inference(superposition,[status(thm)],[c_16414,c_4]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_137602,plain,
% 55.75/7.48      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != sK1 ),
% 55.75/7.48      inference(demodulation,[status(thm)],[c_137601,c_17174]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_67,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_300,plain,
% 55.75/7.48      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_67]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_537,plain,
% 55.75/7.48      ( X0 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
% 55.75/7.48      | X0 = sK1
% 55.75/7.48      | sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_300]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_3108,plain,
% 55.75/7.48      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
% 55.75/7.48      | k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) = sK1
% 55.75/7.48      | sK1 != k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_537]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_66,plain,( X0 = X0 ),theory(equality) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_1586,plain,
% 55.75/7.48      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_66]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_555,plain,
% 55.75/7.48      ( X0 != X1
% 55.75/7.48      | X0 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
% 55.75/7.48      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != X1 ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_67]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_825,plain,
% 55.75/7.48      ( X0 != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))
% 55.75/7.48      | X0 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
% 55.75/7.48      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_555]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_1585,plain,
% 55.75/7.48      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))
% 55.75/7.48      | k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
% 55.75/7.48      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_825]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_826,plain,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_4]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_295,plain,
% 55.75/7.48      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_67]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_323,plain,
% 55.75/7.48      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_295]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_416,plain,
% 55.75/7.48      ( k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) != sK1
% 55.75/7.48      | sK1 = k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
% 55.75/7.48      | sK1 != sK1 ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_323]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_297,plain,
% 55.75/7.48      ( sK1 = sK1 ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_66]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_1,plain,
% 55.75/7.48      ( ~ r1_tarski(X0,X1)
% 55.75/7.48      | k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X1 ),
% 55.75/7.48      inference(cnf_transformation,[],[f44]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_286,plain,
% 55.75/7.48      ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
% 55.75/7.48      | k5_xboole_0(k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = sK1 ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_1]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_6,plain,
% 55.75/7.48      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 55.75/7.48      inference(cnf_transformation,[],[f48]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_264,plain,
% 55.75/7.48      ( ~ r2_hidden(sK0,sK1)
% 55.75/7.48      | r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 55.75/7.48      inference(instantiation,[status(thm)],[c_6]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(c_9,negated_conjecture,
% 55.75/7.48      ( r2_hidden(sK0,sK1) ),
% 55.75/7.48      inference(cnf_transformation,[],[f39]) ).
% 55.75/7.48  
% 55.75/7.48  cnf(contradiction,plain,
% 55.75/7.48      ( $false ),
% 55.75/7.48      inference(minisat,
% 55.75/7.48                [status(thm)],
% 55.75/7.48                [c_137602,c_3108,c_1586,c_1585,c_826,c_416,c_297,c_286,
% 55.75/7.48                 c_264,c_9]) ).
% 55.75/7.48  
% 55.75/7.48  
% 55.75/7.48  % SZS output end CNFRefutation for theBenchmark.p
% 55.75/7.48  
% 55.75/7.48  ------                               Statistics
% 55.75/7.48  
% 55.75/7.48  ------ Selected
% 55.75/7.48  
% 55.75/7.48  total_time:                             6.997
% 55.75/7.48  
%------------------------------------------------------------------------------
