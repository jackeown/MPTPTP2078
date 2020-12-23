%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:04 EST 2020

% Result     : Theorem 7.62s
% Output     : CNFRefutation 7.62s
% Verified   : 
% Statistics : Number of formulae       :  114 (1521 expanded)
%              Number of clauses        :   54 ( 570 expanded)
%              Number of leaves         :   19 ( 287 expanded)
%              Depth                    :   21
%              Number of atoms          :  162 (2999 expanded)
%              Number of equality atoms :  108 (1614 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).

fof(f51,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f55])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f43,f55])).

fof(f52,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(definition_unfolding,[],[f52,f43,f37,f56,f56])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_476,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_477,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_480,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1191,plain,
    ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = k4_enumset1(X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_477,c_480])).

cnf(c_14079,plain,
    ( k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_476,c_1191])).

cnf(c_8,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_479,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_787,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_479])).

cnf(c_15238,plain,
    ( r1_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14079,c_787])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_478,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15573,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_15238,c_478])).

cnf(c_18751,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_0,c_15573])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_483,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_482,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2984,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_483,c_482])).

cnf(c_1190,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_483,c_480])).

cnf(c_2991,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2984,c_1190])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3157,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2991,c_10])).

cnf(c_3156,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_2991,c_10])).

cnf(c_3545,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2991,c_3156])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3619,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3545,c_7])).

cnf(c_3625,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_3619,c_3156])).

cnf(c_4794,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3157,c_3625])).

cnf(c_4832,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_4794,c_7])).

cnf(c_5256,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4832,c_3625])).

cnf(c_5246,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_10,c_4832])).

cnf(c_6710,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_5256,c_5246])).

cnf(c_24385,plain,
    ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_18751,c_6710])).

cnf(c_25229,plain,
    ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_24385,c_4832])).

cnf(c_15239,plain,
    ( k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_14079,c_0])).

cnf(c_12,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_998,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_12,c_10])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_701,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_0,c_13])).

cnf(c_915,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_10,c_701])).

cnf(c_5837,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(demodulation,[status(thm)],[c_5256,c_915])).

cnf(c_6119,plain,
    ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
    inference(superposition,[status(thm)],[c_5256,c_5837])).

cnf(c_8076,plain,
    ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_998,c_6119])).

cnf(c_15260,plain,
    ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_15239,c_8076])).

cnf(c_995,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_15237,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_14079,c_995])).

cnf(c_5252,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_3625,c_4832])).

cnf(c_15245,plain,
    ( k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_15237,c_5252])).

cnf(c_16299,plain,
    ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != sK1 ),
    inference(light_normalisation,[status(thm)],[c_15260,c_15245])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25229,c_16299])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.62/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.62/1.49  
% 7.62/1.49  ------  iProver source info
% 7.62/1.49  
% 7.62/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.62/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.62/1.49  git: non_committed_changes: false
% 7.62/1.49  git: last_make_outside_of_git: false
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  ------ Parsing...
% 7.62/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.62/1.49  
% 7.62/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.62/1.49  ------ Proving...
% 7.62/1.49  ------ Problem Properties 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  clauses                                 14
% 7.62/1.49  conjectures                             2
% 7.62/1.49  EPR                                     3
% 7.62/1.49  Horn                                    14
% 7.62/1.49  unary                                   8
% 7.62/1.49  binary                                  5
% 7.62/1.49  lits                                    21
% 7.62/1.49  lits eq                                 10
% 7.62/1.49  fd_pure                                 0
% 7.62/1.49  fd_pseudo                               0
% 7.62/1.49  fd_cond                                 0
% 7.62/1.49  fd_pseudo_cond                          1
% 7.62/1.49  AC symbols                              0
% 7.62/1.49  
% 7.62/1.49  ------ Input Options Time Limit: Unbounded
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ 
% 7.62/1.49  Current options:
% 7.62/1.49  ------ 
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  ------ Proving...
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS status Theorem for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  fof(f1,axiom,(
% 7.62/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f31,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f1])).
% 7.62/1.49  
% 7.62/1.49  fof(f18,conjecture,(
% 7.62/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f19,negated_conjecture,(
% 7.62/1.49    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 7.62/1.49    inference(negated_conjecture,[],[f18])).
% 7.62/1.49  
% 7.62/1.49  fof(f25,plain,(
% 7.62/1.49    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 7.62/1.49    inference(ennf_transformation,[],[f19])).
% 7.62/1.49  
% 7.62/1.49  fof(f29,plain,(
% 7.62/1.49    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 7.62/1.49    introduced(choice_axiom,[])).
% 7.62/1.49  
% 7.62/1.49  fof(f30,plain,(
% 7.62/1.49    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 7.62/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).
% 7.62/1.49  
% 7.62/1.49  fof(f51,plain,(
% 7.62/1.49    r2_hidden(sK0,sK1)),
% 7.62/1.49    inference(cnf_transformation,[],[f30])).
% 7.62/1.49  
% 7.62/1.49  fof(f16,axiom,(
% 7.62/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f20,plain,(
% 7.62/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 7.62/1.49    inference(unused_predicate_definition_removal,[],[f16])).
% 7.62/1.49  
% 7.62/1.49  fof(f24,plain,(
% 7.62/1.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 7.62/1.49    inference(ennf_transformation,[],[f20])).
% 7.62/1.49  
% 7.62/1.49  fof(f49,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f24])).
% 7.62/1.49  
% 7.62/1.49  fof(f11,axiom,(
% 7.62/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f44,plain,(
% 7.62/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f11])).
% 7.62/1.49  
% 7.62/1.49  fof(f12,axiom,(
% 7.62/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f45,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f12])).
% 7.62/1.49  
% 7.62/1.49  fof(f13,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f46,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f13])).
% 7.62/1.49  
% 7.62/1.49  fof(f14,axiom,(
% 7.62/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f47,plain,(
% 7.62/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f14])).
% 7.62/1.49  
% 7.62/1.49  fof(f15,axiom,(
% 7.62/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f48,plain,(
% 7.62/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f15])).
% 7.62/1.49  
% 7.62/1.49  fof(f53,plain,(
% 7.62/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f47,f48])).
% 7.62/1.49  
% 7.62/1.49  fof(f54,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f46,f53])).
% 7.62/1.49  
% 7.62/1.49  fof(f55,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f45,f54])).
% 7.62/1.49  
% 7.62/1.49  fof(f56,plain,(
% 7.62/1.49    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f44,f55])).
% 7.62/1.49  
% 7.62/1.49  fof(f61,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f49,f56])).
% 7.62/1.49  
% 7.62/1.49  fof(f5,axiom,(
% 7.62/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f22,plain,(
% 7.62/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.62/1.49    inference(ennf_transformation,[],[f5])).
% 7.62/1.49  
% 7.62/1.49  fof(f38,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f22])).
% 7.62/1.49  
% 7.62/1.49  fof(f7,axiom,(
% 7.62/1.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f40,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f7])).
% 7.62/1.49  
% 7.62/1.49  fof(f4,axiom,(
% 7.62/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f37,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f4])).
% 7.62/1.49  
% 7.62/1.49  fof(f59,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f40,f37])).
% 7.62/1.49  
% 7.62/1.49  fof(f8,axiom,(
% 7.62/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f21,plain,(
% 7.62/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 7.62/1.49    inference(unused_predicate_definition_removal,[],[f8])).
% 7.62/1.49  
% 7.62/1.49  fof(f23,plain,(
% 7.62/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 7.62/1.49    inference(ennf_transformation,[],[f21])).
% 7.62/1.49  
% 7.62/1.49  fof(f41,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f23])).
% 7.62/1.49  
% 7.62/1.49  fof(f60,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f41,f37])).
% 7.62/1.49  
% 7.62/1.49  fof(f2,axiom,(
% 7.62/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f26,plain,(
% 7.62/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.62/1.49    inference(nnf_transformation,[],[f2])).
% 7.62/1.49  
% 7.62/1.49  fof(f27,plain,(
% 7.62/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.62/1.49    inference(flattening,[],[f26])).
% 7.62/1.49  
% 7.62/1.49  fof(f32,plain,(
% 7.62/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.62/1.49    inference(cnf_transformation,[],[f27])).
% 7.62/1.49  
% 7.62/1.49  fof(f65,plain,(
% 7.62/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.62/1.49    inference(equality_resolution,[],[f32])).
% 7.62/1.49  
% 7.62/1.49  fof(f3,axiom,(
% 7.62/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f28,plain,(
% 7.62/1.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.62/1.49    inference(nnf_transformation,[],[f3])).
% 7.62/1.49  
% 7.62/1.49  fof(f36,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f28])).
% 7.62/1.49  
% 7.62/1.49  fof(f57,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 7.62/1.49    inference(definition_unfolding,[],[f36,f37])).
% 7.62/1.49  
% 7.62/1.49  fof(f9,axiom,(
% 7.62/1.49    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f42,plain,(
% 7.62/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f9])).
% 7.62/1.49  
% 7.62/1.49  fof(f6,axiom,(
% 7.62/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f39,plain,(
% 7.62/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.62/1.49    inference(cnf_transformation,[],[f6])).
% 7.62/1.49  
% 7.62/1.49  fof(f17,axiom,(
% 7.62/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f50,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.62/1.49    inference(cnf_transformation,[],[f17])).
% 7.62/1.49  
% 7.62/1.49  fof(f10,axiom,(
% 7.62/1.49    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.62/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.62/1.49  
% 7.62/1.49  fof(f43,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.62/1.49    inference(cnf_transformation,[],[f10])).
% 7.62/1.49  
% 7.62/1.49  fof(f62,plain,(
% 7.62/1.49    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 7.62/1.49    inference(definition_unfolding,[],[f50,f43,f55])).
% 7.62/1.49  
% 7.62/1.49  fof(f52,plain,(
% 7.62/1.49    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 7.62/1.49    inference(cnf_transformation,[],[f30])).
% 7.62/1.49  
% 7.62/1.49  fof(f63,plain,(
% 7.62/1.49    k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1),
% 7.62/1.49    inference(definition_unfolding,[],[f52,f43,f37,f56,f56])).
% 7.62/1.49  
% 7.62/1.49  cnf(c_0,plain,
% 7.62/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14,negated_conjecture,
% 7.62/1.49      ( r2_hidden(sK0,sK1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_476,plain,
% 7.62/1.49      ( r2_hidden(sK0,sK1) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_11,plain,
% 7.62/1.49      ( ~ r2_hidden(X0,X1)
% 7.62/1.49      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_477,plain,
% 7.62/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.62/1.49      | r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_480,plain,
% 7.62/1.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1191,plain,
% 7.62/1.49      ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) = k4_enumset1(X0,X0,X0,X0,X0,X0)
% 7.62/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_477,c_480]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_14079,plain,
% 7.62/1.49      ( k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_476,c_1191]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8,plain,
% 7.62/1.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 7.62/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_479,plain,
% 7.62/1.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_787,plain,
% 7.62/1.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_0,c_479]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15238,plain,
% 7.62/1.49      ( r1_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_14079,c_787]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_9,plain,
% 7.62/1.49      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_478,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 7.62/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15573,plain,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_15238,c_478]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_18751,plain,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_0,c_15573]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3,plain,
% 7.62/1.49      ( r1_tarski(X0,X0) ),
% 7.62/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_483,plain,
% 7.62/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4,plain,
% 7.62/1.49      ( ~ r1_tarski(X0,X1)
% 7.62/1.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_482,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 7.62/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.62/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2984,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_483,c_482]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_1190,plain,
% 7.62/1.49      ( k3_xboole_0(X0,X0) = X0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_483,c_480]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_2991,plain,
% 7.62/1.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_2984,c_1190]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_10,plain,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3157,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2991,c_10]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3156,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2991,c_10]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3545,plain,
% 7.62/1.49      ( k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_2991,c_3156]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_7,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.62/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3619,plain,
% 7.62/1.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_3545,c_7]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_3625,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_3619,c_3156]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4794,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3157,c_3625]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_4832,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_4794,c_7]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5256,plain,
% 7.62/1.49      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_4832,c_3625]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5246,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_10,c_4832]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6710,plain,
% 7.62/1.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X2)) = k5_xboole_0(X2,X1) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_5256,c_5246]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_24385,plain,
% 7.62/1.49      ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_18751,c_6710]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_25229,plain,
% 7.62/1.49      ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1) = sK1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_24385,c_4832]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15239,plain,
% 7.62/1.49      ( k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_14079,c_0]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_12,plain,
% 7.62/1.49      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.62/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_998,plain,
% 7.62/1.49      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_12,c_10]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_13,negated_conjecture,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 7.62/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_701,plain,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_0,c_13]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_915,plain,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_10,c_701]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5837,plain,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_5256,c_915]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_6119,plain,
% 7.62/1.49      ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),k5_xboole_0(sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))) != sK1 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_5256,c_5837]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_8076,plain,
% 7.62/1.49      ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_998,c_6119]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15260,plain,
% 7.62/1.49      ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_15239,c_8076]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_995,plain,
% 7.62/1.49      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15237,plain,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_14079,c_995]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_5252,plain,
% 7.62/1.49      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 7.62/1.49      inference(superposition,[status(thm)],[c_3625,c_4832]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_15245,plain,
% 7.62/1.49      ( k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = sK1 ),
% 7.62/1.49      inference(demodulation,[status(thm)],[c_15237,c_5252]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(c_16299,plain,
% 7.62/1.49      ( k5_xboole_0(k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))),sK1) != sK1 ),
% 7.62/1.49      inference(light_normalisation,[status(thm)],[c_15260,c_15245]) ).
% 7.62/1.49  
% 7.62/1.49  cnf(contradiction,plain,
% 7.62/1.49      ( $false ),
% 7.62/1.49      inference(minisat,[status(thm)],[c_25229,c_16299]) ).
% 7.62/1.49  
% 7.62/1.49  
% 7.62/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.62/1.49  
% 7.62/1.49  ------                               Statistics
% 7.62/1.49  
% 7.62/1.49  ------ Selected
% 7.62/1.49  
% 7.62/1.49  total_time:                             0.729
% 7.62/1.49  
%------------------------------------------------------------------------------
