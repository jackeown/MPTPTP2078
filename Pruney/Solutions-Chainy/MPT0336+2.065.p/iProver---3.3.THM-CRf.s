%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:44 EST 2020

% Result     : Theorem 31.89s
% Output     : CNFRefutation 31.89s
% Verified   : 
% Statistics : Number of formulae       :  360 (16619 expanded)
%              Number of clauses        :  300 (6582 expanded)
%              Number of leaves         :   18 (3579 expanded)
%              Depth                    :   40
%              Number of atoms          :  490 (34689 expanded)
%              Number of equality atoms :  335 (12374 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31])).

fof(f55,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f66,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f47,f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f40])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f54,f40,f60])).

fof(f56,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f27])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f49,f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_280,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k3_xboole_0(X1,X0) = X1
    | k3_xboole_0(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_281,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK1,sK2) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_7,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_460,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(sK1,sK2) ),
    inference(theory_normalisation,[status(thm)],[c_281,c_7,c_0])).

cnf(c_13,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_890,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1756,plain,
    ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_890])).

cnf(c_5280,plain,
    ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X1,X2),X0)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1756])).

cnf(c_13539,plain,
    ( r1_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0),sK1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_460,c_5280])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_899,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_14532,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0),sK1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13539,c_899])).

cnf(c_1755,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_460,c_7])).

cnf(c_920,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_2253,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_1755,c_920])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_884,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3017,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_884,c_899])).

cnf(c_13549,plain,
    ( r1_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3017,c_5280])).

cnf(c_14324,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13549,c_899])).

cnf(c_17569,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14324,c_0])).

cnf(c_19494,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK2),sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_17569])).

cnf(c_3371,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3017,c_7])).

cnf(c_3872,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_3371,c_7])).

cnf(c_5683,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_3872])).

cnf(c_21283,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK2),sK3))) = k3_xboole_0(sK3,k3_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_19494,c_5683])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_898,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2101,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_898])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_891,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5131,plain,
    ( r1_xboole_0(X0,sK3) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3017,c_891])).

cnf(c_6025,plain,
    ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2101,c_5131])).

cnf(c_6043,plain,
    ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6025,c_899])).

cnf(c_3018,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2101,c_899])).

cnf(c_5125,plain,
    ( r1_xboole_0(X0,sK2) != iProver_top
    | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3018,c_891])).

cnf(c_11277,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_884,c_5125])).

cnf(c_11301,plain,
    ( k3_xboole_0(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11277,c_899])).

cnf(c_21425,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK2),sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_21283,c_6043,c_11301])).

cnf(c_83235,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK1),sK2),sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2253,c_21425])).

cnf(c_921,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_3863,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,sK2))) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_921,c_3371])).

cnf(c_23295,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_1755,c_3863])).

cnf(c_23452,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_23295,c_460])).

cnf(c_919,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_3377,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,sK2)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3017,c_919])).

cnf(c_4613,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3377,c_921])).

cnf(c_6423,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_6043,c_7])).

cnf(c_6939,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_6423,c_921])).

cnf(c_23453,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_23452,c_4613,c_6939])).

cnf(c_23604,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_23453,c_3377])).

cnf(c_83480,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK1),sK2),sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_83235,c_23604])).

cnf(c_6045,plain,
    ( r1_xboole_0(k1_xboole_0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6025,c_898])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_888,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6464,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6045,c_888])).

cnf(c_6428,plain,
    ( k3_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6043,c_0])).

cnf(c_6466,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6464,c_6428])).

cnf(c_1853,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_460,c_921])).

cnf(c_3375,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3017,c_921])).

cnf(c_3922,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_3375,c_7])).

cnf(c_5791,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_3922])).

cnf(c_21520,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_1853,c_5791])).

cnf(c_21521,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(sK1,sK2),X0))) ),
    inference(superposition,[status(thm)],[c_1755,c_5791])).

cnf(c_21719,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),X0) ),
    inference(demodulation,[status(thm)],[c_21521,c_5791])).

cnf(c_1844,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(sK1,X0)) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_460,c_920])).

cnf(c_2429,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1844,c_920])).

cnf(c_3861,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,sK2)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3371])).

cnf(c_11380,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK3,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11301,c_920])).

cnf(c_12755,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3861,c_11380])).

cnf(c_6442,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6043,c_3375])).

cnf(c_11363,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11301,c_6442])).

cnf(c_11498,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_11363,c_7])).

cnf(c_12806,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_12755,c_11498])).

cnf(c_21720,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_21719,c_2429,c_12806])).

cnf(c_21721,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_21520,c_5791,c_21720])).

cnf(c_6914,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_6423])).

cnf(c_8098,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,sK2)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_6914,c_921])).

cnf(c_21722,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) = k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_21721,c_8098])).

cnf(c_4609,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_3377,c_7])).

cnf(c_10670,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_4609])).

cnf(c_35520,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_460,c_10670])).

cnf(c_35768,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_35520,c_3861])).

cnf(c_3926,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3375,c_921])).

cnf(c_29110,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_7,c_3926])).

cnf(c_76468,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k1_xboole_0)) = k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))) ),
    inference(superposition,[status(thm)],[c_35768,c_29110])).

cnf(c_76658,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k1_xboole_0)) = k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_76468,c_29110])).

cnf(c_76659,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k1_xboole_0)) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_76658,c_11363])).

cnf(c_17532,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK3,k3_xboole_0(sK2,X0))),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_14324])).

cnf(c_17692,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17532,c_3375])).

cnf(c_17794,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17692,c_0])).

cnf(c_18968,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_17794,c_7])).

cnf(c_50935,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_18968,c_920])).

cnf(c_50971,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k1_xboole_0)),X0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_18968,c_1844])).

cnf(c_11370,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_11301,c_7])).

cnf(c_3877,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(sK3,X1)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3371,c_920])).

cnf(c_28152,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k3_xboole_0(sK2,X1),k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_11370,c_3877])).

cnf(c_12063,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_11498,c_920])).

cnf(c_28275,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_28152,c_12063])).

cnf(c_51270,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k1_xboole_0)),X0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_50971,c_28275])).

cnf(c_51286,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_50935,c_51270])).

cnf(c_6432,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6043,c_921])).

cnf(c_51287,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_51286,c_6432])).

cnf(c_68075,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[status(thm)],[c_35768,c_920])).

cnf(c_2249,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0),k3_xboole_0(sK1,X1)) = k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_1755,c_920])).

cnf(c_3379,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,sK3)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3017,c_921])).

cnf(c_4663,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(X0,sK3),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3379,c_921])).

cnf(c_76018,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0)) = k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),sK3))) ),
    inference(superposition,[status(thm)],[c_2249,c_4663])).

cnf(c_21566,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0),X0) = k3_xboole_0(sK3,k3_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_17692,c_5791])).

cnf(c_21657,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_21566,c_6043,c_11301])).

cnf(c_22978,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)),k1_xboole_0),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_21657])).

cnf(c_1854,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(X0,sK1)) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_460,c_921])).

cnf(c_27310,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)),k1_xboole_0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22978,c_1854])).

cnf(c_25101,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)),k1_xboole_0),k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_23604,c_21657])).

cnf(c_27395,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_27310,c_25101])).

cnf(c_3376,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3017,c_920])).

cnf(c_4493,plain,
    ( k3_xboole_0(k3_xboole_0(sK3,X0),k3_xboole_0(sK2,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3376,c_920])).

cnf(c_32341,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK2),k1_xboole_0)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_23453,c_4493])).

cnf(c_23551,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK2))) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_7,c_23453])).

cnf(c_32342,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK2)),k1_xboole_0)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_23551,c_4493])).

cnf(c_30815,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK2)),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[status(thm)],[c_23551,c_11380])).

cnf(c_5678,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_3872])).

cnf(c_15352,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_5678,c_11380])).

cnf(c_4480,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(X1,sK3))) = k3_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_920,c_3376])).

cnf(c_3658,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK3,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3018,c_7])).

cnf(c_4126,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,sK3)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_3658])).

cnf(c_4350,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(X1,sK3))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_4126,c_919])).

cnf(c_4508,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4480,c_4350])).

cnf(c_12062,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_11498,c_921])).

cnf(c_15374,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k1_xboole_0) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(demodulation,[status(thm)],[c_15352,c_4508,c_12062])).

cnf(c_30844,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK2)),k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_30815,c_11498,c_15374])).

cnf(c_32487,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_32342,c_30844])).

cnf(c_32488,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK2),k1_xboole_0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(demodulation,[status(thm)],[c_32341,c_32487])).

cnf(c_23602,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK2),k1_xboole_0) = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[status(thm)],[c_23453,c_3376])).

cnf(c_4293,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_3861,c_7])).

cnf(c_12761,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_4293,c_11380])).

cnf(c_12802,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_12761,c_12062])).

cnf(c_23611,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK2),k1_xboole_0) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_23602,c_6432,c_12802])).

cnf(c_32489,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) = k3_xboole_0(X0,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_32488,c_23611])).

cnf(c_4498,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(sK3,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3376,c_919])).

cnf(c_32645,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK2)),k1_xboole_0)) = k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1))) ),
    inference(superposition,[status(thm)],[c_23551,c_4498])).

cnf(c_32769,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_32645,c_30844])).

cnf(c_2235,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_0,c_1755])).

cnf(c_35327,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_3371,c_2235])).

cnf(c_1765,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_460,c_919])).

cnf(c_3884,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3371,c_1765])).

cnf(c_3885,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3884,c_3377])).

cnf(c_35413,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_35327,c_3885])).

cnf(c_76039,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_76018,c_27395,c_32489,c_32769,c_35413])).

cnf(c_76660,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_76659,c_51287,c_68075,c_76039])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_900,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3025,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_900])).

cnf(c_3870,plain,
    ( k3_xboole_0(k1_xboole_0,X0) != k1_xboole_0
    | r1_xboole_0(k3_xboole_0(sK2,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3371,c_3025])).

cnf(c_24,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10219,plain,
    ( ~ r1_xboole_0(sK3,X0)
    | r1_xboole_0(sK3,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_30252,plain,
    ( r1_xboole_0(sK3,k3_xboole_0(sK2,X0))
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_10219])).

cnf(c_30253,plain,
    ( r1_xboole_0(sK3,k3_xboole_0(sK2,X0)) = iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30252])).

cnf(c_9132,plain,
    ( r1_xboole_0(X0,sK3)
    | ~ r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_70905,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,X0),sK3)
    | ~ r1_xboole_0(sK3,k3_xboole_0(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_9132])).

cnf(c_70935,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,X0),sK3) = iProver_top
    | r1_xboole_0(sK3,k3_xboole_0(sK2,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70905])).

cnf(c_80398,plain,
    ( r1_xboole_0(k3_xboole_0(sK2,X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3870,c_24,c_30253,c_70935])).

cnf(c_80404,plain,
    ( r1_xboole_0(k3_xboole_0(X0,sK2),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_80398])).

cnf(c_81322,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_80404,c_899])).

cnf(c_83481,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_83480,c_6466,c_21722,c_76660,c_81322])).

cnf(c_6928,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_6423,c_7])).

cnf(c_83247,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)),X0) = k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),X0)) ),
    inference(superposition,[status(thm)],[c_2253,c_6928])).

cnf(c_83463,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),X0)) = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),X0) ),
    inference(demodulation,[status(thm)],[c_83247,c_2253])).

cnf(c_4140,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(sK3,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_3658,c_7])).

cnf(c_23598,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)),X0) = k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0)) ),
    inference(superposition,[status(thm)],[c_23453,c_4140])).

cnf(c_23603,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[status(thm)],[c_23453,c_3658])).

cnf(c_6723,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_6428,c_7])).

cnf(c_7154,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_6723,c_7])).

cnf(c_22183,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[status(thm)],[c_0,c_7154])).

cnf(c_23610,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_23603,c_6432,c_22183])).

cnf(c_23614,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0)) = k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) ),
    inference(demodulation,[status(thm)],[c_23598,c_23610])).

cnf(c_23615,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) ),
    inference(light_normalisation,[status(thm)],[c_23614,c_21722])).

cnf(c_83464,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) = k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_83463,c_21722,c_23604,c_23615])).

cnf(c_2252,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X1))) = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
    inference(superposition,[status(thm)],[c_1755,c_919])).

cnf(c_80706,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0),X0)) = k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_10670,c_2252])).

cnf(c_3876,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3371,c_921])).

cnf(c_80714,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_3876,c_2252])).

cnf(c_21561,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),k1_xboole_0),X0) = k3_xboole_0(sK3,k3_xboole_0(sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_14324,c_5791])).

cnf(c_21661,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),k1_xboole_0),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_21561,c_6043,c_11301])).

cnf(c_80740,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)),sK3)),k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_21661,c_2252])).

cnf(c_25083,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[status(thm)],[c_23604,c_920])).

cnf(c_4659,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(X0,sK3),X1)) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_3379,c_7])).

cnf(c_13383,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(sK3,X1))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_4659])).

cnf(c_40809,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK3,X2)))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_7,c_13383])).

cnf(c_5786,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(k3_xboole_0(X1,k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_0,c_3922])).

cnf(c_17243,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_919,c_5786])).

cnf(c_15305,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)),X0) ),
    inference(superposition,[status(thm)],[c_919,c_5678])).

cnf(c_15343,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X2),X1)) ),
    inference(superposition,[status(thm)],[c_5678,c_919])).

cnf(c_15308,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,X1)),X0) ),
    inference(superposition,[status(thm)],[c_921,c_5678])).

cnf(c_5793,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(X2,k1_xboole_0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_920,c_3922])).

cnf(c_15390,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),X2) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_15308,c_5793])).

cnf(c_15395,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(X1,k1_xboole_0),k3_xboole_0(X2,X0)) ),
    inference(demodulation,[status(thm)],[c_15305,c_15343,c_15390])).

cnf(c_17336,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0),X2) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_17243,c_15395])).

cnf(c_17337,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)),X2) ),
    inference(demodulation,[status(thm)],[c_17336,c_4508])).

cnf(c_32680,plain,
    ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK3,X2)))) = k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_4498,c_919])).

cnf(c_41113,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_40809,c_4508,c_17337,c_32680])).

cnf(c_80443,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,X0),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_80398,c_899])).

cnf(c_80940,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_80740,c_6466,c_11363,c_25083,c_41113,c_80443])).

cnf(c_3882,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(X1,sK3)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3371,c_921])).

cnf(c_80761,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X1,sK3))) ),
    inference(superposition,[status(thm)],[c_3882,c_2252])).

cnf(c_2241,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X1))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_919,c_1755])).

cnf(c_40552,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,k3_xboole_0(X1,sK3))) ),
    inference(superposition,[status(thm)],[c_3882,c_2241])).

cnf(c_4672,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK3),k3_xboole_0(X1,sK2)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3379,c_921])).

cnf(c_35219,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X1,k3_xboole_0(X2,sK3))) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_4672,c_921])).

cnf(c_2240,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
    inference(superposition,[status(thm)],[c_7,c_1755])).

cnf(c_3880,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_3371,c_919])).

cnf(c_39101,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) = k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_2240,c_3880])).

cnf(c_3868,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_921,c_3371])).

cnf(c_2237,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_921,c_1755])).

cnf(c_37025,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_3868,c_2237])).

cnf(c_3927,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(sK3,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3375,c_920])).

cnf(c_29802,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_3927,c_1755])).

cnf(c_17575,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14324,c_921])).

cnf(c_17600,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,sK1),sK3)),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14324,c_1854])).

cnf(c_11379,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11301,c_921])).

cnf(c_12607,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,X0),k1_xboole_0) = k3_xboole_0(sK3,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_6723,c_11379])).

cnf(c_12660,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,X0),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_12607,c_11379])).

cnf(c_17677,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,sK1),sK3)),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_17600,c_12660])).

cnf(c_17679,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_17575,c_17677])).

cnf(c_17680,plain,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17679,c_6043])).

cnf(c_29832,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,X0)) = k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_29802,c_17680])).

cnf(c_37237,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) = k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_37025,c_29832])).

cnf(c_39106,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_39101,c_37237])).

cnf(c_3867,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,sK2))) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_920,c_3371])).

cnf(c_25899,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_3867])).

cnf(c_39107,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_39106,c_25899])).

cnf(c_40658,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) ),
    inference(demodulation,[status(thm)],[c_40552,c_35219,c_39107])).

cnf(c_80926,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X1,sK3))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) ),
    inference(light_normalisation,[status(thm)],[c_80761,c_40658])).

cnf(c_28756,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_3882,c_1755])).

cnf(c_28220,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_3877,c_1755])).

cnf(c_4614,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(sK3,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3377,c_920])).

cnf(c_28245,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(X0,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_28220,c_4614])).

cnf(c_28784,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,sK3)) = k3_xboole_0(X0,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_28756,c_28245])).

cnf(c_80927,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_80926,c_28784])).

cnf(c_80928,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,sK1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) ),
    inference(demodulation,[status(thm)],[c_80927,c_32489])).

cnf(c_80942,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) = k3_xboole_0(X0,k3_xboole_0(sK1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_80940,c_80928])).

cnf(c_80943,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_80942,c_32489])).

cnf(c_18948,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_17794])).

cnf(c_19210,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)),X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_18948,c_7])).

cnf(c_80768,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))),X1))) = k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) ),
    inference(superposition,[status(thm)],[c_19210,c_2252])).

cnf(c_17788,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(X0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_17692,c_7])).

cnf(c_47083,plain,
    ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k1_xboole_0)),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_460,c_17788])).

cnf(c_47464,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(k1_xboole_0,sK2) ),
    inference(demodulation,[status(thm)],[c_47083,c_17788])).

cnf(c_47465,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_47464,c_6428])).

cnf(c_80917,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_80768,c_6466,c_47465])).

cnf(c_19223,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18948,c_7])).

cnf(c_2243,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X1))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_921,c_1755])).

cnf(c_54640,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)))),X1)) = k3_xboole_0(sK1,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_19223,c_2243])).

cnf(c_53925,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)),X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) ),
    inference(superposition,[status(thm)],[c_19210,c_2241])).

cnf(c_50891,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_23604,c_18968])).

cnf(c_54155,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_53925,c_50891])).

cnf(c_54953,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_54640,c_18948,c_54155])).

cnf(c_25070,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_23604,c_7])).

cnf(c_25148,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_25070,c_21722])).

cnf(c_54954,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_54953,c_25148,c_39107])).

cnf(c_80918,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) ),
    inference(demodulation,[status(thm)],[c_80917,c_54954])).

cnf(c_80944,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(demodulation,[status(thm)],[c_80943,c_80918])).

cnf(c_80950,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_80944,c_80940])).

cnf(c_80984,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_80714,c_80950])).

cnf(c_80990,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0),X0)) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_80706,c_80984])).

cnf(c_80991,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_80990,c_27395])).

cnf(c_83465,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_83464,c_80991])).

cnf(c_83482,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_83481,c_83465])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_887,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_883,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_897,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11751,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_883,c_897])).

cnf(c_143816,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))) = X0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_887,c_11751])).

cnf(c_146730,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = sK2 ),
    inference(superposition,[status(thm)],[c_2101,c_143816])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_889,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_146800,plain,
    ( r1_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_146730,c_889])).

cnf(c_147078,plain,
    ( k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_146800,c_899])).

cnf(c_167841,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,sK1)),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14532,c_14532,c_83482,c_147078])).

cnf(c_81325,plain,
    ( r1_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_80404,c_5131])).

cnf(c_82573,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0)) = k3_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_81325,c_888])).

cnf(c_82575,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,sK2) ),
    inference(light_normalisation,[status(thm)],[c_82573,c_12806])).

cnf(c_167842,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_167841,c_82575])).

cnf(c_167976,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_167842,c_7])).

cnf(c_168534,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_167976,c_460])).

cnf(c_2055,plain,
    ( r1_xboole_0(X0,sK2)
    | k3_xboole_0(X0,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_85170,plain,
    ( r1_xboole_0(sK1,sK2)
    | k3_xboole_0(sK1,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2055])).

cnf(c_1795,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1183,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_997,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_942,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_168534,c_85170,c_1795,c_1183,c_997,c_942,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 17:26:15 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 31.89/4.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.89/4.51  
% 31.89/4.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.89/4.51  
% 31.89/4.51  ------  iProver source info
% 31.89/4.51  
% 31.89/4.51  git: date: 2020-06-30 10:37:57 +0100
% 31.89/4.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.89/4.51  git: non_committed_changes: false
% 31.89/4.51  git: last_make_outside_of_git: false
% 31.89/4.51  
% 31.89/4.51  ------ 
% 31.89/4.51  
% 31.89/4.51  ------ Input Options
% 31.89/4.51  
% 31.89/4.51  --out_options                           all
% 31.89/4.51  --tptp_safe_out                         true
% 31.89/4.51  --problem_path                          ""
% 31.89/4.51  --include_path                          ""
% 31.89/4.51  --clausifier                            res/vclausify_rel
% 31.89/4.51  --clausifier_options                    ""
% 31.89/4.51  --stdin                                 false
% 31.89/4.51  --stats_out                             all
% 31.89/4.51  
% 31.89/4.51  ------ General Options
% 31.89/4.51  
% 31.89/4.51  --fof                                   false
% 31.89/4.51  --time_out_real                         305.
% 31.89/4.51  --time_out_virtual                      -1.
% 31.89/4.51  --symbol_type_check                     false
% 31.89/4.51  --clausify_out                          false
% 31.89/4.51  --sig_cnt_out                           false
% 31.89/4.51  --trig_cnt_out                          false
% 31.89/4.51  --trig_cnt_out_tolerance                1.
% 31.89/4.51  --trig_cnt_out_sk_spl                   false
% 31.89/4.51  --abstr_cl_out                          false
% 31.89/4.51  
% 31.89/4.51  ------ Global Options
% 31.89/4.51  
% 31.89/4.51  --schedule                              default
% 31.89/4.51  --add_important_lit                     false
% 31.89/4.51  --prop_solver_per_cl                    1000
% 31.89/4.51  --min_unsat_core                        false
% 31.89/4.51  --soft_assumptions                      false
% 31.89/4.51  --soft_lemma_size                       3
% 31.89/4.51  --prop_impl_unit_size                   0
% 31.89/4.51  --prop_impl_unit                        []
% 31.89/4.51  --share_sel_clauses                     true
% 31.89/4.51  --reset_solvers                         false
% 31.89/4.51  --bc_imp_inh                            [conj_cone]
% 31.89/4.51  --conj_cone_tolerance                   3.
% 31.89/4.51  --extra_neg_conj                        none
% 31.89/4.51  --large_theory_mode                     true
% 31.89/4.51  --prolific_symb_bound                   200
% 31.89/4.51  --lt_threshold                          2000
% 31.89/4.51  --clause_weak_htbl                      true
% 31.89/4.51  --gc_record_bc_elim                     false
% 31.89/4.51  
% 31.89/4.51  ------ Preprocessing Options
% 31.89/4.51  
% 31.89/4.51  --preprocessing_flag                    true
% 31.89/4.51  --time_out_prep_mult                    0.1
% 31.89/4.51  --splitting_mode                        input
% 31.89/4.51  --splitting_grd                         true
% 31.89/4.51  --splitting_cvd                         false
% 31.89/4.51  --splitting_cvd_svl                     false
% 31.89/4.51  --splitting_nvd                         32
% 31.89/4.51  --sub_typing                            true
% 31.89/4.51  --prep_gs_sim                           true
% 31.89/4.51  --prep_unflatten                        true
% 31.89/4.51  --prep_res_sim                          true
% 31.89/4.51  --prep_upred                            true
% 31.89/4.51  --prep_sem_filter                       exhaustive
% 31.89/4.51  --prep_sem_filter_out                   false
% 31.89/4.51  --pred_elim                             true
% 31.89/4.51  --res_sim_input                         true
% 31.89/4.51  --eq_ax_congr_red                       true
% 31.89/4.51  --pure_diseq_elim                       true
% 31.89/4.51  --brand_transform                       false
% 31.89/4.51  --non_eq_to_eq                          false
% 31.89/4.51  --prep_def_merge                        true
% 31.89/4.51  --prep_def_merge_prop_impl              false
% 31.89/4.51  --prep_def_merge_mbd                    true
% 31.89/4.51  --prep_def_merge_tr_red                 false
% 31.89/4.51  --prep_def_merge_tr_cl                  false
% 31.89/4.51  --smt_preprocessing                     true
% 31.89/4.51  --smt_ac_axioms                         fast
% 31.89/4.51  --preprocessed_out                      false
% 31.89/4.51  --preprocessed_stats                    false
% 31.89/4.51  
% 31.89/4.51  ------ Abstraction refinement Options
% 31.89/4.51  
% 31.89/4.51  --abstr_ref                             []
% 31.89/4.51  --abstr_ref_prep                        false
% 31.89/4.51  --abstr_ref_until_sat                   false
% 31.89/4.51  --abstr_ref_sig_restrict                funpre
% 31.89/4.51  --abstr_ref_af_restrict_to_split_sk     false
% 31.89/4.51  --abstr_ref_under                       []
% 31.89/4.51  
% 31.89/4.51  ------ SAT Options
% 31.89/4.51  
% 31.89/4.51  --sat_mode                              false
% 31.89/4.51  --sat_fm_restart_options                ""
% 31.89/4.51  --sat_gr_def                            false
% 31.89/4.51  --sat_epr_types                         true
% 31.89/4.51  --sat_non_cyclic_types                  false
% 31.89/4.51  --sat_finite_models                     false
% 31.89/4.51  --sat_fm_lemmas                         false
% 31.89/4.51  --sat_fm_prep                           false
% 31.89/4.51  --sat_fm_uc_incr                        true
% 31.89/4.51  --sat_out_model                         small
% 31.89/4.51  --sat_out_clauses                       false
% 31.89/4.51  
% 31.89/4.51  ------ QBF Options
% 31.89/4.51  
% 31.89/4.51  --qbf_mode                              false
% 31.89/4.51  --qbf_elim_univ                         false
% 31.89/4.51  --qbf_dom_inst                          none
% 31.89/4.51  --qbf_dom_pre_inst                      false
% 31.89/4.51  --qbf_sk_in                             false
% 31.89/4.51  --qbf_pred_elim                         true
% 31.89/4.51  --qbf_split                             512
% 31.89/4.51  
% 31.89/4.51  ------ BMC1 Options
% 31.89/4.51  
% 31.89/4.51  --bmc1_incremental                      false
% 31.89/4.51  --bmc1_axioms                           reachable_all
% 31.89/4.51  --bmc1_min_bound                        0
% 31.89/4.51  --bmc1_max_bound                        -1
% 31.89/4.51  --bmc1_max_bound_default                -1
% 31.89/4.51  --bmc1_symbol_reachability              true
% 31.89/4.51  --bmc1_property_lemmas                  false
% 31.89/4.51  --bmc1_k_induction                      false
% 31.89/4.51  --bmc1_non_equiv_states                 false
% 31.89/4.51  --bmc1_deadlock                         false
% 31.89/4.51  --bmc1_ucm                              false
% 31.89/4.51  --bmc1_add_unsat_core                   none
% 31.89/4.51  --bmc1_unsat_core_children              false
% 31.89/4.51  --bmc1_unsat_core_extrapolate_axioms    false
% 31.89/4.51  --bmc1_out_stat                         full
% 31.89/4.51  --bmc1_ground_init                      false
% 31.89/4.51  --bmc1_pre_inst_next_state              false
% 31.89/4.51  --bmc1_pre_inst_state                   false
% 31.89/4.51  --bmc1_pre_inst_reach_state             false
% 31.89/4.51  --bmc1_out_unsat_core                   false
% 31.89/4.51  --bmc1_aig_witness_out                  false
% 31.89/4.51  --bmc1_verbose                          false
% 31.89/4.51  --bmc1_dump_clauses_tptp                false
% 31.89/4.51  --bmc1_dump_unsat_core_tptp             false
% 31.89/4.51  --bmc1_dump_file                        -
% 31.89/4.51  --bmc1_ucm_expand_uc_limit              128
% 31.89/4.51  --bmc1_ucm_n_expand_iterations          6
% 31.89/4.51  --bmc1_ucm_extend_mode                  1
% 31.89/4.51  --bmc1_ucm_init_mode                    2
% 31.89/4.51  --bmc1_ucm_cone_mode                    none
% 31.89/4.51  --bmc1_ucm_reduced_relation_type        0
% 31.89/4.51  --bmc1_ucm_relax_model                  4
% 31.89/4.51  --bmc1_ucm_full_tr_after_sat            true
% 31.89/4.51  --bmc1_ucm_expand_neg_assumptions       false
% 31.89/4.51  --bmc1_ucm_layered_model                none
% 31.89/4.51  --bmc1_ucm_max_lemma_size               10
% 31.89/4.51  
% 31.89/4.51  ------ AIG Options
% 31.89/4.51  
% 31.89/4.51  --aig_mode                              false
% 31.89/4.51  
% 31.89/4.51  ------ Instantiation Options
% 31.89/4.51  
% 31.89/4.51  --instantiation_flag                    true
% 31.89/4.51  --inst_sos_flag                         true
% 31.89/4.51  --inst_sos_phase                        true
% 31.89/4.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.89/4.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.89/4.51  --inst_lit_sel_side                     num_symb
% 31.89/4.51  --inst_solver_per_active                1400
% 31.89/4.51  --inst_solver_calls_frac                1.
% 31.89/4.51  --inst_passive_queue_type               priority_queues
% 31.89/4.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.89/4.51  --inst_passive_queues_freq              [25;2]
% 31.89/4.51  --inst_dismatching                      true
% 31.89/4.51  --inst_eager_unprocessed_to_passive     true
% 31.89/4.51  --inst_prop_sim_given                   true
% 31.89/4.51  --inst_prop_sim_new                     false
% 31.89/4.51  --inst_subs_new                         false
% 31.89/4.51  --inst_eq_res_simp                      false
% 31.89/4.51  --inst_subs_given                       false
% 31.89/4.51  --inst_orphan_elimination               true
% 31.89/4.51  --inst_learning_loop_flag               true
% 31.89/4.51  --inst_learning_start                   3000
% 31.89/4.51  --inst_learning_factor                  2
% 31.89/4.51  --inst_start_prop_sim_after_learn       3
% 31.89/4.51  --inst_sel_renew                        solver
% 31.89/4.51  --inst_lit_activity_flag                true
% 31.89/4.51  --inst_restr_to_given                   false
% 31.89/4.51  --inst_activity_threshold               500
% 31.89/4.51  --inst_out_proof                        true
% 31.89/4.51  
% 31.89/4.51  ------ Resolution Options
% 31.89/4.51  
% 31.89/4.51  --resolution_flag                       true
% 31.89/4.51  --res_lit_sel                           adaptive
% 31.89/4.51  --res_lit_sel_side                      none
% 31.89/4.51  --res_ordering                          kbo
% 31.89/4.51  --res_to_prop_solver                    active
% 31.89/4.51  --res_prop_simpl_new                    false
% 31.89/4.51  --res_prop_simpl_given                  true
% 31.89/4.51  --res_passive_queue_type                priority_queues
% 31.89/4.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.89/4.51  --res_passive_queues_freq               [15;5]
% 31.89/4.51  --res_forward_subs                      full
% 31.89/4.51  --res_backward_subs                     full
% 31.89/4.51  --res_forward_subs_resolution           true
% 31.89/4.51  --res_backward_subs_resolution          true
% 31.89/4.51  --res_orphan_elimination                true
% 31.89/4.51  --res_time_limit                        2.
% 31.89/4.51  --res_out_proof                         true
% 31.89/4.51  
% 31.89/4.51  ------ Superposition Options
% 31.89/4.51  
% 31.89/4.51  --superposition_flag                    true
% 31.89/4.51  --sup_passive_queue_type                priority_queues
% 31.89/4.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.89/4.51  --sup_passive_queues_freq               [8;1;4]
% 31.89/4.51  --demod_completeness_check              fast
% 31.89/4.51  --demod_use_ground                      true
% 31.89/4.51  --sup_to_prop_solver                    passive
% 31.89/4.51  --sup_prop_simpl_new                    true
% 31.89/4.51  --sup_prop_simpl_given                  true
% 31.89/4.51  --sup_fun_splitting                     true
% 31.89/4.51  --sup_smt_interval                      50000
% 31.89/4.51  
% 31.89/4.51  ------ Superposition Simplification Setup
% 31.89/4.51  
% 31.89/4.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.89/4.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.89/4.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.89/4.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.89/4.51  --sup_full_triv                         [TrivRules;PropSubs]
% 31.89/4.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.89/4.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.89/4.51  --sup_immed_triv                        [TrivRules]
% 31.89/4.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.89/4.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.89/4.51  --sup_immed_bw_main                     []
% 31.89/4.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.89/4.51  --sup_input_triv                        [Unflattening;TrivRules]
% 31.89/4.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.89/4.51  --sup_input_bw                          []
% 31.89/4.51  
% 31.89/4.51  ------ Combination Options
% 31.89/4.51  
% 31.89/4.51  --comb_res_mult                         3
% 31.89/4.51  --comb_sup_mult                         2
% 31.89/4.51  --comb_inst_mult                        10
% 31.89/4.51  
% 31.89/4.51  ------ Debug Options
% 31.89/4.51  
% 31.89/4.51  --dbg_backtrace                         false
% 31.89/4.51  --dbg_dump_prop_clauses                 false
% 31.89/4.51  --dbg_dump_prop_clauses_file            -
% 31.89/4.51  --dbg_out_stat                          false
% 31.89/4.51  ------ Parsing...
% 31.89/4.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.89/4.51  
% 31.89/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.89/4.51  
% 31.89/4.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.89/4.51  
% 31.89/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.89/4.51  ------ Proving...
% 31.89/4.51  ------ Problem Properties 
% 31.89/4.51  
% 31.89/4.51  
% 31.89/4.51  clauses                                 21
% 31.89/4.51  conjectures                             3
% 31.89/4.51  EPR                                     4
% 31.89/4.51  Horn                                    18
% 31.89/4.51  unary                                   7
% 31.89/4.51  binary                                  12
% 31.89/4.51  lits                                    37
% 31.89/4.51  lits eq                                 9
% 31.89/4.51  fd_pure                                 0
% 31.89/4.51  fd_pseudo                               0
% 31.89/4.51  fd_cond                                 0
% 31.89/4.51  fd_pseudo_cond                          0
% 31.89/4.51  AC symbols                              1
% 31.89/4.51  
% 31.89/4.51  ------ Schedule dynamic 5 is on 
% 31.89/4.51  
% 31.89/4.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.89/4.51  
% 31.89/4.51  
% 31.89/4.51  ------ 
% 31.89/4.51  Current options:
% 31.89/4.51  ------ 
% 31.89/4.51  
% 31.89/4.51  ------ Input Options
% 31.89/4.51  
% 31.89/4.51  --out_options                           all
% 31.89/4.51  --tptp_safe_out                         true
% 31.89/4.51  --problem_path                          ""
% 31.89/4.51  --include_path                          ""
% 31.89/4.51  --clausifier                            res/vclausify_rel
% 31.89/4.51  --clausifier_options                    ""
% 31.89/4.51  --stdin                                 false
% 31.89/4.51  --stats_out                             all
% 31.89/4.51  
% 31.89/4.51  ------ General Options
% 31.89/4.51  
% 31.89/4.51  --fof                                   false
% 31.89/4.51  --time_out_real                         305.
% 31.89/4.51  --time_out_virtual                      -1.
% 31.89/4.51  --symbol_type_check                     false
% 31.89/4.51  --clausify_out                          false
% 31.89/4.51  --sig_cnt_out                           false
% 31.89/4.51  --trig_cnt_out                          false
% 31.89/4.51  --trig_cnt_out_tolerance                1.
% 31.89/4.51  --trig_cnt_out_sk_spl                   false
% 31.89/4.51  --abstr_cl_out                          false
% 31.89/4.51  
% 31.89/4.51  ------ Global Options
% 31.89/4.51  
% 31.89/4.51  --schedule                              default
% 31.89/4.51  --add_important_lit                     false
% 31.89/4.51  --prop_solver_per_cl                    1000
% 31.89/4.51  --min_unsat_core                        false
% 31.89/4.51  --soft_assumptions                      false
% 31.89/4.51  --soft_lemma_size                       3
% 31.89/4.51  --prop_impl_unit_size                   0
% 31.89/4.51  --prop_impl_unit                        []
% 31.89/4.51  --share_sel_clauses                     true
% 31.89/4.51  --reset_solvers                         false
% 31.89/4.51  --bc_imp_inh                            [conj_cone]
% 31.89/4.51  --conj_cone_tolerance                   3.
% 31.89/4.51  --extra_neg_conj                        none
% 31.89/4.51  --large_theory_mode                     true
% 31.89/4.51  --prolific_symb_bound                   200
% 31.89/4.51  --lt_threshold                          2000
% 31.89/4.51  --clause_weak_htbl                      true
% 31.89/4.51  --gc_record_bc_elim                     false
% 31.89/4.51  
% 31.89/4.51  ------ Preprocessing Options
% 31.89/4.51  
% 31.89/4.51  --preprocessing_flag                    true
% 31.89/4.51  --time_out_prep_mult                    0.1
% 31.89/4.51  --splitting_mode                        input
% 31.89/4.51  --splitting_grd                         true
% 31.89/4.51  --splitting_cvd                         false
% 31.89/4.51  --splitting_cvd_svl                     false
% 31.89/4.51  --splitting_nvd                         32
% 31.89/4.51  --sub_typing                            true
% 31.89/4.51  --prep_gs_sim                           true
% 31.89/4.51  --prep_unflatten                        true
% 31.89/4.51  --prep_res_sim                          true
% 31.89/4.51  --prep_upred                            true
% 31.89/4.51  --prep_sem_filter                       exhaustive
% 31.89/4.51  --prep_sem_filter_out                   false
% 31.89/4.51  --pred_elim                             true
% 31.89/4.51  --res_sim_input                         true
% 31.89/4.51  --eq_ax_congr_red                       true
% 31.89/4.51  --pure_diseq_elim                       true
% 31.89/4.51  --brand_transform                       false
% 31.89/4.51  --non_eq_to_eq                          false
% 31.89/4.51  --prep_def_merge                        true
% 31.89/4.51  --prep_def_merge_prop_impl              false
% 31.89/4.51  --prep_def_merge_mbd                    true
% 31.89/4.51  --prep_def_merge_tr_red                 false
% 31.89/4.51  --prep_def_merge_tr_cl                  false
% 31.89/4.51  --smt_preprocessing                     true
% 31.89/4.51  --smt_ac_axioms                         fast
% 31.89/4.51  --preprocessed_out                      false
% 31.89/4.51  --preprocessed_stats                    false
% 31.89/4.51  
% 31.89/4.51  ------ Abstraction refinement Options
% 31.89/4.51  
% 31.89/4.51  --abstr_ref                             []
% 31.89/4.51  --abstr_ref_prep                        false
% 31.89/4.51  --abstr_ref_until_sat                   false
% 31.89/4.51  --abstr_ref_sig_restrict                funpre
% 31.89/4.51  --abstr_ref_af_restrict_to_split_sk     false
% 31.89/4.51  --abstr_ref_under                       []
% 31.89/4.51  
% 31.89/4.51  ------ SAT Options
% 31.89/4.51  
% 31.89/4.51  --sat_mode                              false
% 31.89/4.51  --sat_fm_restart_options                ""
% 31.89/4.51  --sat_gr_def                            false
% 31.89/4.51  --sat_epr_types                         true
% 31.89/4.51  --sat_non_cyclic_types                  false
% 31.89/4.51  --sat_finite_models                     false
% 31.89/4.51  --sat_fm_lemmas                         false
% 31.89/4.51  --sat_fm_prep                           false
% 31.89/4.51  --sat_fm_uc_incr                        true
% 31.89/4.51  --sat_out_model                         small
% 31.89/4.51  --sat_out_clauses                       false
% 31.89/4.51  
% 31.89/4.51  ------ QBF Options
% 31.89/4.51  
% 31.89/4.51  --qbf_mode                              false
% 31.89/4.51  --qbf_elim_univ                         false
% 31.89/4.51  --qbf_dom_inst                          none
% 31.89/4.51  --qbf_dom_pre_inst                      false
% 31.89/4.51  --qbf_sk_in                             false
% 31.89/4.51  --qbf_pred_elim                         true
% 31.89/4.51  --qbf_split                             512
% 31.89/4.51  
% 31.89/4.51  ------ BMC1 Options
% 31.89/4.51  
% 31.89/4.51  --bmc1_incremental                      false
% 31.89/4.51  --bmc1_axioms                           reachable_all
% 31.89/4.51  --bmc1_min_bound                        0
% 31.89/4.51  --bmc1_max_bound                        -1
% 31.89/4.51  --bmc1_max_bound_default                -1
% 31.89/4.51  --bmc1_symbol_reachability              true
% 31.89/4.51  --bmc1_property_lemmas                  false
% 31.89/4.51  --bmc1_k_induction                      false
% 31.89/4.51  --bmc1_non_equiv_states                 false
% 31.89/4.51  --bmc1_deadlock                         false
% 31.89/4.51  --bmc1_ucm                              false
% 31.89/4.51  --bmc1_add_unsat_core                   none
% 31.89/4.51  --bmc1_unsat_core_children              false
% 31.89/4.51  --bmc1_unsat_core_extrapolate_axioms    false
% 31.89/4.51  --bmc1_out_stat                         full
% 31.89/4.51  --bmc1_ground_init                      false
% 31.89/4.51  --bmc1_pre_inst_next_state              false
% 31.89/4.51  --bmc1_pre_inst_state                   false
% 31.89/4.51  --bmc1_pre_inst_reach_state             false
% 31.89/4.51  --bmc1_out_unsat_core                   false
% 31.89/4.51  --bmc1_aig_witness_out                  false
% 31.89/4.51  --bmc1_verbose                          false
% 31.89/4.51  --bmc1_dump_clauses_tptp                false
% 31.89/4.51  --bmc1_dump_unsat_core_tptp             false
% 31.89/4.51  --bmc1_dump_file                        -
% 31.89/4.51  --bmc1_ucm_expand_uc_limit              128
% 31.89/4.51  --bmc1_ucm_n_expand_iterations          6
% 31.89/4.51  --bmc1_ucm_extend_mode                  1
% 31.89/4.51  --bmc1_ucm_init_mode                    2
% 31.89/4.51  --bmc1_ucm_cone_mode                    none
% 31.89/4.51  --bmc1_ucm_reduced_relation_type        0
% 31.89/4.51  --bmc1_ucm_relax_model                  4
% 31.89/4.51  --bmc1_ucm_full_tr_after_sat            true
% 31.89/4.51  --bmc1_ucm_expand_neg_assumptions       false
% 31.89/4.51  --bmc1_ucm_layered_model                none
% 31.89/4.51  --bmc1_ucm_max_lemma_size               10
% 31.89/4.51  
% 31.89/4.51  ------ AIG Options
% 31.89/4.51  
% 31.89/4.51  --aig_mode                              false
% 31.89/4.51  
% 31.89/4.51  ------ Instantiation Options
% 31.89/4.51  
% 31.89/4.51  --instantiation_flag                    true
% 31.89/4.51  --inst_sos_flag                         true
% 31.89/4.51  --inst_sos_phase                        true
% 31.89/4.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.89/4.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.89/4.51  --inst_lit_sel_side                     none
% 31.89/4.51  --inst_solver_per_active                1400
% 31.89/4.51  --inst_solver_calls_frac                1.
% 31.89/4.51  --inst_passive_queue_type               priority_queues
% 31.89/4.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.89/4.51  --inst_passive_queues_freq              [25;2]
% 31.89/4.51  --inst_dismatching                      true
% 31.89/4.51  --inst_eager_unprocessed_to_passive     true
% 31.89/4.51  --inst_prop_sim_given                   true
% 31.89/4.51  --inst_prop_sim_new                     false
% 31.89/4.51  --inst_subs_new                         false
% 31.89/4.51  --inst_eq_res_simp                      false
% 31.89/4.51  --inst_subs_given                       false
% 31.89/4.51  --inst_orphan_elimination               true
% 31.89/4.51  --inst_learning_loop_flag               true
% 31.89/4.51  --inst_learning_start                   3000
% 31.89/4.51  --inst_learning_factor                  2
% 31.89/4.51  --inst_start_prop_sim_after_learn       3
% 31.89/4.51  --inst_sel_renew                        solver
% 31.89/4.51  --inst_lit_activity_flag                true
% 31.89/4.51  --inst_restr_to_given                   false
% 31.89/4.51  --inst_activity_threshold               500
% 31.89/4.51  --inst_out_proof                        true
% 31.89/4.51  
% 31.89/4.51  ------ Resolution Options
% 31.89/4.51  
% 31.89/4.51  --resolution_flag                       false
% 31.89/4.51  --res_lit_sel                           adaptive
% 31.89/4.51  --res_lit_sel_side                      none
% 31.89/4.51  --res_ordering                          kbo
% 31.89/4.51  --res_to_prop_solver                    active
% 31.89/4.51  --res_prop_simpl_new                    false
% 31.89/4.51  --res_prop_simpl_given                  true
% 31.89/4.51  --res_passive_queue_type                priority_queues
% 31.89/4.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.89/4.51  --res_passive_queues_freq               [15;5]
% 31.89/4.51  --res_forward_subs                      full
% 31.89/4.51  --res_backward_subs                     full
% 31.89/4.51  --res_forward_subs_resolution           true
% 31.89/4.51  --res_backward_subs_resolution          true
% 31.89/4.51  --res_orphan_elimination                true
% 31.89/4.51  --res_time_limit                        2.
% 31.89/4.51  --res_out_proof                         true
% 31.89/4.51  
% 31.89/4.51  ------ Superposition Options
% 31.89/4.51  
% 31.89/4.51  --superposition_flag                    true
% 31.89/4.51  --sup_passive_queue_type                priority_queues
% 31.89/4.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.89/4.51  --sup_passive_queues_freq               [8;1;4]
% 31.89/4.51  --demod_completeness_check              fast
% 31.89/4.51  --demod_use_ground                      true
% 31.89/4.51  --sup_to_prop_solver                    passive
% 31.89/4.51  --sup_prop_simpl_new                    true
% 31.89/4.51  --sup_prop_simpl_given                  true
% 31.89/4.51  --sup_fun_splitting                     true
% 31.89/4.51  --sup_smt_interval                      50000
% 31.89/4.51  
% 31.89/4.51  ------ Superposition Simplification Setup
% 31.89/4.51  
% 31.89/4.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.89/4.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.89/4.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.89/4.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.89/4.51  --sup_full_triv                         [TrivRules;PropSubs]
% 31.89/4.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.89/4.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.89/4.51  --sup_immed_triv                        [TrivRules]
% 31.89/4.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.89/4.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.89/4.51  --sup_immed_bw_main                     []
% 31.89/4.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.89/4.51  --sup_input_triv                        [Unflattening;TrivRules]
% 31.89/4.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.89/4.51  --sup_input_bw                          []
% 31.89/4.51  
% 31.89/4.51  ------ Combination Options
% 31.89/4.51  
% 31.89/4.51  --comb_res_mult                         3
% 31.89/4.51  --comb_sup_mult                         2
% 31.89/4.51  --comb_inst_mult                        10
% 31.89/4.51  
% 31.89/4.51  ------ Debug Options
% 31.89/4.51  
% 31.89/4.51  --dbg_backtrace                         false
% 31.89/4.51  --dbg_dump_prop_clauses                 false
% 31.89/4.51  --dbg_dump_prop_clauses_file            -
% 31.89/4.51  --dbg_out_stat                          false
% 31.89/4.51  
% 31.89/4.51  
% 31.89/4.51  
% 31.89/4.51  
% 31.89/4.51  ------ Proving...
% 31.89/4.51  
% 31.89/4.51  
% 31.89/4.51  % SZS status Theorem for theBenchmark.p
% 31.89/4.51  
% 31.89/4.51  % SZS output start CNFRefutation for theBenchmark.p
% 31.89/4.51  
% 31.89/4.51  fof(f7,axiom,(
% 31.89/4.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f21,plain,(
% 31.89/4.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.89/4.51    inference(ennf_transformation,[],[f7])).
% 31.89/4.51  
% 31.89/4.51  fof(f42,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f21])).
% 31.89/4.51  
% 31.89/4.51  fof(f16,conjecture,(
% 31.89/4.51    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f17,negated_conjecture,(
% 31.89/4.51    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 31.89/4.51    inference(negated_conjecture,[],[f16])).
% 31.89/4.51  
% 31.89/4.51  fof(f24,plain,(
% 31.89/4.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 31.89/4.51    inference(ennf_transformation,[],[f17])).
% 31.89/4.51  
% 31.89/4.51  fof(f25,plain,(
% 31.89/4.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 31.89/4.51    inference(flattening,[],[f24])).
% 31.89/4.51  
% 31.89/4.51  fof(f31,plain,(
% 31.89/4.51    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 31.89/4.51    introduced(choice_axiom,[])).
% 31.89/4.51  
% 31.89/4.51  fof(f32,plain,(
% 31.89/4.51    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 31.89/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f31])).
% 31.89/4.51  
% 31.89/4.51  fof(f55,plain,(
% 31.89/4.51    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 31.89/4.51    inference(cnf_transformation,[],[f32])).
% 31.89/4.51  
% 31.89/4.51  fof(f12,axiom,(
% 31.89/4.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f50,plain,(
% 31.89/4.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f12])).
% 31.89/4.51  
% 31.89/4.51  fof(f13,axiom,(
% 31.89/4.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f51,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f13])).
% 31.89/4.51  
% 31.89/4.51  fof(f14,axiom,(
% 31.89/4.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f52,plain,(
% 31.89/4.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f14])).
% 31.89/4.51  
% 31.89/4.51  fof(f59,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 31.89/4.51    inference(definition_unfolding,[],[f51,f52])).
% 31.89/4.51  
% 31.89/4.51  fof(f60,plain,(
% 31.89/4.51    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 31.89/4.51    inference(definition_unfolding,[],[f50,f59])).
% 31.89/4.51  
% 31.89/4.51  fof(f66,plain,(
% 31.89/4.51    r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4))),
% 31.89/4.51    inference(definition_unfolding,[],[f55,f60])).
% 31.89/4.51  
% 31.89/4.51  fof(f6,axiom,(
% 31.89/4.51    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f41,plain,(
% 31.89/4.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f6])).
% 31.89/4.51  
% 31.89/4.51  fof(f1,axiom,(
% 31.89/4.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f33,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f1])).
% 31.89/4.51  
% 31.89/4.51  fof(f10,axiom,(
% 31.89/4.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f47,plain,(
% 31.89/4.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f10])).
% 31.89/4.51  
% 31.89/4.51  fof(f5,axiom,(
% 31.89/4.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f40,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.89/4.51    inference(cnf_transformation,[],[f5])).
% 31.89/4.51  
% 31.89/4.51  fof(f61,plain,(
% 31.89/4.51    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 31.89/4.51    inference(definition_unfolding,[],[f47,f40])).
% 31.89/4.51  
% 31.89/4.51  fof(f2,axiom,(
% 31.89/4.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f26,plain,(
% 31.89/4.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 31.89/4.51    inference(nnf_transformation,[],[f2])).
% 31.89/4.51  
% 31.89/4.51  fof(f34,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f26])).
% 31.89/4.51  
% 31.89/4.51  fof(f57,plain,(
% 31.89/4.51    r1_xboole_0(sK3,sK2)),
% 31.89/4.51    inference(cnf_transformation,[],[f32])).
% 31.89/4.51  
% 31.89/4.51  fof(f3,axiom,(
% 31.89/4.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f19,plain,(
% 31.89/4.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 31.89/4.51    inference(ennf_transformation,[],[f3])).
% 31.89/4.51  
% 31.89/4.51  fof(f36,plain,(
% 31.89/4.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f19])).
% 31.89/4.51  
% 31.89/4.51  fof(f9,axiom,(
% 31.89/4.51    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f23,plain,(
% 31.89/4.51    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 31.89/4.51    inference(ennf_transformation,[],[f9])).
% 31.89/4.51  
% 31.89/4.51  fof(f46,plain,(
% 31.89/4.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 31.89/4.51    inference(cnf_transformation,[],[f23])).
% 31.89/4.51  
% 31.89/4.51  fof(f11,axiom,(
% 31.89/4.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f29,plain,(
% 31.89/4.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 31.89/4.51    inference(nnf_transformation,[],[f11])).
% 31.89/4.51  
% 31.89/4.51  fof(f48,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f29])).
% 31.89/4.51  
% 31.89/4.51  fof(f63,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 31.89/4.51    inference(definition_unfolding,[],[f48,f40])).
% 31.89/4.51  
% 31.89/4.51  fof(f35,plain,(
% 31.89/4.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 31.89/4.51    inference(cnf_transformation,[],[f26])).
% 31.89/4.51  
% 31.89/4.51  fof(f15,axiom,(
% 31.89/4.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f30,plain,(
% 31.89/4.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 31.89/4.51    inference(nnf_transformation,[],[f15])).
% 31.89/4.51  
% 31.89/4.51  fof(f54,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f30])).
% 31.89/4.51  
% 31.89/4.51  fof(f64,plain,(
% 31.89/4.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 31.89/4.51    inference(definition_unfolding,[],[f54,f40,f60])).
% 31.89/4.51  
% 31.89/4.51  fof(f56,plain,(
% 31.89/4.51    r2_hidden(sK4,sK3)),
% 31.89/4.51    inference(cnf_transformation,[],[f32])).
% 31.89/4.51  
% 31.89/4.51  fof(f4,axiom,(
% 31.89/4.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f18,plain,(
% 31.89/4.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 31.89/4.51    inference(rectify,[],[f4])).
% 31.89/4.51  
% 31.89/4.51  fof(f20,plain,(
% 31.89/4.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 31.89/4.51    inference(ennf_transformation,[],[f18])).
% 31.89/4.51  
% 31.89/4.51  fof(f27,plain,(
% 31.89/4.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.89/4.51    introduced(choice_axiom,[])).
% 31.89/4.51  
% 31.89/4.51  fof(f28,plain,(
% 31.89/4.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 31.89/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f27])).
% 31.89/4.51  
% 31.89/4.51  fof(f39,plain,(
% 31.89/4.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 31.89/4.51    inference(cnf_transformation,[],[f28])).
% 31.89/4.51  
% 31.89/4.51  fof(f49,plain,(
% 31.89/4.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 31.89/4.51    inference(cnf_transformation,[],[f29])).
% 31.89/4.51  
% 31.89/4.51  fof(f62,plain,(
% 31.89/4.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0) )),
% 31.89/4.51    inference(definition_unfolding,[],[f49,f40])).
% 31.89/4.51  
% 31.89/4.51  fof(f8,axiom,(
% 31.89/4.51    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 31.89/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.89/4.51  
% 31.89/4.51  fof(f22,plain,(
% 31.89/4.51    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 31.89/4.51    inference(ennf_transformation,[],[f8])).
% 31.89/4.51  
% 31.89/4.51  fof(f43,plain,(
% 31.89/4.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 31.89/4.51    inference(cnf_transformation,[],[f22])).
% 31.89/4.51  
% 31.89/4.51  fof(f58,plain,(
% 31.89/4.51    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 31.89/4.51    inference(cnf_transformation,[],[f32])).
% 31.89/4.51  
% 31.89/4.51  cnf(c_8,plain,
% 31.89/4.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 31.89/4.51      inference(cnf_transformation,[],[f42]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21,negated_conjecture,
% 31.89/4.51      ( r1_tarski(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 31.89/4.51      inference(cnf_transformation,[],[f66]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_280,plain,
% 31.89/4.51      ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 31.89/4.51      | k3_xboole_0(X1,X0) = X1
% 31.89/4.51      | k3_xboole_0(sK1,sK2) != X1 ),
% 31.89/4.51      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_281,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK1,sK2) ),
% 31.89/4.51      inference(unflattening,[status(thm)],[c_280]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_7,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 31.89/4.51      inference(cnf_transformation,[],[f41]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_0,plain,
% 31.89/4.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 31.89/4.51      inference(cnf_transformation,[],[f33]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_460,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(sK1,sK2) ),
% 31.89/4.51      inference(theory_normalisation,[status(thm)],[c_281,c_7,c_0]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_13,plain,
% 31.89/4.51      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 31.89/4.51      inference(cnf_transformation,[],[f61]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_890,plain,
% 31.89/4.51      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_1756,plain,
% 31.89/4.51      ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))),X2) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_890]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_5280,plain,
% 31.89/4.51      ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X1,X2),X0)),X2) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_1756]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_13539,plain,
% 31.89/4.51      ( r1_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0),sK1)),X0) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_460,c_5280]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2,plain,
% 31.89/4.51      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 31.89/4.51      inference(cnf_transformation,[],[f34]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_899,plain,
% 31.89/4.51      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 31.89/4.51      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_14532,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0),sK1)),X0) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_13539,c_899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_1755,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_460,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_920,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2253,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_1755,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_19,negated_conjecture,
% 31.89/4.51      ( r1_xboole_0(sK3,sK2) ),
% 31.89/4.51      inference(cnf_transformation,[],[f57]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_884,plain,
% 31.89/4.51      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3017,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_884,c_899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_13549,plain,
% 31.89/4.51      ( r1_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),X0) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3017,c_5280]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_14324,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),X0) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_13549,c_899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17569,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3))) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_14324,c_0]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_19494,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK2),sK3))) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_17569]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3371,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3017,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3872,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3371,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_5683,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_3872]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21283,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK2),sK3))) = k3_xboole_0(sK3,k3_xboole_0(sK2,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_19494,c_5683]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3,plain,
% 31.89/4.51      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 31.89/4.51      inference(cnf_transformation,[],[f36]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_898,plain,
% 31.89/4.51      ( r1_xboole_0(X0,X1) != iProver_top
% 31.89/4.51      | r1_xboole_0(X1,X0) = iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2101,plain,
% 31.89/4.51      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_884,c_898]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12,plain,
% 31.89/4.51      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 31.89/4.51      inference(cnf_transformation,[],[f46]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_891,plain,
% 31.89/4.51      ( r1_xboole_0(X0,X1) != iProver_top
% 31.89/4.51      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_5131,plain,
% 31.89/4.51      ( r1_xboole_0(X0,sK3) != iProver_top
% 31.89/4.51      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3017,c_891]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6025,plain,
% 31.89/4.51      ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_2101,c_5131]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6043,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6025,c_899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3018,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_2101,c_899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_5125,plain,
% 31.89/4.51      ( r1_xboole_0(X0,sK2) != iProver_top
% 31.89/4.51      | r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3018,c_891]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_11277,plain,
% 31.89/4.51      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_884,c_5125]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_11301,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_11277,c_899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21425,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK2),sK3))) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_21283,c_6043,c_11301]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_83235,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK1),sK2),sK3))) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_2253,c_21425]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_921,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3863,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,sK2))) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_921,c_3371]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23295,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_1755,c_3863]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23452,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK2)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_23295,c_460]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_919,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3377,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,sK2)) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3017,c_919]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4613,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3377,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6423,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6043,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6939,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,sK2)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6423,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23453,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) = k3_xboole_0(k1_xboole_0,sK1) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_23452,c_4613,c_6939]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23604,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23453,c_3377]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_83480,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK1),sK2),sK3))) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_83235,c_23604]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6045,plain,
% 31.89/4.51      ( r1_xboole_0(k1_xboole_0,sK2) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6025,c_898]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_15,plain,
% 31.89/4.51      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 31.89/4.51      inference(cnf_transformation,[],[f63]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_888,plain,
% 31.89/4.51      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 31.89/4.51      | r1_xboole_0(X0,X1) != iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6464,plain,
% 31.89/4.51      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK2)) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6045,c_888]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6428,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,sK2) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6043,c_0]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6466,plain,
% 31.89/4.51      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_6464,c_6428]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_1853,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_460,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3375,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3017,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3922,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3375,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_5791,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_3922]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21520,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(sK1,sK2)))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_1853,c_5791]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21521,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(sK1,sK2),X0))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_1755,c_5791]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21719,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),X0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_21521,c_5791]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_1844,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(sK1,X0)) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_460,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2429,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_1844,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3861,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,sK2)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_3371]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_11380,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK3,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_11301,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12755,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3861,c_11380]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6442,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(sK3,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6043,c_3375]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_11363,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_11301,c_6442]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_11498,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_11363,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12806,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_12755,c_11498]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21720,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_21719,c_2429,c_12806]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21721,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_21520,c_5791,c_21720]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6914,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_6423]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_8098,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,sK2)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6914,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21722,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) = k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_21721,c_8098]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4609,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3377,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_10670,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_4609]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_35520,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK2)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_460,c_10670]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_35768,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k2_enumset1(sK4,sK4,sK4,sK4)) = k3_xboole_0(k1_xboole_0,sK1) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_35520,c_3861]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3926,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3375,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_29110,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_3926]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_76468,plain,
% 31.89/4.51      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k1_xboole_0)) = k3_xboole_0(sK3,k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_35768,c_29110]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_76658,plain,
% 31.89/4.51      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k1_xboole_0)) = k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_76468,c_29110]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_76659,plain,
% 31.89/4.51      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),k1_xboole_0)) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_76658,c_11363]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17532,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK3,k3_xboole_0(sK2,X0))),X0) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_14324]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17692,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),X0) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_17532,c_3375]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17794,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_17692,c_0]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_18968,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),X1)) = k3_xboole_0(k1_xboole_0,X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_17794,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_50935,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X2,k3_xboole_0(k1_xboole_0,X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_18968,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_50971,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k1_xboole_0)),X0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_18968,c_1844]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_11370,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_11301,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3877,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(sK3,X1)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3371,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_28152,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(k3_xboole_0(sK2,X1),k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_11370,c_3877]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12063,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_11498,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_28275,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_28152,c_12063]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_51270,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k1_xboole_0)),X0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_50971,c_28275]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_51286,plain,
% 31.89/4.51      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_50935,c_51270]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6432,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6043,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_51287,plain,
% 31.89/4.51      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_51286,c_6432]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_68075,plain,
% 31.89/4.51      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_35768,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2249,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0),k3_xboole_0(sK1,X1)) = k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_1755,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3379,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,sK3)) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3017,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4663,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(X0,sK3),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3379,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_76018,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0)) = k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),sK3))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_2249,c_4663]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21566,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0),X0) = k3_xboole_0(sK3,k3_xboole_0(sK2,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_17692,c_5791]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21657,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),k1_xboole_0),X0) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_21566,c_6043,c_11301]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_22978,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)),k1_xboole_0),X0) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_21657]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_1854,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(X0,sK1)) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_460,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_27310,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)),k1_xboole_0),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_22978,c_1854]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_25101,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)),k1_xboole_0),k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23604,c_21657]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_27395,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_27310,c_25101]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3376,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(sK3,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3017,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4493,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK3,X0),k3_xboole_0(sK2,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3376,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_32341,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK2),k1_xboole_0)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK2,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23453,c_4493]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23551,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(sK1,k3_xboole_0(sK2,sK2))) = k3_xboole_0(k1_xboole_0,sK1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_23453]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_32342,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK2)),k1_xboole_0)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK2,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23551,c_4493]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_30815,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK2)),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23551,c_11380]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_5678,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_3872]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_15352,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_5678,c_11380]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4480,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(X1,sK3))) = k3_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_920,c_3376]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3658,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(sK3,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3018,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4126,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,sK3)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_3658]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4350,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(X1,sK3))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_4126,c_919]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4508,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_4480,c_4350]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12062,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_11498,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_15374,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k1_xboole_0) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_15352,c_4508,c_12062]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_30844,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK2)),k1_xboole_0) = k3_xboole_0(k1_xboole_0,sK1) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_30815,c_11498,c_15374]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_32487,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK2,X0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_32342,c_30844]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_32488,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK2),k1_xboole_0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_32341,c_32487]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23602,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK2),k1_xboole_0) = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23453,c_3376]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4293,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3861,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12761,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_4293,c_11380]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12802,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK2),X1),k1_xboole_0) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_12761,c_12062]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23611,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),sK2),k1_xboole_0) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_23602,c_6432,c_12802]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_32489,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) = k3_xboole_0(X0,k3_xboole_0(sK1,k1_xboole_0)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_32488,c_23611]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4498,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(sK3,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3376,c_919]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_32645,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,k3_xboole_0(sK2,sK2)),k1_xboole_0)) = k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23551,c_4498]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_32769,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_32645,c_30844]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2235,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_1755]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_35327,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3371,c_2235]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_1765,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(X0,k3_xboole_0(sK1,sK2)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_460,c_919]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3884,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK2)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3371,c_1765]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3885,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_3884,c_3377]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_35413,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_35327,c_3885]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_76039,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(light_normalisation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_76018,c_27395,c_32489,c_32769,c_35413]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_76660,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),k1_xboole_0) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.51      inference(demodulation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_76659,c_51287,c_68075,c_76039]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_1,plain,
% 31.89/4.51      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 31.89/4.51      inference(cnf_transformation,[],[f35]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_900,plain,
% 31.89/4.51      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 31.89/4.51      | r1_xboole_0(X0,X1) = iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3025,plain,
% 31.89/4.51      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 31.89/4.51      | r1_xboole_0(X1,X0) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_900]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3870,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,X0) != k1_xboole_0
% 31.89/4.51      | r1_xboole_0(k3_xboole_0(sK2,X0),sK3) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3371,c_3025]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_24,plain,
% 31.89/4.51      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_10219,plain,
% 31.89/4.51      ( ~ r1_xboole_0(sK3,X0) | r1_xboole_0(sK3,k3_xboole_0(X0,X1)) ),
% 31.89/4.51      inference(instantiation,[status(thm)],[c_12]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_30252,plain,
% 31.89/4.51      ( r1_xboole_0(sK3,k3_xboole_0(sK2,X0)) | ~ r1_xboole_0(sK3,sK2) ),
% 31.89/4.51      inference(instantiation,[status(thm)],[c_10219]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_30253,plain,
% 31.89/4.51      ( r1_xboole_0(sK3,k3_xboole_0(sK2,X0)) = iProver_top
% 31.89/4.51      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_30252]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_9132,plain,
% 31.89/4.51      ( r1_xboole_0(X0,sK3) | ~ r1_xboole_0(sK3,X0) ),
% 31.89/4.51      inference(instantiation,[status(thm)],[c_3]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_70905,plain,
% 31.89/4.51      ( r1_xboole_0(k3_xboole_0(sK2,X0),sK3)
% 31.89/4.51      | ~ r1_xboole_0(sK3,k3_xboole_0(sK2,X0)) ),
% 31.89/4.51      inference(instantiation,[status(thm)],[c_9132]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_70935,plain,
% 31.89/4.51      ( r1_xboole_0(k3_xboole_0(sK2,X0),sK3) = iProver_top
% 31.89/4.51      | r1_xboole_0(sK3,k3_xboole_0(sK2,X0)) != iProver_top ),
% 31.89/4.51      inference(predicate_to_equality,[status(thm)],[c_70905]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80398,plain,
% 31.89/4.51      ( r1_xboole_0(k3_xboole_0(sK2,X0),sK3) = iProver_top ),
% 31.89/4.51      inference(global_propositional_subsumption,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_3870,c_24,c_30253,c_70935]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80404,plain,
% 31.89/4.51      ( r1_xboole_0(k3_xboole_0(X0,sK2),sK3) = iProver_top ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_80398]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_81322,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,sK2),sK3) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_80404,c_899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_83481,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.51      inference(demodulation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_83480,c_6466,c_21722,c_76660,c_81322]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6928,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6423,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_83247,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),sK1)),X0) = k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_2253,c_6928]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_83463,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),X0)) = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0),X0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_83247,c_2253]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4140,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(sK3,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3658,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23598,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)),X0) = k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23453,c_4140]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23603,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) = k3_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23453,c_3658]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_6723,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6428,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_7154,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6723,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_22183,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_7154]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23610,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_23603,c_6432,c_22183]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23614,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0)) = k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_23598,c_23610]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_23615,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0))) = k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_23614,c_21722]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_83464,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) = k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(light_normalisation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_83463,c_21722,c_23604,c_23615]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2252,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X1))) = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_1755,c_919]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80706,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0),X0)) = k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK2,X0))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_10670,c_2252]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3876,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK2,X0),X1)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3371,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80714,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3876,c_2252]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21561,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),k1_xboole_0),X0) = k3_xboole_0(sK3,k3_xboole_0(sK2,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_14324,c_5791]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_21661,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),k1_xboole_0),X0) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_21561,c_6043,c_11301]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80740,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)),sK3)),k1_xboole_0),k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_21661,c_2252]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_25083,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_23604,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4659,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(k3_xboole_0(X0,sK3),X1)) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3379,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_13383,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(sK3,X1))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_4659]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_40809,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK3,X2)))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0),X2) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_13383]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_5786,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(k3_xboole_0(X1,k1_xboole_0),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_3922]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17243,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_919,c_5786]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_15305,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_919,c_5678]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_15343,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(k1_xboole_0,X2),X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_5678,c_919]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_15308,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,X1)),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_921,c_5678]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_5793,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(X2,k1_xboole_0),k3_xboole_0(X1,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_920,c_3922]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_15390,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)),X2) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_15308,c_5793]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_15395,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,X2)))) = k3_xboole_0(k3_xboole_0(X1,k1_xboole_0),k3_xboole_0(X2,X0)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_15305,c_15343,c_15390]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17336,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0),X2) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_17243,c_15395]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17337,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)),X2) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_17336,c_4508]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_32680,plain,
% 31.89/4.51      ( k3_xboole_0(sK2,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK3,X2)))) = k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_4498,c_919]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_41113,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X1,X2)) ),
% 31.89/4.51      inference(light_normalisation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_40809,c_4508,c_17337,c_32680]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80443,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,X0),sK3) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_80398,c_899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80940,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.51      inference(demodulation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_80740,c_6466,c_11363,c_25083,c_41113,c_80443]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3882,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(X1,sK3)) = k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3371,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80761,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X1,sK3))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3882,c_2252]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2241,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X1))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_919,c_1755]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_40552,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,k3_xboole_0(X1,sK3))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3882,c_2241]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4672,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,sK3),k3_xboole_0(X1,sK2)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3379,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_35219,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(X1,k3_xboole_0(X2,sK3))) = k3_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X2,k1_xboole_0))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_4672,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2240,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(sK2,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) = k3_xboole_0(k3_xboole_0(sK1,sK2),X0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_7,c_1755]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3880,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3371,c_919]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_39101,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) = k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_2240,c_3880]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3868,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(sK2,X1))) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_921,c_3371]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2237,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_921,c_1755]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_37025,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3868,c_2237]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3927,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,X0),k3_xboole_0(sK3,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3375,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_29802,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3927,c_1755]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17575,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,X0),sK3)),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_14324,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17600,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,sK1),sK3)),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_14324,c_1854]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_11379,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_11301,c_921]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12607,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,X0),k1_xboole_0) = k3_xboole_0(sK3,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_6723,c_11379]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_12660,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK2,X0),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_12607,c_11379]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17677,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,sK1),sK3)),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_17600,c_12660]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17679,plain,
% 31.89/4.51      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_17575,c_17677]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17680,plain,
% 31.89/4.51      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k1_xboole_0) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_17679,c_6043]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_29832,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,X0)) = k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_29802,c_17680]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_37237,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) = k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_37025,c_29832]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_39106,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_39101,c_37237]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_3867,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,k3_xboole_0(X1,sK2))) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_920,c_3371]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_25899,plain,
% 31.89/4.51      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(X0,sK2),X1)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_3867]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_39107,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_39106,c_25899]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_40658,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_40552,c_35219,c_39107]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80926,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X1,sK3))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_80761,c_40658]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_28756,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,sK3)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3882,c_1755]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_28220,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK3,X0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3877,c_1755]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_4614,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(sK3,X1)) = k3_xboole_0(X1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_3377,c_920]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_28245,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k2_enumset1(sK4,sK4,sK4,sK4)))) = k3_xboole_0(X0,k3_xboole_0(sK1,k1_xboole_0)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_28220,c_4614]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_28784,plain,
% 31.89/4.51      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X0,sK3)) = k3_xboole_0(X0,k3_xboole_0(sK1,k1_xboole_0)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_28756,c_28245]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80927,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,k1_xboole_0))) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_80926,c_28784]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80928,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,sK1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_80927,c_32489]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80942,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) = k3_xboole_0(X0,k3_xboole_0(sK1,k1_xboole_0)) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_80940,c_80928]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80943,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_80942,c_32489]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_18948,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_0,c_17794]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_19210,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)),X1)) = k3_xboole_0(k1_xboole_0,X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_18948,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80768,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)))),X1))) = k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_19210,c_2252]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_17788,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(X0,X1)) = k3_xboole_0(k1_xboole_0,X1) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_17692,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_47083,plain,
% 31.89/4.51      ( k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k1_xboole_0)),k3_xboole_0(sK1,sK2)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_460,c_17788]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_47464,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = k3_xboole_0(k1_xboole_0,sK2) ),
% 31.89/4.51      inference(demodulation,[status(thm)],[c_47083,c_17788]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_47465,plain,
% 31.89/4.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = k1_xboole_0 ),
% 31.89/4.51      inference(light_normalisation,[status(thm)],[c_47464,c_6428]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_80917,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) ),
% 31.89/4.51      inference(light_normalisation,
% 31.89/4.51                [status(thm)],
% 31.89/4.51                [c_80768,c_6466,c_47465]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_19223,plain,
% 31.89/4.51      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 31.89/4.51      inference(superposition,[status(thm)],[c_18948,c_7]) ).
% 31.89/4.51  
% 31.89/4.51  cnf(c_2243,plain,
% 31.89/4.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X1))) = k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(X1,X0)) ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_921,c_1755]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_54640,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)))),X1)) = k3_xboole_0(sK1,k3_xboole_0(X1,k1_xboole_0)) ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_19223,c_2243]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_53925,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)),X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_19210,c_2241]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_50891,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_23604,c_18968]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_54155,plain,
% 31.89/4.52      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),X0)) = k3_xboole_0(k1_xboole_0,X0) ),
% 31.89/4.52      inference(light_normalisation,[status(thm)],[c_53925,c_50891]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_54953,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK1,k3_xboole_0(X0,k1_xboole_0)) ),
% 31.89/4.52      inference(light_normalisation,
% 31.89/4.52                [status(thm)],
% 31.89/4.52                [c_54640,c_18948,c_54155]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_25070,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_23604,c_7]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_25148,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0)) ),
% 31.89/4.52      inference(light_normalisation,[status(thm)],[c_25070,c_21722]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_54954,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X0)) ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_54953,c_25148,c_39107]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_80918,plain,
% 31.89/4.52      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k3_xboole_0(sK1,X1))) ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_80917,c_54954]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_80944,plain,
% 31.89/4.52      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_80943,c_80918]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_80950,plain,
% 31.89/4.52      ( k3_xboole_0(sK1,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1))) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_80944,c_80940]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_80984,plain,
% 31.89/4.52      ( k3_xboole_0(sK3,k3_xboole_0(k3_xboole_0(sK1,sK2),X0)) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_80714,c_80950]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_80990,plain,
% 31.89/4.52      ( k3_xboole_0(sK1,k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)),k1_xboole_0),X0)) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_80706,c_80984]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_80991,plain,
% 31.89/4.52      ( k3_xboole_0(sK1,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.52      inference(light_normalisation,[status(thm)],[c_80990,c_27395]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_83465,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,k1_xboole_0),X0) = k3_xboole_0(sK1,k1_xboole_0) ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_83464,c_80991]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_83482,plain,
% 31.89/4.52      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_83481,c_83465]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_16,plain,
% 31.89/4.52      ( r2_hidden(X0,X1)
% 31.89/4.52      | k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) = X1 ),
% 31.89/4.52      inference(cnf_transformation,[],[f64]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_887,plain,
% 31.89/4.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
% 31.89/4.52      | r2_hidden(X1,X0) = iProver_top ),
% 31.89/4.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_20,negated_conjecture,
% 31.89/4.52      ( r2_hidden(sK4,sK3) ),
% 31.89/4.52      inference(cnf_transformation,[],[f56]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_883,plain,
% 31.89/4.52      ( r2_hidden(sK4,sK3) = iProver_top ),
% 31.89/4.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_4,plain,
% 31.89/4.52      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 31.89/4.52      inference(cnf_transformation,[],[f39]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_897,plain,
% 31.89/4.52      ( r2_hidden(X0,X1) != iProver_top
% 31.89/4.52      | r2_hidden(X0,X2) != iProver_top
% 31.89/4.52      | r1_xboole_0(X2,X1) != iProver_top ),
% 31.89/4.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_11751,plain,
% 31.89/4.52      ( r2_hidden(sK4,X0) != iProver_top
% 31.89/4.52      | r1_xboole_0(X0,sK3) != iProver_top ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_883,c_897]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_143816,plain,
% 31.89/4.52      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))) = X0
% 31.89/4.52      | r1_xboole_0(X0,sK3) != iProver_top ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_887,c_11751]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_146730,plain,
% 31.89/4.52      ( k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))) = sK2 ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_2101,c_143816]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_14,plain,
% 31.89/4.52      ( r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 ),
% 31.89/4.52      inference(cnf_transformation,[],[f62]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_889,plain,
% 31.89/4.52      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
% 31.89/4.52      | r1_xboole_0(X0,X1) = iProver_top ),
% 31.89/4.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_146800,plain,
% 31.89/4.52      ( r1_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_146730,c_889]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_147078,plain,
% 31.89/4.52      ( k3_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = k1_xboole_0 ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_146800,c_899]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_167841,plain,
% 31.89/4.52      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,sK1)),X0) = k1_xboole_0 ),
% 31.89/4.52      inference(light_normalisation,
% 31.89/4.52                [status(thm)],
% 31.89/4.52                [c_14532,c_14532,c_83482,c_147078]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_81325,plain,
% 31.89/4.52      ( r1_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0) = iProver_top ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_80404,c_5131]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_82573,plain,
% 31.89/4.52      ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(k3_xboole_0(X0,sK2),k1_xboole_0)) = k3_xboole_0(X0,sK2) ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_81325,c_888]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_82575,plain,
% 31.89/4.52      ( k5_xboole_0(k3_xboole_0(X0,sK2),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,sK2) ),
% 31.89/4.52      inference(light_normalisation,[status(thm)],[c_82573,c_12806]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_167842,plain,
% 31.89/4.52      ( k3_xboole_0(k3_xboole_0(sK1,sK2),X0) = k1_xboole_0 ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_167841,c_82575]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_167976,plain,
% 31.89/4.52      ( k3_xboole_0(sK1,k3_xboole_0(sK2,X0)) = k1_xboole_0 ),
% 31.89/4.52      inference(superposition,[status(thm)],[c_167842,c_7]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_168534,plain,
% 31.89/4.52      ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 31.89/4.52      inference(demodulation,[status(thm)],[c_167976,c_460]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_2055,plain,
% 31.89/4.52      ( r1_xboole_0(X0,sK2) | k3_xboole_0(X0,sK2) != k1_xboole_0 ),
% 31.89/4.52      inference(instantiation,[status(thm)],[c_1]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_85170,plain,
% 31.89/4.52      ( r1_xboole_0(sK1,sK2) | k3_xboole_0(sK1,sK2) != k1_xboole_0 ),
% 31.89/4.52      inference(instantiation,[status(thm)],[c_2055]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_1795,plain,
% 31.89/4.52      ( r1_xboole_0(sK2,sK1) | ~ r1_xboole_0(sK1,sK2) ),
% 31.89/4.52      inference(instantiation,[status(thm)],[c_3]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_1183,plain,
% 31.89/4.52      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 31.89/4.52      inference(instantiation,[status(thm)],[c_3]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_11,plain,
% 31.89/4.52      ( ~ r1_xboole_0(X0,X1)
% 31.89/4.52      | ~ r1_xboole_0(X0,X2)
% 31.89/4.52      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 31.89/4.52      inference(cnf_transformation,[],[f43]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_997,plain,
% 31.89/4.52      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
% 31.89/4.52      | ~ r1_xboole_0(sK2,sK3)
% 31.89/4.52      | ~ r1_xboole_0(sK2,sK1) ),
% 31.89/4.52      inference(instantiation,[status(thm)],[c_11]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_942,plain,
% 31.89/4.52      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
% 31.89/4.52      | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 31.89/4.52      inference(instantiation,[status(thm)],[c_3]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(c_18,negated_conjecture,
% 31.89/4.52      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 31.89/4.52      inference(cnf_transformation,[],[f58]) ).
% 31.89/4.52  
% 31.89/4.52  cnf(contradiction,plain,
% 31.89/4.52      ( $false ),
% 31.89/4.52      inference(minisat,
% 31.89/4.52                [status(thm)],
% 31.89/4.52                [c_168534,c_85170,c_1795,c_1183,c_997,c_942,c_18,c_19]) ).
% 31.89/4.52  
% 31.89/4.52  
% 31.89/4.52  % SZS output end CNFRefutation for theBenchmark.p
% 31.89/4.52  
% 31.89/4.52  ------                               Statistics
% 31.89/4.52  
% 31.89/4.52  ------ General
% 31.89/4.52  
% 31.89/4.52  abstr_ref_over_cycles:                  0
% 31.89/4.52  abstr_ref_under_cycles:                 0
% 31.89/4.52  gc_basic_clause_elim:                   0
% 31.89/4.52  forced_gc_time:                         0
% 31.89/4.52  parsing_time:                           0.023
% 31.89/4.52  unif_index_cands_time:                  0.
% 31.89/4.52  unif_index_add_time:                    0.
% 31.89/4.52  orderings_time:                         0.
% 31.89/4.52  out_proof_time:                         0.026
% 31.89/4.52  total_time:                             4.006
% 31.89/4.52  num_of_symbols:                         44
% 31.89/4.52  num_of_terms:                           223953
% 31.89/4.52  
% 31.89/4.52  ------ Preprocessing
% 31.89/4.52  
% 31.89/4.52  num_of_splits:                          0
% 31.89/4.52  num_of_split_atoms:                     0
% 31.89/4.52  num_of_reused_defs:                     0
% 31.89/4.52  num_eq_ax_congr_red:                    9
% 31.89/4.52  num_of_sem_filtered_clauses:            1
% 31.89/4.52  num_of_subtypes:                        0
% 31.89/4.52  monotx_restored_types:                  0
% 31.89/4.52  sat_num_of_epr_types:                   0
% 31.89/4.52  sat_num_of_non_cyclic_types:            0
% 31.89/4.52  sat_guarded_non_collapsed_types:        0
% 31.89/4.52  num_pure_diseq_elim:                    0
% 31.89/4.52  simp_replaced_by:                       0
% 31.89/4.52  res_preprocessed:                       102
% 31.89/4.52  prep_upred:                             0
% 31.89/4.52  prep_unflattend:                        2
% 31.89/4.52  smt_new_axioms:                         0
% 31.89/4.52  pred_elim_cands:                        2
% 31.89/4.52  pred_elim:                              1
% 31.89/4.52  pred_elim_cl:                           1
% 31.89/4.52  pred_elim_cycles:                       3
% 31.89/4.52  merged_defs:                            24
% 31.89/4.52  merged_defs_ncl:                        0
% 31.89/4.52  bin_hyper_res:                          24
% 31.89/4.52  prep_cycles:                            4
% 31.89/4.52  pred_elim_time:                         0.001
% 31.89/4.52  splitting_time:                         0.
% 31.89/4.52  sem_filter_time:                        0.
% 31.89/4.52  monotx_time:                            0.001
% 31.89/4.52  subtype_inf_time:                       0.
% 31.89/4.52  
% 31.89/4.52  ------ Problem properties
% 31.89/4.52  
% 31.89/4.52  clauses:                                21
% 31.89/4.52  conjectures:                            3
% 31.89/4.52  epr:                                    4
% 31.89/4.52  horn:                                   18
% 31.89/4.52  ground:                                 4
% 31.89/4.52  unary:                                  7
% 31.89/4.52  binary:                                 12
% 31.89/4.52  lits:                                   37
% 31.89/4.52  lits_eq:                                9
% 31.89/4.52  fd_pure:                                0
% 31.89/4.52  fd_pseudo:                              0
% 31.89/4.52  fd_cond:                                0
% 31.89/4.52  fd_pseudo_cond:                         0
% 31.89/4.52  ac_symbols:                             1
% 31.89/4.52  
% 31.89/4.52  ------ Propositional Solver
% 31.89/4.52  
% 31.89/4.52  prop_solver_calls:                      55
% 31.89/4.52  prop_fast_solver_calls:                 1387
% 31.89/4.52  smt_solver_calls:                       0
% 31.89/4.52  smt_fast_solver_calls:                  0
% 31.89/4.52  prop_num_of_clauses:                    54961
% 31.89/4.52  prop_preprocess_simplified:             42788
% 31.89/4.52  prop_fo_subsumed:                       19
% 31.89/4.52  prop_solver_time:                       0.
% 31.89/4.52  smt_solver_time:                        0.
% 31.89/4.52  smt_fast_solver_time:                   0.
% 31.89/4.52  prop_fast_solver_time:                  0.
% 31.89/4.52  prop_unsat_core_time:                   0.006
% 31.89/4.52  
% 31.89/4.52  ------ QBF
% 31.89/4.52  
% 31.89/4.52  qbf_q_res:                              0
% 31.89/4.52  qbf_num_tautologies:                    0
% 31.89/4.52  qbf_prep_cycles:                        0
% 31.89/4.52  
% 31.89/4.52  ------ BMC1
% 31.89/4.52  
% 31.89/4.52  bmc1_current_bound:                     -1
% 31.89/4.52  bmc1_last_solved_bound:                 -1
% 31.89/4.52  bmc1_unsat_core_size:                   -1
% 31.89/4.52  bmc1_unsat_core_parents_size:           -1
% 31.89/4.52  bmc1_merge_next_fun:                    0
% 31.89/4.52  bmc1_unsat_core_clauses_time:           0.
% 31.89/4.52  
% 31.89/4.52  ------ Instantiation
% 31.89/4.52  
% 31.89/4.52  inst_num_of_clauses:                    6442
% 31.89/4.52  inst_num_in_passive:                    1029
% 31.89/4.52  inst_num_in_active:                     2202
% 31.89/4.52  inst_num_in_unprocessed:                3216
% 31.89/4.52  inst_num_of_loops:                      2640
% 31.89/4.52  inst_num_of_learning_restarts:          0
% 31.89/4.52  inst_num_moves_active_passive:          436
% 31.89/4.52  inst_lit_activity:                      0
% 31.89/4.52  inst_lit_activity_moves:                1
% 31.89/4.52  inst_num_tautologies:                   0
% 31.89/4.52  inst_num_prop_implied:                  0
% 31.89/4.52  inst_num_existing_simplified:           0
% 31.89/4.52  inst_num_eq_res_simplified:             0
% 31.89/4.52  inst_num_child_elim:                    0
% 31.89/4.52  inst_num_of_dismatching_blockings:      6327
% 31.89/4.52  inst_num_of_non_proper_insts:           6467
% 31.89/4.52  inst_num_of_duplicates:                 0
% 31.89/4.52  inst_inst_num_from_inst_to_res:         0
% 31.89/4.52  inst_dismatching_checking_time:         0.
% 31.89/4.52  
% 31.89/4.52  ------ Resolution
% 31.89/4.52  
% 31.89/4.52  res_num_of_clauses:                     0
% 31.89/4.52  res_num_in_passive:                     0
% 31.89/4.52  res_num_in_active:                      0
% 31.89/4.52  res_num_of_loops:                       106
% 31.89/4.52  res_forward_subset_subsumed:            409
% 31.89/4.52  res_backward_subset_subsumed:           12
% 31.89/4.52  res_forward_subsumed:                   0
% 31.89/4.52  res_backward_subsumed:                  0
% 31.89/4.52  res_forward_subsumption_resolution:     0
% 31.89/4.52  res_backward_subsumption_resolution:    0
% 31.89/4.52  res_clause_to_clause_subsumption:       160408
% 31.89/4.52  res_orphan_elimination:                 0
% 31.89/4.52  res_tautology_del:                      533
% 31.89/4.52  res_num_eq_res_simplified:              0
% 31.89/4.52  res_num_sel_changes:                    0
% 31.89/4.52  res_moves_from_active_to_pass:          0
% 31.89/4.52  
% 31.89/4.52  ------ Superposition
% 31.89/4.52  
% 31.89/4.52  sup_time_total:                         0.
% 31.89/4.52  sup_time_generating:                    0.
% 31.89/4.52  sup_time_sim_full:                      0.
% 31.89/4.52  sup_time_sim_immed:                     0.
% 31.89/4.52  
% 31.89/4.52  sup_num_of_clauses:                     10697
% 31.89/4.52  sup_num_in_active:                      417
% 31.89/4.52  sup_num_in_passive:                     10280
% 31.89/4.52  sup_num_of_loops:                       526
% 31.89/4.52  sup_fw_superposition:                   32321
% 31.89/4.52  sup_bw_superposition:                   27455
% 31.89/4.52  sup_immediate_simplified:               30872
% 31.89/4.52  sup_given_eliminated:                   2
% 31.89/4.52  comparisons_done:                       0
% 31.89/4.52  comparisons_avoided:                    0
% 31.89/4.52  
% 31.89/4.52  ------ Simplifications
% 31.89/4.52  
% 31.89/4.52  
% 31.89/4.52  sim_fw_subset_subsumed:                 293
% 31.89/4.52  sim_bw_subset_subsumed:                 16
% 31.89/4.52  sim_fw_subsumed:                        2813
% 31.89/4.52  sim_bw_subsumed:                        119
% 31.89/4.52  sim_fw_subsumption_res:                 0
% 31.89/4.52  sim_bw_subsumption_res:                 0
% 31.89/4.52  sim_tautology_del:                      67
% 31.89/4.52  sim_eq_tautology_del:                   5244
% 31.89/4.52  sim_eq_res_simp:                        219
% 31.89/4.52  sim_fw_demodulated:                     18300
% 31.89/4.52  sim_bw_demodulated:                     548
% 31.89/4.52  sim_light_normalised:                   18586
% 31.89/4.52  sim_joinable_taut:                      1843
% 31.89/4.52  sim_joinable_simp:                      0
% 31.89/4.52  sim_ac_normalised:                      0
% 31.89/4.52  sim_smt_subsumption:                    0
% 31.89/4.52  
%------------------------------------------------------------------------------
