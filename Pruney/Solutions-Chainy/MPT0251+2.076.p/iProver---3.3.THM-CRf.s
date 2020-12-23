%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:14 EST 2020

% Result     : Theorem 51.34s
% Output     : CNFRefutation 51.34s
% Verified   : 
% Statistics : Number of formulae       :  150 (3795 expanded)
%              Number of clauses        :   88 (1107 expanded)
%              Number of leaves         :   18 ( 874 expanded)
%              Depth                    :   24
%              Number of atoms          :  252 (7103 expanded)
%              Number of equality atoms :  140 (3668 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f32,f57,f57])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f58])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f57,f59])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK1),sK2) != sK2
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_xboole_0(k1_tarski(sK1),sK2) != sK2
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f30])).

fof(f55,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f59])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f56,plain,(
    k2_xboole_0(k1_tarski(sK1),sK2) != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != sK2 ),
    inference(definition_unfolding,[],[f56,f57,f60])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_665,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_656,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1394,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_656])).

cnf(c_1519,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1394])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_657,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1810,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1519,c_657])).

cnf(c_1903,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_1810,c_11])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_663,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5835,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1903,c_663])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_661,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5553,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1903,c_661])).

cnf(c_112494,plain,
    ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5835,c_5553])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_658,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1082,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_658,c_657])).

cnf(c_1291,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1082,c_11])).

cnf(c_1296,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1291,c_1082])).

cnf(c_5833,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_663])).

cnf(c_5551,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1296,c_661])).

cnf(c_93554,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5833,c_5551])).

cnf(c_93560,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_93554])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_659,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_96330,plain,
    ( k5_xboole_0(X0,X0) = X1
    | r1_tarski(X1,k5_xboole_0(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_93560,c_659])).

cnf(c_101782,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_93560,c_96330])).

cnf(c_101784,plain,
    ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_101782])).

cnf(c_112500,plain,
    ( r2_hidden(X0,sP0_iProver_split) != iProver_top ),
    inference(demodulation,[status(thm)],[c_112494,c_101784])).

cnf(c_112504,plain,
    ( r1_tarski(sP0_iProver_split,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_112500])).

cnf(c_112854,plain,
    ( k3_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
    inference(superposition,[status(thm)],[c_112504,c_657])).

cnf(c_113044,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split))) = k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,sP0_iProver_split)) ),
    inference(superposition,[status(thm)],[c_112854,c_0])).

cnf(c_16,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1401,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1082,c_16])).

cnf(c_1406,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1401,c_1296])).

cnf(c_1516,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_1394])).

cnf(c_2481,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1516,c_657])).

cnf(c_1404,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_16,c_0])).

cnf(c_3417,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_2481,c_1404])).

cnf(c_3426,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_1404,c_16])).

cnf(c_1083,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_656,c_657])).

cnf(c_2110,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1083,c_0])).

cnf(c_9830,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_16,c_2110])).

cnf(c_11381,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_9830,c_16])).

cnf(c_11453,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_11381])).

cnf(c_13032,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_3426,c_11453])).

cnf(c_103928,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)),sP0_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_3417,c_13032,c_101784])).

cnf(c_103942,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)),sP0_iProver_split) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(superposition,[status(thm)],[c_1406,c_103928])).

cnf(c_104292,plain,
    ( k5_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(light_normalisation,[status(thm)],[c_103942,c_1406])).

cnf(c_113160,plain,
    ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split))) = X0 ),
    inference(demodulation,[status(thm)],[c_113044,c_104292])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_653,plain,
    ( r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_664,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4415,plain,
    ( r2_hidden(sK1,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_653,c_664])).

cnf(c_4426,plain,
    ( r2_hidden(sK1,k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1516,c_4415])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_655,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2123,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_657])).

cnf(c_23919,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_4426,c_2123])).

cnf(c_30823,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_23919,c_0])).

cnf(c_32189,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_16,c_30823])).

cnf(c_114187,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[status(thm)],[c_113160,c_32189])).

cnf(c_1403,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_656])).

cnf(c_4425,plain,
    ( r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_4415])).

cnf(c_23918,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_4425,c_2123])).

cnf(c_30287,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_23918,c_0])).

cnf(c_31988,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(superposition,[status(thm)],[c_1406,c_30287])).

cnf(c_23907,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_653,c_2123])).

cnf(c_25409,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(superposition,[status(thm)],[c_23907,c_16])).

cnf(c_32072,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(demodulation,[status(thm)],[c_31988,c_1406,c_25409])).

cnf(c_114231,plain,
    ( k5_xboole_0(k3_tarski(k3_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_114187,c_32072])).

cnf(c_96331,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X1) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_93560,c_657])).

cnf(c_97332,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,X1))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_96331,c_16])).

cnf(c_103939,plain,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_16,c_103928])).

cnf(c_105714,plain,
    ( k3_tarski(k3_enumset1(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1))))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_97332,c_103939])).

cnf(c_105997,plain,
    ( k3_tarski(k3_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,k5_xboole_0(X1,X1))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,sP0_iProver_split)),sP0_iProver_split) ),
    inference(light_normalisation,[status(thm)],[c_105714,c_96331,c_101784])).

cnf(c_105998,plain,
    ( k3_tarski(k3_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_105997,c_101784,c_104292])).

cnf(c_114232,plain,
    ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_114231,c_101784,c_104292,c_105998])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1391,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))) != sK2 ),
    inference(demodulation,[status(thm)],[c_0,c_17])).

cnf(c_1532,plain,
    ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK2 ),
    inference(superposition,[status(thm)],[c_16,c_1391])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_114232,c_1532])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:59:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.34/7.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.34/7.00  
% 51.34/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.34/7.00  
% 51.34/7.00  ------  iProver source info
% 51.34/7.00  
% 51.34/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.34/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.34/7.00  git: non_committed_changes: false
% 51.34/7.00  git: last_make_outside_of_git: false
% 51.34/7.00  
% 51.34/7.00  ------ 
% 51.34/7.00  
% 51.34/7.00  ------ Input Options
% 51.34/7.00  
% 51.34/7.00  --out_options                           all
% 51.34/7.00  --tptp_safe_out                         true
% 51.34/7.00  --problem_path                          ""
% 51.34/7.00  --include_path                          ""
% 51.34/7.00  --clausifier                            res/vclausify_rel
% 51.34/7.00  --clausifier_options                    ""
% 51.34/7.00  --stdin                                 false
% 51.34/7.00  --stats_out                             all
% 51.34/7.00  
% 51.34/7.00  ------ General Options
% 51.34/7.00  
% 51.34/7.00  --fof                                   false
% 51.34/7.00  --time_out_real                         305.
% 51.34/7.00  --time_out_virtual                      -1.
% 51.34/7.00  --symbol_type_check                     false
% 51.34/7.00  --clausify_out                          false
% 51.34/7.00  --sig_cnt_out                           false
% 51.34/7.00  --trig_cnt_out                          false
% 51.34/7.00  --trig_cnt_out_tolerance                1.
% 51.34/7.00  --trig_cnt_out_sk_spl                   false
% 51.34/7.00  --abstr_cl_out                          false
% 51.34/7.00  
% 51.34/7.00  ------ Global Options
% 51.34/7.00  
% 51.34/7.00  --schedule                              default
% 51.34/7.00  --add_important_lit                     false
% 51.34/7.00  --prop_solver_per_cl                    1000
% 51.34/7.00  --min_unsat_core                        false
% 51.34/7.00  --soft_assumptions                      false
% 51.34/7.00  --soft_lemma_size                       3
% 51.34/7.00  --prop_impl_unit_size                   0
% 51.34/7.00  --prop_impl_unit                        []
% 51.34/7.00  --share_sel_clauses                     true
% 51.34/7.00  --reset_solvers                         false
% 51.34/7.00  --bc_imp_inh                            [conj_cone]
% 51.34/7.00  --conj_cone_tolerance                   3.
% 51.34/7.00  --extra_neg_conj                        none
% 51.34/7.00  --large_theory_mode                     true
% 51.34/7.00  --prolific_symb_bound                   200
% 51.34/7.00  --lt_threshold                          2000
% 51.34/7.00  --clause_weak_htbl                      true
% 51.34/7.00  --gc_record_bc_elim                     false
% 51.34/7.00  
% 51.34/7.00  ------ Preprocessing Options
% 51.34/7.00  
% 51.34/7.00  --preprocessing_flag                    true
% 51.34/7.00  --time_out_prep_mult                    0.1
% 51.34/7.00  --splitting_mode                        input
% 51.34/7.00  --splitting_grd                         true
% 51.34/7.00  --splitting_cvd                         false
% 51.34/7.00  --splitting_cvd_svl                     false
% 51.34/7.00  --splitting_nvd                         32
% 51.34/7.00  --sub_typing                            true
% 51.34/7.00  --prep_gs_sim                           true
% 51.34/7.00  --prep_unflatten                        true
% 51.34/7.00  --prep_res_sim                          true
% 51.34/7.00  --prep_upred                            true
% 51.34/7.00  --prep_sem_filter                       exhaustive
% 51.34/7.00  --prep_sem_filter_out                   false
% 51.34/7.00  --pred_elim                             true
% 51.34/7.00  --res_sim_input                         true
% 51.34/7.00  --eq_ax_congr_red                       true
% 51.34/7.00  --pure_diseq_elim                       true
% 51.34/7.00  --brand_transform                       false
% 51.34/7.00  --non_eq_to_eq                          false
% 51.34/7.00  --prep_def_merge                        true
% 51.34/7.00  --prep_def_merge_prop_impl              false
% 51.34/7.00  --prep_def_merge_mbd                    true
% 51.34/7.00  --prep_def_merge_tr_red                 false
% 51.34/7.00  --prep_def_merge_tr_cl                  false
% 51.34/7.00  --smt_preprocessing                     true
% 51.34/7.00  --smt_ac_axioms                         fast
% 51.34/7.00  --preprocessed_out                      false
% 51.34/7.00  --preprocessed_stats                    false
% 51.34/7.00  
% 51.34/7.00  ------ Abstraction refinement Options
% 51.34/7.00  
% 51.34/7.00  --abstr_ref                             []
% 51.34/7.00  --abstr_ref_prep                        false
% 51.34/7.00  --abstr_ref_until_sat                   false
% 51.34/7.00  --abstr_ref_sig_restrict                funpre
% 51.34/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.34/7.00  --abstr_ref_under                       []
% 51.34/7.00  
% 51.34/7.00  ------ SAT Options
% 51.34/7.00  
% 51.34/7.00  --sat_mode                              false
% 51.34/7.00  --sat_fm_restart_options                ""
% 51.34/7.00  --sat_gr_def                            false
% 51.34/7.00  --sat_epr_types                         true
% 51.34/7.00  --sat_non_cyclic_types                  false
% 51.34/7.00  --sat_finite_models                     false
% 51.34/7.00  --sat_fm_lemmas                         false
% 51.34/7.00  --sat_fm_prep                           false
% 51.34/7.00  --sat_fm_uc_incr                        true
% 51.34/7.00  --sat_out_model                         small
% 51.34/7.00  --sat_out_clauses                       false
% 51.34/7.00  
% 51.34/7.00  ------ QBF Options
% 51.34/7.00  
% 51.34/7.00  --qbf_mode                              false
% 51.34/7.00  --qbf_elim_univ                         false
% 51.34/7.00  --qbf_dom_inst                          none
% 51.34/7.00  --qbf_dom_pre_inst                      false
% 51.34/7.00  --qbf_sk_in                             false
% 51.34/7.00  --qbf_pred_elim                         true
% 51.34/7.00  --qbf_split                             512
% 51.34/7.00  
% 51.34/7.00  ------ BMC1 Options
% 51.34/7.00  
% 51.34/7.00  --bmc1_incremental                      false
% 51.34/7.00  --bmc1_axioms                           reachable_all
% 51.34/7.00  --bmc1_min_bound                        0
% 51.34/7.00  --bmc1_max_bound                        -1
% 51.34/7.00  --bmc1_max_bound_default                -1
% 51.34/7.00  --bmc1_symbol_reachability              true
% 51.34/7.00  --bmc1_property_lemmas                  false
% 51.34/7.00  --bmc1_k_induction                      false
% 51.34/7.00  --bmc1_non_equiv_states                 false
% 51.34/7.00  --bmc1_deadlock                         false
% 51.34/7.00  --bmc1_ucm                              false
% 51.34/7.00  --bmc1_add_unsat_core                   none
% 51.34/7.00  --bmc1_unsat_core_children              false
% 51.34/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.34/7.00  --bmc1_out_stat                         full
% 51.34/7.00  --bmc1_ground_init                      false
% 51.34/7.00  --bmc1_pre_inst_next_state              false
% 51.34/7.00  --bmc1_pre_inst_state                   false
% 51.34/7.00  --bmc1_pre_inst_reach_state             false
% 51.34/7.00  --bmc1_out_unsat_core                   false
% 51.34/7.00  --bmc1_aig_witness_out                  false
% 51.34/7.00  --bmc1_verbose                          false
% 51.34/7.00  --bmc1_dump_clauses_tptp                false
% 51.34/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.34/7.00  --bmc1_dump_file                        -
% 51.34/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.34/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.34/7.00  --bmc1_ucm_extend_mode                  1
% 51.34/7.00  --bmc1_ucm_init_mode                    2
% 51.34/7.00  --bmc1_ucm_cone_mode                    none
% 51.34/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.34/7.00  --bmc1_ucm_relax_model                  4
% 51.34/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.34/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.34/7.00  --bmc1_ucm_layered_model                none
% 51.34/7.00  --bmc1_ucm_max_lemma_size               10
% 51.34/7.00  
% 51.34/7.00  ------ AIG Options
% 51.34/7.00  
% 51.34/7.00  --aig_mode                              false
% 51.34/7.00  
% 51.34/7.00  ------ Instantiation Options
% 51.34/7.00  
% 51.34/7.00  --instantiation_flag                    true
% 51.34/7.00  --inst_sos_flag                         true
% 51.34/7.00  --inst_sos_phase                        true
% 51.34/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.34/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.34/7.00  --inst_lit_sel_side                     num_symb
% 51.34/7.00  --inst_solver_per_active                1400
% 51.34/7.00  --inst_solver_calls_frac                1.
% 51.34/7.00  --inst_passive_queue_type               priority_queues
% 51.34/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.34/7.00  --inst_passive_queues_freq              [25;2]
% 51.34/7.00  --inst_dismatching                      true
% 51.34/7.00  --inst_eager_unprocessed_to_passive     true
% 51.34/7.00  --inst_prop_sim_given                   true
% 51.34/7.00  --inst_prop_sim_new                     false
% 51.34/7.00  --inst_subs_new                         false
% 51.34/7.00  --inst_eq_res_simp                      false
% 51.34/7.00  --inst_subs_given                       false
% 51.34/7.00  --inst_orphan_elimination               true
% 51.34/7.00  --inst_learning_loop_flag               true
% 51.34/7.00  --inst_learning_start                   3000
% 51.34/7.00  --inst_learning_factor                  2
% 51.34/7.00  --inst_start_prop_sim_after_learn       3
% 51.34/7.00  --inst_sel_renew                        solver
% 51.34/7.00  --inst_lit_activity_flag                true
% 51.34/7.00  --inst_restr_to_given                   false
% 51.34/7.00  --inst_activity_threshold               500
% 51.34/7.00  --inst_out_proof                        true
% 51.34/7.00  
% 51.34/7.00  ------ Resolution Options
% 51.34/7.00  
% 51.34/7.00  --resolution_flag                       true
% 51.34/7.00  --res_lit_sel                           adaptive
% 51.34/7.00  --res_lit_sel_side                      none
% 51.34/7.00  --res_ordering                          kbo
% 51.34/7.00  --res_to_prop_solver                    active
% 51.34/7.00  --res_prop_simpl_new                    false
% 51.34/7.00  --res_prop_simpl_given                  true
% 51.34/7.00  --res_passive_queue_type                priority_queues
% 51.34/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.34/7.00  --res_passive_queues_freq               [15;5]
% 51.34/7.00  --res_forward_subs                      full
% 51.34/7.00  --res_backward_subs                     full
% 51.34/7.00  --res_forward_subs_resolution           true
% 51.34/7.00  --res_backward_subs_resolution          true
% 51.34/7.00  --res_orphan_elimination                true
% 51.34/7.00  --res_time_limit                        2.
% 51.34/7.00  --res_out_proof                         true
% 51.34/7.00  
% 51.34/7.00  ------ Superposition Options
% 51.34/7.00  
% 51.34/7.00  --superposition_flag                    true
% 51.34/7.00  --sup_passive_queue_type                priority_queues
% 51.34/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.34/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.34/7.00  --demod_completeness_check              fast
% 51.34/7.00  --demod_use_ground                      true
% 51.34/7.00  --sup_to_prop_solver                    passive
% 51.34/7.00  --sup_prop_simpl_new                    true
% 51.34/7.00  --sup_prop_simpl_given                  true
% 51.34/7.00  --sup_fun_splitting                     true
% 51.34/7.00  --sup_smt_interval                      50000
% 51.34/7.00  
% 51.34/7.00  ------ Superposition Simplification Setup
% 51.34/7.00  
% 51.34/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.34/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.34/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.34/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.34/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.34/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.34/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.34/7.00  --sup_immed_triv                        [TrivRules]
% 51.34/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.00  --sup_immed_bw_main                     []
% 51.34/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.34/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.34/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.00  --sup_input_bw                          []
% 51.34/7.00  
% 51.34/7.00  ------ Combination Options
% 51.34/7.00  
% 51.34/7.00  --comb_res_mult                         3
% 51.34/7.00  --comb_sup_mult                         2
% 51.34/7.00  --comb_inst_mult                        10
% 51.34/7.00  
% 51.34/7.00  ------ Debug Options
% 51.34/7.00  
% 51.34/7.00  --dbg_backtrace                         false
% 51.34/7.00  --dbg_dump_prop_clauses                 false
% 51.34/7.00  --dbg_dump_prop_clauses_file            -
% 51.34/7.00  --dbg_out_stat                          false
% 51.34/7.00  ------ Parsing...
% 51.34/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.34/7.00  
% 51.34/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 51.34/7.00  
% 51.34/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.34/7.00  
% 51.34/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.34/7.00  ------ Proving...
% 51.34/7.00  ------ Problem Properties 
% 51.34/7.00  
% 51.34/7.00  
% 51.34/7.00  clauses                                 18
% 51.34/7.00  conjectures                             2
% 51.34/7.00  EPR                                     4
% 51.34/7.00  Horn                                    14
% 51.34/7.00  unary                                   7
% 51.34/7.00  binary                                  5
% 51.34/7.00  lits                                    35
% 51.34/7.00  lits eq                                 6
% 51.34/7.00  fd_pure                                 0
% 51.34/7.00  fd_pseudo                               0
% 51.34/7.00  fd_cond                                 0
% 51.34/7.00  fd_pseudo_cond                          1
% 51.34/7.00  AC symbols                              0
% 51.34/7.00  
% 51.34/7.00  ------ Schedule dynamic 5 is on 
% 51.34/7.00  
% 51.34/7.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.34/7.00  
% 51.34/7.00  
% 51.34/7.00  ------ 
% 51.34/7.00  Current options:
% 51.34/7.00  ------ 
% 51.34/7.00  
% 51.34/7.00  ------ Input Options
% 51.34/7.00  
% 51.34/7.00  --out_options                           all
% 51.34/7.00  --tptp_safe_out                         true
% 51.34/7.00  --problem_path                          ""
% 51.34/7.00  --include_path                          ""
% 51.34/7.00  --clausifier                            res/vclausify_rel
% 51.34/7.00  --clausifier_options                    ""
% 51.34/7.00  --stdin                                 false
% 51.34/7.00  --stats_out                             all
% 51.34/7.00  
% 51.34/7.00  ------ General Options
% 51.34/7.00  
% 51.34/7.00  --fof                                   false
% 51.34/7.00  --time_out_real                         305.
% 51.34/7.00  --time_out_virtual                      -1.
% 51.34/7.00  --symbol_type_check                     false
% 51.34/7.00  --clausify_out                          false
% 51.34/7.00  --sig_cnt_out                           false
% 51.34/7.00  --trig_cnt_out                          false
% 51.34/7.00  --trig_cnt_out_tolerance                1.
% 51.34/7.00  --trig_cnt_out_sk_spl                   false
% 51.34/7.00  --abstr_cl_out                          false
% 51.34/7.00  
% 51.34/7.00  ------ Global Options
% 51.34/7.00  
% 51.34/7.00  --schedule                              default
% 51.34/7.00  --add_important_lit                     false
% 51.34/7.00  --prop_solver_per_cl                    1000
% 51.34/7.00  --min_unsat_core                        false
% 51.34/7.00  --soft_assumptions                      false
% 51.34/7.00  --soft_lemma_size                       3
% 51.34/7.00  --prop_impl_unit_size                   0
% 51.34/7.00  --prop_impl_unit                        []
% 51.34/7.00  --share_sel_clauses                     true
% 51.34/7.00  --reset_solvers                         false
% 51.34/7.00  --bc_imp_inh                            [conj_cone]
% 51.34/7.00  --conj_cone_tolerance                   3.
% 51.34/7.00  --extra_neg_conj                        none
% 51.34/7.00  --large_theory_mode                     true
% 51.34/7.00  --prolific_symb_bound                   200
% 51.34/7.00  --lt_threshold                          2000
% 51.34/7.00  --clause_weak_htbl                      true
% 51.34/7.00  --gc_record_bc_elim                     false
% 51.34/7.00  
% 51.34/7.00  ------ Preprocessing Options
% 51.34/7.00  
% 51.34/7.00  --preprocessing_flag                    true
% 51.34/7.00  --time_out_prep_mult                    0.1
% 51.34/7.00  --splitting_mode                        input
% 51.34/7.00  --splitting_grd                         true
% 51.34/7.00  --splitting_cvd                         false
% 51.34/7.00  --splitting_cvd_svl                     false
% 51.34/7.00  --splitting_nvd                         32
% 51.34/7.00  --sub_typing                            true
% 51.34/7.00  --prep_gs_sim                           true
% 51.34/7.00  --prep_unflatten                        true
% 51.34/7.00  --prep_res_sim                          true
% 51.34/7.00  --prep_upred                            true
% 51.34/7.00  --prep_sem_filter                       exhaustive
% 51.34/7.00  --prep_sem_filter_out                   false
% 51.34/7.00  --pred_elim                             true
% 51.34/7.00  --res_sim_input                         true
% 51.34/7.00  --eq_ax_congr_red                       true
% 51.34/7.00  --pure_diseq_elim                       true
% 51.34/7.00  --brand_transform                       false
% 51.34/7.00  --non_eq_to_eq                          false
% 51.34/7.00  --prep_def_merge                        true
% 51.34/7.00  --prep_def_merge_prop_impl              false
% 51.34/7.00  --prep_def_merge_mbd                    true
% 51.34/7.00  --prep_def_merge_tr_red                 false
% 51.34/7.00  --prep_def_merge_tr_cl                  false
% 51.34/7.00  --smt_preprocessing                     true
% 51.34/7.00  --smt_ac_axioms                         fast
% 51.34/7.00  --preprocessed_out                      false
% 51.34/7.00  --preprocessed_stats                    false
% 51.34/7.00  
% 51.34/7.00  ------ Abstraction refinement Options
% 51.34/7.00  
% 51.34/7.00  --abstr_ref                             []
% 51.34/7.00  --abstr_ref_prep                        false
% 51.34/7.00  --abstr_ref_until_sat                   false
% 51.34/7.00  --abstr_ref_sig_restrict                funpre
% 51.34/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.34/7.00  --abstr_ref_under                       []
% 51.34/7.00  
% 51.34/7.00  ------ SAT Options
% 51.34/7.00  
% 51.34/7.00  --sat_mode                              false
% 51.34/7.00  --sat_fm_restart_options                ""
% 51.34/7.00  --sat_gr_def                            false
% 51.34/7.00  --sat_epr_types                         true
% 51.34/7.00  --sat_non_cyclic_types                  false
% 51.34/7.00  --sat_finite_models                     false
% 51.34/7.00  --sat_fm_lemmas                         false
% 51.34/7.00  --sat_fm_prep                           false
% 51.34/7.00  --sat_fm_uc_incr                        true
% 51.34/7.00  --sat_out_model                         small
% 51.34/7.00  --sat_out_clauses                       false
% 51.34/7.00  
% 51.34/7.00  ------ QBF Options
% 51.34/7.00  
% 51.34/7.00  --qbf_mode                              false
% 51.34/7.00  --qbf_elim_univ                         false
% 51.34/7.00  --qbf_dom_inst                          none
% 51.34/7.00  --qbf_dom_pre_inst                      false
% 51.34/7.00  --qbf_sk_in                             false
% 51.34/7.00  --qbf_pred_elim                         true
% 51.34/7.00  --qbf_split                             512
% 51.34/7.00  
% 51.34/7.00  ------ BMC1 Options
% 51.34/7.00  
% 51.34/7.00  --bmc1_incremental                      false
% 51.34/7.00  --bmc1_axioms                           reachable_all
% 51.34/7.00  --bmc1_min_bound                        0
% 51.34/7.00  --bmc1_max_bound                        -1
% 51.34/7.00  --bmc1_max_bound_default                -1
% 51.34/7.00  --bmc1_symbol_reachability              true
% 51.34/7.00  --bmc1_property_lemmas                  false
% 51.34/7.00  --bmc1_k_induction                      false
% 51.34/7.00  --bmc1_non_equiv_states                 false
% 51.34/7.00  --bmc1_deadlock                         false
% 51.34/7.00  --bmc1_ucm                              false
% 51.34/7.00  --bmc1_add_unsat_core                   none
% 51.34/7.00  --bmc1_unsat_core_children              false
% 51.34/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.34/7.00  --bmc1_out_stat                         full
% 51.34/7.00  --bmc1_ground_init                      false
% 51.34/7.00  --bmc1_pre_inst_next_state              false
% 51.34/7.00  --bmc1_pre_inst_state                   false
% 51.34/7.00  --bmc1_pre_inst_reach_state             false
% 51.34/7.00  --bmc1_out_unsat_core                   false
% 51.34/7.00  --bmc1_aig_witness_out                  false
% 51.34/7.00  --bmc1_verbose                          false
% 51.34/7.00  --bmc1_dump_clauses_tptp                false
% 51.34/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.34/7.00  --bmc1_dump_file                        -
% 51.34/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.34/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.34/7.00  --bmc1_ucm_extend_mode                  1
% 51.34/7.00  --bmc1_ucm_init_mode                    2
% 51.34/7.00  --bmc1_ucm_cone_mode                    none
% 51.34/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.34/7.00  --bmc1_ucm_relax_model                  4
% 51.34/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.34/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.34/7.00  --bmc1_ucm_layered_model                none
% 51.34/7.00  --bmc1_ucm_max_lemma_size               10
% 51.34/7.00  
% 51.34/7.00  ------ AIG Options
% 51.34/7.00  
% 51.34/7.00  --aig_mode                              false
% 51.34/7.00  
% 51.34/7.00  ------ Instantiation Options
% 51.34/7.00  
% 51.34/7.00  --instantiation_flag                    true
% 51.34/7.00  --inst_sos_flag                         true
% 51.34/7.00  --inst_sos_phase                        true
% 51.34/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.34/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.34/7.00  --inst_lit_sel_side                     none
% 51.34/7.00  --inst_solver_per_active                1400
% 51.34/7.00  --inst_solver_calls_frac                1.
% 51.34/7.00  --inst_passive_queue_type               priority_queues
% 51.34/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.34/7.00  --inst_passive_queues_freq              [25;2]
% 51.34/7.00  --inst_dismatching                      true
% 51.34/7.00  --inst_eager_unprocessed_to_passive     true
% 51.34/7.00  --inst_prop_sim_given                   true
% 51.34/7.00  --inst_prop_sim_new                     false
% 51.34/7.00  --inst_subs_new                         false
% 51.34/7.00  --inst_eq_res_simp                      false
% 51.34/7.00  --inst_subs_given                       false
% 51.34/7.00  --inst_orphan_elimination               true
% 51.34/7.00  --inst_learning_loop_flag               true
% 51.34/7.00  --inst_learning_start                   3000
% 51.34/7.00  --inst_learning_factor                  2
% 51.34/7.00  --inst_start_prop_sim_after_learn       3
% 51.34/7.00  --inst_sel_renew                        solver
% 51.34/7.00  --inst_lit_activity_flag                true
% 51.34/7.00  --inst_restr_to_given                   false
% 51.34/7.00  --inst_activity_threshold               500
% 51.34/7.00  --inst_out_proof                        true
% 51.34/7.00  
% 51.34/7.00  ------ Resolution Options
% 51.34/7.00  
% 51.34/7.00  --resolution_flag                       false
% 51.34/7.00  --res_lit_sel                           adaptive
% 51.34/7.00  --res_lit_sel_side                      none
% 51.34/7.00  --res_ordering                          kbo
% 51.34/7.00  --res_to_prop_solver                    active
% 51.34/7.00  --res_prop_simpl_new                    false
% 51.34/7.00  --res_prop_simpl_given                  true
% 51.34/7.00  --res_passive_queue_type                priority_queues
% 51.34/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.34/7.00  --res_passive_queues_freq               [15;5]
% 51.34/7.00  --res_forward_subs                      full
% 51.34/7.00  --res_backward_subs                     full
% 51.34/7.00  --res_forward_subs_resolution           true
% 51.34/7.00  --res_backward_subs_resolution          true
% 51.34/7.00  --res_orphan_elimination                true
% 51.34/7.00  --res_time_limit                        2.
% 51.34/7.00  --res_out_proof                         true
% 51.34/7.00  
% 51.34/7.00  ------ Superposition Options
% 51.34/7.00  
% 51.34/7.00  --superposition_flag                    true
% 51.34/7.00  --sup_passive_queue_type                priority_queues
% 51.34/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.34/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.34/7.00  --demod_completeness_check              fast
% 51.34/7.00  --demod_use_ground                      true
% 51.34/7.00  --sup_to_prop_solver                    passive
% 51.34/7.00  --sup_prop_simpl_new                    true
% 51.34/7.00  --sup_prop_simpl_given                  true
% 51.34/7.00  --sup_fun_splitting                     true
% 51.34/7.00  --sup_smt_interval                      50000
% 51.34/7.00  
% 51.34/7.00  ------ Superposition Simplification Setup
% 51.34/7.00  
% 51.34/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.34/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.34/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.34/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.34/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.34/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.34/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.34/7.00  --sup_immed_triv                        [TrivRules]
% 51.34/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.00  --sup_immed_bw_main                     []
% 51.34/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.34/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.34/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.34/7.00  --sup_input_bw                          []
% 51.34/7.00  
% 51.34/7.00  ------ Combination Options
% 51.34/7.00  
% 51.34/7.00  --comb_res_mult                         3
% 51.34/7.00  --comb_sup_mult                         2
% 51.34/7.00  --comb_inst_mult                        10
% 51.34/7.00  
% 51.34/7.00  ------ Debug Options
% 51.34/7.00  
% 51.34/7.00  --dbg_backtrace                         false
% 51.34/7.00  --dbg_dump_prop_clauses                 false
% 51.34/7.00  --dbg_dump_prop_clauses_file            -
% 51.34/7.00  --dbg_out_stat                          false
% 51.34/7.00  
% 51.34/7.00  
% 51.34/7.00  
% 51.34/7.00  
% 51.34/7.00  ------ Proving...
% 51.34/7.00  
% 51.34/7.00  
% 51.34/7.00  % SZS status Theorem for theBenchmark.p
% 51.34/7.00  
% 51.34/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.34/7.00  
% 51.34/7.00  fof(f2,axiom,(
% 51.34/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f18,plain,(
% 51.34/7.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 51.34/7.00    inference(ennf_transformation,[],[f2])).
% 51.34/7.00  
% 51.34/7.00  fof(f22,plain,(
% 51.34/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 51.34/7.00    inference(nnf_transformation,[],[f18])).
% 51.34/7.00  
% 51.34/7.00  fof(f23,plain,(
% 51.34/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.34/7.00    inference(rectify,[],[f22])).
% 51.34/7.00  
% 51.34/7.00  fof(f24,plain,(
% 51.34/7.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 51.34/7.00    introduced(choice_axiom,[])).
% 51.34/7.00  
% 51.34/7.00  fof(f25,plain,(
% 51.34/7.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 51.34/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 51.34/7.00  
% 51.34/7.00  fof(f34,plain,(
% 51.34/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f25])).
% 51.34/7.00  
% 51.34/7.00  fof(f6,axiom,(
% 51.34/7.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f44,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 51.34/7.00    inference(cnf_transformation,[],[f6])).
% 51.34/7.00  
% 51.34/7.00  fof(f9,axiom,(
% 51.34/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f47,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 51.34/7.00    inference(cnf_transformation,[],[f9])).
% 51.34/7.00  
% 51.34/7.00  fof(f5,axiom,(
% 51.34/7.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f43,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f5])).
% 51.34/7.00  
% 51.34/7.00  fof(f57,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 51.34/7.00    inference(definition_unfolding,[],[f47,f43])).
% 51.34/7.00  
% 51.34/7.00  fof(f62,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 51.34/7.00    inference(definition_unfolding,[],[f44,f57])).
% 51.34/7.00  
% 51.34/7.00  fof(f1,axiom,(
% 51.34/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f32,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f1])).
% 51.34/7.00  
% 51.34/7.00  fof(f61,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 51.34/7.00    inference(definition_unfolding,[],[f32,f57,f57])).
% 51.34/7.00  
% 51.34/7.00  fof(f8,axiom,(
% 51.34/7.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f46,plain,(
% 51.34/7.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 51.34/7.00    inference(cnf_transformation,[],[f8])).
% 51.34/7.00  
% 51.34/7.00  fof(f63,plain,(
% 51.34/7.00    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 51.34/7.00    inference(definition_unfolding,[],[f46,f57])).
% 51.34/7.00  
% 51.34/7.00  fof(f7,axiom,(
% 51.34/7.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f20,plain,(
% 51.34/7.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 51.34/7.00    inference(ennf_transformation,[],[f7])).
% 51.34/7.00  
% 51.34/7.00  fof(f45,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f20])).
% 51.34/7.00  
% 51.34/7.00  fof(f3,axiom,(
% 51.34/7.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f19,plain,(
% 51.34/7.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 51.34/7.00    inference(ennf_transformation,[],[f3])).
% 51.34/7.00  
% 51.34/7.00  fof(f26,plain,(
% 51.34/7.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 51.34/7.00    inference(nnf_transformation,[],[f19])).
% 51.34/7.00  
% 51.34/7.00  fof(f39,plain,(
% 51.34/7.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f26])).
% 51.34/7.00  
% 51.34/7.00  fof(f37,plain,(
% 51.34/7.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 51.34/7.00    inference(cnf_transformation,[],[f26])).
% 51.34/7.00  
% 51.34/7.00  fof(f4,axiom,(
% 51.34/7.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f27,plain,(
% 51.34/7.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.34/7.00    inference(nnf_transformation,[],[f4])).
% 51.34/7.00  
% 51.34/7.00  fof(f28,plain,(
% 51.34/7.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 51.34/7.00    inference(flattening,[],[f27])).
% 51.34/7.00  
% 51.34/7.00  fof(f40,plain,(
% 51.34/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 51.34/7.00    inference(cnf_transformation,[],[f28])).
% 51.34/7.00  
% 51.34/7.00  fof(f69,plain,(
% 51.34/7.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 51.34/7.00    inference(equality_resolution,[],[f40])).
% 51.34/7.00  
% 51.34/7.00  fof(f42,plain,(
% 51.34/7.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f28])).
% 51.34/7.00  
% 51.34/7.00  fof(f15,axiom,(
% 51.34/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f54,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 51.34/7.00    inference(cnf_transformation,[],[f15])).
% 51.34/7.00  
% 51.34/7.00  fof(f11,axiom,(
% 51.34/7.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f49,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f11])).
% 51.34/7.00  
% 51.34/7.00  fof(f12,axiom,(
% 51.34/7.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f50,plain,(
% 51.34/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f12])).
% 51.34/7.00  
% 51.34/7.00  fof(f13,axiom,(
% 51.34/7.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f51,plain,(
% 51.34/7.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f13])).
% 51.34/7.00  
% 51.34/7.00  fof(f58,plain,(
% 51.34/7.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 51.34/7.00    inference(definition_unfolding,[],[f50,f51])).
% 51.34/7.00  
% 51.34/7.00  fof(f59,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 51.34/7.00    inference(definition_unfolding,[],[f49,f58])).
% 51.34/7.00  
% 51.34/7.00  fof(f66,plain,(
% 51.34/7.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 51.34/7.00    inference(definition_unfolding,[],[f54,f57,f59])).
% 51.34/7.00  
% 51.34/7.00  fof(f16,conjecture,(
% 51.34/7.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f17,negated_conjecture,(
% 51.34/7.00    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 51.34/7.00    inference(negated_conjecture,[],[f16])).
% 51.34/7.00  
% 51.34/7.00  fof(f21,plain,(
% 51.34/7.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 51.34/7.00    inference(ennf_transformation,[],[f17])).
% 51.34/7.00  
% 51.34/7.00  fof(f30,plain,(
% 51.34/7.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK1),sK2) != sK2 & r2_hidden(sK1,sK2))),
% 51.34/7.00    introduced(choice_axiom,[])).
% 51.34/7.00  
% 51.34/7.00  fof(f31,plain,(
% 51.34/7.00    k2_xboole_0(k1_tarski(sK1),sK2) != sK2 & r2_hidden(sK1,sK2)),
% 51.34/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f30])).
% 51.34/7.00  
% 51.34/7.00  fof(f55,plain,(
% 51.34/7.00    r2_hidden(sK1,sK2)),
% 51.34/7.00    inference(cnf_transformation,[],[f31])).
% 51.34/7.00  
% 51.34/7.00  fof(f33,plain,(
% 51.34/7.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f25])).
% 51.34/7.00  
% 51.34/7.00  fof(f14,axiom,(
% 51.34/7.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f29,plain,(
% 51.34/7.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 51.34/7.00    inference(nnf_transformation,[],[f14])).
% 51.34/7.00  
% 51.34/7.00  fof(f53,plain,(
% 51.34/7.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f29])).
% 51.34/7.00  
% 51.34/7.00  fof(f10,axiom,(
% 51.34/7.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 51.34/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.34/7.00  
% 51.34/7.00  fof(f48,plain,(
% 51.34/7.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 51.34/7.00    inference(cnf_transformation,[],[f10])).
% 51.34/7.00  
% 51.34/7.00  fof(f60,plain,(
% 51.34/7.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 51.34/7.00    inference(definition_unfolding,[],[f48,f59])).
% 51.34/7.00  
% 51.34/7.00  fof(f64,plain,(
% 51.34/7.00    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 51.34/7.00    inference(definition_unfolding,[],[f53,f60])).
% 51.34/7.00  
% 51.34/7.00  fof(f56,plain,(
% 51.34/7.00    k2_xboole_0(k1_tarski(sK1),sK2) != sK2),
% 51.34/7.00    inference(cnf_transformation,[],[f31])).
% 51.34/7.00  
% 51.34/7.00  fof(f67,plain,(
% 51.34/7.00    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != sK2),
% 51.34/7.00    inference(definition_unfolding,[],[f56,f57,f60])).
% 51.34/7.00  
% 51.34/7.00  cnf(c_2,plain,
% 51.34/7.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 51.34/7.00      inference(cnf_transformation,[],[f34]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_665,plain,
% 51.34/7.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 51.34/7.00      | r1_tarski(X0,X1) = iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_11,plain,
% 51.34/7.00      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 51.34/7.00      inference(cnf_transformation,[],[f62]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_0,plain,
% 51.34/7.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 51.34/7.00      inference(cnf_transformation,[],[f61]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_13,plain,
% 51.34/7.00      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 51.34/7.00      inference(cnf_transformation,[],[f63]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_656,plain,
% 51.34/7.00      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1394,plain,
% 51.34/7.00      ( r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_0,c_656]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1519,plain,
% 51.34/7.00      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_11,c_1394]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_12,plain,
% 51.34/7.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 51.34/7.00      inference(cnf_transformation,[],[f45]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_657,plain,
% 51.34/7.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1810,plain,
% 51.34/7.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1519,c_657]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1903,plain,
% 51.34/7.00      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
% 51.34/7.00      inference(demodulation,[status(thm)],[c_1810,c_11]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_4,plain,
% 51.34/7.00      ( ~ r2_hidden(X0,X1)
% 51.34/7.00      | r2_hidden(X0,X2)
% 51.34/7.00      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 51.34/7.00      inference(cnf_transformation,[],[f39]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_663,plain,
% 51.34/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.34/7.00      | r2_hidden(X0,X2) = iProver_top
% 51.34/7.00      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_5835,plain,
% 51.34/7.00      ( r2_hidden(X0,X1) = iProver_top
% 51.34/7.00      | r2_hidden(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))) != iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1903,c_663]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_6,plain,
% 51.34/7.00      ( ~ r2_hidden(X0,X1)
% 51.34/7.00      | ~ r2_hidden(X0,X2)
% 51.34/7.00      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 51.34/7.00      inference(cnf_transformation,[],[f37]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_661,plain,
% 51.34/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.34/7.00      | r2_hidden(X0,X2) != iProver_top
% 51.34/7.00      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_5553,plain,
% 51.34/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.34/7.00      | r2_hidden(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))) != iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1903,c_661]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_112494,plain,
% 51.34/7.00      ( r2_hidden(X0,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))) != iProver_top ),
% 51.34/7.00      inference(global_propositional_subsumption,
% 51.34/7.00                [status(thm)],
% 51.34/7.00                [c_5835,c_5553]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_10,plain,
% 51.34/7.00      ( r1_tarski(X0,X0) ),
% 51.34/7.00      inference(cnf_transformation,[],[f69]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_658,plain,
% 51.34/7.00      ( r1_tarski(X0,X0) = iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1082,plain,
% 51.34/7.00      ( k3_xboole_0(X0,X0) = X0 ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_658,c_657]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1291,plain,
% 51.34/7.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1082,c_11]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1296,plain,
% 51.34/7.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 51.34/7.00      inference(light_normalisation,[status(thm)],[c_1291,c_1082]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_5833,plain,
% 51.34/7.00      ( r2_hidden(X0,X1) = iProver_top
% 51.34/7.00      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1296,c_663]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_5551,plain,
% 51.34/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.34/7.00      | r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1296,c_661]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_93554,plain,
% 51.34/7.00      ( r2_hidden(X0,k5_xboole_0(X1,X1)) != iProver_top ),
% 51.34/7.00      inference(global_propositional_subsumption,
% 51.34/7.00                [status(thm)],
% 51.34/7.00                [c_5833,c_5551]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_93560,plain,
% 51.34/7.00      ( r1_tarski(k5_xboole_0(X0,X0),X1) = iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_665,c_93554]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_8,plain,
% 51.34/7.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 51.34/7.00      inference(cnf_transformation,[],[f42]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_659,plain,
% 51.34/7.00      ( X0 = X1
% 51.34/7.00      | r1_tarski(X1,X0) != iProver_top
% 51.34/7.00      | r1_tarski(X0,X1) != iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_96330,plain,
% 51.34/7.00      ( k5_xboole_0(X0,X0) = X1
% 51.34/7.00      | r1_tarski(X1,k5_xboole_0(X0,X0)) != iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_93560,c_659]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_101782,plain,
% 51.34/7.00      ( k5_xboole_0(X0,X0) = k5_xboole_0(X1,X1) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_93560,c_96330]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_101784,plain,
% 51.34/7.00      ( k5_xboole_0(X0,X0) = sP0_iProver_split ),
% 51.34/7.00      inference(splitting,
% 51.34/7.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 51.34/7.00                [c_101782]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_112500,plain,
% 51.34/7.00      ( r2_hidden(X0,sP0_iProver_split) != iProver_top ),
% 51.34/7.00      inference(demodulation,[status(thm)],[c_112494,c_101784]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_112504,plain,
% 51.34/7.00      ( r1_tarski(sP0_iProver_split,X0) = iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_665,c_112500]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_112854,plain,
% 51.34/7.00      ( k3_xboole_0(sP0_iProver_split,X0) = sP0_iProver_split ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_112504,c_657]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_113044,plain,
% 51.34/7.00      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split))) = k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,sP0_iProver_split)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_112854,c_0]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_16,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 51.34/7.00      inference(cnf_transformation,[],[f66]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1401,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1082,c_16]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1406,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 51.34/7.00      inference(light_normalisation,[status(thm)],[c_1401,c_1296]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1516,plain,
% 51.34/7.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_16,c_1394]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_2481,plain,
% 51.34/7.00      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) = X0 ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1516,c_657]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1404,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_16,c_0]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_3417,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)),k5_xboole_0(X0,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_2481,c_1404]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_3426,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1404,c_16]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1083,plain,
% 51.34/7.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_656,c_657]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_2110,plain,
% 51.34/7.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1083,c_0]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_9830,plain,
% 51.34/7.00      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_16,c_2110]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_11381,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_9830,c_16]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_11453,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_0,c_11381]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_13032,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))),k5_xboole_0(X0,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_3426,c_11453]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_103928,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))) = k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)),sP0_iProver_split) ),
% 51.34/7.00      inference(light_normalisation,
% 51.34/7.00                [status(thm)],
% 51.34/7.00                [c_3417,c_13032,c_101784]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_103942,plain,
% 51.34/7.00      ( k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)),sP0_iProver_split) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1406,c_103928]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_104292,plain,
% 51.34/7.00      ( k5_xboole_0(X0,sP0_iProver_split) = X0 ),
% 51.34/7.00      inference(light_normalisation,[status(thm)],[c_103942,c_1406]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_113160,plain,
% 51.34/7.00      ( k5_xboole_0(sP0_iProver_split,k5_xboole_0(X0,k3_xboole_0(X0,sP0_iProver_split))) = X0 ),
% 51.34/7.00      inference(demodulation,[status(thm)],[c_113044,c_104292]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_18,negated_conjecture,
% 51.34/7.00      ( r2_hidden(sK1,sK2) ),
% 51.34/7.00      inference(cnf_transformation,[],[f55]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_653,plain,
% 51.34/7.00      ( r2_hidden(sK1,sK2) = iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_3,plain,
% 51.34/7.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 51.34/7.00      inference(cnf_transformation,[],[f33]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_664,plain,
% 51.34/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.34/7.00      | r2_hidden(X0,X2) = iProver_top
% 51.34/7.00      | r1_tarski(X1,X2) != iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_4415,plain,
% 51.34/7.00      ( r2_hidden(sK1,X0) = iProver_top
% 51.34/7.00      | r1_tarski(sK2,X0) != iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_653,c_664]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_4426,plain,
% 51.34/7.00      ( r2_hidden(sK1,k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2))) = iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1516,c_4415]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_14,plain,
% 51.34/7.00      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 51.34/7.00      inference(cnf_transformation,[],[f64]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_655,plain,
% 51.34/7.00      ( r2_hidden(X0,X1) != iProver_top
% 51.34/7.00      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) = iProver_top ),
% 51.34/7.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_2123,plain,
% 51.34/7.00      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) = k3_enumset1(X0,X0,X0,X0,X0)
% 51.34/7.00      | r2_hidden(X0,X1) != iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_655,c_657]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_23919,plain,
% 51.34/7.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_4426,c_2123]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_30823,plain,
% 51.34/7.00      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_23919,c_0]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_32189,plain,
% 51.34/7.00      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_16,c_30823]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_114187,plain,
% 51.34/7.00      ( k5_xboole_0(k3_tarski(k3_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_113160,c_32189]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1403,plain,
% 51.34/7.00      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_16,c_656]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_4425,plain,
% 51.34/7.00      ( r2_hidden(sK1,k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0))) = iProver_top ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1403,c_4415]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_23918,plain,
% 51.34/7.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_4425,c_2123]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_30287,plain,
% 51.34/7.00      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),k3_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_23918,c_0]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_31988,plain,
% 51.34/7.00      ( k5_xboole_0(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_1406,c_30287]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_23907,plain,
% 51.34/7.00      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_653,c_2123]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_25409,plain,
% 51.34/7.00      ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_23907,c_16]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_32072,plain,
% 51.34/7.00      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 51.34/7.00      inference(demodulation,[status(thm)],[c_31988,c_1406,c_25409]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_114231,plain,
% 51.34/7.00      ( k5_xboole_0(k3_tarski(k3_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
% 51.34/7.00      inference(light_normalisation,[status(thm)],[c_114187,c_32072]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_96331,plain,
% 51.34/7.00      ( k3_xboole_0(k5_xboole_0(X0,X0),X1) = k5_xboole_0(X0,X0) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_93560,c_657]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_97332,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,X1))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X1),k5_xboole_0(X1,X1))) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_96331,c_16]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_103939,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = k5_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)),sP0_iProver_split) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_16,c_103928]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_105714,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X0,X0),k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(k5_xboole_0(X0,X0),X1))))) = k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0))),sP0_iProver_split) ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_97332,c_103939]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_105997,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,k5_xboole_0(X1,X1))))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sP0_iProver_split,sP0_iProver_split)),sP0_iProver_split) ),
% 51.34/7.00      inference(light_normalisation,
% 51.34/7.00                [status(thm)],
% 51.34/7.00                [c_105714,c_96331,c_101784]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_105998,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,sP0_iProver_split,X0)) = X0 ),
% 51.34/7.00      inference(demodulation,[status(thm)],[c_105997,c_101784,c_104292]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_114232,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = sK2 ),
% 51.34/7.00      inference(demodulation,
% 51.34/7.00                [status(thm)],
% 51.34/7.00                [c_114231,c_101784,c_104292,c_105998]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_17,negated_conjecture,
% 51.34/7.00      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != sK2 ),
% 51.34/7.00      inference(cnf_transformation,[],[f67]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1391,plain,
% 51.34/7.00      ( k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK2))) != sK2 ),
% 51.34/7.00      inference(demodulation,[status(thm)],[c_0,c_17]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(c_1532,plain,
% 51.34/7.00      ( k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != sK2 ),
% 51.34/7.00      inference(superposition,[status(thm)],[c_16,c_1391]) ).
% 51.34/7.00  
% 51.34/7.00  cnf(contradiction,plain,
% 51.34/7.00      ( $false ),
% 51.34/7.00      inference(minisat,[status(thm)],[c_114232,c_1532]) ).
% 51.34/7.00  
% 51.34/7.00  
% 51.34/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.34/7.00  
% 51.34/7.00  ------                               Statistics
% 51.34/7.00  
% 51.34/7.00  ------ General
% 51.34/7.00  
% 51.34/7.00  abstr_ref_over_cycles:                  0
% 51.34/7.00  abstr_ref_under_cycles:                 0
% 51.34/7.00  gc_basic_clause_elim:                   0
% 51.34/7.00  forced_gc_time:                         0
% 51.34/7.00  parsing_time:                           0.009
% 51.34/7.00  unif_index_cands_time:                  0.
% 51.34/7.00  unif_index_add_time:                    0.
% 51.34/7.00  orderings_time:                         0.
% 51.34/7.00  out_proof_time:                         0.016
% 51.34/7.00  total_time:                             6.184
% 51.34/7.00  num_of_symbols:                         41
% 51.34/7.00  num_of_terms:                           112706
% 51.34/7.00  
% 51.34/7.00  ------ Preprocessing
% 51.34/7.00  
% 51.34/7.00  num_of_splits:                          0
% 51.34/7.00  num_of_split_atoms:                     1
% 51.34/7.00  num_of_reused_defs:                     0
% 51.34/7.00  num_eq_ax_congr_red:                    6
% 51.34/7.00  num_of_sem_filtered_clauses:            1
% 51.34/7.00  num_of_subtypes:                        0
% 51.34/7.00  monotx_restored_types:                  0
% 51.34/7.00  sat_num_of_epr_types:                   0
% 51.34/7.00  sat_num_of_non_cyclic_types:            0
% 51.34/7.00  sat_guarded_non_collapsed_types:        0
% 51.34/7.00  num_pure_diseq_elim:                    0
% 51.34/7.00  simp_replaced_by:                       0
% 51.34/7.00  res_preprocessed:                       89
% 51.34/7.00  prep_upred:                             0
% 51.34/7.00  prep_unflattend:                        0
% 51.34/7.00  smt_new_axioms:                         0
% 51.34/7.00  pred_elim_cands:                        2
% 51.34/7.00  pred_elim:                              0
% 51.34/7.00  pred_elim_cl:                           0
% 51.34/7.00  pred_elim_cycles:                       2
% 51.34/7.00  merged_defs:                            8
% 51.34/7.00  merged_defs_ncl:                        0
% 51.34/7.00  bin_hyper_res:                          8
% 51.34/7.00  prep_cycles:                            4
% 51.34/7.00  pred_elim_time:                         0.
% 51.34/7.00  splitting_time:                         0.
% 51.34/7.00  sem_filter_time:                        0.
% 51.34/7.00  monotx_time:                            0.001
% 51.34/7.00  subtype_inf_time:                       0.
% 51.34/7.00  
% 51.34/7.00  ------ Problem properties
% 51.34/7.00  
% 51.34/7.00  clauses:                                18
% 51.34/7.00  conjectures:                            2
% 51.34/7.00  epr:                                    4
% 51.34/7.00  horn:                                   14
% 51.34/7.00  ground:                                 2
% 51.34/7.00  unary:                                  7
% 51.34/7.00  binary:                                 5
% 51.34/7.00  lits:                                   35
% 51.34/7.00  lits_eq:                                6
% 51.34/7.00  fd_pure:                                0
% 51.34/7.00  fd_pseudo:                              0
% 51.34/7.00  fd_cond:                                0
% 51.34/7.00  fd_pseudo_cond:                         1
% 51.34/7.00  ac_symbols:                             0
% 51.34/7.00  
% 51.34/7.00  ------ Propositional Solver
% 51.34/7.00  
% 51.34/7.00  prop_solver_calls:                      31
% 51.34/7.00  prop_fast_solver_calls:                 1013
% 51.34/7.00  smt_solver_calls:                       0
% 51.34/7.00  smt_fast_solver_calls:                  0
% 51.34/7.00  prop_num_of_clauses:                    25357
% 51.34/7.00  prop_preprocess_simplified:             34331
% 51.34/7.00  prop_fo_subsumed:                       18
% 51.34/7.00  prop_solver_time:                       0.
% 51.34/7.00  smt_solver_time:                        0.
% 51.34/7.00  smt_fast_solver_time:                   0.
% 51.34/7.00  prop_fast_solver_time:                  0.
% 51.34/7.00  prop_unsat_core_time:                   0.002
% 51.34/7.00  
% 51.34/7.00  ------ QBF
% 51.34/7.00  
% 51.34/7.00  qbf_q_res:                              0
% 51.34/7.00  qbf_num_tautologies:                    0
% 51.34/7.00  qbf_prep_cycles:                        0
% 51.34/7.00  
% 51.34/7.00  ------ BMC1
% 51.34/7.00  
% 51.34/7.00  bmc1_current_bound:                     -1
% 51.34/7.00  bmc1_last_solved_bound:                 -1
% 51.34/7.00  bmc1_unsat_core_size:                   -1
% 51.34/7.00  bmc1_unsat_core_parents_size:           -1
% 51.34/7.00  bmc1_merge_next_fun:                    0
% 51.34/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.34/7.00  
% 51.34/7.00  ------ Instantiation
% 51.34/7.00  
% 51.34/7.00  inst_num_of_clauses:                    4322
% 51.34/7.00  inst_num_in_passive:                    1537
% 51.34/7.00  inst_num_in_active:                     1520
% 51.34/7.00  inst_num_in_unprocessed:                1265
% 51.34/7.00  inst_num_of_loops:                      1820
% 51.34/7.00  inst_num_of_learning_restarts:          0
% 51.34/7.00  inst_num_moves_active_passive:          300
% 51.34/7.00  inst_lit_activity:                      0
% 51.34/7.00  inst_lit_activity_moves:                0
% 51.34/7.00  inst_num_tautologies:                   0
% 51.34/7.00  inst_num_prop_implied:                  0
% 51.34/7.00  inst_num_existing_simplified:           0
% 51.34/7.00  inst_num_eq_res_simplified:             0
% 51.34/7.00  inst_num_child_elim:                    0
% 51.34/7.00  inst_num_of_dismatching_blockings:      21926
% 51.34/7.00  inst_num_of_non_proper_insts:           11284
% 51.34/7.00  inst_num_of_duplicates:                 0
% 51.34/7.00  inst_inst_num_from_inst_to_res:         0
% 51.34/7.00  inst_dismatching_checking_time:         0.
% 51.34/7.00  
% 51.34/7.00  ------ Resolution
% 51.34/7.00  
% 51.34/7.00  res_num_of_clauses:                     0
% 51.34/7.00  res_num_in_passive:                     0
% 51.34/7.00  res_num_in_active:                      0
% 51.34/7.00  res_num_of_loops:                       93
% 51.34/7.00  res_forward_subset_subsumed:            606
% 51.34/7.00  res_backward_subset_subsumed:           0
% 51.34/7.00  res_forward_subsumed:                   0
% 51.34/7.00  res_backward_subsumed:                  0
% 51.34/7.00  res_forward_subsumption_resolution:     0
% 51.34/7.00  res_backward_subsumption_resolution:    0
% 51.34/7.00  res_clause_to_clause_subsumption:       20821
% 51.34/7.00  res_orphan_elimination:                 0
% 51.34/7.00  res_tautology_del:                      960
% 51.34/7.00  res_num_eq_res_simplified:              0
% 51.34/7.00  res_num_sel_changes:                    0
% 51.34/7.00  res_moves_from_active_to_pass:          0
% 51.34/7.00  
% 51.34/7.00  ------ Superposition
% 51.34/7.00  
% 51.34/7.00  sup_time_total:                         0.
% 51.34/7.00  sup_time_generating:                    0.
% 51.34/7.00  sup_time_sim_full:                      0.
% 51.34/7.00  sup_time_sim_immed:                     0.
% 51.34/7.00  
% 51.34/7.00  sup_num_of_clauses:                     4859
% 51.34/7.00  sup_num_in_active:                      338
% 51.34/7.00  sup_num_in_passive:                     4521
% 51.34/7.00  sup_num_of_loops:                       362
% 51.34/7.00  sup_fw_superposition:                   16653
% 51.34/7.00  sup_bw_superposition:                   14837
% 51.34/7.00  sup_immediate_simplified:               8714
% 51.34/7.00  sup_given_eliminated:                   4
% 51.34/7.00  comparisons_done:                       0
% 51.34/7.00  comparisons_avoided:                    0
% 51.34/7.00  
% 51.34/7.00  ------ Simplifications
% 51.34/7.00  
% 51.34/7.00  
% 51.34/7.00  sim_fw_subset_subsumed:                 127
% 51.34/7.00  sim_bw_subset_subsumed:                 27
% 51.34/7.00  sim_fw_subsumed:                        370
% 51.34/7.00  sim_bw_subsumed:                        24
% 51.34/7.00  sim_fw_subsumption_res:                 0
% 51.34/7.00  sim_bw_subsumption_res:                 0
% 51.34/7.00  sim_tautology_del:                      80
% 51.34/7.00  sim_eq_tautology_del:                   2070
% 51.34/7.00  sim_eq_res_simp:                        0
% 51.34/7.00  sim_fw_demodulated:                     4499
% 51.34/7.00  sim_bw_demodulated:                     303
% 51.34/7.00  sim_light_normalised:                   5176
% 51.34/7.00  sim_joinable_taut:                      0
% 51.34/7.00  sim_joinable_simp:                      0
% 51.34/7.00  sim_ac_normalised:                      0
% 51.34/7.00  sim_smt_subsumption:                    0
% 51.34/7.00  
%------------------------------------------------------------------------------
