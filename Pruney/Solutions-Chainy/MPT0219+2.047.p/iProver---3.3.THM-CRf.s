%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:17 EST 2020

% Result     : Theorem 15.92s
% Output     : CNFRefutation 15.92s
% Verified   : 
% Statistics : Number of formulae       :  209 (84120 expanded)
%              Number of clauses        :  146 (32003 expanded)
%              Number of leaves         :   20 (18579 expanded)
%              Depth                    :   50
%              Number of atoms          :  293 (137417 expanded)
%              Number of equality atoms :  202 (79828 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :   11 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f25,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( sK1 != sK2
    & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f33])).

fof(f59,plain,(
    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f53,f47])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f62])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f63])).

fof(f68,plain,(
    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f59,f61,f64,f64,f64])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f58,f64,f64])).

fof(f60,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_804,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_19])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_423,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_421,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3246,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_421])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_419,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2012,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_419])).

cnf(c_3475,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3246,c_2012])).

cnf(c_3482,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_423,c_3475])).

cnf(c_11,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_416,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_415,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1150,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_416,c_415])).

cnf(c_30420,plain,
    ( r1_tarski(k5_xboole_0(X0,X0),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3482,c_1150])).

cnf(c_30431,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X0),X1) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_30420,c_415])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_414,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1151,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_414,c_415])).

cnf(c_11553,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1151,c_0])).

cnf(c_31631,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30431,c_11553])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_413,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_777,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_413])).

cnf(c_2313,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X0)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_777])).

cnf(c_9954,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4))),X0))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_2313])).

cnf(c_32113,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X1,k1_xboole_0),X0))))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_31631,c_9954])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_773,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_16])).

cnf(c_1169,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_773,c_16])).

cnf(c_1170,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_1169,c_773])).

cnf(c_32136,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X1,k1_xboole_0),X0)))))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32113,c_1170])).

cnf(c_32137,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X1,X0)))))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_32136,c_14])).

cnf(c_67447,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_804,c_32137])).

cnf(c_32074,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_31631,c_16])).

cnf(c_774,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_16,c_4])).

cnf(c_4020,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_774,c_16])).

cnf(c_12281,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4020,c_1150])).

cnf(c_12292,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_16,c_12281])).

cnf(c_12475,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_12292,c_16])).

cnf(c_772,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_16])).

cnf(c_1729,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_16,c_772])).

cnf(c_1814,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_1729,c_16])).

cnf(c_1838,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_1814,c_16])).

cnf(c_5261,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X0),X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_16,c_1838])).

cnf(c_10261,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_1150,c_5261])).

cnf(c_10314,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_10261,c_16])).

cnf(c_32085,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_31631,c_10314])).

cnf(c_32200,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_32085,c_31631])).

cnf(c_32202,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_32200,c_1170])).

cnf(c_32203,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_32202,c_14])).

cnf(c_33294,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X0))) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_32203,c_32074])).

cnf(c_33555,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X0))) = X1 ),
    inference(demodulation,[status(thm)],[c_33294,c_14])).

cnf(c_34273,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0)))))),k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_12475,c_33555])).

cnf(c_34639,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))))),k5_xboole_0(X1,k5_xboole_0(X2,X0))))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_34273,c_1170])).

cnf(c_34640,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0)))),k5_xboole_0(X1,k5_xboole_0(X2,X0)))))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_34639,c_1170])).

cnf(c_34641,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,k5_xboole_0(X2,X0))))))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_34640,c_1170])).

cnf(c_34642,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k5_xboole_0(X1,k5_xboole_0(X2,X0)))))))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_34641,c_1170])).

cnf(c_34643,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X0),k5_xboole_0(X1,k5_xboole_0(X2,X0))))))))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_34642,c_1170])).

cnf(c_34644,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_34643,c_14,c_32203])).

cnf(c_775,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_16,c_4])).

cnf(c_5576,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X0)))) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_4,c_775])).

cnf(c_5758,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5576,c_4])).

cnf(c_6202,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X0))),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5758,c_16])).

cnf(c_12954,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),X1)) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_6202,c_1150])).

cnf(c_12960,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_16,c_12954])).

cnf(c_13313,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_16,c_12960])).

cnf(c_13747,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),X2))))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_16,c_13313])).

cnf(c_13751,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_12960,c_13313])).

cnf(c_13768,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X1),X2))))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ),
    inference(superposition,[status(thm)],[c_13313,c_10314])).

cnf(c_13782,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_13313,c_10314])).

cnf(c_14090,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ),
    inference(demodulation,[status(thm)],[c_13768,c_13782])).

cnf(c_14092,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_14090,c_10314])).

cnf(c_14205,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2)))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_13747,c_13751,c_14092])).

cnf(c_14207,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_14205,c_16])).

cnf(c_32046,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_31631,c_14207])).

cnf(c_32286,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_32046,c_31631])).

cnf(c_32288,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_32286,c_14])).

cnf(c_34796,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k5_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_32288,c_32288])).

cnf(c_34945,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_34796,c_1170])).

cnf(c_34946,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0))))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_34945,c_1170])).

cnf(c_34947,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_34946,c_1170])).

cnf(c_34948,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0))))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_34947,c_773,c_1170,c_32074])).

cnf(c_34949,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_34948,c_773,c_32074])).

cnf(c_34950,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_34949,c_1170,c_32074])).

cnf(c_34951,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(demodulation,[status(thm)],[c_34950,c_14,c_31631])).

cnf(c_36341,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_34644,c_34951])).

cnf(c_36522,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36341,c_14,c_1170])).

cnf(c_37099,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14,c_36522])).

cnf(c_37180,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_36522,c_14207])).

cnf(c_37213,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_36522,c_34644])).

cnf(c_37215,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),X1) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(demodulation,[status(thm)],[c_37213,c_1170,c_34951])).

cnf(c_37399,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1))),k5_xboole_0(X2,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_37180,c_36522,c_37215])).

cnf(c_37401,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),k5_xboole_0(X2,k1_xboole_0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_37399,c_1170])).

cnf(c_37402,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k1_xboole_0)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_37401,c_1170])).

cnf(c_37403,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k1_xboole_0))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_37402,c_1170])).

cnf(c_37404,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_37403,c_14])).

cnf(c_38001,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k1_xboole_0))) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_37099,c_34644])).

cnf(c_38025,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k1_xboole_0)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_38001,c_773,c_1170])).

cnf(c_38026,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_38025,c_14])).

cnf(c_41247,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1)))),k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_37404,c_38026])).

cnf(c_41553,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1)))),k5_xboole_0(k1_xboole_0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_41247,c_14,c_1170])).

cnf(c_32473,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_32074,c_12475])).

cnf(c_12325,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_12281,c_16])).

cnf(c_12387,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_12325,c_16])).

cnf(c_16932,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_12387,c_1170])).

cnf(c_16933,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_16932,c_1170])).

cnf(c_16934,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_16933,c_1170])).

cnf(c_16935,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_16934,c_1170])).

cnf(c_32491,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_32074,c_16935])).

cnf(c_32508,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_32491,c_32074])).

cnf(c_32510,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(light_normalisation,[status(thm)],[c_32508,c_773])).

cnf(c_32560,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_32473,c_32510])).

cnf(c_32562,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_32560,c_14,c_1170,c_31631])).

cnf(c_44845,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) ),
    inference(superposition,[status(thm)],[c_41553,c_32562])).

cnf(c_45299,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1)))) = X2 ),
    inference(demodulation,[status(thm)],[c_44845,c_14,c_38026])).

cnf(c_46168,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_36522,c_45299])).

cnf(c_46763,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(demodulation,[status(thm)],[c_46168,c_14])).

cnf(c_47690,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X0) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_37099,c_46763])).

cnf(c_48141,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X0) = X1 ),
    inference(demodulation,[status(thm)],[c_47690,c_14,c_1170])).

cnf(c_48969,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_37099,c_48141])).

cnf(c_49347,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_48969,c_14,c_1170,c_38026])).

cnf(c_67586,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67447,c_32074,c_49347])).

cnf(c_67587,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67586,c_1170])).

cnf(c_7249,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0) ),
    inference(superposition,[status(thm)],[c_804,c_16])).

cnf(c_25328,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),X0))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0) ),
    inference(demodulation,[status(thm)],[c_7249,c_1170])).

cnf(c_46148,plain,
    ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_25328,c_45299])).

cnf(c_46309,plain,
    ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_45299,c_25328])).

cnf(c_47157,plain,
    ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(demodulation,[status(thm)],[c_46309,c_32074])).

cnf(c_47631,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_46148,c_47157])).

cnf(c_47633,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_47631,c_1170,c_31631])).

cnf(c_47634,plain,
    ( k5_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_47633,c_14,c_34951])).

cnf(c_59002,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_47634,c_46763])).

cnf(c_59004,plain,
    ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_59002,c_14])).

cnf(c_67588,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_67587,c_59004])).

cnf(c_17,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_544,plain,
    ( ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_545,plain,
    ( sK1 = sK2
    | r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_18,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_67588,c_545,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.92/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.92/2.50  
% 15.92/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.92/2.50  
% 15.92/2.50  ------  iProver source info
% 15.92/2.50  
% 15.92/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.92/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.92/2.50  git: non_committed_changes: false
% 15.92/2.50  git: last_make_outside_of_git: false
% 15.92/2.50  
% 15.92/2.50  ------ 
% 15.92/2.50  
% 15.92/2.50  ------ Input Options
% 15.92/2.50  
% 15.92/2.50  --out_options                           all
% 15.92/2.50  --tptp_safe_out                         true
% 15.92/2.50  --problem_path                          ""
% 15.92/2.50  --include_path                          ""
% 15.92/2.50  --clausifier                            res/vclausify_rel
% 15.92/2.50  --clausifier_options                    --mode clausify
% 15.92/2.50  --stdin                                 false
% 15.92/2.50  --stats_out                             sel
% 15.92/2.50  
% 15.92/2.50  ------ General Options
% 15.92/2.50  
% 15.92/2.50  --fof                                   false
% 15.92/2.50  --time_out_real                         604.99
% 15.92/2.50  --time_out_virtual                      -1.
% 15.92/2.50  --symbol_type_check                     false
% 15.92/2.50  --clausify_out                          false
% 15.92/2.50  --sig_cnt_out                           false
% 15.92/2.50  --trig_cnt_out                          false
% 15.92/2.50  --trig_cnt_out_tolerance                1.
% 15.92/2.50  --trig_cnt_out_sk_spl                   false
% 15.92/2.50  --abstr_cl_out                          false
% 15.92/2.50  
% 15.92/2.50  ------ Global Options
% 15.92/2.50  
% 15.92/2.50  --schedule                              none
% 15.92/2.50  --add_important_lit                     false
% 15.92/2.50  --prop_solver_per_cl                    1000
% 15.92/2.50  --min_unsat_core                        false
% 15.92/2.50  --soft_assumptions                      false
% 15.92/2.50  --soft_lemma_size                       3
% 15.92/2.50  --prop_impl_unit_size                   0
% 15.92/2.50  --prop_impl_unit                        []
% 15.92/2.50  --share_sel_clauses                     true
% 15.92/2.50  --reset_solvers                         false
% 15.92/2.50  --bc_imp_inh                            [conj_cone]
% 15.92/2.50  --conj_cone_tolerance                   3.
% 15.92/2.50  --extra_neg_conj                        none
% 15.92/2.50  --large_theory_mode                     true
% 15.92/2.50  --prolific_symb_bound                   200
% 15.92/2.50  --lt_threshold                          2000
% 15.92/2.50  --clause_weak_htbl                      true
% 15.92/2.50  --gc_record_bc_elim                     false
% 15.92/2.50  
% 15.92/2.50  ------ Preprocessing Options
% 15.92/2.50  
% 15.92/2.50  --preprocessing_flag                    true
% 15.92/2.50  --time_out_prep_mult                    0.1
% 15.92/2.50  --splitting_mode                        input
% 15.92/2.50  --splitting_grd                         true
% 15.92/2.50  --splitting_cvd                         false
% 15.92/2.50  --splitting_cvd_svl                     false
% 15.92/2.50  --splitting_nvd                         32
% 15.92/2.50  --sub_typing                            true
% 15.92/2.50  --prep_gs_sim                           false
% 15.92/2.50  --prep_unflatten                        true
% 15.92/2.50  --prep_res_sim                          true
% 15.92/2.50  --prep_upred                            true
% 15.92/2.50  --prep_sem_filter                       exhaustive
% 15.92/2.50  --prep_sem_filter_out                   false
% 15.92/2.50  --pred_elim                             false
% 15.92/2.50  --res_sim_input                         true
% 15.92/2.50  --eq_ax_congr_red                       true
% 15.92/2.50  --pure_diseq_elim                       true
% 15.92/2.50  --brand_transform                       false
% 15.92/2.50  --non_eq_to_eq                          false
% 15.92/2.50  --prep_def_merge                        true
% 15.92/2.50  --prep_def_merge_prop_impl              false
% 15.92/2.50  --prep_def_merge_mbd                    true
% 15.92/2.50  --prep_def_merge_tr_red                 false
% 15.92/2.50  --prep_def_merge_tr_cl                  false
% 15.92/2.50  --smt_preprocessing                     true
% 15.92/2.50  --smt_ac_axioms                         fast
% 15.92/2.50  --preprocessed_out                      false
% 15.92/2.50  --preprocessed_stats                    false
% 15.92/2.50  
% 15.92/2.50  ------ Abstraction refinement Options
% 15.92/2.50  
% 15.92/2.50  --abstr_ref                             []
% 15.92/2.50  --abstr_ref_prep                        false
% 15.92/2.50  --abstr_ref_until_sat                   false
% 15.92/2.50  --abstr_ref_sig_restrict                funpre
% 15.92/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.92/2.50  --abstr_ref_under                       []
% 15.92/2.50  
% 15.92/2.50  ------ SAT Options
% 15.92/2.50  
% 15.92/2.50  --sat_mode                              false
% 15.92/2.50  --sat_fm_restart_options                ""
% 15.92/2.50  --sat_gr_def                            false
% 15.92/2.50  --sat_epr_types                         true
% 15.92/2.50  --sat_non_cyclic_types                  false
% 15.92/2.50  --sat_finite_models                     false
% 15.92/2.50  --sat_fm_lemmas                         false
% 15.92/2.50  --sat_fm_prep                           false
% 15.92/2.50  --sat_fm_uc_incr                        true
% 15.92/2.50  --sat_out_model                         small
% 15.92/2.50  --sat_out_clauses                       false
% 15.92/2.50  
% 15.92/2.50  ------ QBF Options
% 15.92/2.50  
% 15.92/2.50  --qbf_mode                              false
% 15.92/2.50  --qbf_elim_univ                         false
% 15.92/2.50  --qbf_dom_inst                          none
% 15.92/2.50  --qbf_dom_pre_inst                      false
% 15.92/2.50  --qbf_sk_in                             false
% 15.92/2.50  --qbf_pred_elim                         true
% 15.92/2.50  --qbf_split                             512
% 15.92/2.50  
% 15.92/2.50  ------ BMC1 Options
% 15.92/2.50  
% 15.92/2.50  --bmc1_incremental                      false
% 15.92/2.50  --bmc1_axioms                           reachable_all
% 15.92/2.50  --bmc1_min_bound                        0
% 15.92/2.50  --bmc1_max_bound                        -1
% 15.92/2.50  --bmc1_max_bound_default                -1
% 15.92/2.50  --bmc1_symbol_reachability              true
% 15.92/2.50  --bmc1_property_lemmas                  false
% 15.92/2.50  --bmc1_k_induction                      false
% 15.92/2.50  --bmc1_non_equiv_states                 false
% 15.92/2.50  --bmc1_deadlock                         false
% 15.92/2.50  --bmc1_ucm                              false
% 15.92/2.50  --bmc1_add_unsat_core                   none
% 15.92/2.50  --bmc1_unsat_core_children              false
% 15.92/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.92/2.50  --bmc1_out_stat                         full
% 15.92/2.50  --bmc1_ground_init                      false
% 15.92/2.50  --bmc1_pre_inst_next_state              false
% 15.92/2.50  --bmc1_pre_inst_state                   false
% 15.92/2.50  --bmc1_pre_inst_reach_state             false
% 15.92/2.50  --bmc1_out_unsat_core                   false
% 15.92/2.50  --bmc1_aig_witness_out                  false
% 15.92/2.50  --bmc1_verbose                          false
% 15.92/2.50  --bmc1_dump_clauses_tptp                false
% 15.92/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.92/2.50  --bmc1_dump_file                        -
% 15.92/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.92/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.92/2.50  --bmc1_ucm_extend_mode                  1
% 15.92/2.50  --bmc1_ucm_init_mode                    2
% 15.92/2.50  --bmc1_ucm_cone_mode                    none
% 15.92/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.92/2.50  --bmc1_ucm_relax_model                  4
% 15.92/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.92/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.92/2.50  --bmc1_ucm_layered_model                none
% 15.92/2.50  --bmc1_ucm_max_lemma_size               10
% 15.92/2.50  
% 15.92/2.50  ------ AIG Options
% 15.92/2.50  
% 15.92/2.50  --aig_mode                              false
% 15.92/2.50  
% 15.92/2.50  ------ Instantiation Options
% 15.92/2.50  
% 15.92/2.50  --instantiation_flag                    true
% 15.92/2.50  --inst_sos_flag                         false
% 15.92/2.50  --inst_sos_phase                        true
% 15.92/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.92/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.92/2.50  --inst_lit_sel_side                     num_symb
% 15.92/2.50  --inst_solver_per_active                1400
% 15.92/2.50  --inst_solver_calls_frac                1.
% 15.92/2.50  --inst_passive_queue_type               priority_queues
% 15.92/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.92/2.50  --inst_passive_queues_freq              [25;2]
% 15.92/2.50  --inst_dismatching                      true
% 15.92/2.50  --inst_eager_unprocessed_to_passive     true
% 15.92/2.50  --inst_prop_sim_given                   true
% 15.92/2.50  --inst_prop_sim_new                     false
% 15.92/2.50  --inst_subs_new                         false
% 15.92/2.50  --inst_eq_res_simp                      false
% 15.92/2.50  --inst_subs_given                       false
% 15.92/2.50  --inst_orphan_elimination               true
% 15.92/2.50  --inst_learning_loop_flag               true
% 15.92/2.50  --inst_learning_start                   3000
% 15.92/2.50  --inst_learning_factor                  2
% 15.92/2.50  --inst_start_prop_sim_after_learn       3
% 15.92/2.50  --inst_sel_renew                        solver
% 15.92/2.50  --inst_lit_activity_flag                true
% 15.92/2.50  --inst_restr_to_given                   false
% 15.92/2.50  --inst_activity_threshold               500
% 15.92/2.50  --inst_out_proof                        true
% 15.92/2.50  
% 15.92/2.50  ------ Resolution Options
% 15.92/2.50  
% 15.92/2.50  --resolution_flag                       true
% 15.92/2.50  --res_lit_sel                           adaptive
% 15.92/2.50  --res_lit_sel_side                      none
% 15.92/2.50  --res_ordering                          kbo
% 15.92/2.50  --res_to_prop_solver                    active
% 15.92/2.50  --res_prop_simpl_new                    false
% 15.92/2.50  --res_prop_simpl_given                  true
% 15.92/2.50  --res_passive_queue_type                priority_queues
% 15.92/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.92/2.50  --res_passive_queues_freq               [15;5]
% 15.92/2.50  --res_forward_subs                      full
% 15.92/2.50  --res_backward_subs                     full
% 15.92/2.50  --res_forward_subs_resolution           true
% 15.92/2.50  --res_backward_subs_resolution          true
% 15.92/2.50  --res_orphan_elimination                true
% 15.92/2.50  --res_time_limit                        2.
% 15.92/2.50  --res_out_proof                         true
% 15.92/2.50  
% 15.92/2.50  ------ Superposition Options
% 15.92/2.50  
% 15.92/2.50  --superposition_flag                    true
% 15.92/2.50  --sup_passive_queue_type                priority_queues
% 15.92/2.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.92/2.50  --sup_passive_queues_freq               [1;4]
% 15.92/2.50  --demod_completeness_check              fast
% 15.92/2.50  --demod_use_ground                      true
% 15.92/2.50  --sup_to_prop_solver                    passive
% 15.92/2.50  --sup_prop_simpl_new                    true
% 15.92/2.50  --sup_prop_simpl_given                  true
% 15.92/2.50  --sup_fun_splitting                     false
% 15.92/2.50  --sup_smt_interval                      50000
% 15.92/2.50  
% 15.92/2.50  ------ Superposition Simplification Setup
% 15.92/2.50  
% 15.92/2.50  --sup_indices_passive                   []
% 15.92/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.92/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.92/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.92/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.92/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.92/2.50  --sup_full_bw                           [BwDemod]
% 15.92/2.50  --sup_immed_triv                        [TrivRules]
% 15.92/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.92/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.92/2.50  --sup_immed_bw_main                     []
% 15.92/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.92/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.92/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.92/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.92/2.50  
% 15.92/2.50  ------ Combination Options
% 15.92/2.50  
% 15.92/2.50  --comb_res_mult                         3
% 15.92/2.50  --comb_sup_mult                         2
% 15.92/2.50  --comb_inst_mult                        10
% 15.92/2.50  
% 15.92/2.50  ------ Debug Options
% 15.92/2.50  
% 15.92/2.50  --dbg_backtrace                         false
% 15.92/2.50  --dbg_dump_prop_clauses                 false
% 15.92/2.50  --dbg_dump_prop_clauses_file            -
% 15.92/2.50  --dbg_out_stat                          false
% 15.92/2.50  ------ Parsing...
% 15.92/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.92/2.50  
% 15.92/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.92/2.50  
% 15.92/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.92/2.50  
% 15.92/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.92/2.50  ------ Proving...
% 15.92/2.50  ------ Problem Properties 
% 15.92/2.50  
% 15.92/2.50  
% 15.92/2.50  clauses                                 19
% 15.92/2.50  conjectures                             2
% 15.92/2.50  EPR                                     5
% 15.92/2.50  Horn                                    15
% 15.92/2.50  unary                                   9
% 15.92/2.50  binary                                  4
% 15.92/2.50  lits                                    35
% 15.92/2.50  lits eq                                 9
% 15.92/2.50  fd_pure                                 0
% 15.92/2.50  fd_pseudo                               0
% 15.92/2.50  fd_cond                                 0
% 15.92/2.50  fd_pseudo_cond                          2
% 15.92/2.50  AC symbols                              0
% 15.92/2.50  
% 15.92/2.50  ------ Input Options Time Limit: Unbounded
% 15.92/2.50  
% 15.92/2.50  
% 15.92/2.50  ------ 
% 15.92/2.50  Current options:
% 15.92/2.50  ------ 
% 15.92/2.50  
% 15.92/2.50  ------ Input Options
% 15.92/2.50  
% 15.92/2.50  --out_options                           all
% 15.92/2.50  --tptp_safe_out                         true
% 15.92/2.50  --problem_path                          ""
% 15.92/2.50  --include_path                          ""
% 15.92/2.50  --clausifier                            res/vclausify_rel
% 15.92/2.50  --clausifier_options                    --mode clausify
% 15.92/2.50  --stdin                                 false
% 15.92/2.50  --stats_out                             sel
% 15.92/2.50  
% 15.92/2.50  ------ General Options
% 15.92/2.50  
% 15.92/2.50  --fof                                   false
% 15.92/2.50  --time_out_real                         604.99
% 15.92/2.50  --time_out_virtual                      -1.
% 15.92/2.50  --symbol_type_check                     false
% 15.92/2.50  --clausify_out                          false
% 15.92/2.50  --sig_cnt_out                           false
% 15.92/2.50  --trig_cnt_out                          false
% 15.92/2.50  --trig_cnt_out_tolerance                1.
% 15.92/2.50  --trig_cnt_out_sk_spl                   false
% 15.92/2.50  --abstr_cl_out                          false
% 15.92/2.50  
% 15.92/2.50  ------ Global Options
% 15.92/2.50  
% 15.92/2.50  --schedule                              none
% 15.92/2.50  --add_important_lit                     false
% 15.92/2.50  --prop_solver_per_cl                    1000
% 15.92/2.50  --min_unsat_core                        false
% 15.92/2.50  --soft_assumptions                      false
% 15.92/2.50  --soft_lemma_size                       3
% 15.92/2.50  --prop_impl_unit_size                   0
% 15.92/2.50  --prop_impl_unit                        []
% 15.92/2.50  --share_sel_clauses                     true
% 15.92/2.50  --reset_solvers                         false
% 15.92/2.50  --bc_imp_inh                            [conj_cone]
% 15.92/2.50  --conj_cone_tolerance                   3.
% 15.92/2.50  --extra_neg_conj                        none
% 15.92/2.50  --large_theory_mode                     true
% 15.92/2.50  --prolific_symb_bound                   200
% 15.92/2.50  --lt_threshold                          2000
% 15.92/2.50  --clause_weak_htbl                      true
% 15.92/2.50  --gc_record_bc_elim                     false
% 15.92/2.50  
% 15.92/2.50  ------ Preprocessing Options
% 15.92/2.50  
% 15.92/2.50  --preprocessing_flag                    true
% 15.92/2.50  --time_out_prep_mult                    0.1
% 15.92/2.50  --splitting_mode                        input
% 15.92/2.50  --splitting_grd                         true
% 15.92/2.50  --splitting_cvd                         false
% 15.92/2.50  --splitting_cvd_svl                     false
% 15.92/2.50  --splitting_nvd                         32
% 15.92/2.50  --sub_typing                            true
% 15.92/2.50  --prep_gs_sim                           false
% 15.92/2.50  --prep_unflatten                        true
% 15.92/2.50  --prep_res_sim                          true
% 15.92/2.50  --prep_upred                            true
% 15.92/2.50  --prep_sem_filter                       exhaustive
% 15.92/2.50  --prep_sem_filter_out                   false
% 15.92/2.50  --pred_elim                             false
% 15.92/2.50  --res_sim_input                         true
% 15.92/2.50  --eq_ax_congr_red                       true
% 15.92/2.50  --pure_diseq_elim                       true
% 15.92/2.50  --brand_transform                       false
% 15.92/2.50  --non_eq_to_eq                          false
% 15.92/2.50  --prep_def_merge                        true
% 15.92/2.50  --prep_def_merge_prop_impl              false
% 15.92/2.50  --prep_def_merge_mbd                    true
% 15.92/2.50  --prep_def_merge_tr_red                 false
% 15.92/2.50  --prep_def_merge_tr_cl                  false
% 15.92/2.50  --smt_preprocessing                     true
% 15.92/2.50  --smt_ac_axioms                         fast
% 15.92/2.50  --preprocessed_out                      false
% 15.92/2.50  --preprocessed_stats                    false
% 15.92/2.50  
% 15.92/2.50  ------ Abstraction refinement Options
% 15.92/2.50  
% 15.92/2.50  --abstr_ref                             []
% 15.92/2.50  --abstr_ref_prep                        false
% 15.92/2.50  --abstr_ref_until_sat                   false
% 15.92/2.50  --abstr_ref_sig_restrict                funpre
% 15.92/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.92/2.50  --abstr_ref_under                       []
% 15.92/2.50  
% 15.92/2.50  ------ SAT Options
% 15.92/2.50  
% 15.92/2.50  --sat_mode                              false
% 15.92/2.50  --sat_fm_restart_options                ""
% 15.92/2.50  --sat_gr_def                            false
% 15.92/2.50  --sat_epr_types                         true
% 15.92/2.50  --sat_non_cyclic_types                  false
% 15.92/2.50  --sat_finite_models                     false
% 15.92/2.50  --sat_fm_lemmas                         false
% 15.92/2.50  --sat_fm_prep                           false
% 15.92/2.50  --sat_fm_uc_incr                        true
% 15.92/2.50  --sat_out_model                         small
% 15.92/2.50  --sat_out_clauses                       false
% 15.92/2.50  
% 15.92/2.50  ------ QBF Options
% 15.92/2.50  
% 15.92/2.50  --qbf_mode                              false
% 15.92/2.50  --qbf_elim_univ                         false
% 15.92/2.50  --qbf_dom_inst                          none
% 15.92/2.50  --qbf_dom_pre_inst                      false
% 15.92/2.50  --qbf_sk_in                             false
% 15.92/2.50  --qbf_pred_elim                         true
% 15.92/2.50  --qbf_split                             512
% 15.92/2.50  
% 15.92/2.50  ------ BMC1 Options
% 15.92/2.50  
% 15.92/2.50  --bmc1_incremental                      false
% 15.92/2.50  --bmc1_axioms                           reachable_all
% 15.92/2.50  --bmc1_min_bound                        0
% 15.92/2.50  --bmc1_max_bound                        -1
% 15.92/2.50  --bmc1_max_bound_default                -1
% 15.92/2.50  --bmc1_symbol_reachability              true
% 15.92/2.50  --bmc1_property_lemmas                  false
% 15.92/2.50  --bmc1_k_induction                      false
% 15.92/2.50  --bmc1_non_equiv_states                 false
% 15.92/2.50  --bmc1_deadlock                         false
% 15.92/2.50  --bmc1_ucm                              false
% 15.92/2.50  --bmc1_add_unsat_core                   none
% 15.92/2.50  --bmc1_unsat_core_children              false
% 15.92/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.92/2.50  --bmc1_out_stat                         full
% 15.92/2.50  --bmc1_ground_init                      false
% 15.92/2.50  --bmc1_pre_inst_next_state              false
% 15.92/2.50  --bmc1_pre_inst_state                   false
% 15.92/2.50  --bmc1_pre_inst_reach_state             false
% 15.92/2.50  --bmc1_out_unsat_core                   false
% 15.92/2.50  --bmc1_aig_witness_out                  false
% 15.92/2.50  --bmc1_verbose                          false
% 15.92/2.50  --bmc1_dump_clauses_tptp                false
% 15.92/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.92/2.50  --bmc1_dump_file                        -
% 15.92/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.92/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.92/2.50  --bmc1_ucm_extend_mode                  1
% 15.92/2.50  --bmc1_ucm_init_mode                    2
% 15.92/2.50  --bmc1_ucm_cone_mode                    none
% 15.92/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.92/2.50  --bmc1_ucm_relax_model                  4
% 15.92/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.92/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.92/2.50  --bmc1_ucm_layered_model                none
% 15.92/2.50  --bmc1_ucm_max_lemma_size               10
% 15.92/2.50  
% 15.92/2.50  ------ AIG Options
% 15.92/2.50  
% 15.92/2.50  --aig_mode                              false
% 15.92/2.50  
% 15.92/2.50  ------ Instantiation Options
% 15.92/2.50  
% 15.92/2.50  --instantiation_flag                    true
% 15.92/2.50  --inst_sos_flag                         false
% 15.92/2.50  --inst_sos_phase                        true
% 15.92/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.92/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.92/2.50  --inst_lit_sel_side                     num_symb
% 15.92/2.50  --inst_solver_per_active                1400
% 15.92/2.50  --inst_solver_calls_frac                1.
% 15.92/2.50  --inst_passive_queue_type               priority_queues
% 15.92/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.92/2.50  --inst_passive_queues_freq              [25;2]
% 15.92/2.50  --inst_dismatching                      true
% 15.92/2.50  --inst_eager_unprocessed_to_passive     true
% 15.92/2.50  --inst_prop_sim_given                   true
% 15.92/2.50  --inst_prop_sim_new                     false
% 15.92/2.50  --inst_subs_new                         false
% 15.92/2.50  --inst_eq_res_simp                      false
% 15.92/2.50  --inst_subs_given                       false
% 15.92/2.50  --inst_orphan_elimination               true
% 15.92/2.50  --inst_learning_loop_flag               true
% 15.92/2.50  --inst_learning_start                   3000
% 15.92/2.50  --inst_learning_factor                  2
% 15.92/2.50  --inst_start_prop_sim_after_learn       3
% 15.92/2.50  --inst_sel_renew                        solver
% 15.92/2.50  --inst_lit_activity_flag                true
% 15.92/2.50  --inst_restr_to_given                   false
% 15.92/2.50  --inst_activity_threshold               500
% 15.92/2.50  --inst_out_proof                        true
% 15.92/2.50  
% 15.92/2.50  ------ Resolution Options
% 15.92/2.50  
% 15.92/2.50  --resolution_flag                       true
% 15.92/2.50  --res_lit_sel                           adaptive
% 15.92/2.50  --res_lit_sel_side                      none
% 15.92/2.50  --res_ordering                          kbo
% 15.92/2.50  --res_to_prop_solver                    active
% 15.92/2.50  --res_prop_simpl_new                    false
% 15.92/2.50  --res_prop_simpl_given                  true
% 15.92/2.50  --res_passive_queue_type                priority_queues
% 15.92/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.92/2.50  --res_passive_queues_freq               [15;5]
% 15.92/2.50  --res_forward_subs                      full
% 15.92/2.50  --res_backward_subs                     full
% 15.92/2.50  --res_forward_subs_resolution           true
% 15.92/2.50  --res_backward_subs_resolution          true
% 15.92/2.50  --res_orphan_elimination                true
% 15.92/2.50  --res_time_limit                        2.
% 15.92/2.50  --res_out_proof                         true
% 15.92/2.50  
% 15.92/2.50  ------ Superposition Options
% 15.92/2.50  
% 15.92/2.50  --superposition_flag                    true
% 15.92/2.50  --sup_passive_queue_type                priority_queues
% 15.92/2.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.92/2.50  --sup_passive_queues_freq               [1;4]
% 15.92/2.50  --demod_completeness_check              fast
% 15.92/2.50  --demod_use_ground                      true
% 15.92/2.50  --sup_to_prop_solver                    passive
% 15.92/2.50  --sup_prop_simpl_new                    true
% 15.92/2.50  --sup_prop_simpl_given                  true
% 15.92/2.50  --sup_fun_splitting                     false
% 15.92/2.50  --sup_smt_interval                      50000
% 15.92/2.50  
% 15.92/2.50  ------ Superposition Simplification Setup
% 15.92/2.50  
% 15.92/2.50  --sup_indices_passive                   []
% 15.92/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.92/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.92/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.92/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.92/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.92/2.50  --sup_full_bw                           [BwDemod]
% 15.92/2.50  --sup_immed_triv                        [TrivRules]
% 15.92/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.92/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.92/2.50  --sup_immed_bw_main                     []
% 15.92/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.92/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.92/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.92/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.92/2.50  
% 15.92/2.50  ------ Combination Options
% 15.92/2.50  
% 15.92/2.50  --comb_res_mult                         3
% 15.92/2.50  --comb_sup_mult                         2
% 15.92/2.50  --comb_inst_mult                        10
% 15.92/2.50  
% 15.92/2.50  ------ Debug Options
% 15.92/2.50  
% 15.92/2.50  --dbg_backtrace                         false
% 15.92/2.50  --dbg_dump_prop_clauses                 false
% 15.92/2.50  --dbg_dump_prop_clauses_file            -
% 15.92/2.50  --dbg_out_stat                          false
% 15.92/2.50  
% 15.92/2.50  
% 15.92/2.50  
% 15.92/2.50  
% 15.92/2.50  ------ Proving...
% 15.92/2.50  
% 15.92/2.50  
% 15.92/2.50  % SZS status Theorem for theBenchmark.p
% 15.92/2.50  
% 15.92/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.92/2.50  
% 15.92/2.50  fof(f1,axiom,(
% 15.92/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f35,plain,(
% 15.92/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f1])).
% 15.92/2.50  
% 15.92/2.50  fof(f18,conjecture,(
% 15.92/2.50    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f19,negated_conjecture,(
% 15.92/2.50    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 15.92/2.50    inference(negated_conjecture,[],[f18])).
% 15.92/2.50  
% 15.92/2.50  fof(f25,plain,(
% 15.92/2.50    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 15.92/2.50    inference(ennf_transformation,[],[f19])).
% 15.92/2.50  
% 15.92/2.50  fof(f33,plain,(
% 15.92/2.50    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 15.92/2.50    introduced(choice_axiom,[])).
% 15.92/2.50  
% 15.92/2.50  fof(f34,plain,(
% 15.92/2.50    sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 15.92/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f33])).
% 15.92/2.50  
% 15.92/2.50  fof(f59,plain,(
% 15.92/2.50    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 15.92/2.50    inference(cnf_transformation,[],[f34])).
% 15.92/2.50  
% 15.92/2.50  fof(f12,axiom,(
% 15.92/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f53,plain,(
% 15.92/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.92/2.50    inference(cnf_transformation,[],[f12])).
% 15.92/2.50  
% 15.92/2.50  fof(f6,axiom,(
% 15.92/2.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f47,plain,(
% 15.92/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f6])).
% 15.92/2.50  
% 15.92/2.50  fof(f61,plain,(
% 15.92/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 15.92/2.50    inference(definition_unfolding,[],[f53,f47])).
% 15.92/2.50  
% 15.92/2.50  fof(f13,axiom,(
% 15.92/2.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f54,plain,(
% 15.92/2.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f13])).
% 15.92/2.50  
% 15.92/2.50  fof(f14,axiom,(
% 15.92/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f55,plain,(
% 15.92/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f14])).
% 15.92/2.50  
% 15.92/2.50  fof(f15,axiom,(
% 15.92/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f56,plain,(
% 15.92/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f15])).
% 15.92/2.50  
% 15.92/2.50  fof(f16,axiom,(
% 15.92/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f57,plain,(
% 15.92/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f16])).
% 15.92/2.50  
% 15.92/2.50  fof(f62,plain,(
% 15.92/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 15.92/2.50    inference(definition_unfolding,[],[f56,f57])).
% 15.92/2.50  
% 15.92/2.50  fof(f63,plain,(
% 15.92/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 15.92/2.50    inference(definition_unfolding,[],[f55,f62])).
% 15.92/2.50  
% 15.92/2.50  fof(f64,plain,(
% 15.92/2.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 15.92/2.50    inference(definition_unfolding,[],[f54,f63])).
% 15.92/2.50  
% 15.92/2.50  fof(f68,plain,(
% 15.92/2.50    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 15.92/2.50    inference(definition_unfolding,[],[f59,f61,f64,f64,f64])).
% 15.92/2.50  
% 15.92/2.50  fof(f2,axiom,(
% 15.92/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f21,plain,(
% 15.92/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.92/2.50    inference(ennf_transformation,[],[f2])).
% 15.92/2.50  
% 15.92/2.50  fof(f26,plain,(
% 15.92/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.92/2.50    inference(nnf_transformation,[],[f21])).
% 15.92/2.50  
% 15.92/2.50  fof(f27,plain,(
% 15.92/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.92/2.50    inference(rectify,[],[f26])).
% 15.92/2.50  
% 15.92/2.50  fof(f28,plain,(
% 15.92/2.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.92/2.50    introduced(choice_axiom,[])).
% 15.92/2.50  
% 15.92/2.50  fof(f29,plain,(
% 15.92/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.92/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 15.92/2.50  
% 15.92/2.50  fof(f37,plain,(
% 15.92/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f29])).
% 15.92/2.50  
% 15.92/2.50  fof(f3,axiom,(
% 15.92/2.50    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f20,plain,(
% 15.92/2.50    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 15.92/2.50    inference(rectify,[],[f3])).
% 15.92/2.50  
% 15.92/2.50  fof(f39,plain,(
% 15.92/2.50    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 15.92/2.50    inference(cnf_transformation,[],[f20])).
% 15.92/2.50  
% 15.92/2.50  fof(f65,plain,(
% 15.92/2.50    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 15.92/2.50    inference(definition_unfolding,[],[f39,f61])).
% 15.92/2.50  
% 15.92/2.50  fof(f4,axiom,(
% 15.92/2.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f22,plain,(
% 15.92/2.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 15.92/2.50    inference(ennf_transformation,[],[f4])).
% 15.92/2.50  
% 15.92/2.50  fof(f30,plain,(
% 15.92/2.50    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 15.92/2.50    inference(nnf_transformation,[],[f22])).
% 15.92/2.50  
% 15.92/2.50  fof(f43,plain,(
% 15.92/2.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f30])).
% 15.92/2.50  
% 15.92/2.50  fof(f41,plain,(
% 15.92/2.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 15.92/2.50    inference(cnf_transformation,[],[f30])).
% 15.92/2.50  
% 15.92/2.50  fof(f5,axiom,(
% 15.92/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f31,plain,(
% 15.92/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.92/2.50    inference(nnf_transformation,[],[f5])).
% 15.92/2.50  
% 15.92/2.50  fof(f32,plain,(
% 15.92/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.92/2.50    inference(flattening,[],[f31])).
% 15.92/2.50  
% 15.92/2.50  fof(f44,plain,(
% 15.92/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.92/2.50    inference(cnf_transformation,[],[f32])).
% 15.92/2.50  
% 15.92/2.50  fof(f70,plain,(
% 15.92/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.92/2.50    inference(equality_resolution,[],[f44])).
% 15.92/2.50  
% 15.92/2.50  fof(f7,axiom,(
% 15.92/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f23,plain,(
% 15.92/2.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.92/2.50    inference(ennf_transformation,[],[f7])).
% 15.92/2.50  
% 15.92/2.50  fof(f48,plain,(
% 15.92/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f23])).
% 15.92/2.50  
% 15.92/2.50  fof(f8,axiom,(
% 15.92/2.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f49,plain,(
% 15.92/2.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f8])).
% 15.92/2.50  
% 15.92/2.50  fof(f11,axiom,(
% 15.92/2.50    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f52,plain,(
% 15.92/2.50    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 15.92/2.50    inference(cnf_transformation,[],[f11])).
% 15.92/2.50  
% 15.92/2.50  fof(f10,axiom,(
% 15.92/2.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f51,plain,(
% 15.92/2.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.92/2.50    inference(cnf_transformation,[],[f10])).
% 15.92/2.50  
% 15.92/2.50  fof(f66,plain,(
% 15.92/2.50    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 15.92/2.50    inference(definition_unfolding,[],[f51,f61])).
% 15.92/2.50  
% 15.92/2.50  fof(f9,axiom,(
% 15.92/2.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f50,plain,(
% 15.92/2.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.92/2.50    inference(cnf_transformation,[],[f9])).
% 15.92/2.50  
% 15.92/2.50  fof(f17,axiom,(
% 15.92/2.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 15.92/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.92/2.50  
% 15.92/2.50  fof(f24,plain,(
% 15.92/2.50    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 15.92/2.50    inference(ennf_transformation,[],[f17])).
% 15.92/2.50  
% 15.92/2.50  fof(f58,plain,(
% 15.92/2.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 15.92/2.50    inference(cnf_transformation,[],[f24])).
% 15.92/2.50  
% 15.92/2.50  fof(f67,plain,(
% 15.92/2.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))) )),
% 15.92/2.50    inference(definition_unfolding,[],[f58,f64,f64])).
% 15.92/2.50  
% 15.92/2.50  fof(f60,plain,(
% 15.92/2.50    sK1 != sK2),
% 15.92/2.50    inference(cnf_transformation,[],[f34])).
% 15.92/2.50  
% 15.92/2.50  cnf(c_0,plain,
% 15.92/2.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.92/2.50      inference(cnf_transformation,[],[f35]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_19,negated_conjecture,
% 15.92/2.50      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 15.92/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_804,plain,
% 15.92/2.50      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_0,c_19]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_2,plain,
% 15.92/2.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.92/2.50      inference(cnf_transformation,[],[f37]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_423,plain,
% 15.92/2.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.92/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.92/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_4,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 15.92/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_5,plain,
% 15.92/2.50      ( ~ r2_hidden(X0,X1)
% 15.92/2.50      | r2_hidden(X0,X2)
% 15.92/2.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 15.92/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_421,plain,
% 15.92/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.92/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.92/2.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 15.92/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_3246,plain,
% 15.92/2.50      ( r2_hidden(X0,X1) = iProver_top
% 15.92/2.50      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) != iProver_top ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_4,c_421]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_7,plain,
% 15.92/2.50      ( ~ r2_hidden(X0,X1)
% 15.92/2.50      | ~ r2_hidden(X0,X2)
% 15.92/2.50      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(cnf_transformation,[],[f41]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_419,plain,
% 15.92/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.92/2.50      | r2_hidden(X0,X2) != iProver_top
% 15.92/2.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top ),
% 15.92/2.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_2012,plain,
% 15.92/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.92/2.50      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) != iProver_top ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_4,c_419]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_3475,plain,
% 15.92/2.50      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) != iProver_top ),
% 15.92/2.50      inference(global_propositional_subsumption,
% 15.92/2.50                [status(thm)],
% 15.92/2.50                [c_3246,c_2012]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_3482,plain,
% 15.92/2.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1) = iProver_top ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_423,c_3475]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_11,plain,
% 15.92/2.50      ( r1_tarski(X0,X0) ),
% 15.92/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_416,plain,
% 15.92/2.50      ( r1_tarski(X0,X0) = iProver_top ),
% 15.92/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_12,plain,
% 15.92/2.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.92/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_415,plain,
% 15.92/2.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.92/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_1150,plain,
% 15.92/2.50      ( k3_xboole_0(X0,X0) = X0 ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_416,c_415]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_30420,plain,
% 15.92/2.50      ( r1_tarski(k5_xboole_0(X0,X0),X1) = iProver_top ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_3482,c_1150]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_30431,plain,
% 15.92/2.50      ( k3_xboole_0(k5_xboole_0(X0,X0),X1) = k5_xboole_0(X0,X0) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_30420,c_415]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_13,plain,
% 15.92/2.50      ( r1_tarski(k1_xboole_0,X0) ),
% 15.92/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_414,plain,
% 15.92/2.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.92/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_1151,plain,
% 15.92/2.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_414,c_415]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_11553,plain,
% 15.92/2.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_1151,c_0]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_31631,plain,
% 15.92/2.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_30431,c_11553]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_16,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_15,plain,
% 15.92/2.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 15.92/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_413,plain,
% 15.92/2.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 15.92/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_777,plain,
% 15.92/2.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(k5_xboole_0(X1,X2),X0))))) = iProver_top ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_413]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_2313,plain,
% 15.92/2.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X3)),X0)))))) = iProver_top ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_777]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_9954,plain,
% 15.92/2.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X4))),X0))))))) = iProver_top ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_2313]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32113,plain,
% 15.92/2.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X1,k1_xboole_0),X0))))))) = iProver_top ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_31631,c_9954]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_14,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.92/2.50      inference(cnf_transformation,[],[f50]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_773,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_14,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_1169,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,X2))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_773,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_1170,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_1169,c_773]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32136,plain,
% 15.92/2.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(k5_xboole_0(X1,k1_xboole_0),X0)))))))) = iProver_top ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_32113,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32137,plain,
% 15.92/2.50      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X1,X0)))))))) = iProver_top ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_32136,c_14]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_67447,plain,
% 15.92/2.50      ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))))) = iProver_top ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_804,c_32137]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32074,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_31631,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_774,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_4]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_4020,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)))))) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_774,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_12281,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_4020,c_1150]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_12292,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),X2)))))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_12281]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_12475,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2))))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_12292,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_772,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X1)) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_4,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_1729,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1))) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_772]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_1814,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_1729,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_1838,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_1814,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_5261,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X0),X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_1838]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_10261,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_1150,c_5261]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_10314,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_10261,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32085,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_31631,c_10314]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32200,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_32085,c_31631]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32202,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_32200,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32203,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_32202,c_14]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_33294,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X0))) = k5_xboole_0(X1,k1_xboole_0) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_32203,c_32074]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_33555,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X0))) = X1 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_33294,c_14]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34273,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0)))))),k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,X2) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_12475,c_33555]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34639,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))))),k5_xboole_0(X1,k5_xboole_0(X2,X0))))) = k5_xboole_0(X1,X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34273,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34640,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0)))),k5_xboole_0(X1,k5_xboole_0(X2,X0)))))) = k5_xboole_0(X1,X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34639,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34641,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,k5_xboole_0(X2,X0))))))) = k5_xboole_0(X1,X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34640,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34642,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,X0)),k5_xboole_0(X1,k5_xboole_0(X2,X0)))))))) = k5_xboole_0(X1,X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34641,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34643,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,X0),k5_xboole_0(X1,k5_xboole_0(X2,X0))))))))) = k5_xboole_0(X1,X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34642,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34644,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0)))) = k5_xboole_0(X1,X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34643,c_14,c_32203]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_775,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_4]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_5576,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X0)))) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_4,c_775]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_5758,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X0)))) = X0 ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_5576,c_4]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_6202,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X0))),X1)) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_5758,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_12954,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,X0)),X1)) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_6202,c_1150]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_12960,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(k5_xboole_0(X0,X0),X1))) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_12954]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_13313,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)))) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_12960]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_13747,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)),X2))))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_16,c_13313]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_13751,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_12960,c_13313]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_13768,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X1),X2))))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_13313,c_10314]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_13782,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X0),X1)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_13313,c_10314]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_14090,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_13768,c_13782]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_14092,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X1,X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_14090,c_10314]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_14205,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2)))) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_13747,c_13751,c_14092]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_14207,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_14205,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32046,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_31631,c_14207]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32286,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))) = k5_xboole_0(X0,k1_xboole_0) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_32046,c_31631]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32288,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X0))) = X0 ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_32286,c_14]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34796,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),k5_xboole_0(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X0)),X0)) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_32288,c_32288]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34945,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X0,X1)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34796,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34946,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0))))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34945,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34947,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0)))))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34946,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34948,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0))))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 15.92/2.50      inference(demodulation,
% 15.92/2.50                [status(thm)],
% 15.92/2.50                [c_34947,c_773,c_1170,c_32074]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34949,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,X0)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34948,c_773,c_32074]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34950,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,X1)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34949,c_1170,c_32074]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_34951,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_34950,c_14,c_31631]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_36341,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_34644,c_34951]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_36522,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,X2)) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_36341,c_14,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37099,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_14,c_36522]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37180,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),X1),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_36522,c_14207]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37213,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),X1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k1_xboole_0)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_36522,c_34644]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37215,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))),X1) = k5_xboole_0(k1_xboole_0,X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_37213,c_1170,c_34951]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37399,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1))),k5_xboole_0(X2,k1_xboole_0))) = k1_xboole_0 ),
% 15.92/2.50      inference(light_normalisation,
% 15.92/2.50                [status(thm)],
% 15.92/2.50                [c_37180,c_36522,c_37215]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37401,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X0,X1)),k5_xboole_0(X2,k1_xboole_0))))) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_37399,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37402,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k1_xboole_0)))))) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_37401,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37403,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k1_xboole_0))))))) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_37402,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_37404,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))))) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_37403,c_14]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_38001,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k1_xboole_0))) = k5_xboole_0(X2,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_37099,c_34644]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_38025,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k1_xboole_0)))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_38001,c_773,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_38026,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_38025,c_14]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_41247,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1)))),k5_xboole_0(k1_xboole_0,X2)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_37404,c_38026]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_41553,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1)))),k5_xboole_0(k1_xboole_0,X2)) = k1_xboole_0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_41247,c_14,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32473,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X1)))))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_32074,c_12475]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_12325,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_12281,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_12387,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_12325,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_16932,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))),X2))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_12387,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_16933,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X0,X1)),X2)))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_16932,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_16934,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X1),X2))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_16933,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_16935,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X1,X2)))))) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_16934,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32491,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X1))))) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_32074,c_16935]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32508,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)))) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_32491,c_32074]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32510,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_32508,c_773]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32560,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_32473,c_32510]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_32562,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k1_xboole_0,X1)) = X0 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_32560,c_14,c_1170,c_31631]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_44845,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1)))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_41553,c_32562]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_45299,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X1)))) = X2 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_44845,c_14,c_38026]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_46168,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,k5_xboole_0(X2,k1_xboole_0)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_36522,c_45299]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_46763,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_46168,c_14]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_47690,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X0) = k5_xboole_0(X1,k1_xboole_0) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_37099,c_46763]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_48141,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)),X0) = X1 ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_47690,c_14,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_48969,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_37099,c_48141]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_49347,plain,
% 15.92/2.50      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X1,X0) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_48969,c_14,c_1170,c_38026]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_67586,plain,
% 15.92/2.50      ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = iProver_top ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_67447,c_32074,c_49347]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_67587,plain,
% 15.92/2.50      ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) = iProver_top ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_67586,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_7249,plain,
% 15.92/2.50      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),X0)) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_804,c_16]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_25328,plain,
% 15.92/2.50      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),X0))) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),X0) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_7249,c_1170]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_46148,plain,
% 15.92/2.50      ( k5_xboole_0(k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_25328,c_45299]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_46309,plain,
% 15.92/2.50      ( k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_45299,c_25328]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_47157,plain,
% 15.92/2.50      ( k3_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_46309,c_32074]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_47631,plain,
% 15.92/2.50      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_46148,c_47157]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_47633,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k1_xboole_0)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_47631,c_1170,c_31631]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_47634,plain,
% 15.92/2.50      ( k5_xboole_0(k1_xboole_0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_47633,c_14,c_34951]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_59002,plain,
% 15.92/2.50      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = k5_xboole_0(X0,k1_xboole_0) ),
% 15.92/2.50      inference(superposition,[status(thm)],[c_47634,c_46763]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_59004,plain,
% 15.92/2.50      ( k5_xboole_0(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k5_xboole_0(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) = X0 ),
% 15.92/2.50      inference(light_normalisation,[status(thm)],[c_59002,c_14]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_67588,plain,
% 15.92/2.50      ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 15.92/2.50      inference(demodulation,[status(thm)],[c_67587,c_59004]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_17,plain,
% 15.92/2.50      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))
% 15.92/2.50      | X1 = X0 ),
% 15.92/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_544,plain,
% 15.92/2.50      ( ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
% 15.92/2.50      | sK1 = sK2 ),
% 15.92/2.50      inference(instantiation,[status(thm)],[c_17]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_545,plain,
% 15.92/2.50      ( sK1 = sK2
% 15.92/2.50      | r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 15.92/2.50      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(c_18,negated_conjecture,
% 15.92/2.50      ( sK1 != sK2 ),
% 15.92/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.92/2.50  
% 15.92/2.50  cnf(contradiction,plain,
% 15.92/2.50      ( $false ),
% 15.92/2.50      inference(minisat,[status(thm)],[c_67588,c_545,c_18]) ).
% 15.92/2.50  
% 15.92/2.50  
% 15.92/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.92/2.50  
% 15.92/2.50  ------                               Statistics
% 15.92/2.50  
% 15.92/2.50  ------ Selected
% 15.92/2.50  
% 15.92/2.50  total_time:                             1.952
% 15.92/2.50  
%------------------------------------------------------------------------------
