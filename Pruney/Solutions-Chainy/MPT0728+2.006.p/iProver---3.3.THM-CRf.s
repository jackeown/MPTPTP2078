%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:18 EST 2020

% Result     : Theorem 23.44s
% Output     : CNFRefutation 23.44s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 356 expanded)
%              Number of clauses        :   34 (  52 expanded)
%              Number of leaves         :   17 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :  196 ( 542 expanded)
%              Number of equality atoms :   72 ( 311 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f62,plain,(
    ! [X2,X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))) ),
    inference(definition_unfolding,[],[f42,f59,f58])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f59,f57])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,conjecture,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,
    ( ? [X0] : ~ r2_hidden(X0,k1_ordinal1(X0))
   => ~ r2_hidden(sK1,k1_ordinal1(sK1)) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ~ r2_hidden(sK1,k1_ordinal1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).

fof(f55,plain,(
    ~ r2_hidden(sK1,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f61,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f53,f58,f60])).

fof(f67,plain,(
    ~ r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f55,f61])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_10,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_466,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_532,plain,
    ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_466,c_14])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_471,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1686,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_471])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_473,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2449,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X3)) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) = iProver_top
    | r1_tarski(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1686,c_473])).

cnf(c_22322,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X3))) = iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_532,c_2449])).

cnf(c_16,negated_conjecture,
    ( ~ r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_461,plain,
    ( r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_64171,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK1,X0)) != iProver_top
    | r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22322,c_461])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_20,plain,
    ( r2_hidden(sK1,sK1) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_34,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_634,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_636,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X0,X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_638,plain,
    ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_636])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_635,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0))
    | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_640,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) = iProver_top
    | r1_tarski(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X1,X1,X1,X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_642,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top
    | r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_640])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_699,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X0))
    | r2_hidden(X0,k5_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_708,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X0)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_710,plain,
    ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(sK1,k5_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = iProver_top
    | r2_hidden(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_64145,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != iProver_top
    | r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22322,c_461])).

cnf(c_67502,plain,
    ( r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_64171,c_20,c_34,c_638,c_642,c_710,c_64145])).

cnf(c_67511,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_67502,c_461])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:27:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.44/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.44/3.49  
% 23.44/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.44/3.49  
% 23.44/3.49  ------  iProver source info
% 23.44/3.49  
% 23.44/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.44/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.44/3.49  git: non_committed_changes: false
% 23.44/3.49  git: last_make_outside_of_git: false
% 23.44/3.49  
% 23.44/3.49  ------ 
% 23.44/3.49  
% 23.44/3.49  ------ Input Options
% 23.44/3.49  
% 23.44/3.49  --out_options                           all
% 23.44/3.49  --tptp_safe_out                         true
% 23.44/3.49  --problem_path                          ""
% 23.44/3.49  --include_path                          ""
% 23.44/3.49  --clausifier                            res/vclausify_rel
% 23.44/3.49  --clausifier_options                    --mode clausify
% 23.44/3.49  --stdin                                 false
% 23.44/3.49  --stats_out                             sel
% 23.44/3.49  
% 23.44/3.49  ------ General Options
% 23.44/3.49  
% 23.44/3.49  --fof                                   false
% 23.44/3.49  --time_out_real                         604.99
% 23.44/3.49  --time_out_virtual                      -1.
% 23.44/3.49  --symbol_type_check                     false
% 23.44/3.49  --clausify_out                          false
% 23.44/3.49  --sig_cnt_out                           false
% 23.44/3.49  --trig_cnt_out                          false
% 23.44/3.49  --trig_cnt_out_tolerance                1.
% 23.44/3.49  --trig_cnt_out_sk_spl                   false
% 23.44/3.49  --abstr_cl_out                          false
% 23.44/3.49  
% 23.44/3.49  ------ Global Options
% 23.44/3.49  
% 23.44/3.49  --schedule                              none
% 23.44/3.49  --add_important_lit                     false
% 23.44/3.49  --prop_solver_per_cl                    1000
% 23.44/3.49  --min_unsat_core                        false
% 23.44/3.49  --soft_assumptions                      false
% 23.44/3.49  --soft_lemma_size                       3
% 23.44/3.49  --prop_impl_unit_size                   0
% 23.44/3.49  --prop_impl_unit                        []
% 23.44/3.49  --share_sel_clauses                     true
% 23.44/3.49  --reset_solvers                         false
% 23.44/3.49  --bc_imp_inh                            [conj_cone]
% 23.44/3.49  --conj_cone_tolerance                   3.
% 23.44/3.49  --extra_neg_conj                        none
% 23.44/3.49  --large_theory_mode                     true
% 23.44/3.49  --prolific_symb_bound                   200
% 23.44/3.49  --lt_threshold                          2000
% 23.44/3.49  --clause_weak_htbl                      true
% 23.44/3.49  --gc_record_bc_elim                     false
% 23.44/3.49  
% 23.44/3.49  ------ Preprocessing Options
% 23.44/3.49  
% 23.44/3.49  --preprocessing_flag                    true
% 23.44/3.49  --time_out_prep_mult                    0.1
% 23.44/3.49  --splitting_mode                        input
% 23.44/3.49  --splitting_grd                         true
% 23.44/3.49  --splitting_cvd                         false
% 23.44/3.49  --splitting_cvd_svl                     false
% 23.44/3.49  --splitting_nvd                         32
% 23.44/3.49  --sub_typing                            true
% 23.44/3.49  --prep_gs_sim                           false
% 23.44/3.49  --prep_unflatten                        true
% 23.44/3.49  --prep_res_sim                          true
% 23.44/3.49  --prep_upred                            true
% 23.44/3.49  --prep_sem_filter                       exhaustive
% 23.44/3.49  --prep_sem_filter_out                   false
% 23.44/3.49  --pred_elim                             false
% 23.44/3.49  --res_sim_input                         true
% 23.44/3.49  --eq_ax_congr_red                       true
% 23.44/3.49  --pure_diseq_elim                       true
% 23.44/3.49  --brand_transform                       false
% 23.44/3.49  --non_eq_to_eq                          false
% 23.44/3.49  --prep_def_merge                        true
% 23.44/3.49  --prep_def_merge_prop_impl              false
% 23.44/3.50  --prep_def_merge_mbd                    true
% 23.44/3.50  --prep_def_merge_tr_red                 false
% 23.44/3.50  --prep_def_merge_tr_cl                  false
% 23.44/3.50  --smt_preprocessing                     true
% 23.44/3.50  --smt_ac_axioms                         fast
% 23.44/3.50  --preprocessed_out                      false
% 23.44/3.50  --preprocessed_stats                    false
% 23.44/3.50  
% 23.44/3.50  ------ Abstraction refinement Options
% 23.44/3.50  
% 23.44/3.50  --abstr_ref                             []
% 23.44/3.50  --abstr_ref_prep                        false
% 23.44/3.50  --abstr_ref_until_sat                   false
% 23.44/3.50  --abstr_ref_sig_restrict                funpre
% 23.44/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.44/3.50  --abstr_ref_under                       []
% 23.44/3.50  
% 23.44/3.50  ------ SAT Options
% 23.44/3.50  
% 23.44/3.50  --sat_mode                              false
% 23.44/3.50  --sat_fm_restart_options                ""
% 23.44/3.50  --sat_gr_def                            false
% 23.44/3.50  --sat_epr_types                         true
% 23.44/3.50  --sat_non_cyclic_types                  false
% 23.44/3.50  --sat_finite_models                     false
% 23.44/3.50  --sat_fm_lemmas                         false
% 23.44/3.50  --sat_fm_prep                           false
% 23.44/3.50  --sat_fm_uc_incr                        true
% 23.44/3.50  --sat_out_model                         small
% 23.44/3.50  --sat_out_clauses                       false
% 23.44/3.50  
% 23.44/3.50  ------ QBF Options
% 23.44/3.50  
% 23.44/3.50  --qbf_mode                              false
% 23.44/3.50  --qbf_elim_univ                         false
% 23.44/3.50  --qbf_dom_inst                          none
% 23.44/3.50  --qbf_dom_pre_inst                      false
% 23.44/3.50  --qbf_sk_in                             false
% 23.44/3.50  --qbf_pred_elim                         true
% 23.44/3.50  --qbf_split                             512
% 23.44/3.50  
% 23.44/3.50  ------ BMC1 Options
% 23.44/3.50  
% 23.44/3.50  --bmc1_incremental                      false
% 23.44/3.50  --bmc1_axioms                           reachable_all
% 23.44/3.50  --bmc1_min_bound                        0
% 23.44/3.50  --bmc1_max_bound                        -1
% 23.44/3.50  --bmc1_max_bound_default                -1
% 23.44/3.50  --bmc1_symbol_reachability              true
% 23.44/3.50  --bmc1_property_lemmas                  false
% 23.44/3.50  --bmc1_k_induction                      false
% 23.44/3.50  --bmc1_non_equiv_states                 false
% 23.44/3.50  --bmc1_deadlock                         false
% 23.44/3.50  --bmc1_ucm                              false
% 23.44/3.50  --bmc1_add_unsat_core                   none
% 23.44/3.50  --bmc1_unsat_core_children              false
% 23.44/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.44/3.50  --bmc1_out_stat                         full
% 23.44/3.50  --bmc1_ground_init                      false
% 23.44/3.50  --bmc1_pre_inst_next_state              false
% 23.44/3.50  --bmc1_pre_inst_state                   false
% 23.44/3.50  --bmc1_pre_inst_reach_state             false
% 23.44/3.50  --bmc1_out_unsat_core                   false
% 23.44/3.50  --bmc1_aig_witness_out                  false
% 23.44/3.50  --bmc1_verbose                          false
% 23.44/3.50  --bmc1_dump_clauses_tptp                false
% 23.44/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.44/3.50  --bmc1_dump_file                        -
% 23.44/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.44/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.44/3.50  --bmc1_ucm_extend_mode                  1
% 23.44/3.50  --bmc1_ucm_init_mode                    2
% 23.44/3.50  --bmc1_ucm_cone_mode                    none
% 23.44/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.44/3.50  --bmc1_ucm_relax_model                  4
% 23.44/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.44/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.44/3.50  --bmc1_ucm_layered_model                none
% 23.44/3.50  --bmc1_ucm_max_lemma_size               10
% 23.44/3.50  
% 23.44/3.50  ------ AIG Options
% 23.44/3.50  
% 23.44/3.50  --aig_mode                              false
% 23.44/3.50  
% 23.44/3.50  ------ Instantiation Options
% 23.44/3.50  
% 23.44/3.50  --instantiation_flag                    true
% 23.44/3.50  --inst_sos_flag                         false
% 23.44/3.50  --inst_sos_phase                        true
% 23.44/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.44/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.44/3.50  --inst_lit_sel_side                     num_symb
% 23.44/3.50  --inst_solver_per_active                1400
% 23.44/3.50  --inst_solver_calls_frac                1.
% 23.44/3.50  --inst_passive_queue_type               priority_queues
% 23.44/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.44/3.50  --inst_passive_queues_freq              [25;2]
% 23.44/3.50  --inst_dismatching                      true
% 23.44/3.50  --inst_eager_unprocessed_to_passive     true
% 23.44/3.50  --inst_prop_sim_given                   true
% 23.44/3.50  --inst_prop_sim_new                     false
% 23.44/3.50  --inst_subs_new                         false
% 23.44/3.50  --inst_eq_res_simp                      false
% 23.44/3.50  --inst_subs_given                       false
% 23.44/3.50  --inst_orphan_elimination               true
% 23.44/3.50  --inst_learning_loop_flag               true
% 23.44/3.50  --inst_learning_start                   3000
% 23.44/3.50  --inst_learning_factor                  2
% 23.44/3.50  --inst_start_prop_sim_after_learn       3
% 23.44/3.50  --inst_sel_renew                        solver
% 23.44/3.50  --inst_lit_activity_flag                true
% 23.44/3.50  --inst_restr_to_given                   false
% 23.44/3.50  --inst_activity_threshold               500
% 23.44/3.50  --inst_out_proof                        true
% 23.44/3.50  
% 23.44/3.50  ------ Resolution Options
% 23.44/3.50  
% 23.44/3.50  --resolution_flag                       true
% 23.44/3.50  --res_lit_sel                           adaptive
% 23.44/3.50  --res_lit_sel_side                      none
% 23.44/3.50  --res_ordering                          kbo
% 23.44/3.50  --res_to_prop_solver                    active
% 23.44/3.50  --res_prop_simpl_new                    false
% 23.44/3.50  --res_prop_simpl_given                  true
% 23.44/3.50  --res_passive_queue_type                priority_queues
% 23.44/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.44/3.50  --res_passive_queues_freq               [15;5]
% 23.44/3.50  --res_forward_subs                      full
% 23.44/3.50  --res_backward_subs                     full
% 23.44/3.50  --res_forward_subs_resolution           true
% 23.44/3.50  --res_backward_subs_resolution          true
% 23.44/3.50  --res_orphan_elimination                true
% 23.44/3.50  --res_time_limit                        2.
% 23.44/3.50  --res_out_proof                         true
% 23.44/3.50  
% 23.44/3.50  ------ Superposition Options
% 23.44/3.50  
% 23.44/3.50  --superposition_flag                    true
% 23.44/3.50  --sup_passive_queue_type                priority_queues
% 23.44/3.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.44/3.50  --sup_passive_queues_freq               [1;4]
% 23.44/3.50  --demod_completeness_check              fast
% 23.44/3.50  --demod_use_ground                      true
% 23.44/3.50  --sup_to_prop_solver                    passive
% 23.44/3.50  --sup_prop_simpl_new                    true
% 23.44/3.50  --sup_prop_simpl_given                  true
% 23.44/3.50  --sup_fun_splitting                     false
% 23.44/3.50  --sup_smt_interval                      50000
% 23.44/3.50  
% 23.44/3.50  ------ Superposition Simplification Setup
% 23.44/3.50  
% 23.44/3.50  --sup_indices_passive                   []
% 23.44/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.44/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.44/3.50  --sup_full_bw                           [BwDemod]
% 23.44/3.50  --sup_immed_triv                        [TrivRules]
% 23.44/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.44/3.50  --sup_immed_bw_main                     []
% 23.44/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.44/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.44/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.44/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.44/3.50  
% 23.44/3.50  ------ Combination Options
% 23.44/3.50  
% 23.44/3.50  --comb_res_mult                         3
% 23.44/3.50  --comb_sup_mult                         2
% 23.44/3.50  --comb_inst_mult                        10
% 23.44/3.50  
% 23.44/3.50  ------ Debug Options
% 23.44/3.50  
% 23.44/3.50  --dbg_backtrace                         false
% 23.44/3.50  --dbg_dump_prop_clauses                 false
% 23.44/3.50  --dbg_dump_prop_clauses_file            -
% 23.44/3.50  --dbg_out_stat                          false
% 23.44/3.50  ------ Parsing...
% 23.44/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.44/3.50  
% 23.44/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.44/3.50  
% 23.44/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.44/3.50  
% 23.44/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.44/3.50  ------ Proving...
% 23.44/3.50  ------ Problem Properties 
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  clauses                                 16
% 23.44/3.50  conjectures                             1
% 23.44/3.50  EPR                                     4
% 23.44/3.50  Horn                                    12
% 23.44/3.50  unary                                   4
% 23.44/3.50  binary                                  5
% 23.44/3.50  lits                                    35
% 23.44/3.50  lits eq                                 2
% 23.44/3.50  fd_pure                                 0
% 23.44/3.50  fd_pseudo                               0
% 23.44/3.50  fd_cond                                 0
% 23.44/3.50  fd_pseudo_cond                          1
% 23.44/3.50  AC symbols                              0
% 23.44/3.50  
% 23.44/3.50  ------ Input Options Time Limit: Unbounded
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  ------ 
% 23.44/3.50  Current options:
% 23.44/3.50  ------ 
% 23.44/3.50  
% 23.44/3.50  ------ Input Options
% 23.44/3.50  
% 23.44/3.50  --out_options                           all
% 23.44/3.50  --tptp_safe_out                         true
% 23.44/3.50  --problem_path                          ""
% 23.44/3.50  --include_path                          ""
% 23.44/3.50  --clausifier                            res/vclausify_rel
% 23.44/3.50  --clausifier_options                    --mode clausify
% 23.44/3.50  --stdin                                 false
% 23.44/3.50  --stats_out                             sel
% 23.44/3.50  
% 23.44/3.50  ------ General Options
% 23.44/3.50  
% 23.44/3.50  --fof                                   false
% 23.44/3.50  --time_out_real                         604.99
% 23.44/3.50  --time_out_virtual                      -1.
% 23.44/3.50  --symbol_type_check                     false
% 23.44/3.50  --clausify_out                          false
% 23.44/3.50  --sig_cnt_out                           false
% 23.44/3.50  --trig_cnt_out                          false
% 23.44/3.50  --trig_cnt_out_tolerance                1.
% 23.44/3.50  --trig_cnt_out_sk_spl                   false
% 23.44/3.50  --abstr_cl_out                          false
% 23.44/3.50  
% 23.44/3.50  ------ Global Options
% 23.44/3.50  
% 23.44/3.50  --schedule                              none
% 23.44/3.50  --add_important_lit                     false
% 23.44/3.50  --prop_solver_per_cl                    1000
% 23.44/3.50  --min_unsat_core                        false
% 23.44/3.50  --soft_assumptions                      false
% 23.44/3.50  --soft_lemma_size                       3
% 23.44/3.50  --prop_impl_unit_size                   0
% 23.44/3.50  --prop_impl_unit                        []
% 23.44/3.50  --share_sel_clauses                     true
% 23.44/3.50  --reset_solvers                         false
% 23.44/3.50  --bc_imp_inh                            [conj_cone]
% 23.44/3.50  --conj_cone_tolerance                   3.
% 23.44/3.50  --extra_neg_conj                        none
% 23.44/3.50  --large_theory_mode                     true
% 23.44/3.50  --prolific_symb_bound                   200
% 23.44/3.50  --lt_threshold                          2000
% 23.44/3.50  --clause_weak_htbl                      true
% 23.44/3.50  --gc_record_bc_elim                     false
% 23.44/3.50  
% 23.44/3.50  ------ Preprocessing Options
% 23.44/3.50  
% 23.44/3.50  --preprocessing_flag                    true
% 23.44/3.50  --time_out_prep_mult                    0.1
% 23.44/3.50  --splitting_mode                        input
% 23.44/3.50  --splitting_grd                         true
% 23.44/3.50  --splitting_cvd                         false
% 23.44/3.50  --splitting_cvd_svl                     false
% 23.44/3.50  --splitting_nvd                         32
% 23.44/3.50  --sub_typing                            true
% 23.44/3.50  --prep_gs_sim                           false
% 23.44/3.50  --prep_unflatten                        true
% 23.44/3.50  --prep_res_sim                          true
% 23.44/3.50  --prep_upred                            true
% 23.44/3.50  --prep_sem_filter                       exhaustive
% 23.44/3.50  --prep_sem_filter_out                   false
% 23.44/3.50  --pred_elim                             false
% 23.44/3.50  --res_sim_input                         true
% 23.44/3.50  --eq_ax_congr_red                       true
% 23.44/3.50  --pure_diseq_elim                       true
% 23.44/3.50  --brand_transform                       false
% 23.44/3.50  --non_eq_to_eq                          false
% 23.44/3.50  --prep_def_merge                        true
% 23.44/3.50  --prep_def_merge_prop_impl              false
% 23.44/3.50  --prep_def_merge_mbd                    true
% 23.44/3.50  --prep_def_merge_tr_red                 false
% 23.44/3.50  --prep_def_merge_tr_cl                  false
% 23.44/3.50  --smt_preprocessing                     true
% 23.44/3.50  --smt_ac_axioms                         fast
% 23.44/3.50  --preprocessed_out                      false
% 23.44/3.50  --preprocessed_stats                    false
% 23.44/3.50  
% 23.44/3.50  ------ Abstraction refinement Options
% 23.44/3.50  
% 23.44/3.50  --abstr_ref                             []
% 23.44/3.50  --abstr_ref_prep                        false
% 23.44/3.50  --abstr_ref_until_sat                   false
% 23.44/3.50  --abstr_ref_sig_restrict                funpre
% 23.44/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.44/3.50  --abstr_ref_under                       []
% 23.44/3.50  
% 23.44/3.50  ------ SAT Options
% 23.44/3.50  
% 23.44/3.50  --sat_mode                              false
% 23.44/3.50  --sat_fm_restart_options                ""
% 23.44/3.50  --sat_gr_def                            false
% 23.44/3.50  --sat_epr_types                         true
% 23.44/3.50  --sat_non_cyclic_types                  false
% 23.44/3.50  --sat_finite_models                     false
% 23.44/3.50  --sat_fm_lemmas                         false
% 23.44/3.50  --sat_fm_prep                           false
% 23.44/3.50  --sat_fm_uc_incr                        true
% 23.44/3.50  --sat_out_model                         small
% 23.44/3.50  --sat_out_clauses                       false
% 23.44/3.50  
% 23.44/3.50  ------ QBF Options
% 23.44/3.50  
% 23.44/3.50  --qbf_mode                              false
% 23.44/3.50  --qbf_elim_univ                         false
% 23.44/3.50  --qbf_dom_inst                          none
% 23.44/3.50  --qbf_dom_pre_inst                      false
% 23.44/3.50  --qbf_sk_in                             false
% 23.44/3.50  --qbf_pred_elim                         true
% 23.44/3.50  --qbf_split                             512
% 23.44/3.50  
% 23.44/3.50  ------ BMC1 Options
% 23.44/3.50  
% 23.44/3.50  --bmc1_incremental                      false
% 23.44/3.50  --bmc1_axioms                           reachable_all
% 23.44/3.50  --bmc1_min_bound                        0
% 23.44/3.50  --bmc1_max_bound                        -1
% 23.44/3.50  --bmc1_max_bound_default                -1
% 23.44/3.50  --bmc1_symbol_reachability              true
% 23.44/3.50  --bmc1_property_lemmas                  false
% 23.44/3.50  --bmc1_k_induction                      false
% 23.44/3.50  --bmc1_non_equiv_states                 false
% 23.44/3.50  --bmc1_deadlock                         false
% 23.44/3.50  --bmc1_ucm                              false
% 23.44/3.50  --bmc1_add_unsat_core                   none
% 23.44/3.50  --bmc1_unsat_core_children              false
% 23.44/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.44/3.50  --bmc1_out_stat                         full
% 23.44/3.50  --bmc1_ground_init                      false
% 23.44/3.50  --bmc1_pre_inst_next_state              false
% 23.44/3.50  --bmc1_pre_inst_state                   false
% 23.44/3.50  --bmc1_pre_inst_reach_state             false
% 23.44/3.50  --bmc1_out_unsat_core                   false
% 23.44/3.50  --bmc1_aig_witness_out                  false
% 23.44/3.50  --bmc1_verbose                          false
% 23.44/3.50  --bmc1_dump_clauses_tptp                false
% 23.44/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.44/3.50  --bmc1_dump_file                        -
% 23.44/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.44/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.44/3.50  --bmc1_ucm_extend_mode                  1
% 23.44/3.50  --bmc1_ucm_init_mode                    2
% 23.44/3.50  --bmc1_ucm_cone_mode                    none
% 23.44/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.44/3.50  --bmc1_ucm_relax_model                  4
% 23.44/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.44/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.44/3.50  --bmc1_ucm_layered_model                none
% 23.44/3.50  --bmc1_ucm_max_lemma_size               10
% 23.44/3.50  
% 23.44/3.50  ------ AIG Options
% 23.44/3.50  
% 23.44/3.50  --aig_mode                              false
% 23.44/3.50  
% 23.44/3.50  ------ Instantiation Options
% 23.44/3.50  
% 23.44/3.50  --instantiation_flag                    true
% 23.44/3.50  --inst_sos_flag                         false
% 23.44/3.50  --inst_sos_phase                        true
% 23.44/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.44/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.44/3.50  --inst_lit_sel_side                     num_symb
% 23.44/3.50  --inst_solver_per_active                1400
% 23.44/3.50  --inst_solver_calls_frac                1.
% 23.44/3.50  --inst_passive_queue_type               priority_queues
% 23.44/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.44/3.50  --inst_passive_queues_freq              [25;2]
% 23.44/3.50  --inst_dismatching                      true
% 23.44/3.50  --inst_eager_unprocessed_to_passive     true
% 23.44/3.50  --inst_prop_sim_given                   true
% 23.44/3.50  --inst_prop_sim_new                     false
% 23.44/3.50  --inst_subs_new                         false
% 23.44/3.50  --inst_eq_res_simp                      false
% 23.44/3.50  --inst_subs_given                       false
% 23.44/3.50  --inst_orphan_elimination               true
% 23.44/3.50  --inst_learning_loop_flag               true
% 23.44/3.50  --inst_learning_start                   3000
% 23.44/3.50  --inst_learning_factor                  2
% 23.44/3.50  --inst_start_prop_sim_after_learn       3
% 23.44/3.50  --inst_sel_renew                        solver
% 23.44/3.50  --inst_lit_activity_flag                true
% 23.44/3.50  --inst_restr_to_given                   false
% 23.44/3.50  --inst_activity_threshold               500
% 23.44/3.50  --inst_out_proof                        true
% 23.44/3.50  
% 23.44/3.50  ------ Resolution Options
% 23.44/3.50  
% 23.44/3.50  --resolution_flag                       true
% 23.44/3.50  --res_lit_sel                           adaptive
% 23.44/3.50  --res_lit_sel_side                      none
% 23.44/3.50  --res_ordering                          kbo
% 23.44/3.50  --res_to_prop_solver                    active
% 23.44/3.50  --res_prop_simpl_new                    false
% 23.44/3.50  --res_prop_simpl_given                  true
% 23.44/3.50  --res_passive_queue_type                priority_queues
% 23.44/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.44/3.50  --res_passive_queues_freq               [15;5]
% 23.44/3.50  --res_forward_subs                      full
% 23.44/3.50  --res_backward_subs                     full
% 23.44/3.50  --res_forward_subs_resolution           true
% 23.44/3.50  --res_backward_subs_resolution          true
% 23.44/3.50  --res_orphan_elimination                true
% 23.44/3.50  --res_time_limit                        2.
% 23.44/3.50  --res_out_proof                         true
% 23.44/3.50  
% 23.44/3.50  ------ Superposition Options
% 23.44/3.50  
% 23.44/3.50  --superposition_flag                    true
% 23.44/3.50  --sup_passive_queue_type                priority_queues
% 23.44/3.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.44/3.50  --sup_passive_queues_freq               [1;4]
% 23.44/3.50  --demod_completeness_check              fast
% 23.44/3.50  --demod_use_ground                      true
% 23.44/3.50  --sup_to_prop_solver                    passive
% 23.44/3.50  --sup_prop_simpl_new                    true
% 23.44/3.50  --sup_prop_simpl_given                  true
% 23.44/3.50  --sup_fun_splitting                     false
% 23.44/3.50  --sup_smt_interval                      50000
% 23.44/3.50  
% 23.44/3.50  ------ Superposition Simplification Setup
% 23.44/3.50  
% 23.44/3.50  --sup_indices_passive                   []
% 23.44/3.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 23.44/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.44/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.44/3.50  --sup_full_bw                           [BwDemod]
% 23.44/3.50  --sup_immed_triv                        [TrivRules]
% 23.44/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.44/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.44/3.50  --sup_immed_bw_main                     []
% 23.44/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.44/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.44/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 23.44/3.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 23.44/3.50  
% 23.44/3.50  ------ Combination Options
% 23.44/3.50  
% 23.44/3.50  --comb_res_mult                         3
% 23.44/3.50  --comb_sup_mult                         2
% 23.44/3.50  --comb_inst_mult                        10
% 23.44/3.50  
% 23.44/3.50  ------ Debug Options
% 23.44/3.50  
% 23.44/3.50  --dbg_backtrace                         false
% 23.44/3.50  --dbg_dump_prop_clauses                 false
% 23.44/3.50  --dbg_dump_prop_clauses_file            -
% 23.44/3.50  --dbg_out_stat                          false
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  ------ Proving...
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  % SZS status Theorem for theBenchmark.p
% 23.44/3.50  
% 23.44/3.50   Resolution empty clause
% 23.44/3.50  
% 23.44/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.44/3.50  
% 23.44/3.50  fof(f4,axiom,(
% 23.44/3.50    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f42,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 23.44/3.50    inference(cnf_transformation,[],[f4])).
% 23.44/3.50  
% 23.44/3.50  fof(f5,axiom,(
% 23.44/3.50    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f43,plain,(
% 23.44/3.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f5])).
% 23.44/3.50  
% 23.44/3.50  fof(f59,plain,(
% 23.44/3.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 23.44/3.50    inference(definition_unfolding,[],[f43,f58])).
% 23.44/3.50  
% 23.44/3.50  fof(f10,axiom,(
% 23.44/3.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f48,plain,(
% 23.44/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.44/3.50    inference(cnf_transformation,[],[f10])).
% 23.44/3.50  
% 23.44/3.50  fof(f7,axiom,(
% 23.44/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f45,plain,(
% 23.44/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f7])).
% 23.44/3.50  
% 23.44/3.50  fof(f8,axiom,(
% 23.44/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f46,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f8])).
% 23.44/3.50  
% 23.44/3.50  fof(f9,axiom,(
% 23.44/3.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f47,plain,(
% 23.44/3.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f9])).
% 23.44/3.50  
% 23.44/3.50  fof(f56,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 23.44/3.50    inference(definition_unfolding,[],[f46,f47])).
% 23.44/3.50  
% 23.44/3.50  fof(f57,plain,(
% 23.44/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 23.44/3.50    inference(definition_unfolding,[],[f45,f56])).
% 23.44/3.50  
% 23.44/3.50  fof(f58,plain,(
% 23.44/3.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 23.44/3.50    inference(definition_unfolding,[],[f48,f57])).
% 23.44/3.50  
% 23.44/3.50  fof(f62,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)))) )),
% 23.44/3.50    inference(definition_unfolding,[],[f42,f59,f58])).
% 23.44/3.50  
% 23.44/3.50  fof(f12,axiom,(
% 23.44/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f52,plain,(
% 23.44/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 23.44/3.50    inference(cnf_transformation,[],[f12])).
% 23.44/3.50  
% 23.44/3.50  fof(f66,plain,(
% 23.44/3.50    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 23.44/3.50    inference(definition_unfolding,[],[f52,f59,f57])).
% 23.44/3.50  
% 23.44/3.50  fof(f2,axiom,(
% 23.44/3.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f18,plain,(
% 23.44/3.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 23.44/3.50    inference(ennf_transformation,[],[f2])).
% 23.44/3.50  
% 23.44/3.50  fof(f25,plain,(
% 23.44/3.50    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 23.44/3.50    inference(nnf_transformation,[],[f18])).
% 23.44/3.50  
% 23.44/3.50  fof(f37,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f25])).
% 23.44/3.50  
% 23.44/3.50  fof(f1,axiom,(
% 23.44/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f17,plain,(
% 23.44/3.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 23.44/3.50    inference(ennf_transformation,[],[f1])).
% 23.44/3.50  
% 23.44/3.50  fof(f21,plain,(
% 23.44/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 23.44/3.50    inference(nnf_transformation,[],[f17])).
% 23.44/3.50  
% 23.44/3.50  fof(f22,plain,(
% 23.44/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.44/3.50    inference(rectify,[],[f21])).
% 23.44/3.50  
% 23.44/3.50  fof(f23,plain,(
% 23.44/3.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f24,plain,(
% 23.44/3.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 23.44/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 23.44/3.50  
% 23.44/3.50  fof(f32,plain,(
% 23.44/3.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f24])).
% 23.44/3.50  
% 23.44/3.50  fof(f15,conjecture,(
% 23.44/3.50    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f16,negated_conjecture,(
% 23.44/3.50    ~! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 23.44/3.50    inference(negated_conjecture,[],[f15])).
% 23.44/3.50  
% 23.44/3.50  fof(f20,plain,(
% 23.44/3.50    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0))),
% 23.44/3.50    inference(ennf_transformation,[],[f16])).
% 23.44/3.50  
% 23.44/3.50  fof(f30,plain,(
% 23.44/3.50    ? [X0] : ~r2_hidden(X0,k1_ordinal1(X0)) => ~r2_hidden(sK1,k1_ordinal1(sK1))),
% 23.44/3.50    introduced(choice_axiom,[])).
% 23.44/3.50  
% 23.44/3.50  fof(f31,plain,(
% 23.44/3.50    ~r2_hidden(sK1,k1_ordinal1(sK1))),
% 23.44/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f30])).
% 23.44/3.50  
% 23.44/3.50  fof(f55,plain,(
% 23.44/3.50    ~r2_hidden(sK1,k1_ordinal1(sK1))),
% 23.44/3.50    inference(cnf_transformation,[],[f31])).
% 23.44/3.50  
% 23.44/3.50  fof(f13,axiom,(
% 23.44/3.50    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f53,plain,(
% 23.44/3.50    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f13])).
% 23.44/3.50  
% 23.44/3.50  fof(f6,axiom,(
% 23.44/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f44,plain,(
% 23.44/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f6])).
% 23.44/3.50  
% 23.44/3.50  fof(f60,plain,(
% 23.44/3.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 23.44/3.50    inference(definition_unfolding,[],[f44,f57])).
% 23.44/3.50  
% 23.44/3.50  fof(f61,plain,(
% 23.44/3.50    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 23.44/3.50    inference(definition_unfolding,[],[f53,f58,f60])).
% 23.44/3.50  
% 23.44/3.50  fof(f67,plain,(
% 23.44/3.50    ~r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))))),
% 23.44/3.50    inference(definition_unfolding,[],[f55,f61])).
% 23.44/3.50  
% 23.44/3.50  fof(f14,axiom,(
% 23.44/3.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f19,plain,(
% 23.44/3.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 23.44/3.50    inference(ennf_transformation,[],[f14])).
% 23.44/3.50  
% 23.44/3.50  fof(f54,plain,(
% 23.44/3.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f19])).
% 23.44/3.50  
% 23.44/3.50  fof(f3,axiom,(
% 23.44/3.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f26,plain,(
% 23.44/3.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.44/3.50    inference(nnf_transformation,[],[f3])).
% 23.44/3.50  
% 23.44/3.50  fof(f27,plain,(
% 23.44/3.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.44/3.50    inference(flattening,[],[f26])).
% 23.44/3.50  
% 23.44/3.50  fof(f39,plain,(
% 23.44/3.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.44/3.50    inference(cnf_transformation,[],[f27])).
% 23.44/3.50  
% 23.44/3.50  fof(f69,plain,(
% 23.44/3.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.44/3.50    inference(equality_resolution,[],[f39])).
% 23.44/3.50  
% 23.44/3.50  fof(f11,axiom,(
% 23.44/3.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 23.44/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.44/3.50  
% 23.44/3.50  fof(f28,plain,(
% 23.44/3.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 23.44/3.50    inference(nnf_transformation,[],[f11])).
% 23.44/3.50  
% 23.44/3.50  fof(f29,plain,(
% 23.44/3.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 23.44/3.50    inference(flattening,[],[f28])).
% 23.44/3.50  
% 23.44/3.50  fof(f50,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f29])).
% 23.44/3.50  
% 23.44/3.50  fof(f64,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)) )),
% 23.44/3.50    inference(definition_unfolding,[],[f50,f57])).
% 23.44/3.50  
% 23.44/3.50  fof(f38,plain,(
% 23.44/3.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 23.44/3.50    inference(cnf_transformation,[],[f25])).
% 23.44/3.50  
% 23.44/3.50  cnf(c_10,plain,
% 23.44/3.50      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))) ),
% 23.44/3.50      inference(cnf_transformation,[],[f62]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_466,plain,
% 23.44/3.50      ( r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_14,plain,
% 23.44/3.50      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
% 23.44/3.50      inference(cnf_transformation,[],[f66]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_532,plain,
% 23.44/3.50      ( r1_tarski(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),k3_tarski(k3_enumset1(X0,X0,X0,X0,X2))) = iProver_top ),
% 23.44/3.50      inference(light_normalisation,[status(thm)],[c_466,c_14]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_4,plain,
% 23.44/3.50      ( ~ r2_hidden(X0,X1)
% 23.44/3.50      | r2_hidden(X0,X2)
% 23.44/3.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 23.44/3.50      inference(cnf_transformation,[],[f37]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_471,plain,
% 23.44/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.44/3.50      | r2_hidden(X0,X2) = iProver_top
% 23.44/3.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_1686,plain,
% 23.44/3.50      ( r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top
% 23.44/3.50      | r2_hidden(X0,k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top
% 23.44/3.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_14,c_471]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2,plain,
% 23.44/3.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 23.44/3.50      inference(cnf_transformation,[],[f32]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_473,plain,
% 23.44/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.44/3.50      | r2_hidden(X0,X2) = iProver_top
% 23.44/3.50      | r1_tarski(X1,X2) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_2449,plain,
% 23.44/3.50      ( r2_hidden(X0,X1) = iProver_top
% 23.44/3.50      | r2_hidden(X0,k5_xboole_0(X2,X3)) != iProver_top
% 23.44/3.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) = iProver_top
% 23.44/3.50      | r1_tarski(k1_setfam_1(k3_enumset1(X2,X2,X2,X2,X3)),X1) != iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_1686,c_473]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_22322,plain,
% 23.44/3.50      ( r2_hidden(X0,k5_xboole_0(X1,X2)) != iProver_top
% 23.44/3.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X3))) = iProver_top
% 23.44/3.50      | r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) = iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_532,c_2449]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_16,negated_conjecture,
% 23.44/3.50      ( ~ r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) ),
% 23.44/3.50      inference(cnf_transformation,[],[f67]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_461,plain,
% 23.44/3.50      ( r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_64171,plain,
% 23.44/3.50      ( r2_hidden(sK1,k5_xboole_0(sK1,X0)) != iProver_top
% 23.44/3.50      | r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) = iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_22322,c_461]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_15,plain,
% 23.44/3.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 23.44/3.50      inference(cnf_transformation,[],[f54]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_18,plain,
% 23.44/3.50      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_20,plain,
% 23.44/3.50      ( r2_hidden(sK1,sK1) != iProver_top | r1_tarski(sK1,sK1) != iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_18]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_9,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f69]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_32,plain,
% 23.44/3.50      ( r1_tarski(X0,X0) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_34,plain,
% 23.44/3.50      ( r1_tarski(sK1,sK1) = iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_32]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_634,plain,
% 23.44/3.50      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X0,X0,X0,X0,X1)) ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_9]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_636,plain,
% 23.44/3.50      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X0,X0,X0,X0,X1)) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_638,plain,
% 23.44/3.50      ( r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_636]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_12,plain,
% 23.44/3.50      ( r2_hidden(X0,X1) | ~ r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 23.44/3.50      inference(cnf_transformation,[],[f64]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_635,plain,
% 23.44/3.50      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0))
% 23.44/3.50      | ~ r1_tarski(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X1,X1,X1,X1,X0)) ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_12]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_640,plain,
% 23.44/3.50      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X0)) = iProver_top
% 23.44/3.50      | r1_tarski(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X1,X1,X1,X1,X0)) != iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_642,plain,
% 23.44/3.50      ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = iProver_top
% 23.44/3.50      | r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_640]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_3,plain,
% 23.44/3.50      ( ~ r2_hidden(X0,X1)
% 23.44/3.50      | r2_hidden(X0,X2)
% 23.44/3.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 23.44/3.50      inference(cnf_transformation,[],[f38]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_699,plain,
% 23.44/3.50      ( r2_hidden(X0,X1)
% 23.44/3.50      | ~ r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X0))
% 23.44/3.50      | r2_hidden(X0,k5_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X0))) ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_708,plain,
% 23.44/3.50      ( r2_hidden(X0,X1) = iProver_top
% 23.44/3.50      | r2_hidden(X0,k3_enumset1(X2,X2,X2,X2,X0)) != iProver_top
% 23.44/3.50      | r2_hidden(X0,k5_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X0))) = iProver_top ),
% 23.44/3.50      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_710,plain,
% 23.44/3.50      ( r2_hidden(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) != iProver_top
% 23.44/3.50      | r2_hidden(sK1,k5_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) = iProver_top
% 23.44/3.50      | r2_hidden(sK1,sK1) = iProver_top ),
% 23.44/3.50      inference(instantiation,[status(thm)],[c_708]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_64145,plain,
% 23.44/3.50      ( r2_hidden(sK1,k5_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != iProver_top
% 23.44/3.50      | r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) = iProver_top ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_22322,c_461]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_67502,plain,
% 23.44/3.50      ( r2_hidden(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) = iProver_top ),
% 23.44/3.50      inference(global_propositional_subsumption,
% 23.44/3.50                [status(thm)],
% 23.44/3.50                [c_64171,c_20,c_34,c_638,c_642,c_710,c_64145]) ).
% 23.44/3.50  
% 23.44/3.50  cnf(c_67511,plain,
% 23.44/3.50      ( $false ),
% 23.44/3.50      inference(superposition,[status(thm)],[c_67502,c_461]) ).
% 23.44/3.50  
% 23.44/3.50  
% 23.44/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.44/3.50  
% 23.44/3.50  ------                               Statistics
% 23.44/3.50  
% 23.44/3.50  ------ Selected
% 23.44/3.50  
% 23.44/3.50  total_time:                             2.996
% 23.44/3.50  
%------------------------------------------------------------------------------
