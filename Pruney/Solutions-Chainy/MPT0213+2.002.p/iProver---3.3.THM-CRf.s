%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:28:38 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 542 expanded)
%              Number of clauses        :   44 ( 145 expanded)
%              Number of leaves         :   12 ( 152 expanded)
%              Depth                    :   25
%              Number of atoms          :  272 (2853 expanded)
%              Number of equality atoms :   99 ( 573 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :   14 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f36,f24,f24])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f24])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).

fof(f38,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | o_0_0_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f24])).

fof(f7,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f8])).

fof(f43,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    o_0_0_xboole_0 != k3_tarski(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f43,f24,f24])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_746,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_744,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1216,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_744])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_741,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_740,plain,
    ( k4_xboole_0(X0,X1) = o_0_0_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_958,plain,
    ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_741,c_740])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_743,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1011,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_743])).

cnf(c_1233,plain,
    ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1216,c_1011])).

cnf(c_2043,plain,
    ( k4_xboole_0(o_0_0_xboole_0,X0) = X1
    | r2_hidden(sK0(o_0_0_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_1233])).

cnf(c_2078,plain,
    ( o_0_0_xboole_0 = X0
    | r2_hidden(sK0(o_0_0_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2043,c_11])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_734,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1238,plain,
    ( r2_hidden(X0,k3_tarski(o_0_0_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_1233])).

cnf(c_1323,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(o_0_0_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_1238])).

cnf(c_1391,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_1323])).

cnf(c_1397,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_1391])).

cnf(c_1452,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_1397])).

cnf(c_1556,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_1452])).

cnf(c_2290,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_1556])).

cnf(c_2330,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_2290])).

cnf(c_2496,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_2330])).

cnf(c_2536,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_2496])).

cnf(c_2650,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_2536])).

cnf(c_3357,plain,
    ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2078,c_2650])).

cnf(c_2690,plain,
    ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_734,c_2650])).

cnf(c_3358,plain,
    ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2078,c_2690])).

cnf(c_3362,plain,
    ( k3_tarski(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3357,c_3358])).

cnf(c_376,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_875,plain,
    ( k3_tarski(o_0_0_xboole_0) != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = k3_tarski(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_876,plain,
    ( k3_tarski(o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k3_tarski(o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_47,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_39,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_37,plain,
    ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_18,negated_conjecture,
    ( o_0_0_xboole_0 != k3_tarski(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3362,c_876,c_47,c_39,c_37,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:07:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.18/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.18/0.99  
% 1.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.18/0.99  
% 1.18/0.99  ------  iProver source info
% 1.18/0.99  
% 1.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.18/0.99  git: non_committed_changes: false
% 1.18/0.99  git: last_make_outside_of_git: false
% 1.18/0.99  
% 1.18/0.99  ------ 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options
% 1.18/0.99  
% 1.18/0.99  --out_options                           all
% 1.18/0.99  --tptp_safe_out                         true
% 1.18/0.99  --problem_path                          ""
% 1.18/0.99  --include_path                          ""
% 1.18/0.99  --clausifier                            res/vclausify_rel
% 1.18/0.99  --clausifier_options                    --mode clausify
% 1.18/0.99  --stdin                                 false
% 1.18/0.99  --stats_out                             all
% 1.18/0.99  
% 1.18/0.99  ------ General Options
% 1.18/0.99  
% 1.18/0.99  --fof                                   false
% 1.18/0.99  --time_out_real                         305.
% 1.18/0.99  --time_out_virtual                      -1.
% 1.18/0.99  --symbol_type_check                     false
% 1.18/0.99  --clausify_out                          false
% 1.18/0.99  --sig_cnt_out                           false
% 1.18/0.99  --trig_cnt_out                          false
% 1.18/0.99  --trig_cnt_out_tolerance                1.
% 1.18/0.99  --trig_cnt_out_sk_spl                   false
% 1.18/0.99  --abstr_cl_out                          false
% 1.18/0.99  
% 1.18/0.99  ------ Global Options
% 1.18/0.99  
% 1.18/0.99  --schedule                              default
% 1.18/0.99  --add_important_lit                     false
% 1.18/0.99  --prop_solver_per_cl                    1000
% 1.18/0.99  --min_unsat_core                        false
% 1.18/0.99  --soft_assumptions                      false
% 1.18/0.99  --soft_lemma_size                       3
% 1.18/0.99  --prop_impl_unit_size                   0
% 1.18/0.99  --prop_impl_unit                        []
% 1.18/0.99  --share_sel_clauses                     true
% 1.18/0.99  --reset_solvers                         false
% 1.18/0.99  --bc_imp_inh                            [conj_cone]
% 1.18/0.99  --conj_cone_tolerance                   3.
% 1.18/0.99  --extra_neg_conj                        none
% 1.18/0.99  --large_theory_mode                     true
% 1.18/0.99  --prolific_symb_bound                   200
% 1.18/0.99  --lt_threshold                          2000
% 1.18/0.99  --clause_weak_htbl                      true
% 1.18/0.99  --gc_record_bc_elim                     false
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing Options
% 1.18/0.99  
% 1.18/0.99  --preprocessing_flag                    true
% 1.18/0.99  --time_out_prep_mult                    0.1
% 1.18/0.99  --splitting_mode                        input
% 1.18/0.99  --splitting_grd                         true
% 1.18/0.99  --splitting_cvd                         false
% 1.18/0.99  --splitting_cvd_svl                     false
% 1.18/0.99  --splitting_nvd                         32
% 1.18/0.99  --sub_typing                            true
% 1.18/0.99  --prep_gs_sim                           true
% 1.18/0.99  --prep_unflatten                        true
% 1.18/0.99  --prep_res_sim                          true
% 1.18/0.99  --prep_upred                            true
% 1.18/0.99  --prep_sem_filter                       exhaustive
% 1.18/0.99  --prep_sem_filter_out                   false
% 1.18/0.99  --pred_elim                             true
% 1.18/0.99  --res_sim_input                         true
% 1.18/0.99  --eq_ax_congr_red                       true
% 1.18/0.99  --pure_diseq_elim                       true
% 1.18/0.99  --brand_transform                       false
% 1.18/0.99  --non_eq_to_eq                          false
% 1.18/0.99  --prep_def_merge                        true
% 1.18/0.99  --prep_def_merge_prop_impl              false
% 1.18/0.99  --prep_def_merge_mbd                    true
% 1.18/0.99  --prep_def_merge_tr_red                 false
% 1.18/0.99  --prep_def_merge_tr_cl                  false
% 1.18/0.99  --smt_preprocessing                     true
% 1.18/0.99  --smt_ac_axioms                         fast
% 1.18/0.99  --preprocessed_out                      false
% 1.18/0.99  --preprocessed_stats                    false
% 1.18/0.99  
% 1.18/0.99  ------ Abstraction refinement Options
% 1.18/0.99  
% 1.18/0.99  --abstr_ref                             []
% 1.18/0.99  --abstr_ref_prep                        false
% 1.18/0.99  --abstr_ref_until_sat                   false
% 1.18/0.99  --abstr_ref_sig_restrict                funpre
% 1.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.99  --abstr_ref_under                       []
% 1.18/0.99  
% 1.18/0.99  ------ SAT Options
% 1.18/0.99  
% 1.18/0.99  --sat_mode                              false
% 1.18/0.99  --sat_fm_restart_options                ""
% 1.18/0.99  --sat_gr_def                            false
% 1.18/0.99  --sat_epr_types                         true
% 1.18/0.99  --sat_non_cyclic_types                  false
% 1.18/0.99  --sat_finite_models                     false
% 1.18/0.99  --sat_fm_lemmas                         false
% 1.18/0.99  --sat_fm_prep                           false
% 1.18/0.99  --sat_fm_uc_incr                        true
% 1.18/0.99  --sat_out_model                         small
% 1.18/0.99  --sat_out_clauses                       false
% 1.18/0.99  
% 1.18/0.99  ------ QBF Options
% 1.18/0.99  
% 1.18/0.99  --qbf_mode                              false
% 1.18/0.99  --qbf_elim_univ                         false
% 1.18/0.99  --qbf_dom_inst                          none
% 1.18/0.99  --qbf_dom_pre_inst                      false
% 1.18/0.99  --qbf_sk_in                             false
% 1.18/0.99  --qbf_pred_elim                         true
% 1.18/0.99  --qbf_split                             512
% 1.18/0.99  
% 1.18/0.99  ------ BMC1 Options
% 1.18/0.99  
% 1.18/0.99  --bmc1_incremental                      false
% 1.18/0.99  --bmc1_axioms                           reachable_all
% 1.18/0.99  --bmc1_min_bound                        0
% 1.18/0.99  --bmc1_max_bound                        -1
% 1.18/0.99  --bmc1_max_bound_default                -1
% 1.18/0.99  --bmc1_symbol_reachability              true
% 1.18/0.99  --bmc1_property_lemmas                  false
% 1.18/0.99  --bmc1_k_induction                      false
% 1.18/0.99  --bmc1_non_equiv_states                 false
% 1.18/0.99  --bmc1_deadlock                         false
% 1.18/0.99  --bmc1_ucm                              false
% 1.18/0.99  --bmc1_add_unsat_core                   none
% 1.18/0.99  --bmc1_unsat_core_children              false
% 1.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.99  --bmc1_out_stat                         full
% 1.18/0.99  --bmc1_ground_init                      false
% 1.18/0.99  --bmc1_pre_inst_next_state              false
% 1.18/0.99  --bmc1_pre_inst_state                   false
% 1.18/0.99  --bmc1_pre_inst_reach_state             false
% 1.18/0.99  --bmc1_out_unsat_core                   false
% 1.18/0.99  --bmc1_aig_witness_out                  false
% 1.18/0.99  --bmc1_verbose                          false
% 1.18/0.99  --bmc1_dump_clauses_tptp                false
% 1.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.99  --bmc1_dump_file                        -
% 1.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.99  --bmc1_ucm_extend_mode                  1
% 1.18/0.99  --bmc1_ucm_init_mode                    2
% 1.18/0.99  --bmc1_ucm_cone_mode                    none
% 1.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.99  --bmc1_ucm_relax_model                  4
% 1.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.99  --bmc1_ucm_layered_model                none
% 1.18/0.99  --bmc1_ucm_max_lemma_size               10
% 1.18/0.99  
% 1.18/0.99  ------ AIG Options
% 1.18/0.99  
% 1.18/0.99  --aig_mode                              false
% 1.18/0.99  
% 1.18/0.99  ------ Instantiation Options
% 1.18/0.99  
% 1.18/0.99  --instantiation_flag                    true
% 1.18/0.99  --inst_sos_flag                         false
% 1.18/0.99  --inst_sos_phase                        true
% 1.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.99  --inst_lit_sel_side                     num_symb
% 1.18/0.99  --inst_solver_per_active                1400
% 1.18/0.99  --inst_solver_calls_frac                1.
% 1.18/0.99  --inst_passive_queue_type               priority_queues
% 1.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/0.99  --inst_passive_queues_freq              [25;2]
% 1.18/0.99  --inst_dismatching                      true
% 1.18/0.99  --inst_eager_unprocessed_to_passive     true
% 1.18/0.99  --inst_prop_sim_given                   true
% 1.18/0.99  --inst_prop_sim_new                     false
% 1.18/0.99  --inst_subs_new                         false
% 1.18/0.99  --inst_eq_res_simp                      false
% 1.18/0.99  --inst_subs_given                       false
% 1.18/0.99  --inst_orphan_elimination               true
% 1.18/0.99  --inst_learning_loop_flag               true
% 1.18/0.99  --inst_learning_start                   3000
% 1.18/0.99  --inst_learning_factor                  2
% 1.18/0.99  --inst_start_prop_sim_after_learn       3
% 1.18/0.99  --inst_sel_renew                        solver
% 1.18/0.99  --inst_lit_activity_flag                true
% 1.18/0.99  --inst_restr_to_given                   false
% 1.18/0.99  --inst_activity_threshold               500
% 1.18/0.99  --inst_out_proof                        true
% 1.18/0.99  
% 1.18/0.99  ------ Resolution Options
% 1.18/0.99  
% 1.18/0.99  --resolution_flag                       true
% 1.18/0.99  --res_lit_sel                           adaptive
% 1.18/0.99  --res_lit_sel_side                      none
% 1.18/0.99  --res_ordering                          kbo
% 1.18/0.99  --res_to_prop_solver                    active
% 1.18/0.99  --res_prop_simpl_new                    false
% 1.18/0.99  --res_prop_simpl_given                  true
% 1.18/0.99  --res_passive_queue_type                priority_queues
% 1.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/0.99  --res_passive_queues_freq               [15;5]
% 1.18/0.99  --res_forward_subs                      full
% 1.18/0.99  --res_backward_subs                     full
% 1.18/0.99  --res_forward_subs_resolution           true
% 1.18/0.99  --res_backward_subs_resolution          true
% 1.18/0.99  --res_orphan_elimination                true
% 1.18/0.99  --res_time_limit                        2.
% 1.18/0.99  --res_out_proof                         true
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Options
% 1.18/0.99  
% 1.18/0.99  --superposition_flag                    true
% 1.18/0.99  --sup_passive_queue_type                priority_queues
% 1.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.99  --demod_completeness_check              fast
% 1.18/0.99  --demod_use_ground                      true
% 1.18/0.99  --sup_to_prop_solver                    passive
% 1.18/0.99  --sup_prop_simpl_new                    true
% 1.18/0.99  --sup_prop_simpl_given                  true
% 1.18/0.99  --sup_fun_splitting                     false
% 1.18/0.99  --sup_smt_interval                      50000
% 1.18/0.99  
% 1.18/0.99  ------ Superposition Simplification Setup
% 1.18/0.99  
% 1.18/0.99  --sup_indices_passive                   []
% 1.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_full_bw                           [BwDemod]
% 1.18/0.99  --sup_immed_triv                        [TrivRules]
% 1.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_immed_bw_main                     []
% 1.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.99  
% 1.18/0.99  ------ Combination Options
% 1.18/0.99  
% 1.18/0.99  --comb_res_mult                         3
% 1.18/0.99  --comb_sup_mult                         2
% 1.18/0.99  --comb_inst_mult                        10
% 1.18/0.99  
% 1.18/0.99  ------ Debug Options
% 1.18/0.99  
% 1.18/0.99  --dbg_backtrace                         false
% 1.18/0.99  --dbg_dump_prop_clauses                 false
% 1.18/0.99  --dbg_dump_prop_clauses_file            -
% 1.18/0.99  --dbg_out_stat                          false
% 1.18/0.99  ------ Parsing...
% 1.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.18/0.99  ------ Proving...
% 1.18/0.99  ------ Problem Properties 
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  clauses                                 18
% 1.18/0.99  conjectures                             1
% 1.18/0.99  EPR                                     2
% 1.18/0.99  Horn                                    12
% 1.18/0.99  unary                                   3
% 1.18/0.99  binary                                  6
% 1.18/0.99  lits                                    44
% 1.18/0.99  lits eq                                 11
% 1.18/0.99  fd_pure                                 0
% 1.18/0.99  fd_pseudo                               0
% 1.18/0.99  fd_cond                                 0
% 1.18/0.99  fd_pseudo_cond                          7
% 1.18/0.99  AC symbols                              0
% 1.18/0.99  
% 1.18/0.99  ------ Schedule dynamic 5 is on 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.18/0.99  
% 1.18/0.99  
% 1.18/0.99  ------ 
% 1.18/0.99  Current options:
% 1.18/0.99  ------ 
% 1.18/0.99  
% 1.18/0.99  ------ Input Options
% 1.18/0.99  
% 1.18/0.99  --out_options                           all
% 1.18/0.99  --tptp_safe_out                         true
% 1.18/0.99  --problem_path                          ""
% 1.18/0.99  --include_path                          ""
% 1.18/0.99  --clausifier                            res/vclausify_rel
% 1.18/0.99  --clausifier_options                    --mode clausify
% 1.18/0.99  --stdin                                 false
% 1.18/0.99  --stats_out                             all
% 1.18/0.99  
% 1.18/0.99  ------ General Options
% 1.18/0.99  
% 1.18/0.99  --fof                                   false
% 1.18/0.99  --time_out_real                         305.
% 1.18/0.99  --time_out_virtual                      -1.
% 1.18/0.99  --symbol_type_check                     false
% 1.18/0.99  --clausify_out                          false
% 1.18/0.99  --sig_cnt_out                           false
% 1.18/0.99  --trig_cnt_out                          false
% 1.18/0.99  --trig_cnt_out_tolerance                1.
% 1.18/0.99  --trig_cnt_out_sk_spl                   false
% 1.18/0.99  --abstr_cl_out                          false
% 1.18/0.99  
% 1.18/0.99  ------ Global Options
% 1.18/0.99  
% 1.18/0.99  --schedule                              default
% 1.18/0.99  --add_important_lit                     false
% 1.18/0.99  --prop_solver_per_cl                    1000
% 1.18/0.99  --min_unsat_core                        false
% 1.18/0.99  --soft_assumptions                      false
% 1.18/0.99  --soft_lemma_size                       3
% 1.18/0.99  --prop_impl_unit_size                   0
% 1.18/0.99  --prop_impl_unit                        []
% 1.18/0.99  --share_sel_clauses                     true
% 1.18/0.99  --reset_solvers                         false
% 1.18/0.99  --bc_imp_inh                            [conj_cone]
% 1.18/0.99  --conj_cone_tolerance                   3.
% 1.18/0.99  --extra_neg_conj                        none
% 1.18/0.99  --large_theory_mode                     true
% 1.18/0.99  --prolific_symb_bound                   200
% 1.18/0.99  --lt_threshold                          2000
% 1.18/0.99  --clause_weak_htbl                      true
% 1.18/0.99  --gc_record_bc_elim                     false
% 1.18/0.99  
% 1.18/0.99  ------ Preprocessing Options
% 1.18/0.99  
% 1.18/0.99  --preprocessing_flag                    true
% 1.18/0.99  --time_out_prep_mult                    0.1
% 1.18/0.99  --splitting_mode                        input
% 1.18/0.99  --splitting_grd                         true
% 1.18/0.99  --splitting_cvd                         false
% 1.18/0.99  --splitting_cvd_svl                     false
% 1.18/0.99  --splitting_nvd                         32
% 1.18/0.99  --sub_typing                            true
% 1.18/0.99  --prep_gs_sim                           true
% 1.18/0.99  --prep_unflatten                        true
% 1.18/0.99  --prep_res_sim                          true
% 1.18/0.99  --prep_upred                            true
% 1.18/0.99  --prep_sem_filter                       exhaustive
% 1.18/0.99  --prep_sem_filter_out                   false
% 1.18/0.99  --pred_elim                             true
% 1.18/0.99  --res_sim_input                         true
% 1.18/0.99  --eq_ax_congr_red                       true
% 1.18/0.99  --pure_diseq_elim                       true
% 1.18/0.99  --brand_transform                       false
% 1.18/0.99  --non_eq_to_eq                          false
% 1.18/0.99  --prep_def_merge                        true
% 1.18/0.99  --prep_def_merge_prop_impl              false
% 1.18/0.99  --prep_def_merge_mbd                    true
% 1.18/0.99  --prep_def_merge_tr_red                 false
% 1.18/0.99  --prep_def_merge_tr_cl                  false
% 1.18/0.99  --smt_preprocessing                     true
% 1.18/0.99  --smt_ac_axioms                         fast
% 1.18/0.99  --preprocessed_out                      false
% 1.18/0.99  --preprocessed_stats                    false
% 1.18/0.99  
% 1.18/0.99  ------ Abstraction refinement Options
% 1.18/0.99  
% 1.18/0.99  --abstr_ref                             []
% 1.18/0.99  --abstr_ref_prep                        false
% 1.18/0.99  --abstr_ref_until_sat                   false
% 1.18/0.99  --abstr_ref_sig_restrict                funpre
% 1.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.99  --abstr_ref_under                       []
% 1.18/0.99  
% 1.18/0.99  ------ SAT Options
% 1.18/0.99  
% 1.18/0.99  --sat_mode                              false
% 1.18/0.99  --sat_fm_restart_options                ""
% 1.18/1.00  --sat_gr_def                            false
% 1.18/1.00  --sat_epr_types                         true
% 1.18/1.00  --sat_non_cyclic_types                  false
% 1.18/1.00  --sat_finite_models                     false
% 1.18/1.00  --sat_fm_lemmas                         false
% 1.18/1.00  --sat_fm_prep                           false
% 1.18/1.00  --sat_fm_uc_incr                        true
% 1.18/1.00  --sat_out_model                         small
% 1.18/1.00  --sat_out_clauses                       false
% 1.18/1.00  
% 1.18/1.00  ------ QBF Options
% 1.18/1.00  
% 1.18/1.00  --qbf_mode                              false
% 1.18/1.00  --qbf_elim_univ                         false
% 1.18/1.00  --qbf_dom_inst                          none
% 1.18/1.00  --qbf_dom_pre_inst                      false
% 1.18/1.00  --qbf_sk_in                             false
% 1.18/1.00  --qbf_pred_elim                         true
% 1.18/1.00  --qbf_split                             512
% 1.18/1.00  
% 1.18/1.00  ------ BMC1 Options
% 1.18/1.00  
% 1.18/1.00  --bmc1_incremental                      false
% 1.18/1.00  --bmc1_axioms                           reachable_all
% 1.18/1.00  --bmc1_min_bound                        0
% 1.18/1.00  --bmc1_max_bound                        -1
% 1.18/1.00  --bmc1_max_bound_default                -1
% 1.18/1.00  --bmc1_symbol_reachability              true
% 1.18/1.00  --bmc1_property_lemmas                  false
% 1.18/1.00  --bmc1_k_induction                      false
% 1.18/1.00  --bmc1_non_equiv_states                 false
% 1.18/1.00  --bmc1_deadlock                         false
% 1.18/1.00  --bmc1_ucm                              false
% 1.18/1.00  --bmc1_add_unsat_core                   none
% 1.18/1.00  --bmc1_unsat_core_children              false
% 1.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/1.00  --bmc1_out_stat                         full
% 1.18/1.00  --bmc1_ground_init                      false
% 1.18/1.00  --bmc1_pre_inst_next_state              false
% 1.18/1.00  --bmc1_pre_inst_state                   false
% 1.18/1.00  --bmc1_pre_inst_reach_state             false
% 1.18/1.00  --bmc1_out_unsat_core                   false
% 1.18/1.00  --bmc1_aig_witness_out                  false
% 1.18/1.00  --bmc1_verbose                          false
% 1.18/1.00  --bmc1_dump_clauses_tptp                false
% 1.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.18/1.00  --bmc1_dump_file                        -
% 1.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.18/1.00  --bmc1_ucm_extend_mode                  1
% 1.18/1.00  --bmc1_ucm_init_mode                    2
% 1.18/1.00  --bmc1_ucm_cone_mode                    none
% 1.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.18/1.00  --bmc1_ucm_relax_model                  4
% 1.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/1.00  --bmc1_ucm_layered_model                none
% 1.18/1.00  --bmc1_ucm_max_lemma_size               10
% 1.18/1.00  
% 1.18/1.00  ------ AIG Options
% 1.18/1.00  
% 1.18/1.00  --aig_mode                              false
% 1.18/1.00  
% 1.18/1.00  ------ Instantiation Options
% 1.18/1.00  
% 1.18/1.00  --instantiation_flag                    true
% 1.18/1.00  --inst_sos_flag                         false
% 1.18/1.00  --inst_sos_phase                        true
% 1.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/1.00  --inst_lit_sel_side                     none
% 1.18/1.00  --inst_solver_per_active                1400
% 1.18/1.00  --inst_solver_calls_frac                1.
% 1.18/1.00  --inst_passive_queue_type               priority_queues
% 1.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/1.00  --inst_passive_queues_freq              [25;2]
% 1.18/1.00  --inst_dismatching                      true
% 1.18/1.00  --inst_eager_unprocessed_to_passive     true
% 1.18/1.00  --inst_prop_sim_given                   true
% 1.18/1.00  --inst_prop_sim_new                     false
% 1.18/1.00  --inst_subs_new                         false
% 1.18/1.00  --inst_eq_res_simp                      false
% 1.18/1.00  --inst_subs_given                       false
% 1.18/1.00  --inst_orphan_elimination               true
% 1.18/1.00  --inst_learning_loop_flag               true
% 1.18/1.00  --inst_learning_start                   3000
% 1.18/1.00  --inst_learning_factor                  2
% 1.18/1.00  --inst_start_prop_sim_after_learn       3
% 1.18/1.00  --inst_sel_renew                        solver
% 1.18/1.00  --inst_lit_activity_flag                true
% 1.18/1.00  --inst_restr_to_given                   false
% 1.18/1.00  --inst_activity_threshold               500
% 1.18/1.00  --inst_out_proof                        true
% 1.18/1.00  
% 1.18/1.00  ------ Resolution Options
% 1.18/1.00  
% 1.18/1.00  --resolution_flag                       false
% 1.18/1.00  --res_lit_sel                           adaptive
% 1.18/1.00  --res_lit_sel_side                      none
% 1.18/1.00  --res_ordering                          kbo
% 1.18/1.00  --res_to_prop_solver                    active
% 1.18/1.00  --res_prop_simpl_new                    false
% 1.18/1.00  --res_prop_simpl_given                  true
% 1.18/1.00  --res_passive_queue_type                priority_queues
% 1.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/1.00  --res_passive_queues_freq               [15;5]
% 1.18/1.00  --res_forward_subs                      full
% 1.18/1.00  --res_backward_subs                     full
% 1.18/1.00  --res_forward_subs_resolution           true
% 1.18/1.00  --res_backward_subs_resolution          true
% 1.18/1.00  --res_orphan_elimination                true
% 1.18/1.00  --res_time_limit                        2.
% 1.18/1.00  --res_out_proof                         true
% 1.18/1.00  
% 1.18/1.00  ------ Superposition Options
% 1.18/1.00  
% 1.18/1.00  --superposition_flag                    true
% 1.18/1.00  --sup_passive_queue_type                priority_queues
% 1.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.18/1.00  --demod_completeness_check              fast
% 1.18/1.00  --demod_use_ground                      true
% 1.18/1.00  --sup_to_prop_solver                    passive
% 1.18/1.00  --sup_prop_simpl_new                    true
% 1.18/1.00  --sup_prop_simpl_given                  true
% 1.18/1.00  --sup_fun_splitting                     false
% 1.18/1.00  --sup_smt_interval                      50000
% 1.18/1.00  
% 1.18/1.00  ------ Superposition Simplification Setup
% 1.18/1.00  
% 1.18/1.00  --sup_indices_passive                   []
% 1.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_full_bw                           [BwDemod]
% 1.18/1.00  --sup_immed_triv                        [TrivRules]
% 1.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_immed_bw_main                     []
% 1.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/1.00  
% 1.18/1.00  ------ Combination Options
% 1.18/1.00  
% 1.18/1.00  --comb_res_mult                         3
% 1.18/1.00  --comb_sup_mult                         2
% 1.18/1.00  --comb_inst_mult                        10
% 1.18/1.00  
% 1.18/1.00  ------ Debug Options
% 1.18/1.00  
% 1.18/1.00  --dbg_backtrace                         false
% 1.18/1.00  --dbg_dump_prop_clauses                 false
% 1.18/1.00  --dbg_dump_prop_clauses_file            -
% 1.18/1.00  --dbg_out_stat                          false
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  ------ Proving...
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  % SZS status Theorem for theBenchmark.p
% 1.18/1.00  
% 1.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.18/1.00  
% 1.18/1.00  fof(f2,axiom,(
% 1.18/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f10,plain,(
% 1.18/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.18/1.00    inference(nnf_transformation,[],[f2])).
% 1.18/1.00  
% 1.18/1.00  fof(f11,plain,(
% 1.18/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.18/1.00    inference(flattening,[],[f10])).
% 1.18/1.00  
% 1.18/1.00  fof(f12,plain,(
% 1.18/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.18/1.00    inference(rectify,[],[f11])).
% 1.18/1.00  
% 1.18/1.00  fof(f13,plain,(
% 1.18/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f14,plain,(
% 1.18/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 1.18/1.00  
% 1.18/1.00  fof(f28,plain,(
% 1.18/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f14])).
% 1.18/1.00  
% 1.18/1.00  fof(f5,axiom,(
% 1.18/1.00    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f36,plain,(
% 1.18/1.00    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f5])).
% 1.18/1.00  
% 1.18/1.00  fof(f1,axiom,(
% 1.18/1.00    k1_xboole_0 = o_0_0_xboole_0),
% 1.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f24,plain,(
% 1.18/1.00    k1_xboole_0 = o_0_0_xboole_0),
% 1.18/1.00    inference(cnf_transformation,[],[f1])).
% 1.18/1.00  
% 1.18/1.00  fof(f46,plain,(
% 1.18/1.00    ( ! [X0] : (o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0)) )),
% 1.18/1.00    inference(definition_unfolding,[],[f36,f24,f24])).
% 1.18/1.00  
% 1.18/1.00  fof(f26,plain,(
% 1.18/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.18/1.00    inference(cnf_transformation,[],[f14])).
% 1.18/1.00  
% 1.18/1.00  fof(f49,plain,(
% 1.18/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.18/1.00    inference(equality_resolution,[],[f26])).
% 1.18/1.00  
% 1.18/1.00  fof(f3,axiom,(
% 1.18/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f15,plain,(
% 1.18/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.18/1.00    inference(nnf_transformation,[],[f3])).
% 1.18/1.00  
% 1.18/1.00  fof(f16,plain,(
% 1.18/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.18/1.00    inference(flattening,[],[f15])).
% 1.18/1.00  
% 1.18/1.00  fof(f31,plain,(
% 1.18/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.18/1.00    inference(cnf_transformation,[],[f16])).
% 1.18/1.00  
% 1.18/1.00  fof(f52,plain,(
% 1.18/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.18/1.00    inference(equality_resolution,[],[f31])).
% 1.18/1.00  
% 1.18/1.00  fof(f4,axiom,(
% 1.18/1.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f17,plain,(
% 1.18/1.00    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.18/1.00    inference(nnf_transformation,[],[f4])).
% 1.18/1.00  
% 1.18/1.00  fof(f35,plain,(
% 1.18/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f17])).
% 1.18/1.00  
% 1.18/1.00  fof(f44,plain,(
% 1.18/1.00    ( ! [X0,X1] : (o_0_0_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.18/1.00    inference(definition_unfolding,[],[f35,f24])).
% 1.18/1.00  
% 1.18/1.00  fof(f25,plain,(
% 1.18/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.18/1.00    inference(cnf_transformation,[],[f14])).
% 1.18/1.00  
% 1.18/1.00  fof(f50,plain,(
% 1.18/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.18/1.00    inference(equality_resolution,[],[f25])).
% 1.18/1.00  
% 1.18/1.00  fof(f6,axiom,(
% 1.18/1.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f18,plain,(
% 1.18/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 1.18/1.00    inference(nnf_transformation,[],[f6])).
% 1.18/1.00  
% 1.18/1.00  fof(f19,plain,(
% 1.18/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.18/1.00    inference(rectify,[],[f18])).
% 1.18/1.00  
% 1.18/1.00  fof(f22,plain,(
% 1.18/1.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f21,plain,(
% 1.18/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f20,plain,(
% 1.18/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 1.18/1.00    introduced(choice_axiom,[])).
% 1.18/1.00  
% 1.18/1.00  fof(f23,plain,(
% 1.18/1.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 1.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f19,f22,f21,f20])).
% 1.18/1.00  
% 1.18/1.00  fof(f38,plain,(
% 1.18/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 1.18/1.00    inference(cnf_transformation,[],[f23])).
% 1.18/1.00  
% 1.18/1.00  fof(f54,plain,(
% 1.18/1.00    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 1.18/1.00    inference(equality_resolution,[],[f38])).
% 1.18/1.00  
% 1.18/1.00  fof(f33,plain,(
% 1.18/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f16])).
% 1.18/1.00  
% 1.18/1.00  fof(f34,plain,(
% 1.18/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.18/1.00    inference(cnf_transformation,[],[f17])).
% 1.18/1.00  
% 1.18/1.00  fof(f45,plain,(
% 1.18/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | o_0_0_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.18/1.00    inference(definition_unfolding,[],[f34,f24])).
% 1.18/1.00  
% 1.18/1.00  fof(f7,conjecture,(
% 1.18/1.00    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/1.00  
% 1.18/1.00  fof(f8,negated_conjecture,(
% 1.18/1.00    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.18/1.00    inference(negated_conjecture,[],[f7])).
% 1.18/1.00  
% 1.18/1.00  fof(f9,plain,(
% 1.18/1.00    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 1.18/1.00    inference(flattening,[],[f8])).
% 1.18/1.00  
% 1.18/1.00  fof(f43,plain,(
% 1.18/1.00    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 1.18/1.00    inference(cnf_transformation,[],[f9])).
% 1.18/1.00  
% 1.18/1.00  fof(f47,plain,(
% 1.18/1.00    o_0_0_xboole_0 != k3_tarski(o_0_0_xboole_0)),
% 1.18/1.00    inference(definition_unfolding,[],[f43,f24,f24])).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2,plain,
% 1.18/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 1.18/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 1.18/1.00      | k4_xboole_0(X0,X1) = X2 ),
% 1.18/1.00      inference(cnf_transformation,[],[f28]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_746,plain,
% 1.18/1.00      ( k4_xboole_0(X0,X1) = X2
% 1.18/1.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 1.18/1.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_11,plain,
% 1.18/1.00      ( k4_xboole_0(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
% 1.18/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_4,plain,
% 1.18/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 1.18/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_744,plain,
% 1.18/1.00      ( r2_hidden(X0,X1) != iProver_top
% 1.18/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1216,plain,
% 1.18/1.00      ( r2_hidden(X0,X1) != iProver_top
% 1.18/1.00      | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_11,c_744]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_8,plain,
% 1.18/1.00      ( r1_tarski(X0,X0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f52]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_741,plain,
% 1.18/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_9,plain,
% 1.18/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = o_0_0_xboole_0 ),
% 1.18/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_740,plain,
% 1.18/1.00      ( k4_xboole_0(X0,X1) = o_0_0_xboole_0
% 1.18/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_958,plain,
% 1.18/1.00      ( k4_xboole_0(X0,X0) = o_0_0_xboole_0 ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_741,c_740]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_5,plain,
% 1.18/1.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 1.18/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_743,plain,
% 1.18/1.00      ( r2_hidden(X0,X1) = iProver_top
% 1.18/1.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1011,plain,
% 1.18/1.00      ( r2_hidden(X0,X1) = iProver_top
% 1.18/1.00      | r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_958,c_743]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1233,plain,
% 1.18/1.00      ( r2_hidden(X0,o_0_0_xboole_0) != iProver_top ),
% 1.18/1.00      inference(global_propositional_subsumption,
% 1.18/1.00                [status(thm)],
% 1.18/1.00                [c_1216,c_1011]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2043,plain,
% 1.18/1.00      ( k4_xboole_0(o_0_0_xboole_0,X0) = X1
% 1.18/1.00      | r2_hidden(sK0(o_0_0_xboole_0,X0,X1),X1) = iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_746,c_1233]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2078,plain,
% 1.18/1.00      ( o_0_0_xboole_0 = X0
% 1.18/1.00      | r2_hidden(sK0(o_0_0_xboole_0,X1,X0),X0) = iProver_top ),
% 1.18/1.00      inference(demodulation,[status(thm)],[c_2043,c_11]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_16,plain,
% 1.18/1.00      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 1.18/1.00      inference(cnf_transformation,[],[f54]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_734,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 1.18/1.00      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 1.18/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1238,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(o_0_0_xboole_0)) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_1233]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1323,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(o_0_0_xboole_0))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_1238]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1391,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_1323]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1397,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_1391]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1452,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_1397]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_1556,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_1452]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2290,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_1556]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2330,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_2290]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2496,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_2330]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2536,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_2496]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2650,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_2536]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_3357,plain,
% 1.18/1.00      ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))) = o_0_0_xboole_0 ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_2078,c_2650]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_2690,plain,
% 1.18/1.00      ( r2_hidden(X0,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0))))))))))))) != iProver_top ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_734,c_2650]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_3358,plain,
% 1.18/1.00      ( k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(o_0_0_xboole_0)))))))))))) = o_0_0_xboole_0 ),
% 1.18/1.00      inference(superposition,[status(thm)],[c_2078,c_2690]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_3362,plain,
% 1.18/1.00      ( k3_tarski(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 1.18/1.00      inference(demodulation,[status(thm)],[c_3357,c_3358]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_376,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_875,plain,
% 1.18/1.00      ( k3_tarski(o_0_0_xboole_0) != X0
% 1.18/1.00      | o_0_0_xboole_0 != X0
% 1.18/1.00      | o_0_0_xboole_0 = k3_tarski(o_0_0_xboole_0) ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_376]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_876,plain,
% 1.18/1.00      ( k3_tarski(o_0_0_xboole_0) != o_0_0_xboole_0
% 1.18/1.00      | o_0_0_xboole_0 = k3_tarski(o_0_0_xboole_0)
% 1.18/1.00      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_875]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_6,plain,
% 1.18/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.18/1.00      inference(cnf_transformation,[],[f33]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_47,plain,
% 1.18/1.00      ( ~ r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
% 1.18/1.00      | o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_10,plain,
% 1.18/1.00      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != o_0_0_xboole_0 ),
% 1.18/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_39,plain,
% 1.18/1.00      ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
% 1.18/1.00      | k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) != o_0_0_xboole_0 ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_37,plain,
% 1.18/1.00      ( k4_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 1.18/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(c_18,negated_conjecture,
% 1.18/1.00      ( o_0_0_xboole_0 != k3_tarski(o_0_0_xboole_0) ),
% 1.18/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.18/1.00  
% 1.18/1.00  cnf(contradiction,plain,
% 1.18/1.00      ( $false ),
% 1.18/1.00      inference(minisat,[status(thm)],[c_3362,c_876,c_47,c_39,c_37,c_18]) ).
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.18/1.00  
% 1.18/1.00  ------                               Statistics
% 1.18/1.00  
% 1.18/1.00  ------ General
% 1.18/1.00  
% 1.18/1.00  abstr_ref_over_cycles:                  0
% 1.18/1.00  abstr_ref_under_cycles:                 0
% 1.18/1.00  gc_basic_clause_elim:                   0
% 1.18/1.00  forced_gc_time:                         0
% 1.18/1.00  parsing_time:                           0.011
% 1.18/1.00  unif_index_cands_time:                  0.
% 1.18/1.00  unif_index_add_time:                    0.
% 1.18/1.00  orderings_time:                         0.
% 1.18/1.00  out_proof_time:                         0.007
% 1.18/1.00  total_time:                             0.143
% 1.18/1.00  num_of_symbols:                         40
% 1.18/1.00  num_of_terms:                           4669
% 1.18/1.00  
% 1.18/1.00  ------ Preprocessing
% 1.18/1.00  
% 1.18/1.00  num_of_splits:                          0
% 1.18/1.00  num_of_split_atoms:                     0
% 1.18/1.00  num_of_reused_defs:                     0
% 1.18/1.00  num_eq_ax_congr_red:                    36
% 1.18/1.00  num_of_sem_filtered_clauses:            1
% 1.18/1.00  num_of_subtypes:                        0
% 1.18/1.00  monotx_restored_types:                  0
% 1.18/1.00  sat_num_of_epr_types:                   0
% 1.18/1.00  sat_num_of_non_cyclic_types:            0
% 1.18/1.00  sat_guarded_non_collapsed_types:        0
% 1.18/1.00  num_pure_diseq_elim:                    0
% 1.18/1.00  simp_replaced_by:                       0
% 1.18/1.00  res_preprocessed:                       83
% 1.18/1.00  prep_upred:                             0
% 1.18/1.00  prep_unflattend:                        0
% 1.18/1.00  smt_new_axioms:                         0
% 1.18/1.00  pred_elim_cands:                        2
% 1.18/1.00  pred_elim:                              0
% 1.18/1.00  pred_elim_cl:                           0
% 1.18/1.00  pred_elim_cycles:                       2
% 1.18/1.00  merged_defs:                            8
% 1.18/1.00  merged_defs_ncl:                        0
% 1.18/1.00  bin_hyper_res:                          8
% 1.18/1.00  prep_cycles:                            4
% 1.18/1.00  pred_elim_time:                         0.
% 1.18/1.00  splitting_time:                         0.
% 1.18/1.00  sem_filter_time:                        0.
% 1.18/1.00  monotx_time:                            0.
% 1.18/1.00  subtype_inf_time:                       0.
% 1.18/1.00  
% 1.18/1.00  ------ Problem properties
% 1.18/1.00  
% 1.18/1.00  clauses:                                18
% 1.18/1.00  conjectures:                            1
% 1.18/1.00  epr:                                    2
% 1.18/1.00  horn:                                   12
% 1.18/1.00  ground:                                 1
% 1.18/1.00  unary:                                  3
% 1.18/1.00  binary:                                 6
% 1.18/1.00  lits:                                   44
% 1.18/1.00  lits_eq:                                11
% 1.18/1.00  fd_pure:                                0
% 1.18/1.00  fd_pseudo:                              0
% 1.18/1.00  fd_cond:                                0
% 1.18/1.00  fd_pseudo_cond:                         7
% 1.18/1.00  ac_symbols:                             0
% 1.18/1.00  
% 1.18/1.00  ------ Propositional Solver
% 1.18/1.00  
% 1.18/1.00  prop_solver_calls:                      28
% 1.18/1.00  prop_fast_solver_calls:                 466
% 1.18/1.00  smt_solver_calls:                       0
% 1.18/1.00  smt_fast_solver_calls:                  0
% 1.18/1.00  prop_num_of_clauses:                    1376
% 1.18/1.00  prop_preprocess_simplified:             3974
% 1.18/1.00  prop_fo_subsumed:                       2
% 1.18/1.00  prop_solver_time:                       0.
% 1.18/1.00  smt_solver_time:                        0.
% 1.18/1.00  smt_fast_solver_time:                   0.
% 1.18/1.00  prop_fast_solver_time:                  0.
% 1.18/1.00  prop_unsat_core_time:                   0.
% 1.18/1.00  
% 1.18/1.00  ------ QBF
% 1.18/1.00  
% 1.18/1.00  qbf_q_res:                              0
% 1.18/1.00  qbf_num_tautologies:                    0
% 1.18/1.00  qbf_prep_cycles:                        0
% 1.18/1.00  
% 1.18/1.00  ------ BMC1
% 1.18/1.00  
% 1.18/1.00  bmc1_current_bound:                     -1
% 1.18/1.00  bmc1_last_solved_bound:                 -1
% 1.18/1.00  bmc1_unsat_core_size:                   -1
% 1.18/1.00  bmc1_unsat_core_parents_size:           -1
% 1.18/1.00  bmc1_merge_next_fun:                    0
% 1.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.18/1.00  
% 1.18/1.00  ------ Instantiation
% 1.18/1.00  
% 1.18/1.00  inst_num_of_clauses:                    355
% 1.18/1.00  inst_num_in_passive:                    82
% 1.18/1.00  inst_num_in_active:                     130
% 1.18/1.00  inst_num_in_unprocessed:                143
% 1.18/1.00  inst_num_of_loops:                      170
% 1.18/1.00  inst_num_of_learning_restarts:          0
% 1.18/1.00  inst_num_moves_active_passive:          36
% 1.18/1.00  inst_lit_activity:                      0
% 1.18/1.00  inst_lit_activity_moves:                0
% 1.18/1.00  inst_num_tautologies:                   0
% 1.18/1.00  inst_num_prop_implied:                  0
% 1.18/1.00  inst_num_existing_simplified:           0
% 1.18/1.00  inst_num_eq_res_simplified:             0
% 1.18/1.00  inst_num_child_elim:                    0
% 1.18/1.00  inst_num_of_dismatching_blockings:      77
% 1.18/1.00  inst_num_of_non_proper_insts:           233
% 1.18/1.00  inst_num_of_duplicates:                 0
% 1.18/1.00  inst_inst_num_from_inst_to_res:         0
% 1.18/1.00  inst_dismatching_checking_time:         0.
% 1.18/1.00  
% 1.18/1.00  ------ Resolution
% 1.18/1.00  
% 1.18/1.00  res_num_of_clauses:                     0
% 1.18/1.00  res_num_in_passive:                     0
% 1.18/1.00  res_num_in_active:                      0
% 1.18/1.00  res_num_of_loops:                       87
% 1.18/1.00  res_forward_subset_subsumed:            31
% 1.18/1.00  res_backward_subset_subsumed:           0
% 1.18/1.00  res_forward_subsumed:                   0
% 1.18/1.00  res_backward_subsumed:                  0
% 1.18/1.00  res_forward_subsumption_resolution:     0
% 1.18/1.00  res_backward_subsumption_resolution:    0
% 1.18/1.00  res_clause_to_clause_subsumption:       254
% 1.18/1.00  res_orphan_elimination:                 0
% 1.18/1.00  res_tautology_del:                      42
% 1.18/1.00  res_num_eq_res_simplified:              0
% 1.18/1.00  res_num_sel_changes:                    0
% 1.18/1.00  res_moves_from_active_to_pass:          0
% 1.18/1.00  
% 1.18/1.00  ------ Superposition
% 1.18/1.00  
% 1.18/1.00  sup_time_total:                         0.
% 1.18/1.00  sup_time_generating:                    0.
% 1.18/1.00  sup_time_sim_full:                      0.
% 1.18/1.00  sup_time_sim_immed:                     0.
% 1.18/1.00  
% 1.18/1.00  sup_num_of_clauses:                     128
% 1.18/1.00  sup_num_in_active:                      34
% 1.18/1.00  sup_num_in_passive:                     94
% 1.18/1.00  sup_num_of_loops:                       33
% 1.18/1.00  sup_fw_superposition:                   61
% 1.18/1.00  sup_bw_superposition:                   74
% 1.18/1.00  sup_immediate_simplified:               4
% 1.18/1.00  sup_given_eliminated:                   0
% 1.18/1.00  comparisons_done:                       0
% 1.18/1.00  comparisons_avoided:                    0
% 1.18/1.00  
% 1.18/1.00  ------ Simplifications
% 1.18/1.00  
% 1.18/1.00  
% 1.18/1.00  sim_fw_subset_subsumed:                 0
% 1.18/1.00  sim_bw_subset_subsumed:                 0
% 1.18/1.00  sim_fw_subsumed:                        2
% 1.18/1.00  sim_bw_subsumed:                        0
% 1.18/1.00  sim_fw_subsumption_res:                 0
% 1.18/1.00  sim_bw_subsumption_res:                 0
% 1.18/1.00  sim_tautology_del:                      5
% 1.18/1.00  sim_eq_tautology_del:                   11
% 1.18/1.00  sim_eq_res_simp:                        1
% 1.18/1.00  sim_fw_demodulated:                     4
% 1.18/1.00  sim_bw_demodulated:                     2
% 1.18/1.00  sim_light_normalised:                   9
% 1.18/1.00  sim_joinable_taut:                      0
% 1.18/1.00  sim_joinable_simp:                      0
% 1.18/1.00  sim_ac_normalised:                      0
% 1.18/1.00  sim_smt_subsumption:                    0
% 1.18/1.00  
%------------------------------------------------------------------------------
