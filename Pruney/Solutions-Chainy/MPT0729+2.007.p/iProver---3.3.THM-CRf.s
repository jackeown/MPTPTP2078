%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:22 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 184 expanded)
%              Number of clauses        :   30 (  45 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  275 ( 568 expanded)
%              Number of equality atoms :  140 ( 307 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK2 != sK3
      & k1_ordinal1(sK2) = k1_ordinal1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( sK2 != sK3
    & k1_ordinal1(sK2) = k1_ordinal1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f29])).

fof(f53,plain,(
    k1_ordinal1(sK2) = k1_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f50,f48,f47])).

fof(f58,plain,(
    k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2))) = k3_tarski(k2_tarski(sK3,k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f53,f55,f55])).

fof(f9,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f48,f47,f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_20,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2))) = k3_tarski(k2_tarski(sK3,k2_tarski(sK3,sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4470,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4617,plain,
    ( r2_hidden(sK3,k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_4470])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_4471,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,k2_tarski(X1,X1))),k2_tarski(X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4475,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4469,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4599,plain,
    ( r2_hidden(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4475,c_4469])).

cnf(c_4680,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))),k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_4471,c_4599])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4479,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4772,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_tarski(X1,X1)) = iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4680,c_4479])).

cnf(c_9011,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4617,c_4772])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4472,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9066,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9011,c_4472])).

cnf(c_4771,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2))),k2_tarski(sK3,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_20,c_4680])).

cnf(c_0,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4480,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4731,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(k4_xboole_0(X1,X2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_4480])).

cnf(c_4953,plain,
    ( r2_hidden(X0,k2_tarski(sK3,sK3)) = iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2)))) != iProver_top
    | r2_hidden(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4771,c_4731])).

cnf(c_5047,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | r2_hidden(sK2,k2_tarski(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4470,c_4953])).

cnf(c_5262,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5047,c_4472])).

cnf(c_9123,plain,
    ( sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9066,c_5262])).

cnf(c_19,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_9164,plain,
    ( sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_9123,c_19])).

cnf(c_9165,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9164])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:25:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.74/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/0.97  
% 3.74/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.97  
% 3.74/0.97  ------  iProver source info
% 3.74/0.97  
% 3.74/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.97  git: non_committed_changes: false
% 3.74/0.97  git: last_make_outside_of_git: false
% 3.74/0.97  
% 3.74/0.97  ------ 
% 3.74/0.97  ------ Parsing...
% 3.74/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  ------ Proving...
% 3.74/0.97  ------ Problem Properties 
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  clauses                                 20
% 3.74/0.97  conjectures                             5
% 3.74/0.97  EPR                                     5
% 3.74/0.97  Horn                                    13
% 3.74/0.97  unary                                   6
% 3.74/0.97  binary                                  5
% 3.74/0.97  lits                                    45
% 3.74/0.97  lits eq                                 16
% 3.74/0.97  fd_pure                                 0
% 3.74/0.97  fd_pseudo                               0
% 3.74/0.97  fd_cond                                 0
% 3.74/0.97  fd_pseudo_cond                          7
% 3.74/0.97  AC symbols                              0
% 3.74/0.97  
% 3.74/0.97  ------ Input Options Time Limit: Unbounded
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing...
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.74/0.97  Current options:
% 3.74/0.97  ------ 
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing...
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.74/0.97  
% 3.74/0.97  ------ Proving...
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  % SZS status Theorem for theBenchmark.p
% 3.74/0.97  
% 3.74/0.97   Resolution empty clause
% 3.74/0.97  
% 3.74/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/0.97  
% 3.74/0.97  fof(f11,conjecture,(
% 3.74/0.97    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f12,negated_conjecture,(
% 3.74/0.97    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 3.74/0.97    inference(negated_conjecture,[],[f11])).
% 3.74/0.97  
% 3.74/0.97  fof(f16,plain,(
% 3.74/0.97    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 3.74/0.97    inference(ennf_transformation,[],[f12])).
% 3.74/0.97  
% 3.74/0.97  fof(f29,plain,(
% 3.74/0.97    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK2 != sK3 & k1_ordinal1(sK2) = k1_ordinal1(sK3))),
% 3.74/0.97    introduced(choice_axiom,[])).
% 3.74/0.97  
% 3.74/0.97  fof(f30,plain,(
% 3.74/0.97    sK2 != sK3 & k1_ordinal1(sK2) = k1_ordinal1(sK3)),
% 3.74/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f29])).
% 3.74/0.97  
% 3.74/0.97  fof(f53,plain,(
% 3.74/0.97    k1_ordinal1(sK2) = k1_ordinal1(sK3)),
% 3.74/0.97    inference(cnf_transformation,[],[f30])).
% 3.74/0.97  
% 3.74/0.97  fof(f8,axiom,(
% 3.74/0.97    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f50,plain,(
% 3.74/0.97    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.74/0.97    inference(cnf_transformation,[],[f8])).
% 3.74/0.97  
% 3.74/0.97  fof(f6,axiom,(
% 3.74/0.97    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f48,plain,(
% 3.74/0.97    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.74/0.97    inference(cnf_transformation,[],[f6])).
% 3.74/0.97  
% 3.74/0.97  fof(f5,axiom,(
% 3.74/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f47,plain,(
% 3.74/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.74/0.97    inference(cnf_transformation,[],[f5])).
% 3.74/0.97  
% 3.74/0.97  fof(f55,plain,(
% 3.74/0.97    ( ! [X0] : (k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))) = k1_ordinal1(X0)) )),
% 3.74/0.97    inference(definition_unfolding,[],[f50,f48,f47])).
% 3.74/0.97  
% 3.74/0.97  fof(f58,plain,(
% 3.74/0.97    k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2))) = k3_tarski(k2_tarski(sK3,k2_tarski(sK3,sK3)))),
% 3.74/0.97    inference(definition_unfolding,[],[f53,f55,f55])).
% 3.74/0.97  
% 3.74/0.97  fof(f9,axiom,(
% 3.74/0.97    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f51,plain,(
% 3.74/0.97    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.74/0.97    inference(cnf_transformation,[],[f9])).
% 3.74/0.97  
% 3.74/0.97  fof(f57,plain,(
% 3.74/0.97    ( ! [X0] : (r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))))) )),
% 3.74/0.97    inference(definition_unfolding,[],[f51,f55])).
% 3.74/0.97  
% 3.74/0.97  fof(f7,axiom,(
% 3.74/0.97    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f14,plain,(
% 3.74/0.97    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | r2_hidden(X0,X1))),
% 3.74/0.97    inference(ennf_transformation,[],[f7])).
% 3.74/0.97  
% 3.74/0.97  fof(f49,plain,(
% 3.74/0.97    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 | r2_hidden(X0,X1)) )),
% 3.74/0.97    inference(cnf_transformation,[],[f14])).
% 3.74/0.97  
% 3.74/0.97  fof(f56,plain,(
% 3.74/0.97    ( ! [X0,X1] : (k4_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0)) = X1 | r2_hidden(X0,X1)) )),
% 3.74/0.97    inference(definition_unfolding,[],[f49,f48,f47,f47])).
% 3.74/0.97  
% 3.74/0.97  fof(f3,axiom,(
% 3.74/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f22,plain,(
% 3.74/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/0.97    inference(nnf_transformation,[],[f3])).
% 3.74/0.97  
% 3.74/0.97  fof(f23,plain,(
% 3.74/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/0.97    inference(flattening,[],[f22])).
% 3.74/0.97  
% 3.74/0.97  fof(f38,plain,(
% 3.74/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.74/0.97    inference(cnf_transformation,[],[f23])).
% 3.74/0.97  
% 3.74/0.97  fof(f63,plain,(
% 3.74/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.74/0.97    inference(equality_resolution,[],[f38])).
% 3.74/0.97  
% 3.74/0.97  fof(f10,axiom,(
% 3.74/0.97    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f15,plain,(
% 3.74/0.97    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.74/0.97    inference(ennf_transformation,[],[f10])).
% 3.74/0.97  
% 3.74/0.97  fof(f52,plain,(
% 3.74/0.97    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.74/0.97    inference(cnf_transformation,[],[f15])).
% 3.74/0.97  
% 3.74/0.97  fof(f2,axiom,(
% 3.74/0.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f17,plain,(
% 3.74/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.74/0.97    inference(nnf_transformation,[],[f2])).
% 3.74/0.97  
% 3.74/0.97  fof(f18,plain,(
% 3.74/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.74/0.97    inference(flattening,[],[f17])).
% 3.74/0.97  
% 3.74/0.97  fof(f19,plain,(
% 3.74/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.74/0.97    inference(rectify,[],[f18])).
% 3.74/0.97  
% 3.74/0.97  fof(f20,plain,(
% 3.74/0.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.74/0.97    introduced(choice_axiom,[])).
% 3.74/0.97  
% 3.74/0.97  fof(f21,plain,(
% 3.74/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.74/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.74/0.97  
% 3.74/0.97  fof(f34,plain,(
% 3.74/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.74/0.97    inference(cnf_transformation,[],[f21])).
% 3.74/0.97  
% 3.74/0.97  fof(f59,plain,(
% 3.74/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.74/0.97    inference(equality_resolution,[],[f34])).
% 3.74/0.97  
% 3.74/0.97  fof(f4,axiom,(
% 3.74/0.97    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f24,plain,(
% 3.74/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.74/0.97    inference(nnf_transformation,[],[f4])).
% 3.74/0.97  
% 3.74/0.97  fof(f25,plain,(
% 3.74/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.74/0.97    inference(flattening,[],[f24])).
% 3.74/0.97  
% 3.74/0.97  fof(f26,plain,(
% 3.74/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.74/0.97    inference(rectify,[],[f25])).
% 3.74/0.97  
% 3.74/0.97  fof(f27,plain,(
% 3.74/0.97    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.74/0.97    introduced(choice_axiom,[])).
% 3.74/0.97  
% 3.74/0.97  fof(f28,plain,(
% 3.74/0.97    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.74/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.74/0.97  
% 3.74/0.97  fof(f41,plain,(
% 3.74/0.97    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.74/0.97    inference(cnf_transformation,[],[f28])).
% 3.74/0.97  
% 3.74/0.97  fof(f68,plain,(
% 3.74/0.97    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 3.74/0.97    inference(equality_resolution,[],[f41])).
% 3.74/0.97  
% 3.74/0.97  fof(f1,axiom,(
% 3.74/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.74/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.74/0.97  
% 3.74/0.97  fof(f13,plain,(
% 3.74/0.97    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.74/0.97    inference(ennf_transformation,[],[f1])).
% 3.74/0.97  
% 3.74/0.97  fof(f31,plain,(
% 3.74/0.97    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.74/0.97    inference(cnf_transformation,[],[f13])).
% 3.74/0.97  
% 3.74/0.97  fof(f54,plain,(
% 3.74/0.97    sK2 != sK3),
% 3.74/0.97    inference(cnf_transformation,[],[f30])).
% 3.74/0.97  
% 3.74/0.97  cnf(c_20,negated_conjecture,
% 3.74/0.97      ( k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2))) = k3_tarski(k2_tarski(sK3,k2_tarski(sK3,sK3))) ),
% 3.74/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_17,plain,
% 3.74/0.97      ( r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) ),
% 3.74/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4470,plain,
% 3.74/0.97      ( r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) = iProver_top ),
% 3.74/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4617,plain,
% 3.74/0.97      ( r2_hidden(sK3,k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2)))) = iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_20,c_4470]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_16,plain,
% 3.74/0.97      ( r2_hidden(X0,X1)
% 3.74/0.97      | k4_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0)) = X1 ),
% 3.74/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4471,plain,
% 3.74/0.97      ( k4_xboole_0(k3_tarski(k2_tarski(X0,k2_tarski(X1,X1))),k2_tarski(X1,X1)) = X0
% 3.74/0.97      | r2_hidden(X1,X0) = iProver_top ),
% 3.74/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_9,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f63]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4475,plain,
% 3.74/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.74/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_18,negated_conjecture,
% 3.74/0.97      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.74/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4469,plain,
% 3.74/0.97      ( r1_tarski(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 3.74/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4599,plain,
% 3.74/0.97      ( r2_hidden(X0,X0) != iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_4475,c_4469]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4680,plain,
% 3.74/0.97      ( k4_xboole_0(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))),k2_tarski(X0,X0)) = X0 ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_4471,c_4599]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4,plain,
% 3.74/0.97      ( ~ r2_hidden(X0,X1)
% 3.74/0.97      | r2_hidden(X0,X2)
% 3.74/0.97      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.74/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4479,plain,
% 3.74/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.74/0.97      | r2_hidden(X0,X2) = iProver_top
% 3.74/0.97      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 3.74/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4772,plain,
% 3.74/0.97      ( r2_hidden(X0,X1) = iProver_top
% 3.74/0.97      | r2_hidden(X0,k2_tarski(X1,X1)) = iProver_top
% 3.74/0.97      | r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) != iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_4680,c_4479]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_9011,plain,
% 3.74/0.97      ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top
% 3.74/0.97      | r2_hidden(sK3,sK2) = iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_4617,c_4772]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_15,plain,
% 3.74/0.97      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.74/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4472,plain,
% 3.74/0.97      ( X0 = X1 | X0 = X2 | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 3.74/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_9066,plain,
% 3.74/0.97      ( sK3 = sK2 | r2_hidden(sK3,sK2) = iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_9011,c_4472]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4771,plain,
% 3.74/0.97      ( k4_xboole_0(k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2))),k2_tarski(sK3,sK3)) = sK3 ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_20,c_4680]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_0,negated_conjecture,
% 3.74/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.74/0.97      inference(cnf_transformation,[],[f31]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4480,plain,
% 3.74/0.97      ( r2_hidden(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 3.74/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4731,plain,
% 3.74/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.74/0.97      | r2_hidden(X0,X2) = iProver_top
% 3.74/0.97      | r2_hidden(k4_xboole_0(X1,X2),X0) != iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_4479,c_4480]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_4953,plain,
% 3.74/0.97      ( r2_hidden(X0,k2_tarski(sK3,sK3)) = iProver_top
% 3.74/0.97      | r2_hidden(X0,k3_tarski(k2_tarski(sK2,k2_tarski(sK2,sK2)))) != iProver_top
% 3.74/0.97      | r2_hidden(sK3,X0) != iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_4771,c_4731]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_5047,plain,
% 3.74/0.97      ( r2_hidden(sK3,sK2) != iProver_top
% 3.74/0.97      | r2_hidden(sK2,k2_tarski(sK3,sK3)) = iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_4470,c_4953]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_5262,plain,
% 3.74/0.97      ( sK3 = sK2 | r2_hidden(sK3,sK2) != iProver_top ),
% 3.74/0.97      inference(superposition,[status(thm)],[c_5047,c_4472]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_9123,plain,
% 3.74/0.97      ( sK3 = sK2 ),
% 3.74/0.97      inference(global_propositional_subsumption,[status(thm)],[c_9066,c_5262]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_19,negated_conjecture,
% 3.74/0.97      ( sK2 != sK3 ),
% 3.74/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_9164,plain,
% 3.74/0.97      ( sK2 != sK2 ),
% 3.74/0.97      inference(demodulation,[status(thm)],[c_9123,c_19]) ).
% 3.74/0.97  
% 3.74/0.97  cnf(c_9165,plain,
% 3.74/0.97      ( $false ),
% 3.74/0.97      inference(equality_resolution_simp,[status(thm)],[c_9164]) ).
% 3.74/0.97  
% 3.74/0.97  
% 3.74/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/0.97  
% 3.74/0.97  ------                               Statistics
% 3.74/0.97  
% 3.74/0.97  ------ Selected
% 3.74/0.97  
% 3.74/0.97  total_time:                             0.273
% 3.74/0.97  
%------------------------------------------------------------------------------
