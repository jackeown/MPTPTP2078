%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:23 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 294 expanded)
%              Number of clauses        :   44 (  54 expanded)
%              Number of leaves         :   15 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  389 (1095 expanded)
%              Number of equality atoms :  231 ( 728 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK3 != sK4
      & k1_ordinal1(sK3) = k1_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK3 != sK4
    & k1_ordinal1(sK3) = k1_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f14,f28])).

fof(f55,plain,(
    k1_ordinal1(sK3) = k1_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f57])).

fof(f60,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f53,f58,f59])).

fof(f68,plain,(
    k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3))) = k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f55,f60,f60])).

fof(f9,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0] : r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f58])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f56,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f13,f15])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f51])).

fof(f22,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4) != X0
            & sK2(X0,X1,X2,X3,X4) != X1
            & sK2(X0,X1,X2,X3,X4) != X2
            & sK2(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
        & ( sK2(X0,X1,X2,X3,X4) = X0
          | sK2(X0,X1,X2,X3,X4) = X1
          | sK2(X0,X1,X2,X3,X4) = X2
          | sK2(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK2(X0,X1,X2,X3,X4) != X0
              & sK2(X0,X1,X2,X3,X4) != X1
              & sK2(X0,X1,X2,X3,X4) != X2
              & sK2(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
          & ( sK2(X0,X1,X2,X3,X4) = X0
            | sK2(X0,X1,X2,X3,X4) = X1
            | sK2(X0,X1,X2,X3,X4) = X2
            | sK2(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X0 = X6
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | ~ r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X6,X4) ) ),
    inference(equality_resolution,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_21,negated_conjecture,
    ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3))) = k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
    ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1250,plain,
    ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1357,plain,
    ( r2_hidden(sK4,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1250])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1263,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1919,plain,
    ( r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_1263])).

cnf(c_20,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_25,plain,
    ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_27,plain,
    ( sP0(sK3,sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ r2_hidden(X5,X4)
    | X5 = X3
    | X5 = X2
    | X5 = X1
    | X5 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_705,plain,
    ( ~ r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X0 = X5
    | X0 = X9
    | X0 = X7
    | X0 = X3
    | k2_enumset1(X2,X4,X6,X8) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_18])).

cnf(c_706,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
    | X0 = X2
    | X0 = X1
    | X0 = X4
    | X0 = X3 ),
    inference(unflattening,[status(thm)],[c_705])).

cnf(c_708,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | r2_hidden(X3,X4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_726,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | k2_enumset1(X4,X5,X7,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_727,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(unflattening,[status(thm)],[c_726])).

cnf(c_729,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_895,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1318,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_1319,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1318])).

cnf(c_1398,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ r2_hidden(sK4,X4)
    | sK4 = X0
    | sK4 = X3
    | sK4 = X2
    | sK4 = X1 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1516,plain,
    ( ~ sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0))
    | ~ r2_hidden(sK4,k2_enumset1(X3,X2,X1,X0))
    | sK4 = X0
    | sK4 = X3
    | sK4 = X2
    | sK4 = X1 ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_1517,plain,
    ( sK4 = X0
    | sK4 = X1
    | sK4 = X2
    | sK4 = X3
    | sP0(X0,X3,X2,X1,k2_enumset1(X1,X2,X3,X0)) != iProver_top
    | r2_hidden(sK4,k2_enumset1(X1,X2,X3,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1516])).

cnf(c_1519,plain,
    ( sK4 = sK3
    | sP0(sK3,sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_5542,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1919,c_20,c_27,c_708,c_729,c_1319,c_1519])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1269,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5546,plain,
    ( r2_hidden(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5542,c_1269])).

cnf(c_1910,plain,
    ( sP0(sK4,X0,sK4,sK4,k2_enumset1(sK4,sK4,X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_5137,plain,
    ( sP0(sK4,sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_5138,plain,
    ( sP0(sK4,sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5137])).

cnf(c_1354,plain,
    ( ~ sP0(sK4,X0,X1,X2,X3)
    | ~ r2_hidden(sK3,X3)
    | sK3 = X0
    | sK3 = X2
    | sK3 = X1
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1434,plain,
    ( ~ sP0(sK4,X0,sK4,X1,X2)
    | ~ r2_hidden(sK3,X2)
    | sK3 = X0
    | sK3 = X1
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1509,plain,
    ( ~ sP0(sK4,X0,sK4,sK4,X1)
    | ~ r2_hidden(sK3,X1)
    | sK3 = X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_1909,plain,
    ( ~ sP0(sK4,X0,sK4,sK4,k2_enumset1(sK4,sK4,X0,sK4))
    | ~ r2_hidden(sK3,k2_enumset1(sK4,sK4,X0,sK4))
    | sK3 = X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_2976,plain,
    ( ~ sP0(sK4,sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_2977,plain,
    ( sK3 = sK4
    | sP0(sK4,sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2976])).

cnf(c_1920,plain,
    ( r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1263])).

cnf(c_1924,plain,
    ( r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_22,plain,
    ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_24,plain,
    ( r2_hidden(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5546,c_5138,c_2977,c_1924,c_24,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:49:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.61/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.06  
% 2.61/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.61/1.06  
% 2.61/1.06  ------  iProver source info
% 2.61/1.06  
% 2.61/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.61/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.61/1.06  git: non_committed_changes: false
% 2.61/1.06  git: last_make_outside_of_git: false
% 2.61/1.06  
% 2.61/1.06  ------ 
% 2.61/1.06  ------ Parsing...
% 2.61/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.61/1.06  
% 2.61/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.61/1.06  
% 2.61/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.61/1.06  
% 2.61/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.61/1.06  ------ Proving...
% 2.61/1.06  ------ Problem Properties 
% 2.61/1.06  
% 2.61/1.06  
% 2.61/1.06  clauses                                 22
% 2.61/1.06  conjectures                             2
% 2.61/1.06  EPR                                     7
% 2.61/1.06  Horn                                    18
% 2.61/1.06  unary                                   4
% 2.61/1.06  binary                                  8
% 2.61/1.06  lits                                    57
% 2.61/1.06  lits eq                                 18
% 2.61/1.06  fd_pure                                 0
% 2.61/1.06  fd_pseudo                               0
% 2.61/1.06  fd_cond                                 0
% 2.61/1.06  fd_pseudo_cond                          5
% 2.61/1.06  AC symbols                              0
% 2.61/1.06  
% 2.61/1.06  ------ Input Options Time Limit: Unbounded
% 2.61/1.06  
% 2.61/1.06  
% 2.61/1.06  ------ 
% 2.61/1.06  Current options:
% 2.61/1.06  ------ 
% 2.61/1.06  
% 2.61/1.06  
% 2.61/1.06  
% 2.61/1.06  
% 2.61/1.06  ------ Proving...
% 2.61/1.06  
% 2.61/1.06  
% 2.61/1.06  % SZS status Theorem for theBenchmark.p
% 2.61/1.06  
% 2.61/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.61/1.06  
% 2.61/1.06  fof(f10,conjecture,(
% 2.61/1.06    ! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f11,negated_conjecture,(
% 2.61/1.06    ~! [X0,X1] : (k1_ordinal1(X0) = k1_ordinal1(X1) => X0 = X1)),
% 2.61/1.06    inference(negated_conjecture,[],[f10])).
% 2.61/1.06  
% 2.61/1.06  fof(f14,plain,(
% 2.61/1.06    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1))),
% 2.61/1.06    inference(ennf_transformation,[],[f11])).
% 2.61/1.06  
% 2.61/1.06  fof(f28,plain,(
% 2.61/1.06    ? [X0,X1] : (X0 != X1 & k1_ordinal1(X0) = k1_ordinal1(X1)) => (sK3 != sK4 & k1_ordinal1(sK3) = k1_ordinal1(sK4))),
% 2.61/1.06    introduced(choice_axiom,[])).
% 2.61/1.06  
% 2.61/1.06  fof(f29,plain,(
% 2.61/1.06    sK3 != sK4 & k1_ordinal1(sK3) = k1_ordinal1(sK4)),
% 2.61/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f14,f28])).
% 2.61/1.06  
% 2.61/1.06  fof(f55,plain,(
% 2.61/1.06    k1_ordinal1(sK3) = k1_ordinal1(sK4)),
% 2.61/1.06    inference(cnf_transformation,[],[f29])).
% 2.61/1.06  
% 2.61/1.06  fof(f8,axiom,(
% 2.61/1.06    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f53,plain,(
% 2.61/1.06    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.61/1.06    inference(cnf_transformation,[],[f8])).
% 2.61/1.06  
% 2.61/1.06  fof(f6,axiom,(
% 2.61/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f40,plain,(
% 2.61/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.61/1.06    inference(cnf_transformation,[],[f6])).
% 2.61/1.06  
% 2.61/1.06  fof(f58,plain,(
% 2.61/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.61/1.06    inference(definition_unfolding,[],[f40,f57])).
% 2.61/1.06  
% 2.61/1.06  fof(f3,axiom,(
% 2.61/1.06    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f37,plain,(
% 2.61/1.06    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.61/1.06    inference(cnf_transformation,[],[f3])).
% 2.61/1.06  
% 2.61/1.06  fof(f4,axiom,(
% 2.61/1.06    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f38,plain,(
% 2.61/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.61/1.06    inference(cnf_transformation,[],[f4])).
% 2.61/1.06  
% 2.61/1.06  fof(f5,axiom,(
% 2.61/1.06    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f39,plain,(
% 2.61/1.06    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.61/1.06    inference(cnf_transformation,[],[f5])).
% 2.61/1.06  
% 2.61/1.06  fof(f57,plain,(
% 2.61/1.06    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.61/1.06    inference(definition_unfolding,[],[f38,f39])).
% 2.61/1.06  
% 2.61/1.06  fof(f59,plain,(
% 2.61/1.06    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.61/1.06    inference(definition_unfolding,[],[f37,f57])).
% 2.61/1.06  
% 2.61/1.06  fof(f60,plain,(
% 2.61/1.06    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.61/1.06    inference(definition_unfolding,[],[f53,f58,f59])).
% 2.61/1.06  
% 2.61/1.06  fof(f68,plain,(
% 2.61/1.06    k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3))) = k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4)))),
% 2.61/1.06    inference(definition_unfolding,[],[f55,f60,f60])).
% 2.61/1.06  
% 2.61/1.06  fof(f9,axiom,(
% 2.61/1.06    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f54,plain,(
% 2.61/1.06    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.61/1.06    inference(cnf_transformation,[],[f9])).
% 2.61/1.06  
% 2.61/1.06  fof(f67,plain,(
% 2.61/1.06    ( ! [X0] : (r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0))))) )),
% 2.61/1.06    inference(definition_unfolding,[],[f54,f60])).
% 2.61/1.06  
% 2.61/1.06  fof(f2,axiom,(
% 2.61/1.06    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f17,plain,(
% 2.61/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.61/1.06    inference(nnf_transformation,[],[f2])).
% 2.61/1.06  
% 2.61/1.06  fof(f18,plain,(
% 2.61/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.61/1.06    inference(flattening,[],[f17])).
% 2.61/1.06  
% 2.61/1.06  fof(f19,plain,(
% 2.61/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.61/1.06    inference(rectify,[],[f18])).
% 2.61/1.06  
% 2.61/1.06  fof(f20,plain,(
% 2.61/1.06    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.61/1.06    introduced(choice_axiom,[])).
% 2.61/1.06  
% 2.61/1.06  fof(f21,plain,(
% 2.61/1.06    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.61/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 2.61/1.06  
% 2.61/1.06  fof(f31,plain,(
% 2.61/1.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.61/1.06    inference(cnf_transformation,[],[f21])).
% 2.61/1.06  
% 2.61/1.06  fof(f66,plain,(
% 2.61/1.06    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 2.61/1.06    inference(definition_unfolding,[],[f31,f58])).
% 2.61/1.06  
% 2.61/1.06  fof(f71,plain,(
% 2.61/1.06    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.61/1.06    inference(equality_resolution,[],[f66])).
% 2.61/1.06  
% 2.61/1.06  fof(f56,plain,(
% 2.61/1.06    sK3 != sK4),
% 2.61/1.06    inference(cnf_transformation,[],[f29])).
% 2.61/1.06  
% 2.61/1.06  fof(f7,axiom,(
% 2.61/1.06    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f13,plain,(
% 2.61/1.06    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 2.61/1.06    inference(ennf_transformation,[],[f7])).
% 2.61/1.06  
% 2.61/1.06  fof(f15,plain,(
% 2.61/1.06    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 2.61/1.06    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.61/1.06  
% 2.61/1.06  fof(f16,plain,(
% 2.61/1.06    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 2.61/1.06    inference(definition_folding,[],[f13,f15])).
% 2.61/1.06  
% 2.61/1.06  fof(f27,plain,(
% 2.61/1.06    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 2.61/1.06    inference(nnf_transformation,[],[f16])).
% 2.61/1.06  
% 2.61/1.06  fof(f51,plain,(
% 2.61/1.06    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 2.61/1.06    inference(cnf_transformation,[],[f27])).
% 2.61/1.06  
% 2.61/1.06  fof(f76,plain,(
% 2.61/1.06    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3))) )),
% 2.61/1.06    inference(equality_resolution,[],[f51])).
% 2.61/1.06  
% 2.61/1.06  fof(f22,plain,(
% 2.61/1.06    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 2.61/1.06    inference(nnf_transformation,[],[f15])).
% 2.61/1.06  
% 2.61/1.06  fof(f23,plain,(
% 2.61/1.06    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 2.61/1.06    inference(flattening,[],[f22])).
% 2.61/1.06  
% 2.61/1.06  fof(f24,plain,(
% 2.61/1.06    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.61/1.06    inference(rectify,[],[f23])).
% 2.61/1.06  
% 2.61/1.06  fof(f25,plain,(
% 2.61/1.06    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK2(X0,X1,X2,X3,X4) != X0 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X0 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4))))),
% 2.61/1.06    introduced(choice_axiom,[])).
% 2.61/1.06  
% 2.61/1.06  fof(f26,plain,(
% 2.61/1.06    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK2(X0,X1,X2,X3,X4) != X0 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X0 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 2.61/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 2.61/1.06  
% 2.61/1.06  fof(f41,plain,(
% 2.61/1.06    ( ! [X6,X4,X2,X0,X3,X1] : (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.61/1.06    inference(cnf_transformation,[],[f26])).
% 2.61/1.06  
% 2.61/1.06  fof(f42,plain,(
% 2.61/1.06    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | ~sP0(X0,X1,X2,X3,X4)) )),
% 2.61/1.06    inference(cnf_transformation,[],[f26])).
% 2.61/1.06  
% 2.61/1.06  fof(f75,plain,(
% 2.61/1.06    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X6,X4)) )),
% 2.61/1.06    inference(equality_resolution,[],[f42])).
% 2.61/1.06  
% 2.61/1.06  fof(f1,axiom,(
% 2.61/1.06    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.61/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.61/1.06  
% 2.61/1.06  fof(f12,plain,(
% 2.61/1.06    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.61/1.06    inference(ennf_transformation,[],[f1])).
% 2.61/1.06  
% 2.61/1.06  fof(f30,plain,(
% 2.61/1.06    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.61/1.06    inference(cnf_transformation,[],[f12])).
% 2.61/1.06  
% 2.61/1.06  cnf(c_21,negated_conjecture,
% 2.61/1.06      ( k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3))) = k3_tarski(k2_enumset1(sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 2.61/1.06      inference(cnf_transformation,[],[f68]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_19,plain,
% 2.61/1.06      ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) ),
% 2.61/1.06      inference(cnf_transformation,[],[f67]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1250,plain,
% 2.61/1.06      ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) = iProver_top ),
% 2.61/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1357,plain,
% 2.61/1.06      ( r2_hidden(sK4,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 2.61/1.06      inference(superposition,[status(thm)],[c_21,c_1250]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_6,plain,
% 2.61/1.06      ( r2_hidden(X0,X1)
% 2.61/1.06      | r2_hidden(X0,X2)
% 2.61/1.06      | ~ r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 2.61/1.06      inference(cnf_transformation,[],[f71]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1263,plain,
% 2.61/1.06      ( r2_hidden(X0,X1) = iProver_top
% 2.61/1.06      | r2_hidden(X0,X2) = iProver_top
% 2.61/1.06      | r2_hidden(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) != iProver_top ),
% 2.61/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1919,plain,
% 2.61/1.06      ( r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 2.61/1.06      | r2_hidden(sK4,sK3) = iProver_top ),
% 2.61/1.06      inference(superposition,[status(thm)],[c_1357,c_1263]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_20,negated_conjecture,
% 2.61/1.06      ( sK3 != sK4 ),
% 2.61/1.06      inference(cnf_transformation,[],[f56]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_18,plain,
% 2.61/1.06      ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) ),
% 2.61/1.06      inference(cnf_transformation,[],[f76]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_25,plain,
% 2.61/1.06      ( sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0)) = iProver_top ),
% 2.61/1.06      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_27,plain,
% 2.61/1.06      ( sP0(sK3,sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_25]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_16,plain,
% 2.61/1.06      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.61/1.06      | ~ r2_hidden(X5,X4)
% 2.61/1.06      | X5 = X3
% 2.61/1.06      | X5 = X2
% 2.61/1.06      | X5 = X1
% 2.61/1.06      | X5 = X0 ),
% 2.61/1.06      inference(cnf_transformation,[],[f41]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_705,plain,
% 2.61/1.06      ( ~ r2_hidden(X0,X1)
% 2.61/1.06      | X2 != X3
% 2.61/1.06      | X4 != X5
% 2.61/1.06      | X6 != X7
% 2.61/1.06      | X8 != X9
% 2.61/1.06      | X0 = X5
% 2.61/1.06      | X0 = X9
% 2.61/1.06      | X0 = X7
% 2.61/1.06      | X0 = X3
% 2.61/1.06      | k2_enumset1(X2,X4,X6,X8) != X1 ),
% 2.61/1.06      inference(resolution_lifted,[status(thm)],[c_16,c_18]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_706,plain,
% 2.61/1.06      ( ~ r2_hidden(X0,k2_enumset1(X1,X2,X3,X4))
% 2.61/1.06      | X0 = X2
% 2.61/1.06      | X0 = X1
% 2.61/1.06      | X0 = X4
% 2.61/1.06      | X0 = X3 ),
% 2.61/1.06      inference(unflattening,[status(thm)],[c_705]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_708,plain,
% 2.61/1.06      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_706]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_15,plain,
% 2.61/1.06      ( ~ sP0(X0,X1,X2,X3,X4) | r2_hidden(X3,X4) ),
% 2.61/1.06      inference(cnf_transformation,[],[f75]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_726,plain,
% 2.61/1.06      ( r2_hidden(X0,X1)
% 2.61/1.06      | X2 != X3
% 2.61/1.06      | X4 != X0
% 2.61/1.06      | X5 != X6
% 2.61/1.06      | X7 != X8
% 2.61/1.06      | k2_enumset1(X4,X5,X7,X2) != X1 ),
% 2.61/1.06      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_727,plain,
% 2.61/1.06      ( r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
% 2.61/1.06      inference(unflattening,[status(thm)],[c_726]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_729,plain,
% 2.61/1.06      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_727]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_895,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1318,plain,
% 2.61/1.06      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_895]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1319,plain,
% 2.61/1.06      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1318]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1398,plain,
% 2.61/1.06      ( ~ sP0(X0,X1,X2,X3,X4)
% 2.61/1.06      | ~ r2_hidden(sK4,X4)
% 2.61/1.06      | sK4 = X0
% 2.61/1.06      | sK4 = X3
% 2.61/1.06      | sK4 = X2
% 2.61/1.06      | sK4 = X1 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_16]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1516,plain,
% 2.61/1.06      ( ~ sP0(X0,X1,X2,X3,k2_enumset1(X3,X2,X1,X0))
% 2.61/1.06      | ~ r2_hidden(sK4,k2_enumset1(X3,X2,X1,X0))
% 2.61/1.06      | sK4 = X0
% 2.61/1.06      | sK4 = X3
% 2.61/1.06      | sK4 = X2
% 2.61/1.06      | sK4 = X1 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1398]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1517,plain,
% 2.61/1.06      ( sK4 = X0
% 2.61/1.06      | sK4 = X1
% 2.61/1.06      | sK4 = X2
% 2.61/1.06      | sK4 = X3
% 2.61/1.06      | sP0(X0,X3,X2,X1,k2_enumset1(X1,X2,X3,X0)) != iProver_top
% 2.61/1.06      | r2_hidden(sK4,k2_enumset1(X1,X2,X3,X0)) != iProver_top ),
% 2.61/1.06      inference(predicate_to_equality,[status(thm)],[c_1516]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1519,plain,
% 2.61/1.06      ( sK4 = sK3
% 2.61/1.06      | sP0(sK3,sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top
% 2.61/1.06      | r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1517]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_5542,plain,
% 2.61/1.06      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.61/1.06      inference(global_propositional_subsumption,
% 2.61/1.06                [status(thm)],
% 2.61/1.06                [c_1919,c_20,c_27,c_708,c_729,c_1319,c_1519]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_0,plain,
% 2.61/1.06      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.61/1.06      inference(cnf_transformation,[],[f30]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1269,plain,
% 2.61/1.06      ( r2_hidden(X0,X1) != iProver_top
% 2.61/1.06      | r2_hidden(X1,X0) != iProver_top ),
% 2.61/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_5546,plain,
% 2.61/1.06      ( r2_hidden(sK3,sK4) != iProver_top ),
% 2.61/1.06      inference(superposition,[status(thm)],[c_5542,c_1269]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1910,plain,
% 2.61/1.06      ( sP0(sK4,X0,sK4,sK4,k2_enumset1(sK4,sK4,X0,sK4)) ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_18]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_5137,plain,
% 2.61/1.06      ( sP0(sK4,sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1910]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_5138,plain,
% 2.61/1.06      ( sP0(sK4,sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.61/1.06      inference(predicate_to_equality,[status(thm)],[c_5137]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1354,plain,
% 2.61/1.06      ( ~ sP0(sK4,X0,X1,X2,X3)
% 2.61/1.06      | ~ r2_hidden(sK3,X3)
% 2.61/1.06      | sK3 = X0
% 2.61/1.06      | sK3 = X2
% 2.61/1.06      | sK3 = X1
% 2.61/1.06      | sK3 = sK4 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_16]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1434,plain,
% 2.61/1.06      ( ~ sP0(sK4,X0,sK4,X1,X2)
% 2.61/1.06      | ~ r2_hidden(sK3,X2)
% 2.61/1.06      | sK3 = X0
% 2.61/1.06      | sK3 = X1
% 2.61/1.06      | sK3 = sK4 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1509,plain,
% 2.61/1.06      ( ~ sP0(sK4,X0,sK4,sK4,X1)
% 2.61/1.06      | ~ r2_hidden(sK3,X1)
% 2.61/1.06      | sK3 = X0
% 2.61/1.06      | sK3 = sK4 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1434]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1909,plain,
% 2.61/1.06      ( ~ sP0(sK4,X0,sK4,sK4,k2_enumset1(sK4,sK4,X0,sK4))
% 2.61/1.06      | ~ r2_hidden(sK3,k2_enumset1(sK4,sK4,X0,sK4))
% 2.61/1.06      | sK3 = X0
% 2.61/1.06      | sK3 = sK4 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1509]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_2976,plain,
% 2.61/1.06      ( ~ sP0(sK4,sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4))
% 2.61/1.06      | ~ r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4))
% 2.61/1.06      | sK3 = sK4 ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1909]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_2977,plain,
% 2.61/1.06      ( sK3 = sK4
% 2.61/1.06      | sP0(sK4,sK4,sK4,sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 2.61/1.06      | r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 2.61/1.06      inference(predicate_to_equality,[status(thm)],[c_2976]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1920,plain,
% 2.61/1.06      ( r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 2.61/1.06      | r2_hidden(X0,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 2.61/1.06      | r2_hidden(X0,sK4) = iProver_top ),
% 2.61/1.06      inference(superposition,[status(thm)],[c_21,c_1263]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_1924,plain,
% 2.61/1.06      ( r2_hidden(sK3,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 2.61/1.06      | r2_hidden(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)))) != iProver_top
% 2.61/1.06      | r2_hidden(sK3,sK4) = iProver_top ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_1920]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_22,plain,
% 2.61/1.06      ( r2_hidden(X0,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(X0,X0,X0,X0)))) = iProver_top ),
% 2.61/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(c_24,plain,
% 2.61/1.06      ( r2_hidden(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,k2_enumset1(sK3,sK3,sK3,sK3)))) = iProver_top ),
% 2.61/1.06      inference(instantiation,[status(thm)],[c_22]) ).
% 2.61/1.06  
% 2.61/1.06  cnf(contradiction,plain,
% 2.61/1.06      ( $false ),
% 2.61/1.06      inference(minisat,
% 2.61/1.06                [status(thm)],
% 2.61/1.06                [c_5546,c_5138,c_2977,c_1924,c_24,c_20]) ).
% 2.61/1.06  
% 2.61/1.06  
% 2.61/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.61/1.06  
% 2.61/1.06  ------                               Statistics
% 2.61/1.06  
% 2.61/1.06  ------ Selected
% 2.61/1.06  
% 2.61/1.06  total_time:                             0.287
% 2.61/1.06  
%------------------------------------------------------------------------------
