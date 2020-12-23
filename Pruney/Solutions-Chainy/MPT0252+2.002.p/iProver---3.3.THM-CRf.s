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
% DateTime   : Thu Dec  3 11:33:21 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 124 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  264 ( 327 expanded)
%              Number of equality atoms :  130 ( 181 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f102,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f70,f82])).

fof(f113,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f102])).

fof(f114,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f113])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f76,f82])).

fof(f96,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f67,f83,f83])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK3,sK5)
      & r1_tarski(k2_xboole_0(k2_tarski(sK3,sK4),sK5),sK5) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r2_hidden(sK3,sK5)
    & r1_tarski(k2_xboole_0(k2_tarski(sK3,sK4),sK5),sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f41])).

fof(f80,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK3,sK4),sK5),sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f79,f83])).

fof(f105,plain,(
    r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),sK5)),sK5) ),
    inference(definition_unfolding,[],[f80,f84,f83])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f66,f84])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f84])).

fof(f106,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f88])).

fof(f81,plain,(
    ~ r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_29,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1051,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_23,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),sK5)),sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1047,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),sK5)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1560,plain,
    ( r1_tarski(k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK4))),sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23,c_1047])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1064,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2293,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK4))) = sK5
    | r1_tarski(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_1064])).

cnf(c_22,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1057,plain,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2540,plain,
    ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK4))) = sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2293,c_1057])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1074,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3603,plain,
    ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_1074])).

cnf(c_4234,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1051,c_3603])).

cnf(c_32,negated_conjecture,
    ( ~ r2_hidden(sK3,sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,plain,
    ( r2_hidden(sK3,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4234,c_35])).

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
% 0.12/0.33  % DateTime   : Tue Dec  1 15:56:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.47/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/0.97  
% 2.47/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/0.97  
% 2.47/0.97  ------  iProver source info
% 2.47/0.97  
% 2.47/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.47/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/0.97  git: non_committed_changes: false
% 2.47/0.97  git: last_make_outside_of_git: false
% 2.47/0.97  
% 2.47/0.97  ------ 
% 2.47/0.97  
% 2.47/0.97  ------ Input Options
% 2.47/0.97  
% 2.47/0.97  --out_options                           all
% 2.47/0.97  --tptp_safe_out                         true
% 2.47/0.97  --problem_path                          ""
% 2.47/0.97  --include_path                          ""
% 2.47/0.97  --clausifier                            res/vclausify_rel
% 2.47/0.97  --clausifier_options                    --mode clausify
% 2.47/0.97  --stdin                                 false
% 2.47/0.97  --stats_out                             all
% 2.47/0.97  
% 2.47/0.97  ------ General Options
% 2.47/0.97  
% 2.47/0.97  --fof                                   false
% 2.47/0.97  --time_out_real                         305.
% 2.47/0.97  --time_out_virtual                      -1.
% 2.47/0.97  --symbol_type_check                     false
% 2.47/0.97  --clausify_out                          false
% 2.47/0.97  --sig_cnt_out                           false
% 2.47/0.97  --trig_cnt_out                          false
% 2.47/0.97  --trig_cnt_out_tolerance                1.
% 2.47/0.97  --trig_cnt_out_sk_spl                   false
% 2.47/0.97  --abstr_cl_out                          false
% 2.47/0.97  
% 2.47/0.97  ------ Global Options
% 2.47/0.97  
% 2.47/0.97  --schedule                              default
% 2.47/0.97  --add_important_lit                     false
% 2.47/0.97  --prop_solver_per_cl                    1000
% 2.47/0.97  --min_unsat_core                        false
% 2.47/0.97  --soft_assumptions                      false
% 2.47/0.97  --soft_lemma_size                       3
% 2.47/0.97  --prop_impl_unit_size                   0
% 2.47/0.97  --prop_impl_unit                        []
% 2.47/0.97  --share_sel_clauses                     true
% 2.47/0.97  --reset_solvers                         false
% 2.47/0.97  --bc_imp_inh                            [conj_cone]
% 2.47/0.97  --conj_cone_tolerance                   3.
% 2.47/0.97  --extra_neg_conj                        none
% 2.47/0.97  --large_theory_mode                     true
% 2.47/0.97  --prolific_symb_bound                   200
% 2.47/0.97  --lt_threshold                          2000
% 2.47/0.97  --clause_weak_htbl                      true
% 2.47/0.97  --gc_record_bc_elim                     false
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing Options
% 2.47/0.97  
% 2.47/0.97  --preprocessing_flag                    true
% 2.47/0.97  --time_out_prep_mult                    0.1
% 2.47/0.97  --splitting_mode                        input
% 2.47/0.97  --splitting_grd                         true
% 2.47/0.97  --splitting_cvd                         false
% 2.47/0.97  --splitting_cvd_svl                     false
% 2.47/0.97  --splitting_nvd                         32
% 2.47/0.97  --sub_typing                            true
% 2.47/0.97  --prep_gs_sim                           true
% 2.47/0.97  --prep_unflatten                        true
% 2.47/0.97  --prep_res_sim                          true
% 2.47/0.97  --prep_upred                            true
% 2.47/0.97  --prep_sem_filter                       exhaustive
% 2.47/0.97  --prep_sem_filter_out                   false
% 2.47/0.97  --pred_elim                             true
% 2.47/0.97  --res_sim_input                         true
% 2.47/0.97  --eq_ax_congr_red                       true
% 2.47/0.97  --pure_diseq_elim                       true
% 2.47/0.97  --brand_transform                       false
% 2.47/0.97  --non_eq_to_eq                          false
% 2.47/0.97  --prep_def_merge                        true
% 2.47/0.97  --prep_def_merge_prop_impl              false
% 2.47/0.97  --prep_def_merge_mbd                    true
% 2.47/0.97  --prep_def_merge_tr_red                 false
% 2.47/0.97  --prep_def_merge_tr_cl                  false
% 2.47/0.97  --smt_preprocessing                     true
% 2.47/0.97  --smt_ac_axioms                         fast
% 2.47/0.97  --preprocessed_out                      false
% 2.47/0.97  --preprocessed_stats                    false
% 2.47/0.97  
% 2.47/0.97  ------ Abstraction refinement Options
% 2.47/0.97  
% 2.47/0.97  --abstr_ref                             []
% 2.47/0.97  --abstr_ref_prep                        false
% 2.47/0.97  --abstr_ref_until_sat                   false
% 2.47/0.97  --abstr_ref_sig_restrict                funpre
% 2.47/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.97  --abstr_ref_under                       []
% 2.47/0.97  
% 2.47/0.97  ------ SAT Options
% 2.47/0.97  
% 2.47/0.97  --sat_mode                              false
% 2.47/0.97  --sat_fm_restart_options                ""
% 2.47/0.97  --sat_gr_def                            false
% 2.47/0.97  --sat_epr_types                         true
% 2.47/0.97  --sat_non_cyclic_types                  false
% 2.47/0.97  --sat_finite_models                     false
% 2.47/0.97  --sat_fm_lemmas                         false
% 2.47/0.97  --sat_fm_prep                           false
% 2.47/0.97  --sat_fm_uc_incr                        true
% 2.47/0.97  --sat_out_model                         small
% 2.47/0.97  --sat_out_clauses                       false
% 2.47/0.97  
% 2.47/0.97  ------ QBF Options
% 2.47/0.97  
% 2.47/0.97  --qbf_mode                              false
% 2.47/0.97  --qbf_elim_univ                         false
% 2.47/0.97  --qbf_dom_inst                          none
% 2.47/0.97  --qbf_dom_pre_inst                      false
% 2.47/0.97  --qbf_sk_in                             false
% 2.47/0.97  --qbf_pred_elim                         true
% 2.47/0.97  --qbf_split                             512
% 2.47/0.97  
% 2.47/0.97  ------ BMC1 Options
% 2.47/0.97  
% 2.47/0.97  --bmc1_incremental                      false
% 2.47/0.97  --bmc1_axioms                           reachable_all
% 2.47/0.97  --bmc1_min_bound                        0
% 2.47/0.97  --bmc1_max_bound                        -1
% 2.47/0.97  --bmc1_max_bound_default                -1
% 2.47/0.97  --bmc1_symbol_reachability              true
% 2.47/0.97  --bmc1_property_lemmas                  false
% 2.47/0.97  --bmc1_k_induction                      false
% 2.47/0.97  --bmc1_non_equiv_states                 false
% 2.47/0.97  --bmc1_deadlock                         false
% 2.47/0.97  --bmc1_ucm                              false
% 2.47/0.97  --bmc1_add_unsat_core                   none
% 2.47/0.97  --bmc1_unsat_core_children              false
% 2.47/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.97  --bmc1_out_stat                         full
% 2.47/0.97  --bmc1_ground_init                      false
% 2.47/0.97  --bmc1_pre_inst_next_state              false
% 2.47/0.97  --bmc1_pre_inst_state                   false
% 2.47/0.97  --bmc1_pre_inst_reach_state             false
% 2.47/0.97  --bmc1_out_unsat_core                   false
% 2.47/0.97  --bmc1_aig_witness_out                  false
% 2.47/0.97  --bmc1_verbose                          false
% 2.47/0.97  --bmc1_dump_clauses_tptp                false
% 2.47/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.97  --bmc1_dump_file                        -
% 2.47/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.97  --bmc1_ucm_extend_mode                  1
% 2.47/0.97  --bmc1_ucm_init_mode                    2
% 2.47/0.97  --bmc1_ucm_cone_mode                    none
% 2.47/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.97  --bmc1_ucm_relax_model                  4
% 2.47/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.97  --bmc1_ucm_layered_model                none
% 2.47/0.97  --bmc1_ucm_max_lemma_size               10
% 2.47/0.97  
% 2.47/0.97  ------ AIG Options
% 2.47/0.97  
% 2.47/0.97  --aig_mode                              false
% 2.47/0.97  
% 2.47/0.97  ------ Instantiation Options
% 2.47/0.97  
% 2.47/0.97  --instantiation_flag                    true
% 2.47/0.97  --inst_sos_flag                         false
% 2.47/0.97  --inst_sos_phase                        true
% 2.47/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.97  --inst_lit_sel_side                     num_symb
% 2.47/0.97  --inst_solver_per_active                1400
% 2.47/0.97  --inst_solver_calls_frac                1.
% 2.47/0.97  --inst_passive_queue_type               priority_queues
% 2.47/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.97  --inst_passive_queues_freq              [25;2]
% 2.47/0.97  --inst_dismatching                      true
% 2.47/0.97  --inst_eager_unprocessed_to_passive     true
% 2.47/0.97  --inst_prop_sim_given                   true
% 2.47/0.97  --inst_prop_sim_new                     false
% 2.47/0.97  --inst_subs_new                         false
% 2.47/0.97  --inst_eq_res_simp                      false
% 2.47/0.97  --inst_subs_given                       false
% 2.47/0.97  --inst_orphan_elimination               true
% 2.47/0.97  --inst_learning_loop_flag               true
% 2.47/0.97  --inst_learning_start                   3000
% 2.47/0.97  --inst_learning_factor                  2
% 2.47/0.97  --inst_start_prop_sim_after_learn       3
% 2.47/0.97  --inst_sel_renew                        solver
% 2.47/0.97  --inst_lit_activity_flag                true
% 2.47/0.97  --inst_restr_to_given                   false
% 2.47/0.97  --inst_activity_threshold               500
% 2.47/0.97  --inst_out_proof                        true
% 2.47/0.97  
% 2.47/0.97  ------ Resolution Options
% 2.47/0.97  
% 2.47/0.97  --resolution_flag                       true
% 2.47/0.97  --res_lit_sel                           adaptive
% 2.47/0.97  --res_lit_sel_side                      none
% 2.47/0.97  --res_ordering                          kbo
% 2.47/0.97  --res_to_prop_solver                    active
% 2.47/0.97  --res_prop_simpl_new                    false
% 2.47/0.97  --res_prop_simpl_given                  true
% 2.47/0.97  --res_passive_queue_type                priority_queues
% 2.47/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.97  --res_passive_queues_freq               [15;5]
% 2.47/0.97  --res_forward_subs                      full
% 2.47/0.97  --res_backward_subs                     full
% 2.47/0.97  --res_forward_subs_resolution           true
% 2.47/0.97  --res_backward_subs_resolution          true
% 2.47/0.97  --res_orphan_elimination                true
% 2.47/0.97  --res_time_limit                        2.
% 2.47/0.97  --res_out_proof                         true
% 2.47/0.97  
% 2.47/0.97  ------ Superposition Options
% 2.47/0.97  
% 2.47/0.97  --superposition_flag                    true
% 2.47/0.97  --sup_passive_queue_type                priority_queues
% 2.47/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.97  --demod_completeness_check              fast
% 2.47/0.97  --demod_use_ground                      true
% 2.47/0.97  --sup_to_prop_solver                    passive
% 2.47/0.97  --sup_prop_simpl_new                    true
% 2.47/0.97  --sup_prop_simpl_given                  true
% 2.47/0.97  --sup_fun_splitting                     false
% 2.47/0.97  --sup_smt_interval                      50000
% 2.47/0.97  
% 2.47/0.97  ------ Superposition Simplification Setup
% 2.47/0.97  
% 2.47/0.97  --sup_indices_passive                   []
% 2.47/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_full_bw                           [BwDemod]
% 2.47/0.97  --sup_immed_triv                        [TrivRules]
% 2.47/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_immed_bw_main                     []
% 2.47/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.97  
% 2.47/0.97  ------ Combination Options
% 2.47/0.97  
% 2.47/0.97  --comb_res_mult                         3
% 2.47/0.97  --comb_sup_mult                         2
% 2.47/0.97  --comb_inst_mult                        10
% 2.47/0.97  
% 2.47/0.97  ------ Debug Options
% 2.47/0.97  
% 2.47/0.97  --dbg_backtrace                         false
% 2.47/0.97  --dbg_dump_prop_clauses                 false
% 2.47/0.97  --dbg_dump_prop_clauses_file            -
% 2.47/0.97  --dbg_out_stat                          false
% 2.47/0.97  ------ Parsing...
% 2.47/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/0.97  ------ Proving...
% 2.47/0.97  ------ Problem Properties 
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  clauses                                 33
% 2.47/0.97  conjectures                             2
% 2.47/0.97  EPR                                     4
% 2.47/0.97  Horn                                    24
% 2.47/0.97  unary                                   10
% 2.47/0.97  binary                                  7
% 2.47/0.97  lits                                    76
% 2.47/0.97  lits eq                                 20
% 2.47/0.97  fd_pure                                 0
% 2.47/0.97  fd_pseudo                               0
% 2.47/0.97  fd_cond                                 0
% 2.47/0.97  fd_pseudo_cond                          8
% 2.47/0.97  AC symbols                              0
% 2.47/0.97  
% 2.47/0.97  ------ Schedule dynamic 5 is on 
% 2.47/0.97  
% 2.47/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  ------ 
% 2.47/0.97  Current options:
% 2.47/0.97  ------ 
% 2.47/0.97  
% 2.47/0.97  ------ Input Options
% 2.47/0.97  
% 2.47/0.97  --out_options                           all
% 2.47/0.97  --tptp_safe_out                         true
% 2.47/0.97  --problem_path                          ""
% 2.47/0.97  --include_path                          ""
% 2.47/0.97  --clausifier                            res/vclausify_rel
% 2.47/0.97  --clausifier_options                    --mode clausify
% 2.47/0.97  --stdin                                 false
% 2.47/0.97  --stats_out                             all
% 2.47/0.97  
% 2.47/0.97  ------ General Options
% 2.47/0.97  
% 2.47/0.97  --fof                                   false
% 2.47/0.97  --time_out_real                         305.
% 2.47/0.97  --time_out_virtual                      -1.
% 2.47/0.97  --symbol_type_check                     false
% 2.47/0.97  --clausify_out                          false
% 2.47/0.97  --sig_cnt_out                           false
% 2.47/0.97  --trig_cnt_out                          false
% 2.47/0.97  --trig_cnt_out_tolerance                1.
% 2.47/0.97  --trig_cnt_out_sk_spl                   false
% 2.47/0.97  --abstr_cl_out                          false
% 2.47/0.97  
% 2.47/0.97  ------ Global Options
% 2.47/0.97  
% 2.47/0.97  --schedule                              default
% 2.47/0.97  --add_important_lit                     false
% 2.47/0.97  --prop_solver_per_cl                    1000
% 2.47/0.97  --min_unsat_core                        false
% 2.47/0.97  --soft_assumptions                      false
% 2.47/0.97  --soft_lemma_size                       3
% 2.47/0.97  --prop_impl_unit_size                   0
% 2.47/0.97  --prop_impl_unit                        []
% 2.47/0.97  --share_sel_clauses                     true
% 2.47/0.97  --reset_solvers                         false
% 2.47/0.97  --bc_imp_inh                            [conj_cone]
% 2.47/0.97  --conj_cone_tolerance                   3.
% 2.47/0.97  --extra_neg_conj                        none
% 2.47/0.97  --large_theory_mode                     true
% 2.47/0.97  --prolific_symb_bound                   200
% 2.47/0.97  --lt_threshold                          2000
% 2.47/0.97  --clause_weak_htbl                      true
% 2.47/0.97  --gc_record_bc_elim                     false
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing Options
% 2.47/0.97  
% 2.47/0.97  --preprocessing_flag                    true
% 2.47/0.97  --time_out_prep_mult                    0.1
% 2.47/0.97  --splitting_mode                        input
% 2.47/0.97  --splitting_grd                         true
% 2.47/0.97  --splitting_cvd                         false
% 2.47/0.97  --splitting_cvd_svl                     false
% 2.47/0.97  --splitting_nvd                         32
% 2.47/0.97  --sub_typing                            true
% 2.47/0.97  --prep_gs_sim                           true
% 2.47/0.97  --prep_unflatten                        true
% 2.47/0.97  --prep_res_sim                          true
% 2.47/0.97  --prep_upred                            true
% 2.47/0.97  --prep_sem_filter                       exhaustive
% 2.47/0.97  --prep_sem_filter_out                   false
% 2.47/0.97  --pred_elim                             true
% 2.47/0.97  --res_sim_input                         true
% 2.47/0.97  --eq_ax_congr_red                       true
% 2.47/0.97  --pure_diseq_elim                       true
% 2.47/0.97  --brand_transform                       false
% 2.47/0.97  --non_eq_to_eq                          false
% 2.47/0.97  --prep_def_merge                        true
% 2.47/0.97  --prep_def_merge_prop_impl              false
% 2.47/0.97  --prep_def_merge_mbd                    true
% 2.47/0.97  --prep_def_merge_tr_red                 false
% 2.47/0.97  --prep_def_merge_tr_cl                  false
% 2.47/0.97  --smt_preprocessing                     true
% 2.47/0.97  --smt_ac_axioms                         fast
% 2.47/0.97  --preprocessed_out                      false
% 2.47/0.97  --preprocessed_stats                    false
% 2.47/0.97  
% 2.47/0.97  ------ Abstraction refinement Options
% 2.47/0.97  
% 2.47/0.97  --abstr_ref                             []
% 2.47/0.97  --abstr_ref_prep                        false
% 2.47/0.97  --abstr_ref_until_sat                   false
% 2.47/0.97  --abstr_ref_sig_restrict                funpre
% 2.47/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.97  --abstr_ref_under                       []
% 2.47/0.97  
% 2.47/0.97  ------ SAT Options
% 2.47/0.97  
% 2.47/0.97  --sat_mode                              false
% 2.47/0.97  --sat_fm_restart_options                ""
% 2.47/0.97  --sat_gr_def                            false
% 2.47/0.97  --sat_epr_types                         true
% 2.47/0.97  --sat_non_cyclic_types                  false
% 2.47/0.97  --sat_finite_models                     false
% 2.47/0.97  --sat_fm_lemmas                         false
% 2.47/0.97  --sat_fm_prep                           false
% 2.47/0.97  --sat_fm_uc_incr                        true
% 2.47/0.97  --sat_out_model                         small
% 2.47/0.97  --sat_out_clauses                       false
% 2.47/0.97  
% 2.47/0.97  ------ QBF Options
% 2.47/0.97  
% 2.47/0.97  --qbf_mode                              false
% 2.47/0.97  --qbf_elim_univ                         false
% 2.47/0.97  --qbf_dom_inst                          none
% 2.47/0.97  --qbf_dom_pre_inst                      false
% 2.47/0.97  --qbf_sk_in                             false
% 2.47/0.97  --qbf_pred_elim                         true
% 2.47/0.97  --qbf_split                             512
% 2.47/0.97  
% 2.47/0.97  ------ BMC1 Options
% 2.47/0.97  
% 2.47/0.97  --bmc1_incremental                      false
% 2.47/0.97  --bmc1_axioms                           reachable_all
% 2.47/0.97  --bmc1_min_bound                        0
% 2.47/0.97  --bmc1_max_bound                        -1
% 2.47/0.97  --bmc1_max_bound_default                -1
% 2.47/0.97  --bmc1_symbol_reachability              true
% 2.47/0.97  --bmc1_property_lemmas                  false
% 2.47/0.97  --bmc1_k_induction                      false
% 2.47/0.97  --bmc1_non_equiv_states                 false
% 2.47/0.97  --bmc1_deadlock                         false
% 2.47/0.97  --bmc1_ucm                              false
% 2.47/0.97  --bmc1_add_unsat_core                   none
% 2.47/0.97  --bmc1_unsat_core_children              false
% 2.47/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.97  --bmc1_out_stat                         full
% 2.47/0.97  --bmc1_ground_init                      false
% 2.47/0.97  --bmc1_pre_inst_next_state              false
% 2.47/0.97  --bmc1_pre_inst_state                   false
% 2.47/0.97  --bmc1_pre_inst_reach_state             false
% 2.47/0.97  --bmc1_out_unsat_core                   false
% 2.47/0.97  --bmc1_aig_witness_out                  false
% 2.47/0.97  --bmc1_verbose                          false
% 2.47/0.97  --bmc1_dump_clauses_tptp                false
% 2.47/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.97  --bmc1_dump_file                        -
% 2.47/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.97  --bmc1_ucm_extend_mode                  1
% 2.47/0.97  --bmc1_ucm_init_mode                    2
% 2.47/0.97  --bmc1_ucm_cone_mode                    none
% 2.47/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.97  --bmc1_ucm_relax_model                  4
% 2.47/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.97  --bmc1_ucm_layered_model                none
% 2.47/0.97  --bmc1_ucm_max_lemma_size               10
% 2.47/0.97  
% 2.47/0.97  ------ AIG Options
% 2.47/0.97  
% 2.47/0.97  --aig_mode                              false
% 2.47/0.97  
% 2.47/0.97  ------ Instantiation Options
% 2.47/0.97  
% 2.47/0.97  --instantiation_flag                    true
% 2.47/0.97  --inst_sos_flag                         false
% 2.47/0.97  --inst_sos_phase                        true
% 2.47/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.97  --inst_lit_sel_side                     none
% 2.47/0.97  --inst_solver_per_active                1400
% 2.47/0.97  --inst_solver_calls_frac                1.
% 2.47/0.97  --inst_passive_queue_type               priority_queues
% 2.47/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.97  --inst_passive_queues_freq              [25;2]
% 2.47/0.97  --inst_dismatching                      true
% 2.47/0.97  --inst_eager_unprocessed_to_passive     true
% 2.47/0.97  --inst_prop_sim_given                   true
% 2.47/0.97  --inst_prop_sim_new                     false
% 2.47/0.97  --inst_subs_new                         false
% 2.47/0.97  --inst_eq_res_simp                      false
% 2.47/0.97  --inst_subs_given                       false
% 2.47/0.97  --inst_orphan_elimination               true
% 2.47/0.97  --inst_learning_loop_flag               true
% 2.47/0.97  --inst_learning_start                   3000
% 2.47/0.97  --inst_learning_factor                  2
% 2.47/0.97  --inst_start_prop_sim_after_learn       3
% 2.47/0.97  --inst_sel_renew                        solver
% 2.47/0.97  --inst_lit_activity_flag                true
% 2.47/0.97  --inst_restr_to_given                   false
% 2.47/0.97  --inst_activity_threshold               500
% 2.47/0.97  --inst_out_proof                        true
% 2.47/0.97  
% 2.47/0.97  ------ Resolution Options
% 2.47/0.97  
% 2.47/0.97  --resolution_flag                       false
% 2.47/0.97  --res_lit_sel                           adaptive
% 2.47/0.97  --res_lit_sel_side                      none
% 2.47/0.97  --res_ordering                          kbo
% 2.47/0.97  --res_to_prop_solver                    active
% 2.47/0.97  --res_prop_simpl_new                    false
% 2.47/0.97  --res_prop_simpl_given                  true
% 2.47/0.97  --res_passive_queue_type                priority_queues
% 2.47/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.97  --res_passive_queues_freq               [15;5]
% 2.47/0.97  --res_forward_subs                      full
% 2.47/0.97  --res_backward_subs                     full
% 2.47/0.97  --res_forward_subs_resolution           true
% 2.47/0.97  --res_backward_subs_resolution          true
% 2.47/0.97  --res_orphan_elimination                true
% 2.47/0.97  --res_time_limit                        2.
% 2.47/0.97  --res_out_proof                         true
% 2.47/0.97  
% 2.47/0.97  ------ Superposition Options
% 2.47/0.97  
% 2.47/0.97  --superposition_flag                    true
% 2.47/0.97  --sup_passive_queue_type                priority_queues
% 2.47/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.97  --demod_completeness_check              fast
% 2.47/0.97  --demod_use_ground                      true
% 2.47/0.97  --sup_to_prop_solver                    passive
% 2.47/0.97  --sup_prop_simpl_new                    true
% 2.47/0.97  --sup_prop_simpl_given                  true
% 2.47/0.97  --sup_fun_splitting                     false
% 2.47/0.97  --sup_smt_interval                      50000
% 2.47/0.97  
% 2.47/0.97  ------ Superposition Simplification Setup
% 2.47/0.97  
% 2.47/0.97  --sup_indices_passive                   []
% 2.47/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_full_bw                           [BwDemod]
% 2.47/0.97  --sup_immed_triv                        [TrivRules]
% 2.47/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_immed_bw_main                     []
% 2.47/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.97  
% 2.47/0.97  ------ Combination Options
% 2.47/0.97  
% 2.47/0.97  --comb_res_mult                         3
% 2.47/0.97  --comb_sup_mult                         2
% 2.47/0.97  --comb_inst_mult                        10
% 2.47/0.97  
% 2.47/0.97  ------ Debug Options
% 2.47/0.97  
% 2.47/0.97  --dbg_backtrace                         false
% 2.47/0.97  --dbg_dump_prop_clauses                 false
% 2.47/0.97  --dbg_dump_prop_clauses_file            -
% 2.47/0.97  --dbg_out_stat                          false
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  ------ Proving...
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  % SZS status Theorem for theBenchmark.p
% 2.47/0.97  
% 2.47/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.47/0.97  
% 2.47/0.97  fof(f12,axiom,(
% 2.47/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f24,plain,(
% 2.47/0.97    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.47/0.97    inference(ennf_transformation,[],[f12])).
% 2.47/0.97  
% 2.47/0.97  fof(f36,plain,(
% 2.47/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.47/0.97    inference(nnf_transformation,[],[f24])).
% 2.47/0.97  
% 2.47/0.97  fof(f37,plain,(
% 2.47/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.47/0.97    inference(flattening,[],[f36])).
% 2.47/0.97  
% 2.47/0.97  fof(f38,plain,(
% 2.47/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.47/0.97    inference(rectify,[],[f37])).
% 2.47/0.97  
% 2.47/0.97  fof(f39,plain,(
% 2.47/0.97    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 2.47/0.97    introduced(choice_axiom,[])).
% 2.47/0.97  
% 2.47/0.97  fof(f40,plain,(
% 2.47/0.97    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.47/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 2.47/0.97  
% 2.47/0.97  fof(f70,plain,(
% 2.47/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.47/0.97    inference(cnf_transformation,[],[f40])).
% 2.47/0.97  
% 2.47/0.97  fof(f14,axiom,(
% 2.47/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f77,plain,(
% 2.47/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f14])).
% 2.47/0.97  
% 2.47/0.97  fof(f15,axiom,(
% 2.47/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f78,plain,(
% 2.47/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f15])).
% 2.47/0.97  
% 2.47/0.97  fof(f82,plain,(
% 2.47/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.47/0.97    inference(definition_unfolding,[],[f77,f78])).
% 2.47/0.97  
% 2.47/0.97  fof(f102,plain,(
% 2.47/0.97    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.47/0.97    inference(definition_unfolding,[],[f70,f82])).
% 2.47/0.97  
% 2.47/0.97  fof(f113,plain,(
% 2.47/0.97    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X5,X2) != X3) )),
% 2.47/0.97    inference(equality_resolution,[],[f102])).
% 2.47/0.97  
% 2.47/0.97  fof(f114,plain,(
% 2.47/0.97    ( ! [X2,X0,X5] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2))) )),
% 2.47/0.97    inference(equality_resolution,[],[f113])).
% 2.47/0.97  
% 2.47/0.97  fof(f11,axiom,(
% 2.47/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f67,plain,(
% 2.47/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f11])).
% 2.47/0.97  
% 2.47/0.97  fof(f13,axiom,(
% 2.47/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f76,plain,(
% 2.47/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f13])).
% 2.47/0.97  
% 2.47/0.97  fof(f83,plain,(
% 2.47/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.47/0.97    inference(definition_unfolding,[],[f76,f82])).
% 2.47/0.97  
% 2.47/0.97  fof(f96,plain,(
% 2.47/0.97    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 2.47/0.97    inference(definition_unfolding,[],[f67,f83,f83])).
% 2.47/0.97  
% 2.47/0.97  fof(f17,conjecture,(
% 2.47/0.97    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f18,negated_conjecture,(
% 2.47/0.97    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.47/0.97    inference(negated_conjecture,[],[f17])).
% 2.47/0.97  
% 2.47/0.97  fof(f25,plain,(
% 2.47/0.97    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 2.47/0.97    inference(ennf_transformation,[],[f18])).
% 2.47/0.97  
% 2.47/0.97  fof(f41,plain,(
% 2.47/0.97    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK3,sK5) & r1_tarski(k2_xboole_0(k2_tarski(sK3,sK4),sK5),sK5))),
% 2.47/0.97    introduced(choice_axiom,[])).
% 2.47/0.97  
% 2.47/0.97  fof(f42,plain,(
% 2.47/0.97    ~r2_hidden(sK3,sK5) & r1_tarski(k2_xboole_0(k2_tarski(sK3,sK4),sK5),sK5)),
% 2.47/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f41])).
% 2.47/0.97  
% 2.47/0.97  fof(f80,plain,(
% 2.47/0.97    r1_tarski(k2_xboole_0(k2_tarski(sK3,sK4),sK5),sK5)),
% 2.47/0.97    inference(cnf_transformation,[],[f42])).
% 2.47/0.97  
% 2.47/0.97  fof(f16,axiom,(
% 2.47/0.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f79,plain,(
% 2.47/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.47/0.97    inference(cnf_transformation,[],[f16])).
% 2.47/0.97  
% 2.47/0.97  fof(f84,plain,(
% 2.47/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.47/0.97    inference(definition_unfolding,[],[f79,f83])).
% 2.47/0.97  
% 2.47/0.97  fof(f105,plain,(
% 2.47/0.97    r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),sK5)),sK5)),
% 2.47/0.97    inference(definition_unfolding,[],[f80,f84,f83])).
% 2.47/0.97  
% 2.47/0.97  fof(f5,axiom,(
% 2.47/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f34,plain,(
% 2.47/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.47/0.97    inference(nnf_transformation,[],[f5])).
% 2.47/0.97  
% 2.47/0.97  fof(f35,plain,(
% 2.47/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.47/0.97    inference(flattening,[],[f34])).
% 2.47/0.97  
% 2.47/0.97  fof(f59,plain,(
% 2.47/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f35])).
% 2.47/0.97  
% 2.47/0.97  fof(f10,axiom,(
% 2.47/0.97    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f66,plain,(
% 2.47/0.97    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.47/0.97    inference(cnf_transformation,[],[f10])).
% 2.47/0.97  
% 2.47/0.97  fof(f95,plain,(
% 2.47/0.97    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.47/0.97    inference(definition_unfolding,[],[f66,f84])).
% 2.47/0.97  
% 2.47/0.97  fof(f2,axiom,(
% 2.47/0.97    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.47/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f26,plain,(
% 2.47/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.47/0.97    inference(nnf_transformation,[],[f2])).
% 2.47/0.97  
% 2.47/0.97  fof(f27,plain,(
% 2.47/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.47/0.97    inference(flattening,[],[f26])).
% 2.47/0.97  
% 2.47/0.97  fof(f28,plain,(
% 2.47/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.47/0.97    inference(rectify,[],[f27])).
% 2.47/0.97  
% 2.47/0.97  fof(f29,plain,(
% 2.47/0.97    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.47/0.97    introduced(choice_axiom,[])).
% 2.47/0.97  
% 2.47/0.97  fof(f30,plain,(
% 2.47/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.47/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 2.47/0.97  
% 2.47/0.97  fof(f46,plain,(
% 2.47/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.47/0.97    inference(cnf_transformation,[],[f30])).
% 2.47/0.97  
% 2.47/0.97  fof(f88,plain,(
% 2.47/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 2.47/0.97    inference(definition_unfolding,[],[f46,f84])).
% 2.47/0.97  
% 2.47/0.97  fof(f106,plain,(
% 2.47/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.47/0.97    inference(equality_resolution,[],[f88])).
% 2.47/0.97  
% 2.47/0.97  fof(f81,plain,(
% 2.47/0.97    ~r2_hidden(sK3,sK5)),
% 2.47/0.97    inference(cnf_transformation,[],[f42])).
% 2.47/0.97  
% 2.47/0.97  cnf(c_29,plain,
% 2.47/0.97      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) ),
% 2.47/0.97      inference(cnf_transformation,[],[f114]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1051,plain,
% 2.47/0.97      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) = iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_23,plain,
% 2.47/0.97      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 2.47/0.97      inference(cnf_transformation,[],[f96]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_33,negated_conjecture,
% 2.47/0.97      ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),sK5)),sK5) ),
% 2.47/0.97      inference(cnf_transformation,[],[f105]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1047,plain,
% 2.47/0.97      ( r1_tarski(k3_tarski(k3_enumset1(k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),k3_enumset1(sK3,sK3,sK3,sK3,sK4),sK5)),sK5) = iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1560,plain,
% 2.47/0.97      ( r1_tarski(k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK4))),sK5) = iProver_top ),
% 2.47/0.97      inference(demodulation,[status(thm)],[c_23,c_1047]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_14,plain,
% 2.47/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.47/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1064,plain,
% 2.47/0.97      ( X0 = X1
% 2.47/0.97      | r1_tarski(X0,X1) != iProver_top
% 2.47/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_2293,plain,
% 2.47/0.97      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK4))) = sK5
% 2.47/0.97      | r1_tarski(sK5,k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK4)))) != iProver_top ),
% 2.47/0.97      inference(superposition,[status(thm)],[c_1560,c_1064]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_22,plain,
% 2.47/0.97      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
% 2.47/0.97      inference(cnf_transformation,[],[f95]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1057,plain,
% 2.47/0.97      ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_2540,plain,
% 2.47/0.97      ( k3_tarski(k3_enumset1(sK5,sK5,sK5,sK5,k3_enumset1(sK3,sK3,sK3,sK3,sK4))) = sK5 ),
% 2.47/0.97      inference(forward_subsumption_resolution,
% 2.47/0.97                [status(thm)],
% 2.47/0.97                [c_2293,c_1057]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_4,plain,
% 2.47/0.97      ( ~ r2_hidden(X0,X1)
% 2.47/0.97      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 2.47/0.97      inference(cnf_transformation,[],[f106]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1074,plain,
% 2.47/0.97      ( r2_hidden(X0,X1) != iProver_top
% 2.47/0.97      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_3603,plain,
% 2.47/0.97      ( r2_hidden(X0,k3_enumset1(sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 2.47/0.97      | r2_hidden(X0,sK5) = iProver_top ),
% 2.47/0.97      inference(superposition,[status(thm)],[c_2540,c_1074]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_4234,plain,
% 2.47/0.97      ( r2_hidden(sK3,sK5) = iProver_top ),
% 2.47/0.97      inference(superposition,[status(thm)],[c_1051,c_3603]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_32,negated_conjecture,
% 2.47/0.97      ( ~ r2_hidden(sK3,sK5) ),
% 2.47/0.97      inference(cnf_transformation,[],[f81]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_35,plain,
% 2.47/0.97      ( r2_hidden(sK3,sK5) != iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(contradiction,plain,
% 2.47/0.97      ( $false ),
% 2.47/0.97      inference(minisat,[status(thm)],[c_4234,c_35]) ).
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.47/0.97  
% 2.47/0.97  ------                               Statistics
% 2.47/0.97  
% 2.47/0.97  ------ General
% 2.47/0.97  
% 2.47/0.97  abstr_ref_over_cycles:                  0
% 2.47/0.97  abstr_ref_under_cycles:                 0
% 2.47/0.97  gc_basic_clause_elim:                   0
% 2.47/0.97  forced_gc_time:                         0
% 2.47/0.97  parsing_time:                           0.01
% 2.47/0.97  unif_index_cands_time:                  0.
% 2.47/0.97  unif_index_add_time:                    0.
% 2.47/0.97  orderings_time:                         0.
% 2.47/0.97  out_proof_time:                         0.007
% 2.47/0.97  total_time:                             0.146
% 2.47/0.97  num_of_symbols:                         44
% 2.47/0.97  num_of_terms:                           5223
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing
% 2.47/0.97  
% 2.47/0.97  num_of_splits:                          0
% 2.47/0.97  num_of_split_atoms:                     0
% 2.47/0.97  num_of_reused_defs:                     0
% 2.47/0.97  num_eq_ax_congr_red:                    36
% 2.47/0.97  num_of_sem_filtered_clauses:            1
% 2.47/0.97  num_of_subtypes:                        0
% 2.47/0.97  monotx_restored_types:                  0
% 2.47/0.97  sat_num_of_epr_types:                   0
% 2.47/0.97  sat_num_of_non_cyclic_types:            0
% 2.47/0.97  sat_guarded_non_collapsed_types:        0
% 2.47/0.97  num_pure_diseq_elim:                    0
% 2.47/0.97  simp_replaced_by:                       0
% 2.47/0.97  res_preprocessed:                       149
% 2.47/0.97  prep_upred:                             0
% 2.47/0.97  prep_unflattend:                        0
% 2.47/0.97  smt_new_axioms:                         0
% 2.47/0.97  pred_elim_cands:                        3
% 2.47/0.97  pred_elim:                              0
% 2.47/0.97  pred_elim_cl:                           0
% 2.47/0.97  pred_elim_cycles:                       2
% 2.47/0.97  merged_defs:                            0
% 2.47/0.97  merged_defs_ncl:                        0
% 2.47/0.97  bin_hyper_res:                          0
% 2.47/0.97  prep_cycles:                            4
% 2.47/0.97  pred_elim_time:                         0.001
% 2.47/0.97  splitting_time:                         0.
% 2.47/0.97  sem_filter_time:                        0.
% 2.47/0.97  monotx_time:                            0.
% 2.47/0.97  subtype_inf_time:                       0.
% 2.47/0.97  
% 2.47/0.97  ------ Problem properties
% 2.47/0.97  
% 2.47/0.97  clauses:                                33
% 2.47/0.97  conjectures:                            2
% 2.47/0.97  epr:                                    4
% 2.47/0.97  horn:                                   24
% 2.47/0.97  ground:                                 2
% 2.47/0.97  unary:                                  10
% 2.47/0.97  binary:                                 7
% 2.47/0.97  lits:                                   76
% 2.47/0.97  lits_eq:                                20
% 2.47/0.97  fd_pure:                                0
% 2.47/0.97  fd_pseudo:                              0
% 2.47/0.97  fd_cond:                                0
% 2.47/0.97  fd_pseudo_cond:                         8
% 2.47/0.97  ac_symbols:                             0
% 2.47/0.97  
% 2.47/0.97  ------ Propositional Solver
% 2.47/0.97  
% 2.47/0.97  prop_solver_calls:                      26
% 2.47/0.97  prop_fast_solver_calls:                 779
% 2.47/0.97  smt_solver_calls:                       0
% 2.47/0.97  smt_fast_solver_calls:                  0
% 2.47/0.97  prop_num_of_clauses:                    1271
% 2.47/0.97  prop_preprocess_simplified:             7457
% 2.47/0.97  prop_fo_subsumed:                       0
% 2.47/0.97  prop_solver_time:                       0.
% 2.47/0.97  smt_solver_time:                        0.
% 2.47/0.97  smt_fast_solver_time:                   0.
% 2.47/0.97  prop_fast_solver_time:                  0.
% 2.47/0.97  prop_unsat_core_time:                   0.
% 2.47/0.97  
% 2.47/0.97  ------ QBF
% 2.47/0.97  
% 2.47/0.97  qbf_q_res:                              0
% 2.47/0.97  qbf_num_tautologies:                    0
% 2.47/0.97  qbf_prep_cycles:                        0
% 2.47/0.97  
% 2.47/0.97  ------ BMC1
% 2.47/0.97  
% 2.47/0.97  bmc1_current_bound:                     -1
% 2.47/0.97  bmc1_last_solved_bound:                 -1
% 2.47/0.97  bmc1_unsat_core_size:                   -1
% 2.47/0.97  bmc1_unsat_core_parents_size:           -1
% 2.47/0.97  bmc1_merge_next_fun:                    0
% 2.47/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.47/0.97  
% 2.47/0.97  ------ Instantiation
% 2.47/0.97  
% 2.47/0.97  inst_num_of_clauses:                    421
% 2.47/0.97  inst_num_in_passive:                    292
% 2.47/0.97  inst_num_in_active:                     121
% 2.47/0.97  inst_num_in_unprocessed:                13
% 2.47/0.97  inst_num_of_loops:                      200
% 2.47/0.97  inst_num_of_learning_restarts:          0
% 2.47/0.97  inst_num_moves_active_passive:          75
% 2.47/0.97  inst_lit_activity:                      0
% 2.47/0.97  inst_lit_activity_moves:                0
% 2.47/0.97  inst_num_tautologies:                   0
% 2.47/0.97  inst_num_prop_implied:                  0
% 2.47/0.97  inst_num_existing_simplified:           0
% 2.47/0.97  inst_num_eq_res_simplified:             0
% 2.47/0.97  inst_num_child_elim:                    0
% 2.47/0.97  inst_num_of_dismatching_blockings:      555
% 2.47/0.97  inst_num_of_non_proper_insts:           404
% 2.47/0.97  inst_num_of_duplicates:                 0
% 2.47/0.97  inst_inst_num_from_inst_to_res:         0
% 2.47/0.97  inst_dismatching_checking_time:         0.
% 2.47/0.97  
% 2.47/0.97  ------ Resolution
% 2.47/0.97  
% 2.47/0.97  res_num_of_clauses:                     0
% 2.47/0.97  res_num_in_passive:                     0
% 2.47/0.97  res_num_in_active:                      0
% 2.47/0.97  res_num_of_loops:                       153
% 2.47/0.97  res_forward_subset_subsumed:            93
% 2.47/0.97  res_backward_subset_subsumed:           18
% 2.47/0.97  res_forward_subsumed:                   0
% 2.47/0.97  res_backward_subsumed:                  0
% 2.47/0.97  res_forward_subsumption_resolution:     0
% 2.47/0.97  res_backward_subsumption_resolution:    0
% 2.47/0.97  res_clause_to_clause_subsumption:       244
% 2.47/0.97  res_orphan_elimination:                 0
% 2.47/0.97  res_tautology_del:                      0
% 2.47/0.97  res_num_eq_res_simplified:              0
% 2.47/0.97  res_num_sel_changes:                    0
% 2.47/0.97  res_moves_from_active_to_pass:          0
% 2.47/0.97  
% 2.47/0.97  ------ Superposition
% 2.47/0.97  
% 2.47/0.97  sup_time_total:                         0.
% 2.47/0.97  sup_time_generating:                    0.
% 2.47/0.97  sup_time_sim_full:                      0.
% 2.47/0.97  sup_time_sim_immed:                     0.
% 2.47/0.97  
% 2.47/0.97  sup_num_of_clauses:                     69
% 2.47/0.97  sup_num_in_active:                      33
% 2.47/0.97  sup_num_in_passive:                     36
% 2.47/0.97  sup_num_of_loops:                       38
% 2.47/0.97  sup_fw_superposition:                   59
% 2.47/0.97  sup_bw_superposition:                   26
% 2.47/0.97  sup_immediate_simplified:               4
% 2.47/0.97  sup_given_eliminated:                   0
% 2.47/0.97  comparisons_done:                       0
% 2.47/0.97  comparisons_avoided:                    6
% 2.47/0.97  
% 2.47/0.97  ------ Simplifications
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  sim_fw_subset_subsumed:                 0
% 2.47/0.97  sim_bw_subset_subsumed:                 0
% 2.47/0.97  sim_fw_subsumed:                        5
% 2.47/0.97  sim_bw_subsumed:                        0
% 2.47/0.97  sim_fw_subsumption_res:                 1
% 2.47/0.97  sim_bw_subsumption_res:                 0
% 2.47/0.97  sim_tautology_del:                      2
% 2.47/0.97  sim_eq_tautology_del:                   4
% 2.47/0.97  sim_eq_res_simp:                        0
% 2.47/0.97  sim_fw_demodulated:                     0
% 2.47/0.97  sim_bw_demodulated:                     6
% 2.47/0.97  sim_light_normalised:                   1
% 2.47/0.97  sim_joinable_taut:                      0
% 2.47/0.97  sim_joinable_simp:                      0
% 2.47/0.97  sim_ac_normalised:                      0
% 2.47/0.97  sim_smt_subsumption:                    0
% 2.47/0.97  
%------------------------------------------------------------------------------
