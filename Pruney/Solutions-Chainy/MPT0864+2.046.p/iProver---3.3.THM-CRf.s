%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:55 EST 2020

% Result     : Theorem 3.43s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 296 expanded)
%              Number of clauses        :   42 (  74 expanded)
%              Number of leaves         :   13 (  80 expanded)
%              Depth                    :   21
%              Number of atoms          :  258 (1065 expanded)
%              Number of equality atoms :  201 ( 808 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => k4_tarski(sK3,sK4) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( k2_mcart_1(sK2) = sK2
        | k1_mcart_1(sK2) = sK2 )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK2 ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( k2_mcart_1(sK2) = sK2
      | k1_mcart_1(sK2) = sK2 )
    & k4_tarski(sK3,sK4) = sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f21,f20])).

fof(f40,plain,
    ( k2_mcart_1(sK2) = sK2
    | k1_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f52,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f47])).

fof(f53,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f18])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK1(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f49,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f50,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f51,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f50])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK1(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_13,negated_conjecture,
    ( k1_mcart_1(sK2) = sK2
    | k2_mcart_1(sK2) = sK2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( k4_tarski(sK3,sK4) = sK2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_718,plain,
    ( k1_mcart_1(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_14,c_9])).

cnf(c_809,plain,
    ( k2_mcart_1(sK2) = sK2
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_13,c_718])).

cnf(c_8,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_639,plain,
    ( k2_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_14,c_8])).

cnf(c_811,plain,
    ( sK4 = sK2
    | sK3 = sK2 ),
    inference(demodulation,[status(thm)],[c_809,c_639])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_544,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_540,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_543,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1941,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK1(k2_enumset1(X0,X0,X0,X1)) = X0
    | sK1(k2_enumset1(X0,X0,X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_540,c_543])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X2,X0) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_542,plain,
    ( k4_tarski(X0,X1) != sK1(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1512,plain,
    ( sK1(X0) != sK2
    | k1_xboole_0 = X0
    | r2_hidden(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_542])).

cnf(c_2078,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK1(k2_enumset1(X0,X0,X0,X1)) = X0
    | sK2 != X1
    | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1941,c_1512])).

cnf(c_2327,plain,
    ( k2_enumset1(X0,X0,X0,sK2) = k1_xboole_0
    | sK1(k2_enumset1(X0,X0,X0,sK2)) = X0
    | r2_hidden(sK4,k2_enumset1(X0,X0,X0,sK2)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2078])).

cnf(c_2828,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK2) = k1_xboole_0
    | sK1(k2_enumset1(sK4,sK4,sK4,sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_544,c_2327])).

cnf(c_3335,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK2) = k1_xboole_0
    | sK4 != sK2
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2828,c_1512])).

cnf(c_3783,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK2) = k1_xboole_0
    | sK4 != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3335,c_544])).

cnf(c_3784,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK2) = k1_xboole_0
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_811,c_3783])).

cnf(c_5119,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK3 = sK2 ),
    inference(superposition,[status(thm)],[c_811,c_3784])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_951,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_5281,plain,
    ( sK3 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5119,c_951])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_545,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(X0,X2) != sK1(X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_541,plain,
    ( k4_tarski(X0,X1) != sK1(X2)
    | k1_xboole_0 = X2
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_948,plain,
    ( sK1(X0) != sK2
    | k1_xboole_0 = X0
    | r2_hidden(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_541])).

cnf(c_2086,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK1(k2_enumset1(X0,X0,X0,X1)) = X1
    | sK2 != X0
    | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1941,c_948])).

cnf(c_2547,plain,
    ( k2_enumset1(sK2,sK2,sK2,X0) = k1_xboole_0
    | sK1(k2_enumset1(sK2,sK2,sK2,X0)) = X0
    | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,X0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2086])).

cnf(c_2900,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK1(k2_enumset1(sK2,sK2,sK2,sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_545,c_2547])).

cnf(c_3743,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK3 != sK2
    | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2900,c_948])).

cnf(c_4328,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0
    | sK3 != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3743,c_545])).

cnf(c_5285,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_5281,c_4328])).

cnf(c_5342,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5285])).

cnf(c_7841,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5342,c_951])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.43/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.43/1.00  
% 3.43/1.00  ------  iProver source info
% 3.43/1.00  
% 3.43/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.43/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.43/1.00  git: non_committed_changes: false
% 3.43/1.00  git: last_make_outside_of_git: false
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    --mode clausify
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         false
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     num_symb
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       true
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     false
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   []
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_full_bw                           [BwDemod]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  ------ Parsing...
% 3.43/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.43/1.00  ------ Proving...
% 3.43/1.00  ------ Problem Properties 
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  clauses                                 15
% 3.43/1.00  conjectures                             2
% 3.43/1.00  EPR                                     0
% 3.43/1.00  Horn                                    11
% 3.43/1.00  unary                                   7
% 3.43/1.00  binary                                  2
% 3.43/1.00  lits                                    30
% 3.43/1.00  lits eq                                 21
% 3.43/1.00  fd_pure                                 0
% 3.43/1.00  fd_pseudo                               0
% 3.43/1.00  fd_cond                                 3
% 3.43/1.00  fd_pseudo_cond                          3
% 3.43/1.00  AC symbols                              0
% 3.43/1.00  
% 3.43/1.00  ------ Schedule dynamic 5 is on 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ 
% 3.43/1.00  Current options:
% 3.43/1.00  ------ 
% 3.43/1.00  
% 3.43/1.00  ------ Input Options
% 3.43/1.00  
% 3.43/1.00  --out_options                           all
% 3.43/1.00  --tptp_safe_out                         true
% 3.43/1.00  --problem_path                          ""
% 3.43/1.00  --include_path                          ""
% 3.43/1.00  --clausifier                            res/vclausify_rel
% 3.43/1.00  --clausifier_options                    --mode clausify
% 3.43/1.00  --stdin                                 false
% 3.43/1.00  --stats_out                             all
% 3.43/1.00  
% 3.43/1.00  ------ General Options
% 3.43/1.00  
% 3.43/1.00  --fof                                   false
% 3.43/1.00  --time_out_real                         305.
% 3.43/1.00  --time_out_virtual                      -1.
% 3.43/1.00  --symbol_type_check                     false
% 3.43/1.00  --clausify_out                          false
% 3.43/1.00  --sig_cnt_out                           false
% 3.43/1.00  --trig_cnt_out                          false
% 3.43/1.00  --trig_cnt_out_tolerance                1.
% 3.43/1.00  --trig_cnt_out_sk_spl                   false
% 3.43/1.00  --abstr_cl_out                          false
% 3.43/1.00  
% 3.43/1.00  ------ Global Options
% 3.43/1.00  
% 3.43/1.00  --schedule                              default
% 3.43/1.00  --add_important_lit                     false
% 3.43/1.00  --prop_solver_per_cl                    1000
% 3.43/1.00  --min_unsat_core                        false
% 3.43/1.00  --soft_assumptions                      false
% 3.43/1.00  --soft_lemma_size                       3
% 3.43/1.00  --prop_impl_unit_size                   0
% 3.43/1.00  --prop_impl_unit                        []
% 3.43/1.00  --share_sel_clauses                     true
% 3.43/1.00  --reset_solvers                         false
% 3.43/1.00  --bc_imp_inh                            [conj_cone]
% 3.43/1.00  --conj_cone_tolerance                   3.
% 3.43/1.00  --extra_neg_conj                        none
% 3.43/1.00  --large_theory_mode                     true
% 3.43/1.00  --prolific_symb_bound                   200
% 3.43/1.00  --lt_threshold                          2000
% 3.43/1.00  --clause_weak_htbl                      true
% 3.43/1.00  --gc_record_bc_elim                     false
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing Options
% 3.43/1.00  
% 3.43/1.00  --preprocessing_flag                    true
% 3.43/1.00  --time_out_prep_mult                    0.1
% 3.43/1.00  --splitting_mode                        input
% 3.43/1.00  --splitting_grd                         true
% 3.43/1.00  --splitting_cvd                         false
% 3.43/1.00  --splitting_cvd_svl                     false
% 3.43/1.00  --splitting_nvd                         32
% 3.43/1.00  --sub_typing                            true
% 3.43/1.00  --prep_gs_sim                           true
% 3.43/1.00  --prep_unflatten                        true
% 3.43/1.00  --prep_res_sim                          true
% 3.43/1.00  --prep_upred                            true
% 3.43/1.00  --prep_sem_filter                       exhaustive
% 3.43/1.00  --prep_sem_filter_out                   false
% 3.43/1.00  --pred_elim                             true
% 3.43/1.00  --res_sim_input                         true
% 3.43/1.00  --eq_ax_congr_red                       true
% 3.43/1.00  --pure_diseq_elim                       true
% 3.43/1.00  --brand_transform                       false
% 3.43/1.00  --non_eq_to_eq                          false
% 3.43/1.00  --prep_def_merge                        true
% 3.43/1.00  --prep_def_merge_prop_impl              false
% 3.43/1.00  --prep_def_merge_mbd                    true
% 3.43/1.00  --prep_def_merge_tr_red                 false
% 3.43/1.00  --prep_def_merge_tr_cl                  false
% 3.43/1.00  --smt_preprocessing                     true
% 3.43/1.00  --smt_ac_axioms                         fast
% 3.43/1.00  --preprocessed_out                      false
% 3.43/1.00  --preprocessed_stats                    false
% 3.43/1.00  
% 3.43/1.00  ------ Abstraction refinement Options
% 3.43/1.00  
% 3.43/1.00  --abstr_ref                             []
% 3.43/1.00  --abstr_ref_prep                        false
% 3.43/1.00  --abstr_ref_until_sat                   false
% 3.43/1.00  --abstr_ref_sig_restrict                funpre
% 3.43/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.43/1.00  --abstr_ref_under                       []
% 3.43/1.00  
% 3.43/1.00  ------ SAT Options
% 3.43/1.00  
% 3.43/1.00  --sat_mode                              false
% 3.43/1.00  --sat_fm_restart_options                ""
% 3.43/1.00  --sat_gr_def                            false
% 3.43/1.00  --sat_epr_types                         true
% 3.43/1.00  --sat_non_cyclic_types                  false
% 3.43/1.00  --sat_finite_models                     false
% 3.43/1.00  --sat_fm_lemmas                         false
% 3.43/1.00  --sat_fm_prep                           false
% 3.43/1.00  --sat_fm_uc_incr                        true
% 3.43/1.00  --sat_out_model                         small
% 3.43/1.00  --sat_out_clauses                       false
% 3.43/1.00  
% 3.43/1.00  ------ QBF Options
% 3.43/1.00  
% 3.43/1.00  --qbf_mode                              false
% 3.43/1.00  --qbf_elim_univ                         false
% 3.43/1.00  --qbf_dom_inst                          none
% 3.43/1.00  --qbf_dom_pre_inst                      false
% 3.43/1.00  --qbf_sk_in                             false
% 3.43/1.00  --qbf_pred_elim                         true
% 3.43/1.00  --qbf_split                             512
% 3.43/1.00  
% 3.43/1.00  ------ BMC1 Options
% 3.43/1.00  
% 3.43/1.00  --bmc1_incremental                      false
% 3.43/1.00  --bmc1_axioms                           reachable_all
% 3.43/1.00  --bmc1_min_bound                        0
% 3.43/1.00  --bmc1_max_bound                        -1
% 3.43/1.00  --bmc1_max_bound_default                -1
% 3.43/1.00  --bmc1_symbol_reachability              true
% 3.43/1.00  --bmc1_property_lemmas                  false
% 3.43/1.00  --bmc1_k_induction                      false
% 3.43/1.00  --bmc1_non_equiv_states                 false
% 3.43/1.00  --bmc1_deadlock                         false
% 3.43/1.00  --bmc1_ucm                              false
% 3.43/1.00  --bmc1_add_unsat_core                   none
% 3.43/1.00  --bmc1_unsat_core_children              false
% 3.43/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.43/1.00  --bmc1_out_stat                         full
% 3.43/1.00  --bmc1_ground_init                      false
% 3.43/1.00  --bmc1_pre_inst_next_state              false
% 3.43/1.00  --bmc1_pre_inst_state                   false
% 3.43/1.00  --bmc1_pre_inst_reach_state             false
% 3.43/1.00  --bmc1_out_unsat_core                   false
% 3.43/1.00  --bmc1_aig_witness_out                  false
% 3.43/1.00  --bmc1_verbose                          false
% 3.43/1.00  --bmc1_dump_clauses_tptp                false
% 3.43/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.43/1.00  --bmc1_dump_file                        -
% 3.43/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.43/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.43/1.00  --bmc1_ucm_extend_mode                  1
% 3.43/1.00  --bmc1_ucm_init_mode                    2
% 3.43/1.00  --bmc1_ucm_cone_mode                    none
% 3.43/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.43/1.00  --bmc1_ucm_relax_model                  4
% 3.43/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.43/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.43/1.00  --bmc1_ucm_layered_model                none
% 3.43/1.00  --bmc1_ucm_max_lemma_size               10
% 3.43/1.00  
% 3.43/1.00  ------ AIG Options
% 3.43/1.00  
% 3.43/1.00  --aig_mode                              false
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation Options
% 3.43/1.00  
% 3.43/1.00  --instantiation_flag                    true
% 3.43/1.00  --inst_sos_flag                         false
% 3.43/1.00  --inst_sos_phase                        true
% 3.43/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.43/1.00  --inst_lit_sel_side                     none
% 3.43/1.00  --inst_solver_per_active                1400
% 3.43/1.00  --inst_solver_calls_frac                1.
% 3.43/1.00  --inst_passive_queue_type               priority_queues
% 3.43/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.43/1.00  --inst_passive_queues_freq              [25;2]
% 3.43/1.00  --inst_dismatching                      true
% 3.43/1.00  --inst_eager_unprocessed_to_passive     true
% 3.43/1.00  --inst_prop_sim_given                   true
% 3.43/1.00  --inst_prop_sim_new                     false
% 3.43/1.00  --inst_subs_new                         false
% 3.43/1.00  --inst_eq_res_simp                      false
% 3.43/1.00  --inst_subs_given                       false
% 3.43/1.00  --inst_orphan_elimination               true
% 3.43/1.00  --inst_learning_loop_flag               true
% 3.43/1.00  --inst_learning_start                   3000
% 3.43/1.00  --inst_learning_factor                  2
% 3.43/1.00  --inst_start_prop_sim_after_learn       3
% 3.43/1.00  --inst_sel_renew                        solver
% 3.43/1.00  --inst_lit_activity_flag                true
% 3.43/1.00  --inst_restr_to_given                   false
% 3.43/1.00  --inst_activity_threshold               500
% 3.43/1.00  --inst_out_proof                        true
% 3.43/1.00  
% 3.43/1.00  ------ Resolution Options
% 3.43/1.00  
% 3.43/1.00  --resolution_flag                       false
% 3.43/1.00  --res_lit_sel                           adaptive
% 3.43/1.00  --res_lit_sel_side                      none
% 3.43/1.00  --res_ordering                          kbo
% 3.43/1.00  --res_to_prop_solver                    active
% 3.43/1.00  --res_prop_simpl_new                    false
% 3.43/1.00  --res_prop_simpl_given                  true
% 3.43/1.00  --res_passive_queue_type                priority_queues
% 3.43/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.43/1.00  --res_passive_queues_freq               [15;5]
% 3.43/1.00  --res_forward_subs                      full
% 3.43/1.00  --res_backward_subs                     full
% 3.43/1.00  --res_forward_subs_resolution           true
% 3.43/1.00  --res_backward_subs_resolution          true
% 3.43/1.00  --res_orphan_elimination                true
% 3.43/1.00  --res_time_limit                        2.
% 3.43/1.00  --res_out_proof                         true
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Options
% 3.43/1.00  
% 3.43/1.00  --superposition_flag                    true
% 3.43/1.00  --sup_passive_queue_type                priority_queues
% 3.43/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.43/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.43/1.00  --demod_completeness_check              fast
% 3.43/1.00  --demod_use_ground                      true
% 3.43/1.00  --sup_to_prop_solver                    passive
% 3.43/1.00  --sup_prop_simpl_new                    true
% 3.43/1.00  --sup_prop_simpl_given                  true
% 3.43/1.00  --sup_fun_splitting                     false
% 3.43/1.00  --sup_smt_interval                      50000
% 3.43/1.00  
% 3.43/1.00  ------ Superposition Simplification Setup
% 3.43/1.00  
% 3.43/1.00  --sup_indices_passive                   []
% 3.43/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.43/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.43/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_full_bw                           [BwDemod]
% 3.43/1.00  --sup_immed_triv                        [TrivRules]
% 3.43/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.43/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_immed_bw_main                     []
% 3.43/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.43/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.43/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.43/1.00  
% 3.43/1.00  ------ Combination Options
% 3.43/1.00  
% 3.43/1.00  --comb_res_mult                         3
% 3.43/1.00  --comb_sup_mult                         2
% 3.43/1.00  --comb_inst_mult                        10
% 3.43/1.00  
% 3.43/1.00  ------ Debug Options
% 3.43/1.00  
% 3.43/1.00  --dbg_backtrace                         false
% 3.43/1.00  --dbg_dump_prop_clauses                 false
% 3.43/1.00  --dbg_dump_prop_clauses_file            -
% 3.43/1.00  --dbg_out_stat                          false
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  ------ Proving...
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  % SZS status Theorem for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00   Resolution empty clause
% 3.43/1.00  
% 3.43/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  fof(f9,conjecture,(
% 3.43/1.00    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f10,negated_conjecture,(
% 3.43/1.00    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 3.43/1.00    inference(negated_conjecture,[],[f9])).
% 3.43/1.00  
% 3.43/1.00  fof(f12,plain,(
% 3.43/1.00    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 3.43/1.00    inference(ennf_transformation,[],[f10])).
% 3.43/1.00  
% 3.43/1.00  fof(f21,plain,(
% 3.43/1.00    ( ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => k4_tarski(sK3,sK4) = X0) )),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f20,plain,(
% 3.43/1.00    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & ? [X2,X1] : k4_tarski(X1,X2) = sK2)),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f22,plain,(
% 3.43/1.00    (k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2) & k4_tarski(sK3,sK4) = sK2),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f21,f20])).
% 3.43/1.00  
% 3.43/1.00  fof(f40,plain,(
% 3.43/1.00    k2_mcart_1(sK2) = sK2 | k1_mcart_1(sK2) = sK2),
% 3.43/1.00    inference(cnf_transformation,[],[f22])).
% 3.43/1.00  
% 3.43/1.00  fof(f39,plain,(
% 3.43/1.00    k4_tarski(sK3,sK4) = sK2),
% 3.43/1.00    inference(cnf_transformation,[],[f22])).
% 3.43/1.00  
% 3.43/1.00  fof(f7,axiom,(
% 3.43/1.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f34,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f7])).
% 3.43/1.00  
% 3.43/1.00  fof(f35,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.43/1.00    inference(cnf_transformation,[],[f7])).
% 3.43/1.00  
% 3.43/1.00  fof(f2,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f13,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.43/1.00    inference(nnf_transformation,[],[f2])).
% 3.43/1.00  
% 3.43/1.00  fof(f14,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.43/1.00    inference(flattening,[],[f13])).
% 3.43/1.00  
% 3.43/1.00  fof(f15,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.43/1.00    inference(rectify,[],[f14])).
% 3.43/1.00  
% 3.43/1.00  fof(f16,plain,(
% 3.43/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f17,plain,(
% 3.43/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.43/1.00  
% 3.43/1.00  fof(f25,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.43/1.00    inference(cnf_transformation,[],[f17])).
% 3.43/1.00  
% 3.43/1.00  fof(f4,axiom,(
% 3.43/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f31,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f4])).
% 3.43/1.00  
% 3.43/1.00  fof(f5,axiom,(
% 3.43/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f32,plain,(
% 3.43/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f5])).
% 3.43/1.00  
% 3.43/1.00  fof(f41,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f31,f32])).
% 3.43/1.00  
% 3.43/1.00  fof(f47,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.43/1.00    inference(definition_unfolding,[],[f25,f41])).
% 3.43/1.00  
% 3.43/1.00  fof(f52,plain,(
% 3.43/1.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.43/1.00    inference(equality_resolution,[],[f47])).
% 3.43/1.00  
% 3.43/1.00  fof(f53,plain,(
% 3.43/1.00    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.43/1.00    inference(equality_resolution,[],[f52])).
% 3.43/1.00  
% 3.43/1.00  fof(f8,axiom,(
% 3.43/1.00    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f11,plain,(
% 3.43/1.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.43/1.00    inference(ennf_transformation,[],[f8])).
% 3.43/1.00  
% 3.43/1.00  fof(f18,plain,(
% 3.43/1.00    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 3.43/1.00    introduced(choice_axiom,[])).
% 3.43/1.00  
% 3.43/1.00  fof(f19,plain,(
% 3.43/1.00    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 3.43/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f18])).
% 3.43/1.00  
% 3.43/1.00  fof(f36,plain,(
% 3.43/1.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f19])).
% 3.43/1.00  
% 3.43/1.00  fof(f24,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.43/1.00    inference(cnf_transformation,[],[f17])).
% 3.43/1.00  
% 3.43/1.00  fof(f48,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.43/1.00    inference(definition_unfolding,[],[f24,f41])).
% 3.43/1.00  
% 3.43/1.00  fof(f54,plain,(
% 3.43/1.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 3.43/1.00    inference(equality_resolution,[],[f48])).
% 3.43/1.00  
% 3.43/1.00  fof(f38,plain,(
% 3.43/1.00    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK1(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f19])).
% 3.43/1.00  
% 3.43/1.00  fof(f1,axiom,(
% 3.43/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f23,plain,(
% 3.43/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f1])).
% 3.43/1.00  
% 3.43/1.00  fof(f6,axiom,(
% 3.43/1.00    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f33,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f6])).
% 3.43/1.00  
% 3.43/1.00  fof(f3,axiom,(
% 3.43/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.43/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.43/1.00  
% 3.43/1.00  fof(f30,plain,(
% 3.43/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.43/1.00    inference(cnf_transformation,[],[f3])).
% 3.43/1.00  
% 3.43/1.00  fof(f42,plain,(
% 3.43/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f30,f41])).
% 3.43/1.00  
% 3.43/1.00  fof(f49,plain,(
% 3.43/1.00    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 3.43/1.00    inference(definition_unfolding,[],[f33,f42])).
% 3.43/1.00  
% 3.43/1.00  fof(f26,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.43/1.00    inference(cnf_transformation,[],[f17])).
% 3.43/1.00  
% 3.43/1.00  fof(f46,plain,(
% 3.43/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.43/1.00    inference(definition_unfolding,[],[f26,f41])).
% 3.43/1.00  
% 3.43/1.00  fof(f50,plain,(
% 3.43/1.00    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 3.43/1.00    inference(equality_resolution,[],[f46])).
% 3.43/1.00  
% 3.43/1.00  fof(f51,plain,(
% 3.43/1.00    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 3.43/1.00    inference(equality_resolution,[],[f50])).
% 3.43/1.00  
% 3.43/1.00  fof(f37,plain,(
% 3.43/1.00    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK1(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 3.43/1.00    inference(cnf_transformation,[],[f19])).
% 3.43/1.00  
% 3.43/1.00  cnf(c_13,negated_conjecture,
% 3.43/1.00      ( k1_mcart_1(sK2) = sK2 | k2_mcart_1(sK2) = sK2 ),
% 3.43/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_14,negated_conjecture,
% 3.43/1.00      ( k4_tarski(sK3,sK4) = sK2 ),
% 3.43/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_9,plain,
% 3.43/1.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_718,plain,
% 3.43/1.00      ( k1_mcart_1(sK2) = sK3 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_14,c_9]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_809,plain,
% 3.43/1.00      ( k2_mcart_1(sK2) = sK2 | sK3 = sK2 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_13,c_718]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_8,plain,
% 3.43/1.00      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.43/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_639,plain,
% 3.43/1.00      ( k2_mcart_1(sK2) = sK4 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_14,c_8]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_811,plain,
% 3.43/1.00      ( sK4 = sK2 | sK3 = sK2 ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_809,c_639]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5,plain,
% 3.43/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_544,plain,
% 3.43/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_12,plain,
% 3.43/1.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_540,plain,
% 3.43/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_6,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.43/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_543,plain,
% 3.43/1.00      ( X0 = X1
% 3.43/1.00      | X0 = X2
% 3.43/1.00      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1941,plain,
% 3.43/1.00      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 3.43/1.00      | sK1(k2_enumset1(X0,X0,X0,X1)) = X0
% 3.43/1.00      | sK1(k2_enumset1(X0,X0,X0,X1)) = X1 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_540,c_543]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_10,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,X1) | k4_tarski(X2,X0) != sK1(X1) | k1_xboole_0 = X1 ),
% 3.43/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_542,plain,
% 3.43/1.00      ( k4_tarski(X0,X1) != sK1(X2)
% 3.43/1.00      | k1_xboole_0 = X2
% 3.43/1.00      | r2_hidden(X1,X2) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_1512,plain,
% 3.43/1.00      ( sK1(X0) != sK2 | k1_xboole_0 = X0 | r2_hidden(sK4,X0) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_14,c_542]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2078,plain,
% 3.43/1.00      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 3.43/1.00      | sK1(k2_enumset1(X0,X0,X0,X1)) = X0
% 3.43/1.00      | sK2 != X1
% 3.43/1.00      | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1941,c_1512]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2327,plain,
% 3.43/1.00      ( k2_enumset1(X0,X0,X0,sK2) = k1_xboole_0
% 3.43/1.00      | sK1(k2_enumset1(X0,X0,X0,sK2)) = X0
% 3.43/1.00      | r2_hidden(sK4,k2_enumset1(X0,X0,X0,sK2)) != iProver_top ),
% 3.43/1.00      inference(equality_resolution,[status(thm)],[c_2078]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2828,plain,
% 3.43/1.00      ( k2_enumset1(sK4,sK4,sK4,sK2) = k1_xboole_0
% 3.43/1.00      | sK1(k2_enumset1(sK4,sK4,sK4,sK2)) = sK4 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_544,c_2327]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3335,plain,
% 3.43/1.00      ( k2_enumset1(sK4,sK4,sK4,sK2) = k1_xboole_0
% 3.43/1.00      | sK4 != sK2
% 3.43/1.00      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK2)) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2828,c_1512]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3783,plain,
% 3.43/1.00      ( k2_enumset1(sK4,sK4,sK4,sK2) = k1_xboole_0 | sK4 != sK2 ),
% 3.43/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3335,c_544]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3784,plain,
% 3.43/1.00      ( k2_enumset1(sK4,sK4,sK4,sK2) = k1_xboole_0 | sK3 = sK2 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_811,c_3783]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5119,plain,
% 3.43/1.00      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 | sK3 = sK2 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_811,c_3784]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_0,plain,
% 3.43/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_7,plain,
% 3.43/1.00      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) != k1_xboole_0 ),
% 3.43/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_951,plain,
% 3.43/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5281,plain,
% 3.43/1.00      ( sK3 = sK2 ),
% 3.43/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5119,c_951]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4,plain,
% 3.43/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 3.43/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_545,plain,
% 3.43/1.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_11,plain,
% 3.43/1.00      ( ~ r2_hidden(X0,X1) | k4_tarski(X0,X2) != sK1(X1) | k1_xboole_0 = X1 ),
% 3.43/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_541,plain,
% 3.43/1.00      ( k4_tarski(X0,X1) != sK1(X2)
% 3.43/1.00      | k1_xboole_0 = X2
% 3.43/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.43/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_948,plain,
% 3.43/1.00      ( sK1(X0) != sK2 | k1_xboole_0 = X0 | r2_hidden(sK3,X0) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_14,c_541]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2086,plain,
% 3.43/1.00      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 3.43/1.00      | sK1(k2_enumset1(X0,X0,X0,X1)) = X1
% 3.43/1.00      | sK2 != X0
% 3.43/1.00      | r2_hidden(sK3,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_1941,c_948]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2547,plain,
% 3.43/1.00      ( k2_enumset1(sK2,sK2,sK2,X0) = k1_xboole_0
% 3.43/1.00      | sK1(k2_enumset1(sK2,sK2,sK2,X0)) = X0
% 3.43/1.00      | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,X0)) != iProver_top ),
% 3.43/1.00      inference(equality_resolution,[status(thm)],[c_2086]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_2900,plain,
% 3.43/1.00      ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0
% 3.43/1.00      | sK1(k2_enumset1(sK2,sK2,sK2,sK3)) = sK3 ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_545,c_2547]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_3743,plain,
% 3.43/1.00      ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0
% 3.43/1.00      | sK3 != sK2
% 3.43/1.00      | r2_hidden(sK3,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top ),
% 3.43/1.00      inference(superposition,[status(thm)],[c_2900,c_948]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_4328,plain,
% 3.43/1.00      ( k2_enumset1(sK2,sK2,sK2,sK3) = k1_xboole_0 | sK3 != sK2 ),
% 3.43/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3743,c_545]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5285,plain,
% 3.43/1.00      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 | sK2 != sK2 ),
% 3.43/1.00      inference(demodulation,[status(thm)],[c_5281,c_4328]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_5342,plain,
% 3.43/1.00      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_xboole_0 ),
% 3.43/1.00      inference(equality_resolution_simp,[status(thm)],[c_5285]) ).
% 3.43/1.00  
% 3.43/1.00  cnf(c_7841,plain,
% 3.43/1.00      ( $false ),
% 3.43/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5342,c_951]) ).
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.43/1.00  
% 3.43/1.00  ------                               Statistics
% 3.43/1.00  
% 3.43/1.00  ------ General
% 3.43/1.00  
% 3.43/1.00  abstr_ref_over_cycles:                  0
% 3.43/1.00  abstr_ref_under_cycles:                 0
% 3.43/1.00  gc_basic_clause_elim:                   0
% 3.43/1.00  forced_gc_time:                         0
% 3.43/1.00  parsing_time:                           0.014
% 3.43/1.00  unif_index_cands_time:                  0.
% 3.43/1.00  unif_index_add_time:                    0.
% 3.43/1.00  orderings_time:                         0.
% 3.43/1.00  out_proof_time:                         0.008
% 3.43/1.00  total_time:                             0.334
% 3.43/1.00  num_of_symbols:                         43
% 3.43/1.00  num_of_terms:                           12433
% 3.43/1.00  
% 3.43/1.00  ------ Preprocessing
% 3.43/1.00  
% 3.43/1.00  num_of_splits:                          0
% 3.43/1.00  num_of_split_atoms:                     0
% 3.43/1.00  num_of_reused_defs:                     0
% 3.43/1.00  num_eq_ax_congr_red:                    16
% 3.43/1.00  num_of_sem_filtered_clauses:            1
% 3.43/1.00  num_of_subtypes:                        0
% 3.43/1.00  monotx_restored_types:                  0
% 3.43/1.00  sat_num_of_epr_types:                   0
% 3.43/1.00  sat_num_of_non_cyclic_types:            0
% 3.43/1.00  sat_guarded_non_collapsed_types:        0
% 3.43/1.00  num_pure_diseq_elim:                    0
% 3.43/1.00  simp_replaced_by:                       0
% 3.43/1.00  res_preprocessed:                       60
% 3.43/1.00  prep_upred:                             0
% 3.43/1.00  prep_unflattend:                        28
% 3.43/1.00  smt_new_axioms:                         0
% 3.43/1.00  pred_elim_cands:                        1
% 3.43/1.00  pred_elim:                              0
% 3.43/1.00  pred_elim_cl:                           0
% 3.43/1.00  pred_elim_cycles:                       1
% 3.43/1.00  merged_defs:                            0
% 3.43/1.00  merged_defs_ncl:                        0
% 3.43/1.00  bin_hyper_res:                          0
% 3.43/1.00  prep_cycles:                            3
% 3.43/1.00  pred_elim_time:                         0.006
% 3.43/1.00  splitting_time:                         0.
% 3.43/1.00  sem_filter_time:                        0.
% 3.43/1.00  monotx_time:                            0.001
% 3.43/1.00  subtype_inf_time:                       0.
% 3.43/1.00  
% 3.43/1.00  ------ Problem properties
% 3.43/1.00  
% 3.43/1.00  clauses:                                15
% 3.43/1.00  conjectures:                            2
% 3.43/1.00  epr:                                    0
% 3.43/1.00  horn:                                   11
% 3.43/1.00  ground:                                 2
% 3.43/1.00  unary:                                  7
% 3.43/1.00  binary:                                 2
% 3.43/1.00  lits:                                   30
% 3.43/1.00  lits_eq:                                21
% 3.43/1.00  fd_pure:                                0
% 3.43/1.00  fd_pseudo:                              0
% 3.43/1.00  fd_cond:                                3
% 3.43/1.00  fd_pseudo_cond:                         3
% 3.43/1.00  ac_symbols:                             0
% 3.43/1.00  
% 3.43/1.00  ------ Propositional Solver
% 3.43/1.00  
% 3.43/1.00  prop_solver_calls:                      25
% 3.43/1.00  prop_fast_solver_calls:                 557
% 3.43/1.00  smt_solver_calls:                       0
% 3.43/1.00  smt_fast_solver_calls:                  0
% 3.43/1.00  prop_num_of_clauses:                    3077
% 3.43/1.00  prop_preprocess_simplified:             8005
% 3.43/1.00  prop_fo_subsumed:                       24
% 3.43/1.00  prop_solver_time:                       0.
% 3.43/1.00  smt_solver_time:                        0.
% 3.43/1.00  smt_fast_solver_time:                   0.
% 3.43/1.00  prop_fast_solver_time:                  0.
% 3.43/1.00  prop_unsat_core_time:                   0.
% 3.43/1.00  
% 3.43/1.00  ------ QBF
% 3.43/1.00  
% 3.43/1.00  qbf_q_res:                              0
% 3.43/1.00  qbf_num_tautologies:                    0
% 3.43/1.00  qbf_prep_cycles:                        0
% 3.43/1.00  
% 3.43/1.00  ------ BMC1
% 3.43/1.00  
% 3.43/1.00  bmc1_current_bound:                     -1
% 3.43/1.00  bmc1_last_solved_bound:                 -1
% 3.43/1.00  bmc1_unsat_core_size:                   -1
% 3.43/1.00  bmc1_unsat_core_parents_size:           -1
% 3.43/1.00  bmc1_merge_next_fun:                    0
% 3.43/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.43/1.00  
% 3.43/1.00  ------ Instantiation
% 3.43/1.00  
% 3.43/1.00  inst_num_of_clauses:                    1149
% 3.43/1.00  inst_num_in_passive:                    475
% 3.43/1.00  inst_num_in_active:                     314
% 3.43/1.00  inst_num_in_unprocessed:                360
% 3.43/1.00  inst_num_of_loops:                      350
% 3.43/1.00  inst_num_of_learning_restarts:          0
% 3.43/1.00  inst_num_moves_active_passive:          34
% 3.43/1.00  inst_lit_activity:                      0
% 3.43/1.00  inst_lit_activity_moves:                0
% 3.43/1.00  inst_num_tautologies:                   0
% 3.43/1.00  inst_num_prop_implied:                  0
% 3.43/1.00  inst_num_existing_simplified:           0
% 3.43/1.00  inst_num_eq_res_simplified:             0
% 3.43/1.00  inst_num_child_elim:                    0
% 3.43/1.00  inst_num_of_dismatching_blockings:      611
% 3.43/1.00  inst_num_of_non_proper_insts:           1106
% 3.43/1.00  inst_num_of_duplicates:                 0
% 3.43/1.00  inst_inst_num_from_inst_to_res:         0
% 3.43/1.00  inst_dismatching_checking_time:         0.
% 3.43/1.00  
% 3.43/1.00  ------ Resolution
% 3.43/1.00  
% 3.43/1.00  res_num_of_clauses:                     0
% 3.43/1.00  res_num_in_passive:                     0
% 3.43/1.00  res_num_in_active:                      0
% 3.43/1.00  res_num_of_loops:                       63
% 3.43/1.00  res_forward_subset_subsumed:            59
% 3.43/1.00  res_backward_subset_subsumed:           0
% 3.43/1.00  res_forward_subsumed:                   0
% 3.43/1.00  res_backward_subsumed:                  0
% 3.43/1.00  res_forward_subsumption_resolution:     0
% 3.43/1.00  res_backward_subsumption_resolution:    0
% 3.43/1.00  res_clause_to_clause_subsumption:       430
% 3.43/1.00  res_orphan_elimination:                 0
% 3.43/1.00  res_tautology_del:                      87
% 3.43/1.00  res_num_eq_res_simplified:              0
% 3.43/1.00  res_num_sel_changes:                    0
% 3.43/1.00  res_moves_from_active_to_pass:          0
% 3.43/1.00  
% 3.43/1.00  ------ Superposition
% 3.43/1.00  
% 3.43/1.00  sup_time_total:                         0.
% 3.43/1.00  sup_time_generating:                    0.
% 3.43/1.00  sup_time_sim_full:                      0.
% 3.43/1.00  sup_time_sim_immed:                     0.
% 3.43/1.00  
% 3.43/1.00  sup_num_of_clauses:                     55
% 3.43/1.00  sup_num_in_active:                      42
% 3.43/1.00  sup_num_in_passive:                     13
% 3.43/1.00  sup_num_of_loops:                       68
% 3.43/1.00  sup_fw_superposition:                   56
% 3.43/1.00  sup_bw_superposition:                   91
% 3.43/1.00  sup_immediate_simplified:               39
% 3.43/1.00  sup_given_eliminated:                   0
% 3.43/1.00  comparisons_done:                       0
% 3.43/1.00  comparisons_avoided:                    49
% 3.43/1.00  
% 3.43/1.00  ------ Simplifications
% 3.43/1.00  
% 3.43/1.00  
% 3.43/1.00  sim_fw_subset_subsumed:                 23
% 3.43/1.00  sim_bw_subset_subsumed:                 17
% 3.43/1.00  sim_fw_subsumed:                        14
% 3.43/1.00  sim_bw_subsumed:                        0
% 3.43/1.00  sim_fw_subsumption_res:                 11
% 3.43/1.00  sim_bw_subsumption_res:                 0
% 3.43/1.00  sim_tautology_del:                      4
% 3.43/1.00  sim_eq_tautology_del:                   6
% 3.43/1.00  sim_eq_res_simp:                        1
% 3.43/1.00  sim_fw_demodulated:                     1
% 3.43/1.00  sim_bw_demodulated:                     18
% 3.43/1.00  sim_light_normalised:                   1
% 3.43/1.00  sim_joinable_taut:                      0
% 3.43/1.00  sim_joinable_simp:                      0
% 3.43/1.00  sim_ac_normalised:                      0
% 3.43/1.00  sim_smt_subsumption:                    0
% 3.43/1.00  
%------------------------------------------------------------------------------
