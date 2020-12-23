%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:45 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 253 expanded)
%              Number of clauses        :   27 (  45 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  268 ( 881 expanded)
%              Number of equality atoms :  133 ( 520 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
     => ( ( k2_mcart_1(X0) = X4
          | k2_mcart_1(X0) = X3 )
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ( ( k2_mcart_1(X0) != X4
            & k2_mcart_1(X0) != X3 )
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) )
   => ( ( ( k2_mcart_1(sK2) != sK6
          & k2_mcart_1(sK2) != sK5 )
        | ( k1_mcart_1(sK2) != sK4
          & k1_mcart_1(sK2) != sK3 ) )
      & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ( k2_mcart_1(sK2) != sK6
        & k2_mcart_1(sK2) != sK5 )
      | ( k1_mcart_1(sK2) != sK4
        & k1_mcart_1(sK2) != sK3 ) )
    & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f13,f29])).

fof(f55,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f72,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) ),
    inference(definition_unfolding,[],[f55,f60,f60])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f78,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f79,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f78])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f60,f60])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f80,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,
    ( k2_mcart_1(sK2) != sK6
    | k1_mcart_1(sK2) != sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,
    ( k2_mcart_1(sK2) != sK6
    | k1_mcart_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,
    ( k2_mcart_1(sK2) != sK5
    | k1_mcart_1(sK2) != sK4 ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,
    ( k2_mcart_1(sK2) != sK5
    | k1_mcart_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4601,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4603,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4795,plain,
    ( r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4601,c_4603])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4608,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = k2_enumset1(X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_4606,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4607,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4827,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X2,X2,X2,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X2,X2,X2,X1)
    | r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4606,c_4607])).

cnf(c_6174,plain,
    ( X0 = X1
    | X2 = X1
    | k4_xboole_0(k2_enumset1(X2,X2,X2,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X2,X2,X2,X0) ),
    inference(superposition,[status(thm)],[c_4827,c_4607])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4610,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7336,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X3,k2_enumset1(X1,X1,X1,X2)) != iProver_top
    | r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6174,c_4610])).

cnf(c_7987,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4608,c_7336])).

cnf(c_9212,plain,
    ( k2_mcart_1(sK2) = sK5
    | k2_mcart_1(sK2) = sK6 ),
    inference(superposition,[status(thm)],[c_4795,c_7987])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4602,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4729,plain,
    ( r2_hidden(k1_mcart_1(sK2),k2_enumset1(sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4601,c_4602])).

cnf(c_9211,plain,
    ( k1_mcart_1(sK2) = sK3
    | k1_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_4729,c_7987])).

cnf(c_21,negated_conjecture,
    ( k1_mcart_1(sK2) != sK4
    | k2_mcart_1(sK2) != sK6 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( k1_mcart_1(sK2) != sK3
    | k2_mcart_1(sK2) != sK6 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( k1_mcart_1(sK2) != sK4
    | k2_mcart_1(sK2) != sK5 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( k1_mcart_1(sK2) != sK3
    | k2_mcart_1(sK2) != sK5 ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9212,c_9211,c_21,c_22,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 4.10/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/1.00  
% 4.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.10/1.00  
% 4.10/1.00  ------  iProver source info
% 4.10/1.00  
% 4.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.10/1.00  git: non_committed_changes: false
% 4.10/1.00  git: last_make_outside_of_git: false
% 4.10/1.00  
% 4.10/1.00  ------ 
% 4.10/1.00  ------ Parsing...
% 4.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  ------ Proving...
% 4.10/1.00  ------ Problem Properties 
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  clauses                                 25
% 4.10/1.00  conjectures                             8
% 4.10/1.00  EPR                                     2
% 4.10/1.00  Horn                                    19
% 4.10/1.00  unary                                   3
% 4.10/1.00  binary                                  13
% 4.10/1.00  lits                                    57
% 4.10/1.00  lits eq                                 20
% 4.10/1.00  fd_pure                                 0
% 4.10/1.00  fd_pseudo                               0
% 4.10/1.00  fd_cond                                 0
% 4.10/1.00  fd_pseudo_cond                          6
% 4.10/1.00  AC symbols                              0
% 4.10/1.00  
% 4.10/1.00  ------ Input Options Time Limit: Unbounded
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing...
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 4.10/1.00  Current options:
% 4.10/1.00  ------ 
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing...
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.10/1.00  
% 4.10/1.00  ------ Proving...
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  % SZS status Theorem for theBenchmark.p
% 4.10/1.00  
% 4.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.10/1.00  
% 4.10/1.00  fof(f10,conjecture,(
% 4.10/1.00    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 4.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/1.00  
% 4.10/1.00  fof(f11,negated_conjecture,(
% 4.10/1.00    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 4.10/1.00    inference(negated_conjecture,[],[f10])).
% 4.10/1.00  
% 4.10/1.00  fof(f13,plain,(
% 4.10/1.00    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 4.10/1.00    inference(ennf_transformation,[],[f11])).
% 4.10/1.00  
% 4.10/1.00  fof(f29,plain,(
% 4.10/1.00    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))) => (((k2_mcart_1(sK2) != sK6 & k2_mcart_1(sK2) != sK5) | (k1_mcart_1(sK2) != sK4 & k1_mcart_1(sK2) != sK3)) & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))))),
% 4.10/1.00    introduced(choice_axiom,[])).
% 4.10/1.00  
% 4.10/1.00  fof(f30,plain,(
% 4.10/1.00    ((k2_mcart_1(sK2) != sK6 & k2_mcart_1(sK2) != sK5) | (k1_mcart_1(sK2) != sK4 & k1_mcart_1(sK2) != sK3)) & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 4.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f13,f29])).
% 4.10/1.00  
% 4.10/1.00  fof(f55,plain,(
% 4.10/1.00    r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 4.10/1.00    inference(cnf_transformation,[],[f30])).
% 4.10/1.00  
% 4.10/1.00  fof(f5,axiom,(
% 4.10/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/1.00  
% 4.10/1.00  fof(f45,plain,(
% 4.10/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.10/1.00    inference(cnf_transformation,[],[f5])).
% 4.10/1.00  
% 4.10/1.00  fof(f6,axiom,(
% 4.10/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/1.00  
% 4.10/1.00  fof(f46,plain,(
% 4.10/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.10/1.00    inference(cnf_transformation,[],[f6])).
% 4.10/1.00  
% 4.10/1.00  fof(f60,plain,(
% 4.10/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.10/1.00    inference(definition_unfolding,[],[f45,f46])).
% 4.10/1.00  
% 4.10/1.00  fof(f72,plain,(
% 4.10/1.00    r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)))),
% 4.10/1.00    inference(definition_unfolding,[],[f55,f60,f60])).
% 4.10/1.00  
% 4.10/1.00  fof(f9,axiom,(
% 4.10/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 4.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/1.00  
% 4.10/1.00  fof(f12,plain,(
% 4.10/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 4.10/1.00    inference(ennf_transformation,[],[f9])).
% 4.10/1.00  
% 4.10/1.00  fof(f54,plain,(
% 4.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 4.10/1.00    inference(cnf_transformation,[],[f12])).
% 4.10/1.00  
% 4.10/1.00  fof(f3,axiom,(
% 4.10/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 4.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/1.00  
% 4.10/1.00  fof(f21,plain,(
% 4.10/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 4.10/1.00    inference(nnf_transformation,[],[f3])).
% 4.10/1.00  
% 4.10/1.00  fof(f22,plain,(
% 4.10/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.10/1.00    inference(rectify,[],[f21])).
% 4.10/1.00  
% 4.10/1.00  fof(f23,plain,(
% 4.10/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 4.10/1.00    introduced(choice_axiom,[])).
% 4.10/1.00  
% 4.10/1.00  fof(f24,plain,(
% 4.10/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 4.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 4.10/1.00  
% 4.10/1.00  fof(f41,plain,(
% 4.10/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 4.10/1.00    inference(cnf_transformation,[],[f24])).
% 4.10/1.00  
% 4.10/1.00  fof(f4,axiom,(
% 4.10/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/1.00  
% 4.10/1.00  fof(f44,plain,(
% 4.10/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.10/1.00    inference(cnf_transformation,[],[f4])).
% 4.10/1.00  
% 4.10/1.00  fof(f61,plain,(
% 4.10/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 4.10/1.00    inference(definition_unfolding,[],[f44,f60])).
% 4.10/1.00  
% 4.10/1.00  fof(f64,plain,(
% 4.10/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 4.10/1.00    inference(definition_unfolding,[],[f41,f61])).
% 4.10/1.00  
% 4.10/1.00  fof(f78,plain,(
% 4.10/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 4.10/1.00    inference(equality_resolution,[],[f64])).
% 4.10/1.00  
% 4.10/1.00  fof(f79,plain,(
% 4.10/1.00    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 4.10/1.00    inference(equality_resolution,[],[f78])).
% 4.10/1.00  
% 4.10/1.00  fof(f8,axiom,(
% 4.10/1.00    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/1.00  
% 4.10/1.00  fof(f27,plain,(
% 4.10/1.00    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 4.10/1.00    inference(nnf_transformation,[],[f8])).
% 4.10/1.00  
% 4.10/1.00  fof(f28,plain,(
% 4.10/1.00    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 4.10/1.00    inference(flattening,[],[f27])).
% 4.10/1.00  
% 4.10/1.00  fof(f52,plain,(
% 4.10/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 4.10/1.00    inference(cnf_transformation,[],[f28])).
% 4.10/1.00  
% 4.10/1.00  fof(f69,plain,(
% 4.10/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 4.10/1.00    inference(definition_unfolding,[],[f52,f60,f60])).
% 4.10/1.00  
% 4.10/1.00  fof(f40,plain,(
% 4.10/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 4.10/1.00    inference(cnf_transformation,[],[f24])).
% 4.10/1.00  
% 4.10/1.00  fof(f65,plain,(
% 4.10/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 4.10/1.00    inference(definition_unfolding,[],[f40,f61])).
% 4.10/1.00  
% 4.10/1.00  fof(f80,plain,(
% 4.10/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 4.10/1.00    inference(equality_resolution,[],[f65])).
% 4.10/1.00  
% 4.10/1.00  fof(f1,axiom,(
% 4.10/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.10/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/1.00  
% 4.10/1.00  fof(f14,plain,(
% 4.10/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.10/1.00    inference(nnf_transformation,[],[f1])).
% 4.10/1.00  
% 4.10/1.00  fof(f15,plain,(
% 4.10/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.10/1.00    inference(flattening,[],[f14])).
% 4.10/1.00  
% 4.10/1.00  fof(f16,plain,(
% 4.10/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.10/1.00    inference(rectify,[],[f15])).
% 4.10/1.00  
% 4.10/1.00  fof(f17,plain,(
% 4.10/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.10/1.00    introduced(choice_axiom,[])).
% 4.10/1.00  
% 4.10/1.00  fof(f18,plain,(
% 4.10/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 4.10/1.00  
% 4.10/1.00  fof(f32,plain,(
% 4.10/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.10/1.00    inference(cnf_transformation,[],[f18])).
% 4.10/1.00  
% 4.10/1.00  fof(f74,plain,(
% 4.10/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 4.10/1.00    inference(equality_resolution,[],[f32])).
% 4.10/1.00  
% 4.10/1.00  fof(f53,plain,(
% 4.10/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 4.10/1.00    inference(cnf_transformation,[],[f12])).
% 4.10/1.00  
% 4.10/1.00  fof(f59,plain,(
% 4.10/1.00    k2_mcart_1(sK2) != sK6 | k1_mcart_1(sK2) != sK4),
% 4.10/1.00    inference(cnf_transformation,[],[f30])).
% 4.10/1.00  
% 4.10/1.00  fof(f58,plain,(
% 4.10/1.00    k2_mcart_1(sK2) != sK6 | k1_mcart_1(sK2) != sK3),
% 4.10/1.00    inference(cnf_transformation,[],[f30])).
% 4.10/1.00  
% 4.10/1.00  fof(f57,plain,(
% 4.10/1.00    k2_mcart_1(sK2) != sK5 | k1_mcart_1(sK2) != sK4),
% 4.10/1.00    inference(cnf_transformation,[],[f30])).
% 4.10/1.00  
% 4.10/1.00  fof(f56,plain,(
% 4.10/1.00    k2_mcart_1(sK2) != sK5 | k1_mcart_1(sK2) != sK3),
% 4.10/1.00    inference(cnf_transformation,[],[f30])).
% 4.10/1.00  
% 4.10/1.00  cnf(c_25,negated_conjecture,
% 4.10/1.00      ( r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) ),
% 4.10/1.00      inference(cnf_transformation,[],[f72]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4601,plain,
% 4.10/1.00      ( r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) = iProver_top ),
% 4.10/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_19,plain,
% 4.10/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 4.10/1.00      | r2_hidden(k2_mcart_1(X0),X2) ),
% 4.10/1.00      inference(cnf_transformation,[],[f54]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4603,plain,
% 4.10/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 4.10/1.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 4.10/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4795,plain,
% 4.10/1.00      ( r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
% 4.10/1.00      inference(superposition,[status(thm)],[c_4601,c_4603]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_11,plain,
% 4.10/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 4.10/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4608,plain,
% 4.10/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 4.10/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_16,plain,
% 4.10/1.00      ( r2_hidden(X0,X1)
% 4.10/1.00      | r2_hidden(X2,X1)
% 4.10/1.00      | k4_xboole_0(k2_enumset1(X0,X0,X0,X2),X1) = k2_enumset1(X0,X0,X0,X2) ),
% 4.10/1.00      inference(cnf_transformation,[],[f69]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4606,plain,
% 4.10/1.00      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) = k2_enumset1(X0,X0,X0,X1)
% 4.10/1.00      | r2_hidden(X0,X2) = iProver_top
% 4.10/1.00      | r2_hidden(X1,X2) = iProver_top ),
% 4.10/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_12,plain,
% 4.10/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 4.10/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4607,plain,
% 4.10/1.00      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 4.10/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4827,plain,
% 4.10/1.00      ( X0 = X1
% 4.10/1.00      | k4_xboole_0(k2_enumset1(X2,X2,X2,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X2,X2,X2,X1)
% 4.10/1.00      | r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 4.10/1.00      inference(superposition,[status(thm)],[c_4606,c_4607]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_6174,plain,
% 4.10/1.00      ( X0 = X1
% 4.10/1.00      | X2 = X1
% 4.10/1.00      | k4_xboole_0(k2_enumset1(X2,X2,X2,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X2,X2,X2,X0) ),
% 4.10/1.00      inference(superposition,[status(thm)],[c_4827,c_4607]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4,negated_conjecture,
% 4.10/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 4.10/1.00      inference(cnf_transformation,[],[f74]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4610,plain,
% 4.10/1.00      ( r2_hidden(X0,X1) != iProver_top
% 4.10/1.00      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 4.10/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_7336,plain,
% 4.10/1.00      ( X0 = X1
% 4.10/1.00      | X0 = X2
% 4.10/1.00      | r2_hidden(X3,k2_enumset1(X1,X1,X1,X2)) != iProver_top
% 4.10/1.00      | r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 4.10/1.00      inference(superposition,[status(thm)],[c_6174,c_4610]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_7987,plain,
% 4.10/1.00      ( X0 = X1
% 4.10/1.00      | X2 = X1
% 4.10/1.00      | r2_hidden(X1,k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
% 4.10/1.00      inference(superposition,[status(thm)],[c_4608,c_7336]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_9212,plain,
% 4.10/1.00      ( k2_mcart_1(sK2) = sK5 | k2_mcart_1(sK2) = sK6 ),
% 4.10/1.00      inference(superposition,[status(thm)],[c_4795,c_7987]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_20,plain,
% 4.10/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 4.10/1.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 4.10/1.00      inference(cnf_transformation,[],[f53]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4602,plain,
% 4.10/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 4.10/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 4.10/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_4729,plain,
% 4.10/1.00      ( r2_hidden(k1_mcart_1(sK2),k2_enumset1(sK3,sK3,sK3,sK4)) = iProver_top ),
% 4.10/1.00      inference(superposition,[status(thm)],[c_4601,c_4602]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_9211,plain,
% 4.10/1.00      ( k1_mcart_1(sK2) = sK3 | k1_mcart_1(sK2) = sK4 ),
% 4.10/1.00      inference(superposition,[status(thm)],[c_4729,c_7987]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_21,negated_conjecture,
% 4.10/1.00      ( k1_mcart_1(sK2) != sK4 | k2_mcart_1(sK2) != sK6 ),
% 4.10/1.00      inference(cnf_transformation,[],[f59]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_22,negated_conjecture,
% 4.10/1.00      ( k1_mcart_1(sK2) != sK3 | k2_mcart_1(sK2) != sK6 ),
% 4.10/1.00      inference(cnf_transformation,[],[f58]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_23,negated_conjecture,
% 4.10/1.00      ( k1_mcart_1(sK2) != sK4 | k2_mcart_1(sK2) != sK5 ),
% 4.10/1.00      inference(cnf_transformation,[],[f57]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(c_24,negated_conjecture,
% 4.10/1.00      ( k1_mcart_1(sK2) != sK3 | k2_mcart_1(sK2) != sK5 ),
% 4.10/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.10/1.00  
% 4.10/1.00  cnf(contradiction,plain,
% 4.10/1.00      ( $false ),
% 4.10/1.00      inference(minisat,[status(thm)],[c_9212,c_9211,c_21,c_22,c_23,c_24]) ).
% 4.10/1.00  
% 4.10/1.00  
% 4.10/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.10/1.00  
% 4.10/1.00  ------                               Statistics
% 4.10/1.00  
% 4.10/1.00  ------ Selected
% 4.10/1.00  
% 4.10/1.00  total_time:                             0.315
% 4.10/1.00  
%------------------------------------------------------------------------------
