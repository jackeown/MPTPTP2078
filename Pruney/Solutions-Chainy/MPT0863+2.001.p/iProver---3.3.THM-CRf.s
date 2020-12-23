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
% DateTime   : Thu Dec  3 11:57:45 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 241 expanded)
%              Number of clauses        :   27 (  45 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  259 ( 853 expanded)
%              Number of equality atoms :  130 ( 504 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))
       => ( ( k2_mcart_1(X0) = X4
            | k2_mcart_1(X0) = X3 )
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ( ( k2_mcart_1(X0) != X4
          & k2_mcart_1(X0) != X3 )
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,
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

fof(f29,plain,
    ( ( ( k2_mcart_1(sK2) != sK6
        & k2_mcart_1(sK2) != sK5 )
      | ( k1_mcart_1(sK2) != sK4
        & k1_mcart_1(sK2) != sK3 ) )
    & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f14,f28])).

fof(f52,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f67,plain,(
    r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) ),
    inference(definition_unfolding,[],[f52,f57,f57])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f73,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f61])).

fof(f74,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f73])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f75,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f1])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,
    ( k2_mcart_1(sK2) != sK6
    | k1_mcart_1(sK2) != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,
    ( k2_mcart_1(sK2) != sK6
    | k1_mcart_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,
    ( k2_mcart_1(sK2) != sK5
    | k1_mcart_1(sK2) != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,
    ( k2_mcart_1(sK2) != sK5
    | k1_mcart_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2976,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2977,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3111,plain,
    ( r2_hidden(k1_mcart_1(sK2),k2_enumset1(sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_2977])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2981,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X2)) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2979,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) = X0
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2980,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3167,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X0)) = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2979,c_2980])).

cnf(c_5313,plain,
    ( X0 = X1
    | X2 = X0
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X2,X2,X2,X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_3167,c_2980])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2983,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5432,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X3,k2_enumset1(X1,X1,X1,X1)) != iProver_top
    | r2_hidden(X3,k2_enumset1(X2,X2,X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5313,c_2983])).

cnf(c_6771,plain,
    ( X0 = X1
    | X2 = X0
    | r2_hidden(X0,k2_enumset1(X2,X2,X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_5432])).

cnf(c_7335,plain,
    ( k1_mcart_1(sK2) = sK3
    | k1_mcart_1(sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_3111,c_6771])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2978,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3119,plain,
    ( r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_2978])).

cnf(c_7334,plain,
    ( k2_mcart_1(sK2) = sK5
    | k2_mcart_1(sK2) = sK6 ),
    inference(superposition,[status(thm)],[c_3119,c_6771])).

cnf(c_19,negated_conjecture,
    ( k1_mcart_1(sK2) != sK4
    | k2_mcart_1(sK2) != sK6 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,negated_conjecture,
    ( k1_mcart_1(sK2) != sK3
    | k2_mcart_1(sK2) != sK6 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( k1_mcart_1(sK2) != sK4
    | k2_mcart_1(sK2) != sK5 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_22,negated_conjecture,
    ( k1_mcart_1(sK2) != sK3
    | k2_mcart_1(sK2) != sK5 ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7335,c_7334,c_19,c_20,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 20:19:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.67/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/0.97  
% 3.67/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/0.97  
% 3.67/0.97  ------  iProver source info
% 3.67/0.97  
% 3.67/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.67/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/0.97  git: non_committed_changes: false
% 3.67/0.97  git: last_make_outside_of_git: false
% 3.67/0.97  
% 3.67/0.97  ------ 
% 3.67/0.97  ------ Parsing...
% 3.67/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  ------ Proving...
% 3.67/0.97  ------ Problem Properties 
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  clauses                                 23
% 3.67/0.97  conjectures                             6
% 3.67/0.97  EPR                                     2
% 3.67/0.97  Horn                                    17
% 3.67/0.97  unary                                   3
% 3.67/0.97  binary                                  11
% 3.67/0.97  lits                                    53
% 3.67/0.97  lits eq                                 18
% 3.67/0.97  fd_pure                                 0
% 3.67/0.97  fd_pseudo                               0
% 3.67/0.97  fd_cond                                 0
% 3.67/0.97  fd_pseudo_cond                          6
% 3.67/0.97  AC symbols                              0
% 3.67/0.97  
% 3.67/0.97  ------ Input Options Time Limit: Unbounded
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing...
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.67/0.97  Current options:
% 3.67/0.97  ------ 
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing...
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/0.97  
% 3.67/0.97  ------ Proving...
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  % SZS status Theorem for theBenchmark.p
% 3.67/0.97  
% 3.67/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/0.97  
% 3.67/0.97  fof(f10,conjecture,(
% 3.67/0.97    ! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f11,negated_conjecture,(
% 3.67/0.97    ~! [X0,X1,X2,X3,X4] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))) => ((k2_mcart_1(X0) = X4 | k2_mcart_1(X0) = X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 3.67/0.97    inference(negated_conjecture,[],[f10])).
% 3.67/0.97  
% 3.67/0.97  fof(f14,plain,(
% 3.67/0.97    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4))))),
% 3.67/0.97    inference(ennf_transformation,[],[f11])).
% 3.67/0.97  
% 3.67/0.97  fof(f28,plain,(
% 3.67/0.97    ? [X0,X1,X2,X3,X4] : (((k2_mcart_1(X0) != X4 & k2_mcart_1(X0) != X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k2_tarski(X3,X4)))) => (((k2_mcart_1(sK2) != sK6 & k2_mcart_1(sK2) != sK5) | (k1_mcart_1(sK2) != sK4 & k1_mcart_1(sK2) != sK3)) & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))))),
% 3.67/0.97    introduced(choice_axiom,[])).
% 3.67/0.97  
% 3.67/0.97  fof(f29,plain,(
% 3.67/0.97    ((k2_mcart_1(sK2) != sK6 & k2_mcart_1(sK2) != sK5) | (k1_mcart_1(sK2) != sK4 & k1_mcart_1(sK2) != sK3)) & r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 3.67/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f14,f28])).
% 3.67/0.97  
% 3.67/0.97  fof(f52,plain,(
% 3.67/0.97    r2_hidden(sK2,k2_zfmisc_1(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 3.67/0.97    inference(cnf_transformation,[],[f29])).
% 3.67/0.97  
% 3.67/0.97  fof(f5,axiom,(
% 3.67/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f44,plain,(
% 3.67/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f5])).
% 3.67/0.97  
% 3.67/0.97  fof(f6,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f45,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f6])).
% 3.67/0.97  
% 3.67/0.97  fof(f57,plain,(
% 3.67/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.67/0.97    inference(definition_unfolding,[],[f44,f45])).
% 3.67/0.97  
% 3.67/0.97  fof(f67,plain,(
% 3.67/0.97    r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)))),
% 3.67/0.97    inference(definition_unfolding,[],[f52,f57,f57])).
% 3.67/0.97  
% 3.67/0.97  fof(f9,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f13,plain,(
% 3.67/0.97    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.67/0.97    inference(ennf_transformation,[],[f9])).
% 3.67/0.97  
% 3.67/0.97  fof(f50,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f13])).
% 3.67/0.97  
% 3.67/0.97  fof(f3,axiom,(
% 3.67/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f22,plain,(
% 3.67/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.67/0.97    inference(nnf_transformation,[],[f3])).
% 3.67/0.97  
% 3.67/0.97  fof(f23,plain,(
% 3.67/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.67/0.97    inference(rectify,[],[f22])).
% 3.67/0.97  
% 3.67/0.97  fof(f24,plain,(
% 3.67/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.67/0.97    introduced(choice_axiom,[])).
% 3.67/0.97  
% 3.67/0.97  fof(f25,plain,(
% 3.67/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.67/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 3.67/0.97  
% 3.67/0.97  fof(f40,plain,(
% 3.67/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.67/0.97    inference(cnf_transformation,[],[f25])).
% 3.67/0.97  
% 3.67/0.97  fof(f4,axiom,(
% 3.67/0.97    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f43,plain,(
% 3.67/0.97    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f4])).
% 3.67/0.97  
% 3.67/0.97  fof(f58,plain,(
% 3.67/0.97    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.67/0.97    inference(definition_unfolding,[],[f43,f57])).
% 3.67/0.97  
% 3.67/0.97  fof(f61,plain,(
% 3.67/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.67/0.97    inference(definition_unfolding,[],[f40,f58])).
% 3.67/0.97  
% 3.67/0.97  fof(f73,plain,(
% 3.67/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 3.67/0.97    inference(equality_resolution,[],[f61])).
% 3.67/0.97  
% 3.67/0.97  fof(f74,plain,(
% 3.67/0.97    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 3.67/0.97    inference(equality_resolution,[],[f73])).
% 3.67/0.97  
% 3.67/0.97  fof(f7,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f12,plain,(
% 3.67/0.97    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 3.67/0.97    inference(ennf_transformation,[],[f7])).
% 3.67/0.97  
% 3.67/0.97  fof(f46,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.67/0.97    inference(cnf_transformation,[],[f12])).
% 3.67/0.97  
% 3.67/0.97  fof(f63,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 3.67/0.97    inference(definition_unfolding,[],[f46,f57])).
% 3.67/0.97  
% 3.67/0.97  fof(f39,plain,(
% 3.67/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.67/0.97    inference(cnf_transformation,[],[f25])).
% 3.67/0.97  
% 3.67/0.97  fof(f62,plain,(
% 3.67/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.67/0.97    inference(definition_unfolding,[],[f39,f58])).
% 3.67/0.97  
% 3.67/0.97  fof(f75,plain,(
% 3.67/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.67/0.97    inference(equality_resolution,[],[f62])).
% 3.67/0.97  
% 3.67/0.97  fof(f1,axiom,(
% 3.67/0.97    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.67/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/0.97  
% 3.67/0.97  fof(f15,plain,(
% 3.67/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.67/0.97    inference(nnf_transformation,[],[f1])).
% 3.67/0.97  
% 3.67/0.97  fof(f16,plain,(
% 3.67/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.67/0.97    inference(flattening,[],[f15])).
% 3.67/0.97  
% 3.67/0.97  fof(f17,plain,(
% 3.67/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.67/0.97    inference(rectify,[],[f16])).
% 3.67/0.97  
% 3.67/0.97  fof(f18,plain,(
% 3.67/0.97    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.67/0.97    introduced(choice_axiom,[])).
% 3.67/0.97  
% 3.67/0.97  fof(f19,plain,(
% 3.67/0.97    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.67/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.67/0.97  
% 3.67/0.97  fof(f31,plain,(
% 3.67/0.97    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.67/0.97    inference(cnf_transformation,[],[f19])).
% 3.67/0.97  
% 3.67/0.97  fof(f69,plain,(
% 3.67/0.97    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.67/0.97    inference(equality_resolution,[],[f31])).
% 3.67/0.97  
% 3.67/0.97  fof(f51,plain,(
% 3.67/0.97    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.67/0.97    inference(cnf_transformation,[],[f13])).
% 3.67/0.97  
% 3.67/0.97  fof(f56,plain,(
% 3.67/0.97    k2_mcart_1(sK2) != sK6 | k1_mcart_1(sK2) != sK4),
% 3.67/0.97    inference(cnf_transformation,[],[f29])).
% 3.67/0.97  
% 3.67/0.97  fof(f55,plain,(
% 3.67/0.97    k2_mcart_1(sK2) != sK6 | k1_mcart_1(sK2) != sK3),
% 3.67/0.97    inference(cnf_transformation,[],[f29])).
% 3.67/0.97  
% 3.67/0.97  fof(f54,plain,(
% 3.67/0.97    k2_mcart_1(sK2) != sK5 | k1_mcart_1(sK2) != sK4),
% 3.67/0.97    inference(cnf_transformation,[],[f29])).
% 3.67/0.97  
% 3.67/0.97  fof(f53,plain,(
% 3.67/0.97    k2_mcart_1(sK2) != sK5 | k1_mcart_1(sK2) != sK3),
% 3.67/0.97    inference(cnf_transformation,[],[f29])).
% 3.67/0.97  
% 3.67/0.97  cnf(c_23,negated_conjecture,
% 3.67/0.97      ( r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) ),
% 3.67/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2976,plain,
% 3.67/0.97      ( r2_hidden(sK2,k2_zfmisc_1(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_18,plain,
% 3.67/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.67/0.97      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.67/0.97      inference(cnf_transformation,[],[f50]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2977,plain,
% 3.67/0.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.67/0.97      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3111,plain,
% 3.67/0.97      ( r2_hidden(k1_mcart_1(sK2),k2_enumset1(sK3,sK3,sK3,sK4)) = iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_2976,c_2977]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_11,plain,
% 3.67/0.97      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.67/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2981,plain,
% 3.67/0.97      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_13,plain,
% 3.67/0.97      ( r2_hidden(X0,X1)
% 3.67/0.97      | r2_hidden(X2,X1)
% 3.67/0.97      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X2)) = X1 ),
% 3.67/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2979,plain,
% 3.67/0.97      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X2)) = X0
% 3.67/0.97      | r2_hidden(X1,X0) = iProver_top
% 3.67/0.97      | r2_hidden(X2,X0) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_12,plain,
% 3.67/0.97      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.67/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2980,plain,
% 3.67/0.97      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3167,plain,
% 3.67/0.97      ( X0 = X1
% 3.67/0.97      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X0)) = k2_enumset1(X1,X1,X1,X1)
% 3.67/0.97      | r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) = iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_2979,c_2980]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_5313,plain,
% 3.67/0.97      ( X0 = X1
% 3.67/0.97      | X2 = X0
% 3.67/0.97      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X2,X2,X2,X1)) = k2_enumset1(X0,X0,X0,X0) ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_3167,c_2980]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_4,negated_conjecture,
% 3.67/0.97      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.67/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2983,plain,
% 3.67/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.67/0.97      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_5432,plain,
% 3.67/0.97      ( X0 = X1
% 3.67/0.97      | X2 = X1
% 3.67/0.97      | r2_hidden(X3,k2_enumset1(X1,X1,X1,X1)) != iProver_top
% 3.67/0.97      | r2_hidden(X3,k2_enumset1(X2,X2,X2,X0)) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_5313,c_2983]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_6771,plain,
% 3.67/0.97      ( X0 = X1
% 3.67/0.97      | X2 = X0
% 3.67/0.97      | r2_hidden(X0,k2_enumset1(X2,X2,X2,X1)) != iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_2981,c_5432]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7335,plain,
% 3.67/0.97      ( k1_mcart_1(sK2) = sK3 | k1_mcart_1(sK2) = sK4 ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_3111,c_6771]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_17,plain,
% 3.67/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.67/0.97      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.67/0.97      inference(cnf_transformation,[],[f51]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_2978,plain,
% 3.67/0.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.67/0.97      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.67/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_3119,plain,
% 3.67/0.97      ( r2_hidden(k2_mcart_1(sK2),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_2976,c_2978]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_7334,plain,
% 3.67/0.97      ( k2_mcart_1(sK2) = sK5 | k2_mcart_1(sK2) = sK6 ),
% 3.67/0.97      inference(superposition,[status(thm)],[c_3119,c_6771]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_19,negated_conjecture,
% 3.67/0.97      ( k1_mcart_1(sK2) != sK4 | k2_mcart_1(sK2) != sK6 ),
% 3.67/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_20,negated_conjecture,
% 3.67/0.97      ( k1_mcart_1(sK2) != sK3 | k2_mcart_1(sK2) != sK6 ),
% 3.67/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_21,negated_conjecture,
% 3.67/0.97      ( k1_mcart_1(sK2) != sK4 | k2_mcart_1(sK2) != sK5 ),
% 3.67/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(c_22,negated_conjecture,
% 3.67/0.97      ( k1_mcart_1(sK2) != sK3 | k2_mcart_1(sK2) != sK5 ),
% 3.67/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.67/0.97  
% 3.67/0.97  cnf(contradiction,plain,
% 3.67/0.97      ( $false ),
% 3.67/0.97      inference(minisat,[status(thm)],[c_7335,c_7334,c_19,c_20,c_21,c_22]) ).
% 3.67/0.97  
% 3.67/0.97  
% 3.67/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/0.97  
% 3.67/0.97  ------                               Statistics
% 3.67/0.97  
% 3.67/0.97  ------ Selected
% 3.67/0.97  
% 3.67/0.97  total_time:                             0.224
% 3.67/0.97  
%------------------------------------------------------------------------------
