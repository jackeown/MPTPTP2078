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
% DateTime   : Thu Dec  3 11:57:27 EST 2020

% Result     : Theorem 27.75s
% Output     : CNFRefutation 27.75s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 128 expanded)
%              Number of clauses        :   24 (  25 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  200 ( 300 expanded)
%              Number of equality atoms :   68 ( 125 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK1),sK3)
        | k1_mcart_1(sK1) != sK2 )
      & r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK1),sK3)
      | k1_mcart_1(sK1) != sK2 )
    & r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f22])).

fof(f41,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f51,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f50,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f55,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f48])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),sK3)
    | k1_mcart_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_446,plain,
    ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_448,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_676,plain,
    ( r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_448])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_450,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_453,plain,
    ( X0 = X1
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_454,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1321,plain,
    ( X0 = X1
    | k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_454])).

cnf(c_2535,plain,
    ( X0 = X1
    | k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X0,X0,X0,X0))) = k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X0,X0,X0,X0)) ),
    inference(superposition,[status(thm)],[c_450,c_1321])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_456,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_84518,plain,
    ( X0 = X1
    | r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) != iProver_top
    | r2_hidden(X2,k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2535,c_456])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_452,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_84572,plain,
    ( X0 = X1
    | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_84518,c_452])).

cnf(c_85098,plain,
    ( k1_mcart_1(sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_676,c_84572])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_514,plain,
    ( r2_hidden(k2_mcart_1(sK1),sK3)
    | ~ r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(sK1),sK3)
    | k1_mcart_1(sK1) != sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_85098,c_514,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.75/4.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.75/4.00  
% 27.75/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.75/4.00  
% 27.75/4.00  ------  iProver source info
% 27.75/4.00  
% 27.75/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.75/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.75/4.00  git: non_committed_changes: false
% 27.75/4.00  git: last_make_outside_of_git: false
% 27.75/4.00  
% 27.75/4.00  ------ 
% 27.75/4.00  ------ Parsing...
% 27.75/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.75/4.00  
% 27.75/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.75/4.00  ------ Proving...
% 27.75/4.00  ------ Problem Properties 
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  clauses                                 15
% 27.75/4.00  conjectures                             2
% 27.75/4.00  EPR                                     0
% 27.75/4.00  Horn                                    12
% 27.75/4.00  unary                                   3
% 27.75/4.00  binary                                  7
% 27.75/4.00  lits                                    33
% 27.75/4.00  lits eq                                 6
% 27.75/4.00  fd_pure                                 0
% 27.75/4.00  fd_pseudo                               0
% 27.75/4.00  fd_cond                                 0
% 27.75/4.00  fd_pseudo_cond                          4
% 27.75/4.00  AC symbols                              0
% 27.75/4.00  
% 27.75/4.00  ------ Input Options Time Limit: Unbounded
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  ------ 
% 27.75/4.00  Current options:
% 27.75/4.00  ------ 
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  ------ Proving...
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  % SZS status Theorem for theBenchmark.p
% 27.75/4.00  
% 27.75/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.75/4.00  
% 27.75/4.00  fof(f10,conjecture,(
% 27.75/4.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f11,negated_conjecture,(
% 27.75/4.00    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 27.75/4.00    inference(negated_conjecture,[],[f10])).
% 27.75/4.00  
% 27.75/4.00  fof(f14,plain,(
% 27.75/4.00    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 27.75/4.00    inference(ennf_transformation,[],[f11])).
% 27.75/4.00  
% 27.75/4.00  fof(f22,plain,(
% 27.75/4.00    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) => ((~r2_hidden(k2_mcart_1(sK1),sK3) | k1_mcart_1(sK1) != sK2) & r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 27.75/4.00    introduced(choice_axiom,[])).
% 27.75/4.00  
% 27.75/4.00  fof(f23,plain,(
% 27.75/4.00    (~r2_hidden(k2_mcart_1(sK1),sK3) | k1_mcart_1(sK1) != sK2) & r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 27.75/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f22])).
% 27.75/4.00  
% 27.75/4.00  fof(f41,plain,(
% 27.75/4.00    r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 27.75/4.00    inference(cnf_transformation,[],[f23])).
% 27.75/4.00  
% 27.75/4.00  fof(f2,axiom,(
% 27.75/4.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f30,plain,(
% 27.75/4.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f2])).
% 27.75/4.00  
% 27.75/4.00  fof(f3,axiom,(
% 27.75/4.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f31,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f3])).
% 27.75/4.00  
% 27.75/4.00  fof(f4,axiom,(
% 27.75/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f32,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f4])).
% 27.75/4.00  
% 27.75/4.00  fof(f43,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 27.75/4.00    inference(definition_unfolding,[],[f31,f32])).
% 27.75/4.00  
% 27.75/4.00  fof(f44,plain,(
% 27.75/4.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 27.75/4.00    inference(definition_unfolding,[],[f30,f43])).
% 27.75/4.00  
% 27.75/4.00  fof(f51,plain,(
% 27.75/4.00    r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))),
% 27.75/4.00    inference(definition_unfolding,[],[f41,f44])).
% 27.75/4.00  
% 27.75/4.00  fof(f9,axiom,(
% 27.75/4.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f13,plain,(
% 27.75/4.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 27.75/4.00    inference(ennf_transformation,[],[f9])).
% 27.75/4.00  
% 27.75/4.00  fof(f39,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f13])).
% 27.75/4.00  
% 27.75/4.00  fof(f8,axiom,(
% 27.75/4.00    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f38,plain,(
% 27.75/4.00    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f8])).
% 27.75/4.00  
% 27.75/4.00  fof(f7,axiom,(
% 27.75/4.00    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f37,plain,(
% 27.75/4.00    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f7])).
% 27.75/4.00  
% 27.75/4.00  fof(f45,plain,(
% 27.75/4.00    ( ! [X0] : (k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) = k1_ordinal1(X0)) )),
% 27.75/4.00    inference(definition_unfolding,[],[f37,f44])).
% 27.75/4.00  
% 27.75/4.00  fof(f50,plain,(
% 27.75/4.00    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)))) )),
% 27.75/4.00    inference(definition_unfolding,[],[f38,f45])).
% 27.75/4.00  
% 27.75/4.00  fof(f6,axiom,(
% 27.75/4.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f20,plain,(
% 27.75/4.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 27.75/4.00    inference(nnf_transformation,[],[f6])).
% 27.75/4.00  
% 27.75/4.00  fof(f21,plain,(
% 27.75/4.00    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 27.75/4.00    inference(flattening,[],[f20])).
% 27.75/4.00  
% 27.75/4.00  fof(f36,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f21])).
% 27.75/4.00  
% 27.75/4.00  fof(f47,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 27.75/4.00    inference(definition_unfolding,[],[f36,f44])).
% 27.75/4.00  
% 27.75/4.00  fof(f5,axiom,(
% 27.75/4.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f12,plain,(
% 27.75/4.00    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 27.75/4.00    inference(ennf_transformation,[],[f5])).
% 27.75/4.00  
% 27.75/4.00  fof(f33,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 27.75/4.00    inference(cnf_transformation,[],[f12])).
% 27.75/4.00  
% 27.75/4.00  fof(f46,plain,(
% 27.75/4.00    ( ! [X0,X1] : (k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 27.75/4.00    inference(definition_unfolding,[],[f33,f44])).
% 27.75/4.00  
% 27.75/4.00  fof(f1,axiom,(
% 27.75/4.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 27.75/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.75/4.00  
% 27.75/4.00  fof(f15,plain,(
% 27.75/4.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.75/4.00    inference(nnf_transformation,[],[f1])).
% 27.75/4.00  
% 27.75/4.00  fof(f16,plain,(
% 27.75/4.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.75/4.00    inference(flattening,[],[f15])).
% 27.75/4.00  
% 27.75/4.00  fof(f17,plain,(
% 27.75/4.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.75/4.00    inference(rectify,[],[f16])).
% 27.75/4.00  
% 27.75/4.00  fof(f18,plain,(
% 27.75/4.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 27.75/4.00    introduced(choice_axiom,[])).
% 27.75/4.00  
% 27.75/4.00  fof(f19,plain,(
% 27.75/4.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.75/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 27.75/4.00  
% 27.75/4.00  fof(f25,plain,(
% 27.75/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 27.75/4.00    inference(cnf_transformation,[],[f19])).
% 27.75/4.00  
% 27.75/4.00  fof(f53,plain,(
% 27.75/4.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 27.75/4.00    inference(equality_resolution,[],[f25])).
% 27.75/4.00  
% 27.75/4.00  fof(f35,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f21])).
% 27.75/4.00  
% 27.75/4.00  fof(f48,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 27.75/4.00    inference(definition_unfolding,[],[f35,f44])).
% 27.75/4.00  
% 27.75/4.00  fof(f55,plain,(
% 27.75/4.00    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 27.75/4.00    inference(equality_resolution,[],[f48])).
% 27.75/4.00  
% 27.75/4.00  fof(f40,plain,(
% 27.75/4.00    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 27.75/4.00    inference(cnf_transformation,[],[f13])).
% 27.75/4.00  
% 27.75/4.00  fof(f42,plain,(
% 27.75/4.00    ~r2_hidden(k2_mcart_1(sK1),sK3) | k1_mcart_1(sK1) != sK2),
% 27.75/4.00    inference(cnf_transformation,[],[f23])).
% 27.75/4.00  
% 27.75/4.00  cnf(c_14,negated_conjecture,
% 27.75/4.00      ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 27.75/4.00      inference(cnf_transformation,[],[f51]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_446,plain,
% 27.75/4.00      ( r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
% 27.75/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_12,plain,
% 27.75/4.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 27.75/4.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 27.75/4.00      inference(cnf_transformation,[],[f39]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_448,plain,
% 27.75/4.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 27.75/4.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 27.75/4.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_676,plain,
% 27.75/4.00      ( r2_hidden(k1_mcart_1(sK1),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_446,c_448]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_10,plain,
% 27.75/4.00      ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) ),
% 27.75/4.00      inference(cnf_transformation,[],[f50]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_450,plain,
% 27.75/4.00      ( r2_hidden(X0,k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 27.75/4.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_7,plain,
% 27.75/4.00      ( ~ r2_hidden(X0,X1)
% 27.75/4.00      | r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
% 27.75/4.00      | X2 = X0 ),
% 27.75/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_453,plain,
% 27.75/4.00      ( X0 = X1
% 27.75/4.00      | r2_hidden(X1,X2) != iProver_top
% 27.75/4.00      | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 27.75/4.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_6,plain,
% 27.75/4.00      ( ~ r2_hidden(X0,X1)
% 27.75/4.00      | k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1 ),
% 27.75/4.00      inference(cnf_transformation,[],[f46]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_454,plain,
% 27.75/4.00      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1
% 27.75/4.00      | r2_hidden(X0,X1) != iProver_top ),
% 27.75/4.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_1321,plain,
% 27.75/4.00      ( X0 = X1
% 27.75/4.00      | k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) = k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))
% 27.75/4.00      | r2_hidden(X0,X2) != iProver_top ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_453,c_454]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_2535,plain,
% 27.75/4.00      ( X0 = X1
% 27.75/4.00      | k2_xboole_0(k2_enumset1(X1,X1,X1,X1),k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X0,X0,X0,X0))) = k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X0,X0,X0,X0)) ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_450,c_1321]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_4,plain,
% 27.75/4.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 27.75/4.00      inference(cnf_transformation,[],[f53]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_456,plain,
% 27.75/4.00      ( r2_hidden(X0,X1) != iProver_top
% 27.75/4.00      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 27.75/4.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_84518,plain,
% 27.75/4.00      ( X0 = X1
% 27.75/4.00      | r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) != iProver_top
% 27.75/4.00      | r2_hidden(X2,k4_xboole_0(k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X0,X0,X0,X0))) = iProver_top ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_2535,c_456]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_8,plain,
% 27.75/4.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) ),
% 27.75/4.00      inference(cnf_transformation,[],[f55]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_452,plain,
% 27.75/4.00      ( r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 27.75/4.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_84572,plain,
% 27.75/4.00      ( X0 = X1 | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_84518,c_452]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_85098,plain,
% 27.75/4.00      ( k1_mcart_1(sK1) = sK2 ),
% 27.75/4.00      inference(superposition,[status(thm)],[c_676,c_84572]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_11,plain,
% 27.75/4.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 27.75/4.00      | r2_hidden(k2_mcart_1(X0),X2) ),
% 27.75/4.00      inference(cnf_transformation,[],[f40]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_514,plain,
% 27.75/4.00      ( r2_hidden(k2_mcart_1(sK1),sK3)
% 27.75/4.00      | ~ r2_hidden(sK1,k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
% 27.75/4.00      inference(instantiation,[status(thm)],[c_11]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(c_13,negated_conjecture,
% 27.75/4.00      ( ~ r2_hidden(k2_mcart_1(sK1),sK3) | k1_mcart_1(sK1) != sK2 ),
% 27.75/4.00      inference(cnf_transformation,[],[f42]) ).
% 27.75/4.00  
% 27.75/4.00  cnf(contradiction,plain,
% 27.75/4.00      ( $false ),
% 27.75/4.00      inference(minisat,[status(thm)],[c_85098,c_514,c_13,c_14]) ).
% 27.75/4.00  
% 27.75/4.00  
% 27.75/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.75/4.00  
% 27.75/4.00  ------                               Statistics
% 27.75/4.00  
% 27.75/4.00  ------ Selected
% 27.75/4.00  
% 27.75/4.00  total_time:                             3.41
% 27.75/4.00  
%------------------------------------------------------------------------------
