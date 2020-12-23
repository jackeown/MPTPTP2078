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
% DateTime   : Thu Dec  3 11:35:34 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 429 expanded)
%              Number of clauses        :   38 (  75 expanded)
%              Number of leaves         :   13 ( 118 expanded)
%              Depth                    :   15
%              Number of atoms          :  285 (1459 expanded)
%              Number of equality atoms :  137 ( 745 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f76])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK4(X0,X1) = X0
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f69,f77])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f114,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f96])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK6,sK5)
        | k4_xboole_0(sK5,k1_tarski(sK6)) != sK5 )
      & ( ~ r2_hidden(sK6,sK5)
        | k4_xboole_0(sK5,k1_tarski(sK6)) = sK5 ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( r2_hidden(sK6,sK5)
      | k4_xboole_0(sK5,k1_tarski(sK6)) != sK5 )
    & ( ~ r2_hidden(sK6,sK5)
      | k4_xboole_0(sK5,k1_tarski(sK6)) = sK5 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f40])).

fof(f75,plain,
    ( r2_hidden(sK6,sK5)
    | k4_xboole_0(sK5,k1_tarski(sK6)) != sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f97,plain,
    ( r2_hidden(sK6,sK5)
    | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) != sK5 ),
    inference(definition_unfolding,[],[f75,f57,f77])).

fof(f74,plain,
    ( ~ r2_hidden(sK6,sK5)
    | k4_xboole_0(sK5,k1_tarski(sK6)) = sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,
    ( ~ r2_hidden(sK6,sK5)
    | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
    inference(definition_unfolding,[],[f74,f57,f77])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f112,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f95])).

fof(f113,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f112])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f57])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f82])).

cnf(c_25,plain,
    ( r2_hidden(sK4(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK4(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_927,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK4(X0,X1) = X0
    | r2_hidden(sK4(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_925,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2422,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(X1,X1,X1,X1)
    | sK4(X1,k2_enumset1(X0,X0,X0,X0)) = X1
    | sK4(X1,k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_927,c_925])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK6,sK5)
    | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) != sK5 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_924,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) != sK5
    | r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10733,plain,
    ( sK4(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = X0
    | sK4(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = sK6
    | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(X0,X0,X0,X0))) != sK5
    | r2_hidden(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_924])).

cnf(c_29,negated_conjecture,
    ( ~ r2_hidden(sK6,sK5)
    | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_31,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) != sK5
    | r2_hidden(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_33,plain,
    ( ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_26,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_36,plain,
    ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_983,plain,
    ( r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),sK5)
    | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_981,plain,
    ( r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),k2_enumset1(sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),sK5)
    | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_368,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1167,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK6,X2)
    | X2 != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_368])).

cnf(c_1392,plain,
    ( ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),sK5)
    | r2_hidden(sK6,X0)
    | X0 != sK5
    | sK6 != sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_1581,plain,
    ( ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),sK5)
    | r2_hidden(sK6,sK5)
    | sK5 != sK5
    | sK6 != sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_365,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2368,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_366,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2508,plain,
    ( sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) != X0
    | sK6 != X0
    | sK6 = sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_2509,plain,
    ( sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) != sK6
    | sK6 = sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2508])).

cnf(c_6413,plain,
    ( ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),k2_enumset1(X0,X0,X0,X0))
    | sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_6415,plain,
    ( ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),k2_enumset1(sK6,sK6,sK6,sK6))
    | sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) = sK6 ),
    inference(instantiation,[status(thm)],[c_6413])).

cnf(c_11220,plain,
    ( r2_hidden(sK6,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10733,c_29,c_31,c_33,c_36,c_983,c_981,c_1581,c_2368,c_2509,c_6415])).

cnf(c_923,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11224,plain,
    ( k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
    inference(superposition,[status(thm)],[c_11220,c_923])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_940,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_11347,plain,
    ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11224,c_940])).

cnf(c_11351,plain,
    ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK6,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11347])).

cnf(c_35,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_37,plain,
    ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11351,c_11220,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:41:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.29/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.29/0.98  
% 3.29/0.98  ------  iProver source info
% 3.29/0.98  
% 3.29/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.29/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.29/0.98  git: non_committed_changes: false
% 3.29/0.98  git: last_make_outside_of_git: false
% 3.29/0.98  
% 3.29/0.98  ------ 
% 3.29/0.98  
% 3.29/0.98  ------ Input Options
% 3.29/0.98  
% 3.29/0.98  --out_options                           all
% 3.29/0.98  --tptp_safe_out                         true
% 3.29/0.98  --problem_path                          ""
% 3.29/0.98  --include_path                          ""
% 3.29/0.98  --clausifier                            res/vclausify_rel
% 3.29/0.98  --clausifier_options                    ""
% 3.29/0.98  --stdin                                 false
% 3.29/0.98  --stats_out                             all
% 3.29/0.98  
% 3.29/0.98  ------ General Options
% 3.29/0.98  
% 3.29/0.98  --fof                                   false
% 3.29/0.98  --time_out_real                         305.
% 3.29/0.98  --time_out_virtual                      -1.
% 3.29/0.98  --symbol_type_check                     false
% 3.29/0.98  --clausify_out                          false
% 3.29/0.98  --sig_cnt_out                           false
% 3.29/0.98  --trig_cnt_out                          false
% 3.29/0.98  --trig_cnt_out_tolerance                1.
% 3.29/0.98  --trig_cnt_out_sk_spl                   false
% 3.29/0.98  --abstr_cl_out                          false
% 3.29/0.98  
% 3.29/0.98  ------ Global Options
% 3.29/0.98  
% 3.29/0.98  --schedule                              default
% 3.29/0.98  --add_important_lit                     false
% 3.29/0.98  --prop_solver_per_cl                    1000
% 3.29/0.98  --min_unsat_core                        false
% 3.29/0.98  --soft_assumptions                      false
% 3.29/0.98  --soft_lemma_size                       3
% 3.29/0.98  --prop_impl_unit_size                   0
% 3.29/0.98  --prop_impl_unit                        []
% 3.29/0.98  --share_sel_clauses                     true
% 3.29/0.98  --reset_solvers                         false
% 3.29/0.98  --bc_imp_inh                            [conj_cone]
% 3.29/0.98  --conj_cone_tolerance                   3.
% 3.29/0.98  --extra_neg_conj                        none
% 3.29/0.98  --large_theory_mode                     true
% 3.29/0.98  --prolific_symb_bound                   200
% 3.29/0.98  --lt_threshold                          2000
% 3.29/0.98  --clause_weak_htbl                      true
% 3.29/0.98  --gc_record_bc_elim                     false
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing Options
% 3.29/0.98  
% 3.29/0.98  --preprocessing_flag                    true
% 3.29/0.98  --time_out_prep_mult                    0.1
% 3.29/0.98  --splitting_mode                        input
% 3.29/0.98  --splitting_grd                         true
% 3.29/0.98  --splitting_cvd                         false
% 3.29/0.98  --splitting_cvd_svl                     false
% 3.29/0.98  --splitting_nvd                         32
% 3.29/0.98  --sub_typing                            true
% 3.29/0.98  --prep_gs_sim                           true
% 3.29/0.98  --prep_unflatten                        true
% 3.29/0.98  --prep_res_sim                          true
% 3.29/0.98  --prep_upred                            true
% 3.29/0.98  --prep_sem_filter                       exhaustive
% 3.29/0.98  --prep_sem_filter_out                   false
% 3.29/0.98  --pred_elim                             true
% 3.29/0.98  --res_sim_input                         true
% 3.29/0.98  --eq_ax_congr_red                       true
% 3.29/0.98  --pure_diseq_elim                       true
% 3.29/0.98  --brand_transform                       false
% 3.29/0.98  --non_eq_to_eq                          false
% 3.29/0.98  --prep_def_merge                        true
% 3.29/0.98  --prep_def_merge_prop_impl              false
% 3.29/0.98  --prep_def_merge_mbd                    true
% 3.29/0.98  --prep_def_merge_tr_red                 false
% 3.29/0.98  --prep_def_merge_tr_cl                  false
% 3.29/0.98  --smt_preprocessing                     true
% 3.29/0.98  --smt_ac_axioms                         fast
% 3.29/0.98  --preprocessed_out                      false
% 3.29/0.98  --preprocessed_stats                    false
% 3.29/0.98  
% 3.29/0.98  ------ Abstraction refinement Options
% 3.29/0.98  
% 3.29/0.98  --abstr_ref                             []
% 3.29/0.98  --abstr_ref_prep                        false
% 3.29/0.98  --abstr_ref_until_sat                   false
% 3.29/0.98  --abstr_ref_sig_restrict                funpre
% 3.29/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.98  --abstr_ref_under                       []
% 3.29/0.98  
% 3.29/0.98  ------ SAT Options
% 3.29/0.98  
% 3.29/0.98  --sat_mode                              false
% 3.29/0.98  --sat_fm_restart_options                ""
% 3.29/0.98  --sat_gr_def                            false
% 3.29/0.98  --sat_epr_types                         true
% 3.29/0.98  --sat_non_cyclic_types                  false
% 3.29/0.98  --sat_finite_models                     false
% 3.29/0.98  --sat_fm_lemmas                         false
% 3.29/0.98  --sat_fm_prep                           false
% 3.29/0.98  --sat_fm_uc_incr                        true
% 3.29/0.98  --sat_out_model                         small
% 3.29/0.98  --sat_out_clauses                       false
% 3.29/0.98  
% 3.29/0.98  ------ QBF Options
% 3.29/0.98  
% 3.29/0.98  --qbf_mode                              false
% 3.29/0.98  --qbf_elim_univ                         false
% 3.29/0.98  --qbf_dom_inst                          none
% 3.29/0.98  --qbf_dom_pre_inst                      false
% 3.29/0.98  --qbf_sk_in                             false
% 3.29/0.98  --qbf_pred_elim                         true
% 3.29/0.98  --qbf_split                             512
% 3.29/0.98  
% 3.29/0.98  ------ BMC1 Options
% 3.29/0.98  
% 3.29/0.98  --bmc1_incremental                      false
% 3.29/0.98  --bmc1_axioms                           reachable_all
% 3.29/0.98  --bmc1_min_bound                        0
% 3.29/0.98  --bmc1_max_bound                        -1
% 3.29/0.98  --bmc1_max_bound_default                -1
% 3.29/0.98  --bmc1_symbol_reachability              true
% 3.29/0.98  --bmc1_property_lemmas                  false
% 3.29/0.98  --bmc1_k_induction                      false
% 3.29/0.98  --bmc1_non_equiv_states                 false
% 3.29/0.98  --bmc1_deadlock                         false
% 3.29/0.98  --bmc1_ucm                              false
% 3.29/0.98  --bmc1_add_unsat_core                   none
% 3.29/0.98  --bmc1_unsat_core_children              false
% 3.29/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.98  --bmc1_out_stat                         full
% 3.29/0.98  --bmc1_ground_init                      false
% 3.29/0.98  --bmc1_pre_inst_next_state              false
% 3.29/0.98  --bmc1_pre_inst_state                   false
% 3.29/0.98  --bmc1_pre_inst_reach_state             false
% 3.29/0.98  --bmc1_out_unsat_core                   false
% 3.29/0.98  --bmc1_aig_witness_out                  false
% 3.29/0.98  --bmc1_verbose                          false
% 3.29/0.98  --bmc1_dump_clauses_tptp                false
% 3.29/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.98  --bmc1_dump_file                        -
% 3.29/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.98  --bmc1_ucm_extend_mode                  1
% 3.29/0.98  --bmc1_ucm_init_mode                    2
% 3.29/0.98  --bmc1_ucm_cone_mode                    none
% 3.29/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.98  --bmc1_ucm_relax_model                  4
% 3.29/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.98  --bmc1_ucm_layered_model                none
% 3.29/0.98  --bmc1_ucm_max_lemma_size               10
% 3.29/0.98  
% 3.29/0.98  ------ AIG Options
% 3.29/0.98  
% 3.29/0.98  --aig_mode                              false
% 3.29/0.98  
% 3.29/0.98  ------ Instantiation Options
% 3.29/0.98  
% 3.29/0.98  --instantiation_flag                    true
% 3.29/0.98  --inst_sos_flag                         true
% 3.29/0.98  --inst_sos_phase                        true
% 3.29/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.98  --inst_lit_sel_side                     num_symb
% 3.29/0.98  --inst_solver_per_active                1400
% 3.29/0.98  --inst_solver_calls_frac                1.
% 3.29/0.98  --inst_passive_queue_type               priority_queues
% 3.29/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.98  --inst_passive_queues_freq              [25;2]
% 3.29/0.98  --inst_dismatching                      true
% 3.29/0.98  --inst_eager_unprocessed_to_passive     true
% 3.29/0.98  --inst_prop_sim_given                   true
% 3.29/0.98  --inst_prop_sim_new                     false
% 3.29/0.98  --inst_subs_new                         false
% 3.29/0.98  --inst_eq_res_simp                      false
% 3.29/0.98  --inst_subs_given                       false
% 3.29/0.98  --inst_orphan_elimination               true
% 3.29/0.98  --inst_learning_loop_flag               true
% 3.29/0.98  --inst_learning_start                   3000
% 3.29/0.98  --inst_learning_factor                  2
% 3.29/0.98  --inst_start_prop_sim_after_learn       3
% 3.29/0.98  --inst_sel_renew                        solver
% 3.29/0.98  --inst_lit_activity_flag                true
% 3.29/0.98  --inst_restr_to_given                   false
% 3.29/0.98  --inst_activity_threshold               500
% 3.29/0.98  --inst_out_proof                        true
% 3.29/0.98  
% 3.29/0.98  ------ Resolution Options
% 3.29/0.98  
% 3.29/0.98  --resolution_flag                       true
% 3.29/0.98  --res_lit_sel                           adaptive
% 3.29/0.98  --res_lit_sel_side                      none
% 3.29/0.98  --res_ordering                          kbo
% 3.29/0.98  --res_to_prop_solver                    active
% 3.29/0.98  --res_prop_simpl_new                    false
% 3.29/0.98  --res_prop_simpl_given                  true
% 3.29/0.98  --res_passive_queue_type                priority_queues
% 3.29/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.98  --res_passive_queues_freq               [15;5]
% 3.29/0.98  --res_forward_subs                      full
% 3.29/0.98  --res_backward_subs                     full
% 3.29/0.98  --res_forward_subs_resolution           true
% 3.29/0.98  --res_backward_subs_resolution          true
% 3.29/0.98  --res_orphan_elimination                true
% 3.29/0.98  --res_time_limit                        2.
% 3.29/0.98  --res_out_proof                         true
% 3.29/0.98  
% 3.29/0.98  ------ Superposition Options
% 3.29/0.98  
% 3.29/0.98  --superposition_flag                    true
% 3.29/0.98  --sup_passive_queue_type                priority_queues
% 3.29/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.98  --demod_completeness_check              fast
% 3.29/0.98  --demod_use_ground                      true
% 3.29/0.98  --sup_to_prop_solver                    passive
% 3.29/0.98  --sup_prop_simpl_new                    true
% 3.29/0.98  --sup_prop_simpl_given                  true
% 3.29/0.98  --sup_fun_splitting                     true
% 3.29/0.98  --sup_smt_interval                      50000
% 3.29/0.98  
% 3.29/0.98  ------ Superposition Simplification Setup
% 3.29/0.98  
% 3.29/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.29/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.29/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.29/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.29/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.29/0.98  --sup_immed_triv                        [TrivRules]
% 3.29/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.98  --sup_immed_bw_main                     []
% 3.29/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.29/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.98  --sup_input_bw                          []
% 3.29/0.98  
% 3.29/0.98  ------ Combination Options
% 3.29/0.98  
% 3.29/0.98  --comb_res_mult                         3
% 3.29/0.98  --comb_sup_mult                         2
% 3.29/0.98  --comb_inst_mult                        10
% 3.29/0.98  
% 3.29/0.98  ------ Debug Options
% 3.29/0.98  
% 3.29/0.98  --dbg_backtrace                         false
% 3.29/0.98  --dbg_dump_prop_clauses                 false
% 3.29/0.98  --dbg_dump_prop_clauses_file            -
% 3.29/0.98  --dbg_out_stat                          false
% 3.29/0.98  ------ Parsing...
% 3.29/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.29/0.98  ------ Proving...
% 3.29/0.98  ------ Problem Properties 
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  clauses                                 30
% 3.29/0.98  conjectures                             2
% 3.29/0.98  EPR                                     0
% 3.29/0.98  Horn                                    20
% 3.29/0.98  unary                                   6
% 3.29/0.98  binary                                  7
% 3.29/0.98  lits                                    76
% 3.29/0.98  lits eq                                 30
% 3.29/0.98  fd_pure                                 0
% 3.29/0.98  fd_pseudo                               0
% 3.29/0.98  fd_cond                                 0
% 3.29/0.98  fd_pseudo_cond                          14
% 3.29/0.98  AC symbols                              0
% 3.29/0.98  
% 3.29/0.98  ------ Schedule dynamic 5 is on 
% 3.29/0.98  
% 3.29/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  ------ 
% 3.29/0.98  Current options:
% 3.29/0.98  ------ 
% 3.29/0.98  
% 3.29/0.98  ------ Input Options
% 3.29/0.98  
% 3.29/0.98  --out_options                           all
% 3.29/0.98  --tptp_safe_out                         true
% 3.29/0.98  --problem_path                          ""
% 3.29/0.98  --include_path                          ""
% 3.29/0.98  --clausifier                            res/vclausify_rel
% 3.29/0.98  --clausifier_options                    ""
% 3.29/0.98  --stdin                                 false
% 3.29/0.98  --stats_out                             all
% 3.29/0.98  
% 3.29/0.98  ------ General Options
% 3.29/0.98  
% 3.29/0.98  --fof                                   false
% 3.29/0.98  --time_out_real                         305.
% 3.29/0.98  --time_out_virtual                      -1.
% 3.29/0.98  --symbol_type_check                     false
% 3.29/0.98  --clausify_out                          false
% 3.29/0.98  --sig_cnt_out                           false
% 3.29/0.98  --trig_cnt_out                          false
% 3.29/0.98  --trig_cnt_out_tolerance                1.
% 3.29/0.98  --trig_cnt_out_sk_spl                   false
% 3.29/0.98  --abstr_cl_out                          false
% 3.29/0.98  
% 3.29/0.98  ------ Global Options
% 3.29/0.98  
% 3.29/0.98  --schedule                              default
% 3.29/0.98  --add_important_lit                     false
% 3.29/0.98  --prop_solver_per_cl                    1000
% 3.29/0.98  --min_unsat_core                        false
% 3.29/0.98  --soft_assumptions                      false
% 3.29/0.98  --soft_lemma_size                       3
% 3.29/0.98  --prop_impl_unit_size                   0
% 3.29/0.98  --prop_impl_unit                        []
% 3.29/0.98  --share_sel_clauses                     true
% 3.29/0.98  --reset_solvers                         false
% 3.29/0.98  --bc_imp_inh                            [conj_cone]
% 3.29/0.98  --conj_cone_tolerance                   3.
% 3.29/0.98  --extra_neg_conj                        none
% 3.29/0.98  --large_theory_mode                     true
% 3.29/0.98  --prolific_symb_bound                   200
% 3.29/0.98  --lt_threshold                          2000
% 3.29/0.98  --clause_weak_htbl                      true
% 3.29/0.98  --gc_record_bc_elim                     false
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing Options
% 3.29/0.98  
% 3.29/0.98  --preprocessing_flag                    true
% 3.29/0.98  --time_out_prep_mult                    0.1
% 3.29/0.98  --splitting_mode                        input
% 3.29/0.98  --splitting_grd                         true
% 3.29/0.98  --splitting_cvd                         false
% 3.29/0.98  --splitting_cvd_svl                     false
% 3.29/0.98  --splitting_nvd                         32
% 3.29/0.98  --sub_typing                            true
% 3.29/0.98  --prep_gs_sim                           true
% 3.29/0.98  --prep_unflatten                        true
% 3.29/0.98  --prep_res_sim                          true
% 3.29/0.98  --prep_upred                            true
% 3.29/0.98  --prep_sem_filter                       exhaustive
% 3.29/0.98  --prep_sem_filter_out                   false
% 3.29/0.98  --pred_elim                             true
% 3.29/0.98  --res_sim_input                         true
% 3.29/0.98  --eq_ax_congr_red                       true
% 3.29/0.98  --pure_diseq_elim                       true
% 3.29/0.98  --brand_transform                       false
% 3.29/0.98  --non_eq_to_eq                          false
% 3.29/0.98  --prep_def_merge                        true
% 3.29/0.98  --prep_def_merge_prop_impl              false
% 3.29/0.98  --prep_def_merge_mbd                    true
% 3.29/0.98  --prep_def_merge_tr_red                 false
% 3.29/0.98  --prep_def_merge_tr_cl                  false
% 3.29/0.98  --smt_preprocessing                     true
% 3.29/0.98  --smt_ac_axioms                         fast
% 3.29/0.98  --preprocessed_out                      false
% 3.29/0.98  --preprocessed_stats                    false
% 3.29/0.98  
% 3.29/0.98  ------ Abstraction refinement Options
% 3.29/0.98  
% 3.29/0.98  --abstr_ref                             []
% 3.29/0.98  --abstr_ref_prep                        false
% 3.29/0.98  --abstr_ref_until_sat                   false
% 3.29/0.98  --abstr_ref_sig_restrict                funpre
% 3.29/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.29/0.98  --abstr_ref_under                       []
% 3.29/0.98  
% 3.29/0.98  ------ SAT Options
% 3.29/0.98  
% 3.29/0.98  --sat_mode                              false
% 3.29/0.98  --sat_fm_restart_options                ""
% 3.29/0.98  --sat_gr_def                            false
% 3.29/0.98  --sat_epr_types                         true
% 3.29/0.98  --sat_non_cyclic_types                  false
% 3.29/0.98  --sat_finite_models                     false
% 3.29/0.98  --sat_fm_lemmas                         false
% 3.29/0.98  --sat_fm_prep                           false
% 3.29/0.98  --sat_fm_uc_incr                        true
% 3.29/0.98  --sat_out_model                         small
% 3.29/0.98  --sat_out_clauses                       false
% 3.29/0.98  
% 3.29/0.98  ------ QBF Options
% 3.29/0.98  
% 3.29/0.98  --qbf_mode                              false
% 3.29/0.98  --qbf_elim_univ                         false
% 3.29/0.98  --qbf_dom_inst                          none
% 3.29/0.98  --qbf_dom_pre_inst                      false
% 3.29/0.98  --qbf_sk_in                             false
% 3.29/0.98  --qbf_pred_elim                         true
% 3.29/0.98  --qbf_split                             512
% 3.29/0.98  
% 3.29/0.98  ------ BMC1 Options
% 3.29/0.98  
% 3.29/0.98  --bmc1_incremental                      false
% 3.29/0.98  --bmc1_axioms                           reachable_all
% 3.29/0.98  --bmc1_min_bound                        0
% 3.29/0.98  --bmc1_max_bound                        -1
% 3.29/0.98  --bmc1_max_bound_default                -1
% 3.29/0.98  --bmc1_symbol_reachability              true
% 3.29/0.98  --bmc1_property_lemmas                  false
% 3.29/0.98  --bmc1_k_induction                      false
% 3.29/0.98  --bmc1_non_equiv_states                 false
% 3.29/0.98  --bmc1_deadlock                         false
% 3.29/0.98  --bmc1_ucm                              false
% 3.29/0.98  --bmc1_add_unsat_core                   none
% 3.29/0.98  --bmc1_unsat_core_children              false
% 3.29/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.29/0.98  --bmc1_out_stat                         full
% 3.29/0.98  --bmc1_ground_init                      false
% 3.29/0.98  --bmc1_pre_inst_next_state              false
% 3.29/0.98  --bmc1_pre_inst_state                   false
% 3.29/0.98  --bmc1_pre_inst_reach_state             false
% 3.29/0.98  --bmc1_out_unsat_core                   false
% 3.29/0.98  --bmc1_aig_witness_out                  false
% 3.29/0.98  --bmc1_verbose                          false
% 3.29/0.98  --bmc1_dump_clauses_tptp                false
% 3.29/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.29/0.98  --bmc1_dump_file                        -
% 3.29/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.29/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.29/0.98  --bmc1_ucm_extend_mode                  1
% 3.29/0.98  --bmc1_ucm_init_mode                    2
% 3.29/0.98  --bmc1_ucm_cone_mode                    none
% 3.29/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.29/0.98  --bmc1_ucm_relax_model                  4
% 3.29/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.29/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.29/0.98  --bmc1_ucm_layered_model                none
% 3.29/0.98  --bmc1_ucm_max_lemma_size               10
% 3.29/0.98  
% 3.29/0.98  ------ AIG Options
% 3.29/0.98  
% 3.29/0.98  --aig_mode                              false
% 3.29/0.98  
% 3.29/0.98  ------ Instantiation Options
% 3.29/0.98  
% 3.29/0.98  --instantiation_flag                    true
% 3.29/0.98  --inst_sos_flag                         true
% 3.29/0.98  --inst_sos_phase                        true
% 3.29/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.29/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.29/0.98  --inst_lit_sel_side                     none
% 3.29/0.98  --inst_solver_per_active                1400
% 3.29/0.98  --inst_solver_calls_frac                1.
% 3.29/0.98  --inst_passive_queue_type               priority_queues
% 3.29/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.29/0.98  --inst_passive_queues_freq              [25;2]
% 3.29/0.98  --inst_dismatching                      true
% 3.29/0.98  --inst_eager_unprocessed_to_passive     true
% 3.29/0.98  --inst_prop_sim_given                   true
% 3.29/0.98  --inst_prop_sim_new                     false
% 3.29/0.98  --inst_subs_new                         false
% 3.29/0.98  --inst_eq_res_simp                      false
% 3.29/0.98  --inst_subs_given                       false
% 3.29/0.98  --inst_orphan_elimination               true
% 3.29/0.98  --inst_learning_loop_flag               true
% 3.29/0.98  --inst_learning_start                   3000
% 3.29/0.98  --inst_learning_factor                  2
% 3.29/0.98  --inst_start_prop_sim_after_learn       3
% 3.29/0.98  --inst_sel_renew                        solver
% 3.29/0.98  --inst_lit_activity_flag                true
% 3.29/0.98  --inst_restr_to_given                   false
% 3.29/0.98  --inst_activity_threshold               500
% 3.29/0.98  --inst_out_proof                        true
% 3.29/0.98  
% 3.29/0.98  ------ Resolution Options
% 3.29/0.98  
% 3.29/0.98  --resolution_flag                       false
% 3.29/0.98  --res_lit_sel                           adaptive
% 3.29/0.98  --res_lit_sel_side                      none
% 3.29/0.98  --res_ordering                          kbo
% 3.29/0.98  --res_to_prop_solver                    active
% 3.29/0.98  --res_prop_simpl_new                    false
% 3.29/0.98  --res_prop_simpl_given                  true
% 3.29/0.98  --res_passive_queue_type                priority_queues
% 3.29/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.29/0.98  --res_passive_queues_freq               [15;5]
% 3.29/0.98  --res_forward_subs                      full
% 3.29/0.98  --res_backward_subs                     full
% 3.29/0.98  --res_forward_subs_resolution           true
% 3.29/0.98  --res_backward_subs_resolution          true
% 3.29/0.98  --res_orphan_elimination                true
% 3.29/0.98  --res_time_limit                        2.
% 3.29/0.98  --res_out_proof                         true
% 3.29/0.98  
% 3.29/0.98  ------ Superposition Options
% 3.29/0.98  
% 3.29/0.98  --superposition_flag                    true
% 3.29/0.98  --sup_passive_queue_type                priority_queues
% 3.29/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.29/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.29/0.98  --demod_completeness_check              fast
% 3.29/0.98  --demod_use_ground                      true
% 3.29/0.98  --sup_to_prop_solver                    passive
% 3.29/0.98  --sup_prop_simpl_new                    true
% 3.29/0.98  --sup_prop_simpl_given                  true
% 3.29/0.98  --sup_fun_splitting                     true
% 3.29/0.98  --sup_smt_interval                      50000
% 3.29/0.98  
% 3.29/0.98  ------ Superposition Simplification Setup
% 3.29/0.98  
% 3.29/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.29/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.29/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.29/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.29/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.29/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.29/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.29/0.98  --sup_immed_triv                        [TrivRules]
% 3.29/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.98  --sup_immed_bw_main                     []
% 3.29/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.29/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.29/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.29/0.98  --sup_input_bw                          []
% 3.29/0.98  
% 3.29/0.98  ------ Combination Options
% 3.29/0.98  
% 3.29/0.98  --comb_res_mult                         3
% 3.29/0.98  --comb_sup_mult                         2
% 3.29/0.98  --comb_inst_mult                        10
% 3.29/0.98  
% 3.29/0.98  ------ Debug Options
% 3.29/0.98  
% 3.29/0.98  --dbg_backtrace                         false
% 3.29/0.98  --dbg_dump_prop_clauses                 false
% 3.29/0.98  --dbg_dump_prop_clauses_file            -
% 3.29/0.98  --dbg_out_stat                          false
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  ------ Proving...
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  % SZS status Theorem for theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  fof(f8,axiom,(
% 3.29/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.29/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f35,plain,(
% 3.29/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.98    inference(nnf_transformation,[],[f8])).
% 3.29/0.98  
% 3.29/0.98  fof(f36,plain,(
% 3.29/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.98    inference(rectify,[],[f35])).
% 3.29/0.98  
% 3.29/0.98  fof(f37,plain,(
% 3.29/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f38,plain,(
% 3.29/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.29/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 3.29/0.98  
% 3.29/0.98  fof(f69,plain,(
% 3.29/0.98    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f38])).
% 3.29/0.98  
% 3.29/0.98  fof(f9,axiom,(
% 3.29/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.29/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f71,plain,(
% 3.29/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f9])).
% 3.29/0.98  
% 3.29/0.98  fof(f10,axiom,(
% 3.29/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.29/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f72,plain,(
% 3.29/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f10])).
% 3.29/0.98  
% 3.29/0.98  fof(f11,axiom,(
% 3.29/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.29/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f73,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f11])).
% 3.29/0.98  
% 3.29/0.98  fof(f76,plain,(
% 3.29/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.29/0.98    inference(definition_unfolding,[],[f72,f73])).
% 3.29/0.98  
% 3.29/0.98  fof(f77,plain,(
% 3.29/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.29/0.98    inference(definition_unfolding,[],[f71,f76])).
% 3.29/0.98  
% 3.29/0.98  fof(f94,plain,(
% 3.29/0.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)) )),
% 3.29/0.98    inference(definition_unfolding,[],[f69,f77])).
% 3.29/0.98  
% 3.29/0.98  fof(f67,plain,(
% 3.29/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.29/0.98    inference(cnf_transformation,[],[f38])).
% 3.29/0.98  
% 3.29/0.98  fof(f96,plain,(
% 3.29/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.29/0.98    inference(definition_unfolding,[],[f67,f77])).
% 3.29/0.98  
% 3.29/0.98  fof(f114,plain,(
% 3.29/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.29/0.98    inference(equality_resolution,[],[f96])).
% 3.29/0.98  
% 3.29/0.98  fof(f12,conjecture,(
% 3.29/0.98    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.29/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f13,negated_conjecture,(
% 3.29/0.98    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.29/0.98    inference(negated_conjecture,[],[f12])).
% 3.29/0.98  
% 3.29/0.98  fof(f16,plain,(
% 3.29/0.98    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.29/0.98    inference(ennf_transformation,[],[f13])).
% 3.29/0.98  
% 3.29/0.98  fof(f39,plain,(
% 3.29/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.29/0.98    inference(nnf_transformation,[],[f16])).
% 3.29/0.98  
% 3.29/0.98  fof(f40,plain,(
% 3.29/0.98    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK6,sK5) | k4_xboole_0(sK5,k1_tarski(sK6)) != sK5) & (~r2_hidden(sK6,sK5) | k4_xboole_0(sK5,k1_tarski(sK6)) = sK5))),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f41,plain,(
% 3.29/0.98    (r2_hidden(sK6,sK5) | k4_xboole_0(sK5,k1_tarski(sK6)) != sK5) & (~r2_hidden(sK6,sK5) | k4_xboole_0(sK5,k1_tarski(sK6)) = sK5)),
% 3.29/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f39,f40])).
% 3.29/0.98  
% 3.29/0.98  fof(f75,plain,(
% 3.29/0.98    r2_hidden(sK6,sK5) | k4_xboole_0(sK5,k1_tarski(sK6)) != sK5),
% 3.29/0.98    inference(cnf_transformation,[],[f41])).
% 3.29/0.98  
% 3.29/0.98  fof(f5,axiom,(
% 3.29/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.29/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f57,plain,(
% 3.29/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.29/0.98    inference(cnf_transformation,[],[f5])).
% 3.29/0.98  
% 3.29/0.98  fof(f97,plain,(
% 3.29/0.98    r2_hidden(sK6,sK5) | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) != sK5),
% 3.29/0.98    inference(definition_unfolding,[],[f75,f57,f77])).
% 3.29/0.98  
% 3.29/0.98  fof(f74,plain,(
% 3.29/0.98    ~r2_hidden(sK6,sK5) | k4_xboole_0(sK5,k1_tarski(sK6)) = sK5),
% 3.29/0.98    inference(cnf_transformation,[],[f41])).
% 3.29/0.98  
% 3.29/0.98  fof(f98,plain,(
% 3.29/0.98    ~r2_hidden(sK6,sK5) | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5),
% 3.29/0.98    inference(definition_unfolding,[],[f74,f57,f77])).
% 3.29/0.98  
% 3.29/0.98  fof(f68,plain,(
% 3.29/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.29/0.98    inference(cnf_transformation,[],[f38])).
% 3.29/0.98  
% 3.29/0.98  fof(f95,plain,(
% 3.29/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.29/0.98    inference(definition_unfolding,[],[f68,f77])).
% 3.29/0.98  
% 3.29/0.98  fof(f112,plain,(
% 3.29/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 3.29/0.98    inference(equality_resolution,[],[f95])).
% 3.29/0.98  
% 3.29/0.98  fof(f113,plain,(
% 3.29/0.98    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 3.29/0.98    inference(equality_resolution,[],[f112])).
% 3.29/0.98  
% 3.29/0.98  fof(f3,axiom,(
% 3.29/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.29/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.29/0.98  
% 3.29/0.98  fof(f22,plain,(
% 3.29/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.98    inference(nnf_transformation,[],[f3])).
% 3.29/0.98  
% 3.29/0.98  fof(f23,plain,(
% 3.29/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.98    inference(flattening,[],[f22])).
% 3.29/0.98  
% 3.29/0.98  fof(f24,plain,(
% 3.29/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.98    inference(rectify,[],[f23])).
% 3.29/0.98  
% 3.29/0.98  fof(f25,plain,(
% 3.29/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.29/0.98    introduced(choice_axiom,[])).
% 3.29/0.98  
% 3.29/0.98  fof(f26,plain,(
% 3.29/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 3.29/0.98  
% 3.29/0.98  fof(f52,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f26])).
% 3.29/0.98  
% 3.29/0.98  fof(f80,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.29/0.98    inference(definition_unfolding,[],[f52,f57])).
% 3.29/0.98  
% 3.29/0.98  fof(f54,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.29/0.98    inference(cnf_transformation,[],[f26])).
% 3.29/0.98  
% 3.29/0.98  fof(f78,plain,(
% 3.29/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.29/0.98    inference(definition_unfolding,[],[f54,f57])).
% 3.29/0.98  
% 3.29/0.98  fof(f50,plain,(
% 3.29/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.29/0.98    inference(cnf_transformation,[],[f26])).
% 3.29/0.98  
% 3.29/0.98  fof(f82,plain,(
% 3.29/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.29/0.98    inference(definition_unfolding,[],[f50,f57])).
% 3.29/0.98  
% 3.29/0.98  fof(f103,plain,(
% 3.29/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.29/0.98    inference(equality_resolution,[],[f82])).
% 3.29/0.98  
% 3.29/0.98  cnf(c_25,plain,
% 3.29/0.98      ( r2_hidden(sK4(X0,X1),X1)
% 3.29/0.98      | k2_enumset1(X0,X0,X0,X0) = X1
% 3.29/0.98      | sK4(X0,X1) = X0 ),
% 3.29/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_927,plain,
% 3.29/0.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.29/0.98      | sK4(X0,X1) = X0
% 3.29/0.98      | r2_hidden(sK4(X0,X1),X1) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_27,plain,
% 3.29/0.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.29/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_925,plain,
% 3.29/0.98      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2422,plain,
% 3.29/0.98      ( k2_enumset1(X0,X0,X0,X0) = k2_enumset1(X1,X1,X1,X1)
% 3.29/0.98      | sK4(X1,k2_enumset1(X0,X0,X0,X0)) = X1
% 3.29/0.98      | sK4(X1,k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_927,c_925]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_28,negated_conjecture,
% 3.29/0.98      ( r2_hidden(sK6,sK5)
% 3.29/0.98      | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) != sK5 ),
% 3.29/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_924,plain,
% 3.29/0.98      ( k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) != sK5
% 3.29/0.98      | r2_hidden(sK6,sK5) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_10733,plain,
% 3.29/0.98      ( sK4(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = X0
% 3.29/0.98      | sK4(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = sK6
% 3.29/0.98      | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(X0,X0,X0,X0))) != sK5
% 3.29/0.98      | r2_hidden(sK6,sK5) = iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_2422,c_924]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_29,negated_conjecture,
% 3.29/0.98      ( ~ r2_hidden(sK6,sK5)
% 3.29/0.98      | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
% 3.29/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_31,plain,
% 3.29/0.98      ( k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) != sK5
% 3.29/0.98      | r2_hidden(sK6,sK5) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_33,plain,
% 3.29/0.98      ( ~ r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) | sK6 = sK6 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_26,plain,
% 3.29/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 3.29/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_36,plain,
% 3.29/0.98      ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_9,plain,
% 3.29/0.98      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.29/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.29/0.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.29/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_983,plain,
% 3.29/0.98      ( r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),sK5)
% 3.29/0.98      | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_7,plain,
% 3.29/0.98      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.29/0.98      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.29/0.98      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.29/0.98      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.29/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_981,plain,
% 3.29/0.98      ( r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),k2_enumset1(sK6,sK6,sK6,sK6))
% 3.29/0.98      | ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),sK5)
% 3.29/0.98      | k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_368,plain,
% 3.29/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.29/0.98      theory(equality) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1167,plain,
% 3.29/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(sK6,X2) | X2 != X1 | sK6 != X0 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_368]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1392,plain,
% 3.29/0.98      ( ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),sK5)
% 3.29/0.98      | r2_hidden(sK6,X0)
% 3.29/0.98      | X0 != sK5
% 3.29/0.98      | sK6 != sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_1167]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_1581,plain,
% 3.29/0.98      ( ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),sK5)
% 3.29/0.98      | r2_hidden(sK6,sK5)
% 3.29/0.98      | sK5 != sK5
% 3.29/0.98      | sK6 != sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_1392]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_365,plain,( X0 = X0 ),theory(equality) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2368,plain,
% 3.29/0.98      ( sK5 = sK5 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_365]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_366,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2508,plain,
% 3.29/0.98      ( sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) != X0
% 3.29/0.98      | sK6 != X0
% 3.29/0.98      | sK6 = sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_366]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_2509,plain,
% 3.29/0.98      ( sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) != sK6
% 3.29/0.98      | sK6 = sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5)
% 3.29/0.98      | sK6 != sK6 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_2508]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_6413,plain,
% 3.29/0.98      ( ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),k2_enumset1(X0,X0,X0,X0))
% 3.29/0.98      | sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) = X0 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_6415,plain,
% 3.29/0.98      ( ~ r2_hidden(sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5),k2_enumset1(sK6,sK6,sK6,sK6))
% 3.29/0.98      | sK1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK5) = sK6 ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_6413]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_11220,plain,
% 3.29/0.98      ( r2_hidden(sK6,sK5) = iProver_top ),
% 3.29/0.98      inference(global_propositional_subsumption,
% 3.29/0.98                [status(thm)],
% 3.29/0.98                [c_10733,c_29,c_31,c_33,c_36,c_983,c_981,c_1581,c_2368,
% 3.29/0.98                 c_2509,c_6415]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_923,plain,
% 3.29/0.98      ( k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5
% 3.29/0.98      | r2_hidden(sK6,sK5) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_11224,plain,
% 3.29/0.98      ( k5_xboole_0(sK5,k3_xboole_0(sK5,k2_enumset1(sK6,sK6,sK6,sK6))) = sK5 ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_11220,c_923]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_11,plain,
% 3.29/0.98      ( ~ r2_hidden(X0,X1)
% 3.29/0.98      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.29/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_940,plain,
% 3.29/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.29/0.98      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_11347,plain,
% 3.29/0.98      ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top
% 3.29/0.98      | r2_hidden(X0,sK5) != iProver_top ),
% 3.29/0.98      inference(superposition,[status(thm)],[c_11224,c_940]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_11351,plain,
% 3.29/0.98      ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top
% 3.29/0.98      | r2_hidden(sK6,sK5) != iProver_top ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_11347]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_35,plain,
% 3.29/0.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 3.29/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(c_37,plain,
% 3.29/0.98      ( r2_hidden(sK6,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
% 3.29/0.98      inference(instantiation,[status(thm)],[c_35]) ).
% 3.29/0.98  
% 3.29/0.98  cnf(contradiction,plain,
% 3.29/0.98      ( $false ),
% 3.29/0.98      inference(minisat,[status(thm)],[c_11351,c_11220,c_37]) ).
% 3.29/0.98  
% 3.29/0.98  
% 3.29/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.29/0.98  
% 3.29/0.98  ------                               Statistics
% 3.29/0.98  
% 3.29/0.98  ------ General
% 3.29/0.98  
% 3.29/0.98  abstr_ref_over_cycles:                  0
% 3.29/0.98  abstr_ref_under_cycles:                 0
% 3.29/0.98  gc_basic_clause_elim:                   0
% 3.29/0.98  forced_gc_time:                         0
% 3.29/0.98  parsing_time:                           0.008
% 3.29/0.98  unif_index_cands_time:                  0.
% 3.29/0.98  unif_index_add_time:                    0.
% 3.29/0.98  orderings_time:                         0.
% 3.29/0.98  out_proof_time:                         0.01
% 3.29/0.98  total_time:                             0.432
% 3.29/0.98  num_of_symbols:                         43
% 3.29/0.98  num_of_terms:                           17986
% 3.29/0.98  
% 3.29/0.98  ------ Preprocessing
% 3.29/0.98  
% 3.29/0.98  num_of_splits:                          0
% 3.29/0.98  num_of_split_atoms:                     0
% 3.29/0.98  num_of_reused_defs:                     0
% 3.29/0.98  num_eq_ax_congr_red:                    28
% 3.29/0.98  num_of_sem_filtered_clauses:            1
% 3.29/0.99  num_of_subtypes:                        0
% 3.29/0.99  monotx_restored_types:                  0
% 3.29/0.99  sat_num_of_epr_types:                   0
% 3.29/0.99  sat_num_of_non_cyclic_types:            0
% 3.29/0.99  sat_guarded_non_collapsed_types:        0
% 3.29/0.99  num_pure_diseq_elim:                    0
% 3.29/0.99  simp_replaced_by:                       0
% 3.29/0.99  res_preprocessed:                       103
% 3.29/0.99  prep_upred:                             0
% 3.29/0.99  prep_unflattend:                        0
% 3.29/0.99  smt_new_axioms:                         0
% 3.29/0.99  pred_elim_cands:                        1
% 3.29/0.99  pred_elim:                              0
% 3.29/0.99  pred_elim_cl:                           0
% 3.29/0.99  pred_elim_cycles:                       1
% 3.29/0.99  merged_defs:                            6
% 3.29/0.99  merged_defs_ncl:                        0
% 3.29/0.99  bin_hyper_res:                          6
% 3.29/0.99  prep_cycles:                            3
% 3.29/0.99  pred_elim_time:                         0.
% 3.29/0.99  splitting_time:                         0.
% 3.29/0.99  sem_filter_time:                        0.
% 3.29/0.99  monotx_time:                            0.
% 3.29/0.99  subtype_inf_time:                       0.
% 3.29/0.99  
% 3.29/0.99  ------ Problem properties
% 3.29/0.99  
% 3.29/0.99  clauses:                                30
% 3.29/0.99  conjectures:                            2
% 3.29/0.99  epr:                                    0
% 3.29/0.99  horn:                                   20
% 3.29/0.99  ground:                                 2
% 3.29/0.99  unary:                                  6
% 3.29/0.99  binary:                                 7
% 3.29/0.99  lits:                                   76
% 3.29/0.99  lits_eq:                                30
% 3.29/0.99  fd_pure:                                0
% 3.29/0.99  fd_pseudo:                              0
% 3.29/0.99  fd_cond:                                0
% 3.29/0.99  fd_pseudo_cond:                         14
% 3.29/0.99  ac_symbols:                             0
% 3.29/0.99  
% 3.29/0.99  ------ Propositional Solver
% 3.29/0.99  
% 3.29/0.99  prop_solver_calls:                      27
% 3.29/0.99  prop_fast_solver_calls:                 1007
% 3.29/0.99  smt_solver_calls:                       0
% 3.29/0.99  smt_fast_solver_calls:                  0
% 3.29/0.99  prop_num_of_clauses:                    5893
% 3.29/0.99  prop_preprocess_simplified:             13399
% 3.29/0.99  prop_fo_subsumed:                       3
% 3.29/0.99  prop_solver_time:                       0.
% 3.29/0.99  smt_solver_time:                        0.
% 3.29/0.99  smt_fast_solver_time:                   0.
% 3.29/0.99  prop_fast_solver_time:                  0.
% 3.29/0.99  prop_unsat_core_time:                   0.
% 3.29/0.99  
% 3.29/0.99  ------ QBF
% 3.29/0.99  
% 3.29/0.99  qbf_q_res:                              0
% 3.29/0.99  qbf_num_tautologies:                    0
% 3.29/0.99  qbf_prep_cycles:                        0
% 3.29/0.99  
% 3.29/0.99  ------ BMC1
% 3.29/0.99  
% 3.29/0.99  bmc1_current_bound:                     -1
% 3.29/0.99  bmc1_last_solved_bound:                 -1
% 3.29/0.99  bmc1_unsat_core_size:                   -1
% 3.29/0.99  bmc1_unsat_core_parents_size:           -1
% 3.29/0.99  bmc1_merge_next_fun:                    0
% 3.29/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.29/0.99  
% 3.29/0.99  ------ Instantiation
% 3.29/0.99  
% 3.29/0.99  inst_num_of_clauses:                    1334
% 3.29/0.99  inst_num_in_passive:                    577
% 3.29/0.99  inst_num_in_active:                     345
% 3.29/0.99  inst_num_in_unprocessed:                412
% 3.29/0.99  inst_num_of_loops:                      590
% 3.29/0.99  inst_num_of_learning_restarts:          0
% 3.29/0.99  inst_num_moves_active_passive:          243
% 3.29/0.99  inst_lit_activity:                      0
% 3.29/0.99  inst_lit_activity_moves:                0
% 3.29/0.99  inst_num_tautologies:                   0
% 3.29/0.99  inst_num_prop_implied:                  0
% 3.29/0.99  inst_num_existing_simplified:           0
% 3.29/0.99  inst_num_eq_res_simplified:             0
% 3.29/0.99  inst_num_child_elim:                    0
% 3.29/0.99  inst_num_of_dismatching_blockings:      678
% 3.29/0.99  inst_num_of_non_proper_insts:           1197
% 3.29/0.99  inst_num_of_duplicates:                 0
% 3.29/0.99  inst_inst_num_from_inst_to_res:         0
% 3.29/0.99  inst_dismatching_checking_time:         0.
% 3.29/0.99  
% 3.29/0.99  ------ Resolution
% 3.29/0.99  
% 3.29/0.99  res_num_of_clauses:                     0
% 3.29/0.99  res_num_in_passive:                     0
% 3.29/0.99  res_num_in_active:                      0
% 3.29/0.99  res_num_of_loops:                       106
% 3.29/0.99  res_forward_subset_subsumed:            27
% 3.29/0.99  res_backward_subset_subsumed:           0
% 3.29/0.99  res_forward_subsumed:                   0
% 3.29/0.99  res_backward_subsumed:                  0
% 3.29/0.99  res_forward_subsumption_resolution:     0
% 3.29/0.99  res_backward_subsumption_resolution:    0
% 3.29/0.99  res_clause_to_clause_subsumption:       15106
% 3.29/0.99  res_orphan_elimination:                 0
% 3.29/0.99  res_tautology_del:                      25
% 3.29/0.99  res_num_eq_res_simplified:              0
% 3.29/0.99  res_num_sel_changes:                    0
% 3.29/0.99  res_moves_from_active_to_pass:          0
% 3.29/0.99  
% 3.29/0.99  ------ Superposition
% 3.29/0.99  
% 3.29/0.99  sup_time_total:                         0.
% 3.29/0.99  sup_time_generating:                    0.
% 3.29/0.99  sup_time_sim_full:                      0.
% 3.29/0.99  sup_time_sim_immed:                     0.
% 3.29/0.99  
% 3.29/0.99  sup_num_of_clauses:                     615
% 3.29/0.99  sup_num_in_active:                      114
% 3.29/0.99  sup_num_in_passive:                     501
% 3.29/0.99  sup_num_of_loops:                       116
% 3.29/0.99  sup_fw_superposition:                   674
% 3.29/0.99  sup_bw_superposition:                   193
% 3.29/0.99  sup_immediate_simplified:               23
% 3.29/0.99  sup_given_eliminated:                   0
% 3.29/0.99  comparisons_done:                       0
% 3.29/0.99  comparisons_avoided:                    30
% 3.29/0.99  
% 3.29/0.99  ------ Simplifications
% 3.29/0.99  
% 3.29/0.99  
% 3.29/0.99  sim_fw_subset_subsumed:                 3
% 3.29/0.99  sim_bw_subset_subsumed:                 1
% 3.29/0.99  sim_fw_subsumed:                        17
% 3.29/0.99  sim_bw_subsumed:                        4
% 3.29/0.99  sim_fw_subsumption_res:                 0
% 3.29/0.99  sim_bw_subsumption_res:                 0
% 3.29/0.99  sim_tautology_del:                      34
% 3.29/0.99  sim_eq_tautology_del:                   16
% 3.29/0.99  sim_eq_res_simp:                        3
% 3.29/0.99  sim_fw_demodulated:                     3
% 3.29/0.99  sim_bw_demodulated:                     0
% 3.29/0.99  sim_light_normalised:                   2
% 3.29/0.99  sim_joinable_taut:                      0
% 3.29/0.99  sim_joinable_simp:                      0
% 3.29/0.99  sim_ac_normalised:                      0
% 3.29/0.99  sim_smt_subsumption:                    0
% 3.29/0.99  
%------------------------------------------------------------------------------
