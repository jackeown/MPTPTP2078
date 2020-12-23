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
% DateTime   : Thu Dec  3 11:35:35 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 220 expanded)
%              Number of clauses        :   33 (  37 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  336 ( 934 expanded)
%              Number of equality atoms :  189 ( 559 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f35])).

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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f104,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f76])).

fof(f102,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f90])).

fof(f103,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f102])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK5,sK4)
        | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
      & ( ~ r2_hidden(sK5,sK4)
        | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
    & ( ~ r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).

fof(f73,plain,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f76])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f93,plain,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f72,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(definition_unfolding,[],[f72,f78])).

cnf(c_324,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2184,plain,
    ( X0 != X1
    | X0 = sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
    | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_2185,plain,
    ( sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != sK5
    | sK5 = sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2184])).

cnf(c_327,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1055,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),sK4)
    | X0 != sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_1691,plain,
    ( ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),sK4)
    | r2_hidden(sK5,sK4)
    | sK4 != sK4
    | sK5 != sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_1055])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1646,plain,
    ( ~ r2_hidden(X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(X0,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1647,plain,
    ( r2_hidden(X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_1649,plain,
    ( r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK5,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_1097,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(X3,X4))
    | X2 != X0
    | k4_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_1564,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(X1,sK4)
    | X0 != X1
    | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1565,plain,
    ( X0 != X1
    | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4
    | r2_hidden(X0,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_1567,plain,
    ( k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4
    | sK5 != sK5
    | r2_hidden(sK5,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1504,plain,
    ( ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
    | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = X0
    | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = X2
    | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = X1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1506,plain,
    ( ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_323,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1455,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1040,plain,
    ( r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),sK4)
    | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1032,plain,
    ( r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),sK4)
    | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_19,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_32,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_34,plain,
    ( r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_33,plain,
    ( r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_30,plain,
    ( ~ r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_25,plain,
    ( k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_24,plain,
    ( k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2185,c_1691,c_1649,c_1567,c_1506,c_1455,c_1040,c_1032,c_34,c_33,c_30,c_25,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.79/1.09  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.09  
% 1.79/1.09  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.79/1.09  
% 1.79/1.09  ------  iProver source info
% 1.79/1.09  
% 1.79/1.09  git: date: 2020-06-30 10:37:57 +0100
% 1.79/1.09  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.79/1.09  git: non_committed_changes: false
% 1.79/1.09  git: last_make_outside_of_git: false
% 1.79/1.09  
% 1.79/1.09  ------ 
% 1.79/1.09  
% 1.79/1.09  ------ Input Options
% 1.79/1.09  
% 1.79/1.09  --out_options                           all
% 1.79/1.09  --tptp_safe_out                         true
% 1.79/1.09  --problem_path                          ""
% 1.79/1.09  --include_path                          ""
% 1.79/1.09  --clausifier                            res/vclausify_rel
% 1.79/1.09  --clausifier_options                    --mode clausify
% 1.79/1.09  --stdin                                 false
% 1.79/1.09  --stats_out                             all
% 1.79/1.09  
% 1.79/1.09  ------ General Options
% 1.79/1.09  
% 1.79/1.09  --fof                                   false
% 1.79/1.09  --time_out_real                         305.
% 1.79/1.09  --time_out_virtual                      -1.
% 1.79/1.09  --symbol_type_check                     false
% 1.79/1.09  --clausify_out                          false
% 1.79/1.09  --sig_cnt_out                           false
% 1.79/1.09  --trig_cnt_out                          false
% 1.79/1.09  --trig_cnt_out_tolerance                1.
% 1.79/1.09  --trig_cnt_out_sk_spl                   false
% 1.79/1.09  --abstr_cl_out                          false
% 1.79/1.09  
% 1.79/1.09  ------ Global Options
% 1.79/1.09  
% 1.79/1.09  --schedule                              default
% 1.79/1.09  --add_important_lit                     false
% 1.79/1.09  --prop_solver_per_cl                    1000
% 1.79/1.09  --min_unsat_core                        false
% 1.79/1.09  --soft_assumptions                      false
% 1.79/1.09  --soft_lemma_size                       3
% 1.79/1.09  --prop_impl_unit_size                   0
% 1.79/1.09  --prop_impl_unit                        []
% 1.79/1.09  --share_sel_clauses                     true
% 1.79/1.09  --reset_solvers                         false
% 1.79/1.09  --bc_imp_inh                            [conj_cone]
% 1.79/1.09  --conj_cone_tolerance                   3.
% 1.79/1.09  --extra_neg_conj                        none
% 1.79/1.09  --large_theory_mode                     true
% 1.79/1.09  --prolific_symb_bound                   200
% 1.79/1.09  --lt_threshold                          2000
% 1.79/1.09  --clause_weak_htbl                      true
% 1.79/1.09  --gc_record_bc_elim                     false
% 1.79/1.09  
% 1.79/1.09  ------ Preprocessing Options
% 1.79/1.09  
% 1.79/1.09  --preprocessing_flag                    true
% 1.79/1.09  --time_out_prep_mult                    0.1
% 1.79/1.09  --splitting_mode                        input
% 1.79/1.09  --splitting_grd                         true
% 1.79/1.09  --splitting_cvd                         false
% 1.79/1.09  --splitting_cvd_svl                     false
% 1.79/1.09  --splitting_nvd                         32
% 1.79/1.09  --sub_typing                            true
% 1.79/1.09  --prep_gs_sim                           true
% 1.79/1.09  --prep_unflatten                        true
% 1.79/1.09  --prep_res_sim                          true
% 1.79/1.09  --prep_upred                            true
% 1.79/1.09  --prep_sem_filter                       exhaustive
% 1.79/1.09  --prep_sem_filter_out                   false
% 1.79/1.09  --pred_elim                             true
% 1.79/1.09  --res_sim_input                         true
% 1.79/1.09  --eq_ax_congr_red                       true
% 1.79/1.09  --pure_diseq_elim                       true
% 1.79/1.09  --brand_transform                       false
% 1.79/1.09  --non_eq_to_eq                          false
% 1.79/1.09  --prep_def_merge                        true
% 1.79/1.09  --prep_def_merge_prop_impl              false
% 1.79/1.09  --prep_def_merge_mbd                    true
% 1.79/1.09  --prep_def_merge_tr_red                 false
% 1.79/1.09  --prep_def_merge_tr_cl                  false
% 1.79/1.09  --smt_preprocessing                     true
% 1.79/1.09  --smt_ac_axioms                         fast
% 1.79/1.09  --preprocessed_out                      false
% 1.79/1.09  --preprocessed_stats                    false
% 1.79/1.09  
% 1.79/1.09  ------ Abstraction refinement Options
% 1.79/1.09  
% 1.79/1.09  --abstr_ref                             []
% 1.79/1.09  --abstr_ref_prep                        false
% 1.79/1.09  --abstr_ref_until_sat                   false
% 1.79/1.09  --abstr_ref_sig_restrict                funpre
% 1.79/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/1.09  --abstr_ref_under                       []
% 1.79/1.09  
% 1.79/1.09  ------ SAT Options
% 1.79/1.09  
% 1.79/1.09  --sat_mode                              false
% 1.79/1.09  --sat_fm_restart_options                ""
% 1.79/1.09  --sat_gr_def                            false
% 1.79/1.09  --sat_epr_types                         true
% 1.79/1.09  --sat_non_cyclic_types                  false
% 1.79/1.09  --sat_finite_models                     false
% 1.79/1.09  --sat_fm_lemmas                         false
% 1.79/1.09  --sat_fm_prep                           false
% 1.79/1.09  --sat_fm_uc_incr                        true
% 1.79/1.09  --sat_out_model                         small
% 1.79/1.09  --sat_out_clauses                       false
% 1.79/1.09  
% 1.79/1.09  ------ QBF Options
% 1.79/1.09  
% 1.79/1.09  --qbf_mode                              false
% 1.79/1.09  --qbf_elim_univ                         false
% 1.79/1.09  --qbf_dom_inst                          none
% 1.79/1.09  --qbf_dom_pre_inst                      false
% 1.79/1.09  --qbf_sk_in                             false
% 1.79/1.09  --qbf_pred_elim                         true
% 1.79/1.09  --qbf_split                             512
% 1.79/1.09  
% 1.79/1.09  ------ BMC1 Options
% 1.79/1.09  
% 1.79/1.09  --bmc1_incremental                      false
% 1.79/1.09  --bmc1_axioms                           reachable_all
% 1.79/1.09  --bmc1_min_bound                        0
% 1.79/1.09  --bmc1_max_bound                        -1
% 1.79/1.09  --bmc1_max_bound_default                -1
% 1.79/1.09  --bmc1_symbol_reachability              true
% 1.79/1.09  --bmc1_property_lemmas                  false
% 1.79/1.09  --bmc1_k_induction                      false
% 1.79/1.09  --bmc1_non_equiv_states                 false
% 1.79/1.09  --bmc1_deadlock                         false
% 1.79/1.09  --bmc1_ucm                              false
% 1.79/1.09  --bmc1_add_unsat_core                   none
% 1.79/1.09  --bmc1_unsat_core_children              false
% 1.79/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/1.09  --bmc1_out_stat                         full
% 1.79/1.09  --bmc1_ground_init                      false
% 1.79/1.09  --bmc1_pre_inst_next_state              false
% 1.79/1.09  --bmc1_pre_inst_state                   false
% 1.79/1.09  --bmc1_pre_inst_reach_state             false
% 1.79/1.09  --bmc1_out_unsat_core                   false
% 1.79/1.09  --bmc1_aig_witness_out                  false
% 1.79/1.09  --bmc1_verbose                          false
% 1.79/1.09  --bmc1_dump_clauses_tptp                false
% 1.79/1.09  --bmc1_dump_unsat_core_tptp             false
% 1.79/1.09  --bmc1_dump_file                        -
% 1.79/1.09  --bmc1_ucm_expand_uc_limit              128
% 1.79/1.09  --bmc1_ucm_n_expand_iterations          6
% 1.79/1.09  --bmc1_ucm_extend_mode                  1
% 1.79/1.09  --bmc1_ucm_init_mode                    2
% 1.79/1.09  --bmc1_ucm_cone_mode                    none
% 1.79/1.09  --bmc1_ucm_reduced_relation_type        0
% 1.79/1.09  --bmc1_ucm_relax_model                  4
% 1.79/1.09  --bmc1_ucm_full_tr_after_sat            true
% 1.79/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/1.09  --bmc1_ucm_layered_model                none
% 1.79/1.09  --bmc1_ucm_max_lemma_size               10
% 1.79/1.09  
% 1.79/1.09  ------ AIG Options
% 1.79/1.09  
% 1.79/1.09  --aig_mode                              false
% 1.79/1.09  
% 1.79/1.09  ------ Instantiation Options
% 1.79/1.09  
% 1.79/1.09  --instantiation_flag                    true
% 1.79/1.09  --inst_sos_flag                         false
% 1.79/1.09  --inst_sos_phase                        true
% 1.79/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/1.09  --inst_lit_sel_side                     num_symb
% 1.79/1.09  --inst_solver_per_active                1400
% 1.79/1.09  --inst_solver_calls_frac                1.
% 1.79/1.09  --inst_passive_queue_type               priority_queues
% 1.79/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/1.09  --inst_passive_queues_freq              [25;2]
% 1.79/1.09  --inst_dismatching                      true
% 1.79/1.09  --inst_eager_unprocessed_to_passive     true
% 1.79/1.09  --inst_prop_sim_given                   true
% 1.79/1.09  --inst_prop_sim_new                     false
% 1.79/1.09  --inst_subs_new                         false
% 1.79/1.09  --inst_eq_res_simp                      false
% 1.79/1.09  --inst_subs_given                       false
% 1.79/1.09  --inst_orphan_elimination               true
% 1.79/1.09  --inst_learning_loop_flag               true
% 1.79/1.09  --inst_learning_start                   3000
% 1.79/1.09  --inst_learning_factor                  2
% 1.79/1.09  --inst_start_prop_sim_after_learn       3
% 1.79/1.09  --inst_sel_renew                        solver
% 1.79/1.09  --inst_lit_activity_flag                true
% 1.79/1.09  --inst_restr_to_given                   false
% 1.79/1.09  --inst_activity_threshold               500
% 1.79/1.09  --inst_out_proof                        true
% 1.79/1.09  
% 1.79/1.09  ------ Resolution Options
% 1.79/1.09  
% 1.79/1.09  --resolution_flag                       true
% 1.79/1.09  --res_lit_sel                           adaptive
% 1.79/1.09  --res_lit_sel_side                      none
% 1.79/1.09  --res_ordering                          kbo
% 1.79/1.09  --res_to_prop_solver                    active
% 1.79/1.09  --res_prop_simpl_new                    false
% 1.79/1.09  --res_prop_simpl_given                  true
% 1.79/1.09  --res_passive_queue_type                priority_queues
% 1.79/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/1.09  --res_passive_queues_freq               [15;5]
% 1.79/1.09  --res_forward_subs                      full
% 1.79/1.09  --res_backward_subs                     full
% 1.79/1.09  --res_forward_subs_resolution           true
% 1.79/1.09  --res_backward_subs_resolution          true
% 1.79/1.09  --res_orphan_elimination                true
% 1.79/1.09  --res_time_limit                        2.
% 1.79/1.09  --res_out_proof                         true
% 1.79/1.09  
% 1.79/1.09  ------ Superposition Options
% 1.79/1.09  
% 1.79/1.09  --superposition_flag                    true
% 1.79/1.09  --sup_passive_queue_type                priority_queues
% 1.79/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/1.09  --sup_passive_queues_freq               [8;1;4]
% 1.79/1.09  --demod_completeness_check              fast
% 1.79/1.09  --demod_use_ground                      true
% 1.79/1.09  --sup_to_prop_solver                    passive
% 1.79/1.09  --sup_prop_simpl_new                    true
% 1.79/1.09  --sup_prop_simpl_given                  true
% 1.79/1.09  --sup_fun_splitting                     false
% 1.79/1.09  --sup_smt_interval                      50000
% 1.79/1.09  
% 1.79/1.09  ------ Superposition Simplification Setup
% 1.79/1.09  
% 1.79/1.09  --sup_indices_passive                   []
% 1.79/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.09  --sup_full_bw                           [BwDemod]
% 1.79/1.09  --sup_immed_triv                        [TrivRules]
% 1.79/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.09  --sup_immed_bw_main                     []
% 1.79/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.09  
% 1.79/1.09  ------ Combination Options
% 1.79/1.09  
% 1.79/1.09  --comb_res_mult                         3
% 1.79/1.09  --comb_sup_mult                         2
% 1.79/1.09  --comb_inst_mult                        10
% 1.79/1.09  
% 1.79/1.09  ------ Debug Options
% 1.79/1.09  
% 1.79/1.09  --dbg_backtrace                         false
% 1.79/1.09  --dbg_dump_prop_clauses                 false
% 1.79/1.09  --dbg_dump_prop_clauses_file            -
% 1.79/1.09  --dbg_out_stat                          false
% 1.79/1.09  ------ Parsing...
% 1.79/1.09  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.79/1.09  
% 1.79/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.79/1.09  
% 1.79/1.09  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.79/1.09  
% 1.79/1.09  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.79/1.09  ------ Proving...
% 1.79/1.09  ------ Problem Properties 
% 1.79/1.09  
% 1.79/1.09  
% 1.79/1.09  clauses                                 24
% 1.79/1.09  conjectures                             2
% 1.79/1.09  EPR                                     0
% 1.79/1.09  Horn                                    15
% 1.79/1.09  unary                                   7
% 1.79/1.09  binary                                  8
% 1.79/1.09  lits                                    54
% 1.79/1.09  lits eq                                 22
% 1.79/1.09  fd_pure                                 0
% 1.79/1.09  fd_pseudo                               0
% 1.79/1.09  fd_cond                                 1
% 1.79/1.09  fd_pseudo_cond                          7
% 1.79/1.09  AC symbols                              0
% 1.79/1.09  
% 1.79/1.09  ------ Schedule dynamic 5 is on 
% 1.79/1.09  
% 1.79/1.09  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.79/1.09  
% 1.79/1.09  
% 1.79/1.09  ------ 
% 1.79/1.09  Current options:
% 1.79/1.09  ------ 
% 1.79/1.09  
% 1.79/1.09  ------ Input Options
% 1.79/1.09  
% 1.79/1.09  --out_options                           all
% 1.79/1.09  --tptp_safe_out                         true
% 1.79/1.09  --problem_path                          ""
% 1.79/1.09  --include_path                          ""
% 1.79/1.09  --clausifier                            res/vclausify_rel
% 1.79/1.09  --clausifier_options                    --mode clausify
% 1.79/1.09  --stdin                                 false
% 1.79/1.09  --stats_out                             all
% 1.79/1.09  
% 1.79/1.09  ------ General Options
% 1.79/1.09  
% 1.79/1.09  --fof                                   false
% 1.79/1.09  --time_out_real                         305.
% 1.79/1.09  --time_out_virtual                      -1.
% 1.79/1.09  --symbol_type_check                     false
% 1.79/1.09  --clausify_out                          false
% 1.79/1.09  --sig_cnt_out                           false
% 1.79/1.09  --trig_cnt_out                          false
% 1.79/1.09  --trig_cnt_out_tolerance                1.
% 1.79/1.09  --trig_cnt_out_sk_spl                   false
% 1.79/1.09  --abstr_cl_out                          false
% 1.79/1.09  
% 1.79/1.09  ------ Global Options
% 1.79/1.09  
% 1.79/1.09  --schedule                              default
% 1.79/1.09  --add_important_lit                     false
% 1.79/1.09  --prop_solver_per_cl                    1000
% 1.79/1.09  --min_unsat_core                        false
% 1.79/1.09  --soft_assumptions                      false
% 1.79/1.09  --soft_lemma_size                       3
% 1.79/1.09  --prop_impl_unit_size                   0
% 1.79/1.09  --prop_impl_unit                        []
% 1.79/1.09  --share_sel_clauses                     true
% 1.79/1.09  --reset_solvers                         false
% 1.79/1.09  --bc_imp_inh                            [conj_cone]
% 1.79/1.09  --conj_cone_tolerance                   3.
% 1.79/1.09  --extra_neg_conj                        none
% 1.79/1.09  --large_theory_mode                     true
% 1.79/1.09  --prolific_symb_bound                   200
% 1.79/1.09  --lt_threshold                          2000
% 1.79/1.09  --clause_weak_htbl                      true
% 1.79/1.09  --gc_record_bc_elim                     false
% 1.79/1.09  
% 1.79/1.09  ------ Preprocessing Options
% 1.79/1.09  
% 1.79/1.09  --preprocessing_flag                    true
% 1.79/1.09  --time_out_prep_mult                    0.1
% 1.79/1.09  --splitting_mode                        input
% 1.79/1.09  --splitting_grd                         true
% 1.79/1.09  --splitting_cvd                         false
% 1.79/1.09  --splitting_cvd_svl                     false
% 1.79/1.09  --splitting_nvd                         32
% 1.79/1.09  --sub_typing                            true
% 1.79/1.09  --prep_gs_sim                           true
% 1.79/1.09  --prep_unflatten                        true
% 1.79/1.09  --prep_res_sim                          true
% 1.79/1.09  --prep_upred                            true
% 1.79/1.09  --prep_sem_filter                       exhaustive
% 1.79/1.09  --prep_sem_filter_out                   false
% 1.79/1.09  --pred_elim                             true
% 1.79/1.09  --res_sim_input                         true
% 1.79/1.09  --eq_ax_congr_red                       true
% 1.79/1.09  --pure_diseq_elim                       true
% 1.79/1.09  --brand_transform                       false
% 1.79/1.09  --non_eq_to_eq                          false
% 1.79/1.09  --prep_def_merge                        true
% 1.79/1.09  --prep_def_merge_prop_impl              false
% 1.79/1.09  --prep_def_merge_mbd                    true
% 1.79/1.09  --prep_def_merge_tr_red                 false
% 1.79/1.09  --prep_def_merge_tr_cl                  false
% 1.79/1.09  --smt_preprocessing                     true
% 1.79/1.09  --smt_ac_axioms                         fast
% 1.79/1.09  --preprocessed_out                      false
% 1.79/1.09  --preprocessed_stats                    false
% 1.79/1.09  
% 1.79/1.09  ------ Abstraction refinement Options
% 1.79/1.09  
% 1.79/1.09  --abstr_ref                             []
% 1.79/1.09  --abstr_ref_prep                        false
% 1.79/1.09  --abstr_ref_until_sat                   false
% 1.79/1.09  --abstr_ref_sig_restrict                funpre
% 1.79/1.09  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/1.09  --abstr_ref_under                       []
% 1.79/1.09  
% 1.79/1.09  ------ SAT Options
% 1.79/1.09  
% 1.79/1.09  --sat_mode                              false
% 1.79/1.09  --sat_fm_restart_options                ""
% 1.79/1.09  --sat_gr_def                            false
% 1.79/1.09  --sat_epr_types                         true
% 1.79/1.09  --sat_non_cyclic_types                  false
% 1.79/1.09  --sat_finite_models                     false
% 1.79/1.09  --sat_fm_lemmas                         false
% 1.79/1.09  --sat_fm_prep                           false
% 1.79/1.09  --sat_fm_uc_incr                        true
% 1.79/1.09  --sat_out_model                         small
% 1.79/1.09  --sat_out_clauses                       false
% 1.79/1.09  
% 1.79/1.09  ------ QBF Options
% 1.79/1.09  
% 1.79/1.09  --qbf_mode                              false
% 1.79/1.09  --qbf_elim_univ                         false
% 1.79/1.09  --qbf_dom_inst                          none
% 1.79/1.09  --qbf_dom_pre_inst                      false
% 1.79/1.09  --qbf_sk_in                             false
% 1.79/1.09  --qbf_pred_elim                         true
% 1.79/1.09  --qbf_split                             512
% 1.79/1.09  
% 1.79/1.09  ------ BMC1 Options
% 1.79/1.09  
% 1.79/1.09  --bmc1_incremental                      false
% 1.79/1.09  --bmc1_axioms                           reachable_all
% 1.79/1.09  --bmc1_min_bound                        0
% 1.79/1.09  --bmc1_max_bound                        -1
% 1.79/1.09  --bmc1_max_bound_default                -1
% 1.79/1.09  --bmc1_symbol_reachability              true
% 1.79/1.09  --bmc1_property_lemmas                  false
% 1.79/1.09  --bmc1_k_induction                      false
% 1.79/1.09  --bmc1_non_equiv_states                 false
% 1.79/1.09  --bmc1_deadlock                         false
% 1.79/1.09  --bmc1_ucm                              false
% 1.79/1.09  --bmc1_add_unsat_core                   none
% 1.79/1.09  --bmc1_unsat_core_children              false
% 1.79/1.09  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/1.09  --bmc1_out_stat                         full
% 1.79/1.09  --bmc1_ground_init                      false
% 1.79/1.09  --bmc1_pre_inst_next_state              false
% 1.79/1.09  --bmc1_pre_inst_state                   false
% 1.79/1.09  --bmc1_pre_inst_reach_state             false
% 1.79/1.09  --bmc1_out_unsat_core                   false
% 1.79/1.09  --bmc1_aig_witness_out                  false
% 1.79/1.09  --bmc1_verbose                          false
% 1.79/1.09  --bmc1_dump_clauses_tptp                false
% 1.79/1.09  --bmc1_dump_unsat_core_tptp             false
% 1.79/1.09  --bmc1_dump_file                        -
% 1.79/1.09  --bmc1_ucm_expand_uc_limit              128
% 1.79/1.09  --bmc1_ucm_n_expand_iterations          6
% 1.79/1.09  --bmc1_ucm_extend_mode                  1
% 1.79/1.09  --bmc1_ucm_init_mode                    2
% 1.79/1.09  --bmc1_ucm_cone_mode                    none
% 1.79/1.09  --bmc1_ucm_reduced_relation_type        0
% 1.79/1.09  --bmc1_ucm_relax_model                  4
% 1.79/1.09  --bmc1_ucm_full_tr_after_sat            true
% 1.79/1.09  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/1.09  --bmc1_ucm_layered_model                none
% 1.79/1.09  --bmc1_ucm_max_lemma_size               10
% 1.79/1.09  
% 1.79/1.09  ------ AIG Options
% 1.79/1.09  
% 1.79/1.09  --aig_mode                              false
% 1.79/1.09  
% 1.79/1.09  ------ Instantiation Options
% 1.79/1.09  
% 1.79/1.09  --instantiation_flag                    true
% 1.79/1.09  --inst_sos_flag                         false
% 1.79/1.09  --inst_sos_phase                        true
% 1.79/1.09  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/1.09  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/1.09  --inst_lit_sel_side                     none
% 1.79/1.09  --inst_solver_per_active                1400
% 1.79/1.09  --inst_solver_calls_frac                1.
% 1.79/1.09  --inst_passive_queue_type               priority_queues
% 1.79/1.09  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/1.09  --inst_passive_queues_freq              [25;2]
% 1.79/1.09  --inst_dismatching                      true
% 1.79/1.09  --inst_eager_unprocessed_to_passive     true
% 1.79/1.09  --inst_prop_sim_given                   true
% 1.79/1.09  --inst_prop_sim_new                     false
% 1.79/1.09  --inst_subs_new                         false
% 1.79/1.09  --inst_eq_res_simp                      false
% 1.79/1.09  --inst_subs_given                       false
% 1.79/1.09  --inst_orphan_elimination               true
% 1.79/1.09  --inst_learning_loop_flag               true
% 1.79/1.09  --inst_learning_start                   3000
% 1.79/1.09  --inst_learning_factor                  2
% 1.79/1.09  --inst_start_prop_sim_after_learn       3
% 1.79/1.09  --inst_sel_renew                        solver
% 1.79/1.09  --inst_lit_activity_flag                true
% 1.79/1.09  --inst_restr_to_given                   false
% 1.79/1.09  --inst_activity_threshold               500
% 1.79/1.09  --inst_out_proof                        true
% 1.79/1.09  
% 1.79/1.09  ------ Resolution Options
% 1.79/1.09  
% 1.79/1.09  --resolution_flag                       false
% 1.79/1.09  --res_lit_sel                           adaptive
% 1.79/1.09  --res_lit_sel_side                      none
% 1.79/1.09  --res_ordering                          kbo
% 1.79/1.09  --res_to_prop_solver                    active
% 1.79/1.09  --res_prop_simpl_new                    false
% 1.79/1.09  --res_prop_simpl_given                  true
% 1.79/1.09  --res_passive_queue_type                priority_queues
% 1.79/1.09  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/1.09  --res_passive_queues_freq               [15;5]
% 1.79/1.09  --res_forward_subs                      full
% 1.79/1.09  --res_backward_subs                     full
% 1.79/1.09  --res_forward_subs_resolution           true
% 1.79/1.09  --res_backward_subs_resolution          true
% 1.79/1.09  --res_orphan_elimination                true
% 1.79/1.09  --res_time_limit                        2.
% 1.79/1.09  --res_out_proof                         true
% 1.79/1.09  
% 1.79/1.09  ------ Superposition Options
% 1.79/1.09  
% 1.79/1.09  --superposition_flag                    true
% 1.79/1.09  --sup_passive_queue_type                priority_queues
% 1.79/1.09  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/1.09  --sup_passive_queues_freq               [8;1;4]
% 1.79/1.09  --demod_completeness_check              fast
% 1.79/1.09  --demod_use_ground                      true
% 1.79/1.09  --sup_to_prop_solver                    passive
% 1.79/1.09  --sup_prop_simpl_new                    true
% 1.79/1.09  --sup_prop_simpl_given                  true
% 1.79/1.09  --sup_fun_splitting                     false
% 1.79/1.09  --sup_smt_interval                      50000
% 1.79/1.09  
% 1.79/1.09  ------ Superposition Simplification Setup
% 1.79/1.09  
% 1.79/1.09  --sup_indices_passive                   []
% 1.79/1.09  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.09  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.09  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/1.09  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/1.09  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.09  --sup_full_bw                           [BwDemod]
% 1.79/1.09  --sup_immed_triv                        [TrivRules]
% 1.79/1.09  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/1.09  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.09  --sup_immed_bw_main                     []
% 1.79/1.09  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.09  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/1.09  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/1.09  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/1.09  
% 1.79/1.09  ------ Combination Options
% 1.79/1.09  
% 1.79/1.09  --comb_res_mult                         3
% 1.79/1.09  --comb_sup_mult                         2
% 1.79/1.09  --comb_inst_mult                        10
% 1.79/1.09  
% 1.79/1.09  ------ Debug Options
% 1.79/1.09  
% 1.79/1.09  --dbg_backtrace                         false
% 1.79/1.09  --dbg_dump_prop_clauses                 false
% 1.79/1.09  --dbg_dump_prop_clauses_file            -
% 1.79/1.09  --dbg_out_stat                          false
% 1.79/1.09  
% 1.79/1.09  
% 1.79/1.09  
% 1.79/1.09  
% 1.79/1.09  ------ Proving...
% 1.79/1.09  
% 1.79/1.09  
% 1.79/1.09  % SZS status Theorem for theBenchmark.p
% 1.79/1.09  
% 1.79/1.09  % SZS output start CNFRefutation for theBenchmark.p
% 1.79/1.09  
% 1.79/1.09  fof(f2,axiom,(
% 1.79/1.09    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f26,plain,(
% 1.79/1.09    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/1.09    inference(nnf_transformation,[],[f2])).
% 1.79/1.09  
% 1.79/1.09  fof(f27,plain,(
% 1.79/1.09    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/1.09    inference(flattening,[],[f26])).
% 1.79/1.09  
% 1.79/1.09  fof(f28,plain,(
% 1.79/1.09    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/1.09    inference(rectify,[],[f27])).
% 1.79/1.09  
% 1.79/1.09  fof(f29,plain,(
% 1.79/1.09    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.79/1.09    introduced(choice_axiom,[])).
% 1.79/1.09  
% 1.79/1.09  fof(f30,plain,(
% 1.79/1.09    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 1.79/1.09  
% 1.79/1.09  fof(f45,plain,(
% 1.79/1.09    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.79/1.09    inference(cnf_transformation,[],[f30])).
% 1.79/1.09  
% 1.79/1.09  fof(f96,plain,(
% 1.79/1.09    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.79/1.09    inference(equality_resolution,[],[f45])).
% 1.79/1.09  
% 1.79/1.09  fof(f9,axiom,(
% 1.79/1.09    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f23,plain,(
% 1.79/1.09    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.79/1.09    inference(ennf_transformation,[],[f9])).
% 1.79/1.09  
% 1.79/1.09  fof(f35,plain,(
% 1.79/1.09    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/1.09    inference(nnf_transformation,[],[f23])).
% 1.79/1.09  
% 1.79/1.09  fof(f36,plain,(
% 1.79/1.09    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/1.09    inference(flattening,[],[f35])).
% 1.79/1.09  
% 1.79/1.09  fof(f37,plain,(
% 1.79/1.09    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/1.09    inference(rectify,[],[f36])).
% 1.79/1.09  
% 1.79/1.09  fof(f38,plain,(
% 1.79/1.09    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.79/1.09    introduced(choice_axiom,[])).
% 1.79/1.09  
% 1.79/1.09  fof(f39,plain,(
% 1.79/1.09    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.79/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 1.79/1.09  
% 1.79/1.09  fof(f57,plain,(
% 1.79/1.09    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.79/1.09    inference(cnf_transformation,[],[f39])).
% 1.79/1.09  
% 1.79/1.09  fof(f12,axiom,(
% 1.79/1.09    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f67,plain,(
% 1.79/1.09    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.79/1.09    inference(cnf_transformation,[],[f12])).
% 1.79/1.09  
% 1.79/1.09  fof(f13,axiom,(
% 1.79/1.09    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f68,plain,(
% 1.79/1.09    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.79/1.09    inference(cnf_transformation,[],[f13])).
% 1.79/1.09  
% 1.79/1.09  fof(f14,axiom,(
% 1.79/1.09    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f69,plain,(
% 1.79/1.09    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.79/1.09    inference(cnf_transformation,[],[f14])).
% 1.79/1.09  
% 1.79/1.09  fof(f15,axiom,(
% 1.79/1.09    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f70,plain,(
% 1.79/1.09    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.79/1.09    inference(cnf_transformation,[],[f15])).
% 1.79/1.09  
% 1.79/1.09  fof(f74,plain,(
% 1.79/1.09    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 1.79/1.09    inference(definition_unfolding,[],[f69,f70])).
% 1.79/1.09  
% 1.79/1.09  fof(f75,plain,(
% 1.79/1.09    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 1.79/1.09    inference(definition_unfolding,[],[f68,f74])).
% 1.79/1.09  
% 1.79/1.09  fof(f76,plain,(
% 1.79/1.09    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 1.79/1.09    inference(definition_unfolding,[],[f67,f75])).
% 1.79/1.09  
% 1.79/1.09  fof(f91,plain,(
% 1.79/1.09    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.79/1.09    inference(definition_unfolding,[],[f57,f76])).
% 1.79/1.09  
% 1.79/1.09  fof(f104,plain,(
% 1.79/1.09    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 1.79/1.09    inference(equality_resolution,[],[f91])).
% 1.79/1.09  
% 1.79/1.09  fof(f49,plain,(
% 1.79/1.09    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 1.79/1.09    inference(cnf_transformation,[],[f30])).
% 1.79/1.09  
% 1.79/1.09  fof(f47,plain,(
% 1.79/1.09    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 1.79/1.09    inference(cnf_transformation,[],[f30])).
% 1.79/1.09  
% 1.79/1.09  fof(f58,plain,(
% 1.79/1.09    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.79/1.09    inference(cnf_transformation,[],[f39])).
% 1.79/1.09  
% 1.79/1.09  fof(f90,plain,(
% 1.79/1.09    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.79/1.09    inference(definition_unfolding,[],[f58,f76])).
% 1.79/1.09  
% 1.79/1.09  fof(f102,plain,(
% 1.79/1.09    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 1.79/1.09    inference(equality_resolution,[],[f90])).
% 1.79/1.09  
% 1.79/1.09  fof(f103,plain,(
% 1.79/1.09    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 1.79/1.09    inference(equality_resolution,[],[f102])).
% 1.79/1.09  
% 1.79/1.09  fof(f17,conjecture,(
% 1.79/1.09    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f18,negated_conjecture,(
% 1.79/1.09    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.79/1.09    inference(negated_conjecture,[],[f17])).
% 1.79/1.09  
% 1.79/1.09  fof(f25,plain,(
% 1.79/1.09    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.79/1.09    inference(ennf_transformation,[],[f18])).
% 1.79/1.09  
% 1.79/1.09  fof(f40,plain,(
% 1.79/1.09    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.79/1.09    inference(nnf_transformation,[],[f25])).
% 1.79/1.09  
% 1.79/1.09  fof(f41,plain,(
% 1.79/1.09    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4))),
% 1.79/1.09    introduced(choice_axiom,[])).
% 1.79/1.09  
% 1.79/1.09  fof(f42,plain,(
% 1.79/1.09    (r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4)),
% 1.79/1.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).
% 1.79/1.09  
% 1.79/1.09  fof(f73,plain,(
% 1.79/1.09    r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4),
% 1.79/1.09    inference(cnf_transformation,[],[f42])).
% 1.79/1.09  
% 1.79/1.09  fof(f10,axiom,(
% 1.79/1.09    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f65,plain,(
% 1.79/1.09    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.79/1.09    inference(cnf_transformation,[],[f10])).
% 1.79/1.09  
% 1.79/1.09  fof(f11,axiom,(
% 1.79/1.09    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.79/1.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/1.09  
% 1.79/1.09  fof(f66,plain,(
% 1.79/1.09    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.79/1.09    inference(cnf_transformation,[],[f11])).
% 1.79/1.09  
% 1.79/1.09  fof(f77,plain,(
% 1.79/1.09    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.79/1.09    inference(definition_unfolding,[],[f66,f76])).
% 1.79/1.09  
% 1.79/1.09  fof(f78,plain,(
% 1.79/1.09    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 1.79/1.09    inference(definition_unfolding,[],[f65,f77])).
% 1.79/1.09  
% 1.79/1.09  fof(f93,plain,(
% 1.79/1.09    r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4),
% 1.79/1.09    inference(definition_unfolding,[],[f73,f78])).
% 1.79/1.09  
% 1.79/1.09  fof(f72,plain,(
% 1.79/1.09    ~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4),
% 1.79/1.09    inference(cnf_transformation,[],[f42])).
% 1.79/1.09  
% 1.79/1.09  fof(f94,plain,(
% 1.79/1.09    ~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4),
% 1.79/1.09    inference(definition_unfolding,[],[f72,f78])).
% 1.79/1.09  
% 1.79/1.09  cnf(c_324,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_2184,plain,
% 1.79/1.09      ( X0 != X1
% 1.79/1.09      | X0 = sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
% 1.79/1.09      | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != X1 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_324]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_2185,plain,
% 1.79/1.09      ( sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != sK5
% 1.79/1.09      | sK5 = sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
% 1.79/1.09      | sK5 != sK5 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_2184]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_327,plain,
% 1.79/1.09      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.79/1.09      theory(equality) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1055,plain,
% 1.79/1.09      ( r2_hidden(X0,X1)
% 1.79/1.09      | ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),sK4)
% 1.79/1.09      | X0 != sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
% 1.79/1.09      | X1 != sK4 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_327]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1691,plain,
% 1.79/1.09      ( ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),sK4)
% 1.79/1.09      | r2_hidden(sK5,sK4)
% 1.79/1.09      | sK4 != sK4
% 1.79/1.09      | sK5 != sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_1055]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_6,plain,
% 1.79/1.09      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 1.79/1.09      inference(cnf_transformation,[],[f96]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1646,plain,
% 1.79/1.09      ( ~ r2_hidden(X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 1.79/1.09      | ~ r2_hidden(X0,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_6]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1647,plain,
% 1.79/1.09      ( r2_hidden(X0,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 1.79/1.09      | r2_hidden(X0,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
% 1.79/1.09      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1649,plain,
% 1.79/1.09      ( r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 1.79/1.09      | r2_hidden(sK5,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_1647]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1097,plain,
% 1.79/1.09      ( ~ r2_hidden(X0,X1)
% 1.79/1.09      | r2_hidden(X2,k4_xboole_0(X3,X4))
% 1.79/1.09      | X2 != X0
% 1.79/1.09      | k4_xboole_0(X3,X4) != X1 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_327]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1564,plain,
% 1.79/1.09      ( r2_hidden(X0,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 1.79/1.09      | ~ r2_hidden(X1,sK4)
% 1.79/1.09      | X0 != X1
% 1.79/1.09      | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_1097]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1565,plain,
% 1.79/1.09      ( X0 != X1
% 1.79/1.09      | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4
% 1.79/1.09      | r2_hidden(X0,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = iProver_top
% 1.79/1.09      | r2_hidden(X1,sK4) != iProver_top ),
% 1.79/1.09      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1567,plain,
% 1.79/1.09      ( k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4
% 1.79/1.09      | sK5 != sK5
% 1.79/1.09      | r2_hidden(sK5,k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = iProver_top
% 1.79/1.09      | r2_hidden(sK5,sK4) != iProver_top ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_1565]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_20,plain,
% 1.79/1.09      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
% 1.79/1.09      | X0 = X1
% 1.79/1.09      | X0 = X2
% 1.79/1.09      | X0 = X3 ),
% 1.79/1.09      inference(cnf_transformation,[],[f104]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1504,plain,
% 1.79/1.09      ( ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
% 1.79/1.09      | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = X0
% 1.79/1.09      | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = X2
% 1.79/1.09      | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = X1 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_20]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1506,plain,
% 1.79/1.09      ( ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 1.79/1.09      | sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = sK5 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_1504]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_323,plain,( X0 = X0 ),theory(equality) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1455,plain,
% 1.79/1.09      ( sK4 = sK4 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_323]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_2,plain,
% 1.79/1.09      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 1.79/1.09      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 1.79/1.09      | r2_hidden(sK0(X0,X1,X2),X1)
% 1.79/1.09      | k4_xboole_0(X0,X1) = X2 ),
% 1.79/1.09      inference(cnf_transformation,[],[f49]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1040,plain,
% 1.79/1.09      ( r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 1.79/1.09      | ~ r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),sK4)
% 1.79/1.09      | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_2]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_4,plain,
% 1.79/1.09      ( r2_hidden(sK0(X0,X1,X2),X0)
% 1.79/1.09      | r2_hidden(sK0(X0,X1,X2),X2)
% 1.79/1.09      | k4_xboole_0(X0,X1) = X2 ),
% 1.79/1.09      inference(cnf_transformation,[],[f47]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_1032,plain,
% 1.79/1.09      ( r2_hidden(sK0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4),sK4)
% 1.79/1.09      | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_4]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_19,plain,
% 1.79/1.09      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 1.79/1.09      inference(cnf_transformation,[],[f103]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_32,plain,
% 1.79/1.09      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 1.79/1.09      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_34,plain,
% 1.79/1.09      ( r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_32]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_33,plain,
% 1.79/1.09      ( r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_19]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_30,plain,
% 1.79/1.09      ( ~ r2_hidden(sK5,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 1.79/1.09      | sK5 = sK5 ),
% 1.79/1.09      inference(instantiation,[status(thm)],[c_20]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_22,negated_conjecture,
% 1.79/1.09      ( r2_hidden(sK5,sK4)
% 1.79/1.09      | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4 ),
% 1.79/1.09      inference(cnf_transformation,[],[f93]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_25,plain,
% 1.79/1.09      ( k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != sK4
% 1.79/1.09      | r2_hidden(sK5,sK4) = iProver_top ),
% 1.79/1.09      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_23,negated_conjecture,
% 1.79/1.09      ( ~ r2_hidden(sK5,sK4)
% 1.79/1.09      | k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4 ),
% 1.79/1.09      inference(cnf_transformation,[],[f94]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(c_24,plain,
% 1.79/1.09      ( k4_xboole_0(sK4,k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = sK4
% 1.79/1.09      | r2_hidden(sK5,sK4) != iProver_top ),
% 1.79/1.09      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.79/1.09  
% 1.79/1.09  cnf(contradiction,plain,
% 1.79/1.09      ( $false ),
% 1.79/1.09      inference(minisat,
% 1.79/1.09                [status(thm)],
% 1.79/1.09                [c_2185,c_1691,c_1649,c_1567,c_1506,c_1455,c_1040,c_1032,
% 1.79/1.09                 c_34,c_33,c_30,c_25,c_24,c_23]) ).
% 1.79/1.09  
% 1.79/1.09  
% 1.79/1.09  % SZS output end CNFRefutation for theBenchmark.p
% 1.79/1.09  
% 1.79/1.09  ------                               Statistics
% 1.79/1.09  
% 1.79/1.09  ------ General
% 1.79/1.09  
% 1.79/1.09  abstr_ref_over_cycles:                  0
% 1.79/1.09  abstr_ref_under_cycles:                 0
% 1.79/1.09  gc_basic_clause_elim:                   0
% 1.79/1.09  forced_gc_time:                         0
% 1.79/1.09  parsing_time:                           0.022
% 1.79/1.09  unif_index_cands_time:                  0.
% 1.79/1.09  unif_index_add_time:                    0.
% 1.79/1.09  orderings_time:                         0.
% 1.79/1.09  out_proof_time:                         0.007
% 1.79/1.09  total_time:                             0.182
% 1.79/1.09  num_of_symbols:                         43
% 1.79/1.09  num_of_terms:                           2603
% 1.79/1.09  
% 1.79/1.09  ------ Preprocessing
% 1.79/1.09  
% 1.79/1.09  num_of_splits:                          0
% 1.79/1.09  num_of_split_atoms:                     0
% 1.79/1.09  num_of_reused_defs:                     0
% 1.79/1.09  num_eq_ax_congr_red:                    24
% 1.79/1.09  num_of_sem_filtered_clauses:            1
% 1.79/1.09  num_of_subtypes:                        0
% 1.79/1.09  monotx_restored_types:                  0
% 1.79/1.09  sat_num_of_epr_types:                   0
% 1.79/1.09  sat_num_of_non_cyclic_types:            0
% 1.79/1.09  sat_guarded_non_collapsed_types:        0
% 1.79/1.09  num_pure_diseq_elim:                    0
% 1.79/1.09  simp_replaced_by:                       0
% 1.79/1.09  res_preprocessed:                       87
% 1.79/1.09  prep_upred:                             0
% 1.79/1.09  prep_unflattend:                        4
% 1.79/1.09  smt_new_axioms:                         0
% 1.79/1.09  pred_elim_cands:                        2
% 1.79/1.09  pred_elim:                              0
% 1.79/1.09  pred_elim_cl:                           0
% 1.79/1.09  pred_elim_cycles:                       1
% 1.79/1.09  merged_defs:                            6
% 1.79/1.09  merged_defs_ncl:                        0
% 1.79/1.09  bin_hyper_res:                          6
% 1.79/1.09  prep_cycles:                            3
% 1.79/1.09  pred_elim_time:                         0.001
% 1.79/1.09  splitting_time:                         0.
% 1.79/1.09  sem_filter_time:                        0.
% 1.79/1.09  monotx_time:                            0.
% 1.79/1.09  subtype_inf_time:                       0.
% 1.79/1.09  
% 1.79/1.09  ------ Problem properties
% 1.79/1.09  
% 1.79/1.09  clauses:                                24
% 1.79/1.09  conjectures:                            2
% 1.79/1.09  epr:                                    0
% 1.79/1.09  horn:                                   15
% 1.79/1.09  ground:                                 2
% 1.79/1.09  unary:                                  7
% 1.79/1.09  binary:                                 8
% 1.79/1.09  lits:                                   54
% 1.79/1.09  lits_eq:                                22
% 1.79/1.09  fd_pure:                                0
% 1.79/1.09  fd_pseudo:                              0
% 1.79/1.09  fd_cond:                                1
% 1.79/1.09  fd_pseudo_cond:                         7
% 1.79/1.09  ac_symbols:                             0
% 1.79/1.09  
% 1.79/1.09  ------ Propositional Solver
% 1.79/1.09  
% 1.79/1.09  prop_solver_calls:                      21
% 1.79/1.09  prop_fast_solver_calls:                 456
% 1.79/1.09  smt_solver_calls:                       0
% 1.79/1.09  smt_fast_solver_calls:                  0
% 1.79/1.09  prop_num_of_clauses:                    720
% 1.79/1.09  prop_preprocess_simplified:             3201
% 1.79/1.09  prop_fo_subsumed:                       0
% 1.79/1.09  prop_solver_time:                       0.
% 1.79/1.09  smt_solver_time:                        0.
% 1.79/1.09  smt_fast_solver_time:                   0.
% 1.79/1.09  prop_fast_solver_time:                  0.
% 1.79/1.09  prop_unsat_core_time:                   0.
% 1.79/1.09  
% 1.79/1.09  ------ QBF
% 1.79/1.09  
% 1.79/1.09  qbf_q_res:                              0
% 1.79/1.09  qbf_num_tautologies:                    0
% 1.79/1.09  qbf_prep_cycles:                        0
% 1.79/1.09  
% 1.79/1.09  ------ BMC1
% 1.79/1.09  
% 1.79/1.09  bmc1_current_bound:                     -1
% 1.79/1.09  bmc1_last_solved_bound:                 -1
% 1.79/1.09  bmc1_unsat_core_size:                   -1
% 1.79/1.09  bmc1_unsat_core_parents_size:           -1
% 1.79/1.09  bmc1_merge_next_fun:                    0
% 1.79/1.09  bmc1_unsat_core_clauses_time:           0.
% 1.79/1.09  
% 1.79/1.09  ------ Instantiation
% 1.79/1.09  
% 1.79/1.09  inst_num_of_clauses:                    202
% 1.79/1.09  inst_num_in_passive:                    54
% 1.79/1.09  inst_num_in_active:                     81
% 1.79/1.09  inst_num_in_unprocessed:                66
% 1.79/1.09  inst_num_of_loops:                      115
% 1.79/1.09  inst_num_of_learning_restarts:          0
% 1.79/1.09  inst_num_moves_active_passive:          30
% 1.79/1.09  inst_lit_activity:                      0
% 1.79/1.09  inst_lit_activity_moves:                0
% 1.79/1.09  inst_num_tautologies:                   0
% 1.79/1.09  inst_num_prop_implied:                  0
% 1.79/1.09  inst_num_existing_simplified:           0
% 1.79/1.09  inst_num_eq_res_simplified:             0
% 1.79/1.09  inst_num_child_elim:                    0
% 1.79/1.09  inst_num_of_dismatching_blockings:      169
% 1.79/1.09  inst_num_of_non_proper_insts:           141
% 1.79/1.09  inst_num_of_duplicates:                 0
% 1.79/1.09  inst_inst_num_from_inst_to_res:         0
% 1.79/1.09  inst_dismatching_checking_time:         0.
% 1.79/1.09  
% 1.79/1.09  ------ Resolution
% 1.79/1.09  
% 1.79/1.09  res_num_of_clauses:                     0
% 1.79/1.09  res_num_in_passive:                     0
% 1.79/1.09  res_num_in_active:                      0
% 1.79/1.09  res_num_of_loops:                       90
% 1.79/1.09  res_forward_subset_subsumed:            5
% 1.79/1.09  res_backward_subset_subsumed:           0
% 1.79/1.09  res_forward_subsumed:                   0
% 1.79/1.09  res_backward_subsumed:                  0
% 1.79/1.09  res_forward_subsumption_resolution:     0
% 1.79/1.09  res_backward_subsumption_resolution:    0
% 1.79/1.09  res_clause_to_clause_subsumption:       213
% 1.79/1.09  res_orphan_elimination:                 0
% 1.79/1.09  res_tautology_del:                      15
% 1.79/1.09  res_num_eq_res_simplified:              0
% 1.79/1.09  res_num_sel_changes:                    0
% 1.79/1.09  res_moves_from_active_to_pass:          0
% 1.79/1.09  
% 1.79/1.09  ------ Superposition
% 1.79/1.09  
% 1.79/1.09  sup_time_total:                         0.
% 1.79/1.09  sup_time_generating:                    0.
% 1.79/1.09  sup_time_sim_full:                      0.
% 1.79/1.09  sup_time_sim_immed:                     0.
% 1.79/1.09  
% 1.79/1.09  sup_num_of_clauses:                     46
% 1.79/1.09  sup_num_in_active:                      22
% 1.79/1.09  sup_num_in_passive:                     24
% 1.79/1.09  sup_num_of_loops:                       22
% 1.79/1.09  sup_fw_superposition:                   29
% 1.79/1.09  sup_bw_superposition:                   23
% 1.79/1.09  sup_immediate_simplified:               10
% 1.79/1.09  sup_given_eliminated:                   0
% 1.79/1.09  comparisons_done:                       0
% 1.79/1.09  comparisons_avoided:                    0
% 1.79/1.09  
% 1.79/1.09  ------ Simplifications
% 1.79/1.09  
% 1.79/1.09  
% 1.79/1.09  sim_fw_subset_subsumed:                 0
% 1.79/1.09  sim_bw_subset_subsumed:                 0
% 1.79/1.09  sim_fw_subsumed:                        4
% 1.79/1.09  sim_bw_subsumed:                        0
% 1.79/1.09  sim_fw_subsumption_res:                 0
% 1.79/1.09  sim_bw_subsumption_res:                 0
% 1.79/1.09  sim_tautology_del:                      0
% 1.79/1.09  sim_eq_tautology_del:                   1
% 1.79/1.09  sim_eq_res_simp:                        0
% 1.79/1.09  sim_fw_demodulated:                     0
% 1.79/1.09  sim_bw_demodulated:                     0
% 1.79/1.09  sim_light_normalised:                   7
% 1.79/1.09  sim_joinable_taut:                      0
% 1.79/1.09  sim_joinable_simp:                      0
% 1.79/1.09  sim_ac_normalised:                      0
% 1.79/1.09  sim_smt_subsumption:                    0
% 1.79/1.09  
%------------------------------------------------------------------------------
