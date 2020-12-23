%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:00 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 214 expanded)
%              Number of clauses        :   39 (  46 expanded)
%              Number of leaves         :   13 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  356 (1043 expanded)
%              Number of equality atoms :  188 ( 624 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f100,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) )
        & ( ~ r2_hidden(X0,X1)
          | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) ) )
   => ( ( r2_hidden(sK3,sK4)
        | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) )
      & ( ~ r2_hidden(sK3,sK4)
        | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( r2_hidden(sK3,sK4)
      | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) )
    & ( ~ r2_hidden(sK3,sK4)
      | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).

fof(f70,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f70,f73,f73])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f98,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f99,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f98])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f71,f73,f73])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_17231,plain,
    ( ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X0,X1,X2))
    | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X0
    | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X1
    | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_17233,plain,
    ( ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_17231])).

cnf(c_564,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_15073,plain,
    ( X0 != X1
    | X0 = sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_15074,plain,
    ( sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK3
    | sK3 = sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_15073])).

cnf(c_568,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2145,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK4)
    | X2 != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_4051,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,sK4)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2145])).

cnf(c_10008,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | X0 != sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4051])).

cnf(c_10010,plain,
    ( ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | r2_hidden(sK3,sK4)
    | sK4 != sK4
    | sK3 != sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_10008])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1121,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1118,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4070,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3)
    | k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_1121,c_1118])).

cnf(c_37,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_40,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1472,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(X3,X4))
    | X2 != X0
    | k4_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_568])).

cnf(c_1574,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(X1,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | X1 != X0
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1576,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK3,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1999,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2001,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_2047,plain,
    ( r2_hidden(X0,sK4)
    | k4_xboole_0(sK4,k2_enumset1(X0,X0,X0,X0)) = sK4 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2049,plain,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK4 ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_4707,plain,
    ( k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4070,c_37,c_40,c_1576,c_2001,c_2049])).

cnf(c_563,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4052,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3940,plain,
    ( ~ r2_hidden(X0,sK4)
    | k4_xboole_0(sK4,k2_enumset1(X0,X0,X0,X0)) != sK4 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3942,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK4 ),
    inference(instantiation,[status(thm)],[c_3940])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1400,plain,
    ( ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1392,plain,
    ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK3,sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17233,c_15074,c_10010,c_4707,c_4052,c_3942,c_1400,c_1392,c_40,c_37,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:28:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.12/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.12/0.99  
% 3.12/0.99  ------  iProver source info
% 3.12/0.99  
% 3.12/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.12/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.12/0.99  git: non_committed_changes: false
% 3.12/0.99  git: last_make_outside_of_git: false
% 3.12/0.99  
% 3.12/0.99  ------ 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options
% 3.12/0.99  
% 3.12/0.99  --out_options                           all
% 3.12/0.99  --tptp_safe_out                         true
% 3.12/0.99  --problem_path                          ""
% 3.12/0.99  --include_path                          ""
% 3.12/0.99  --clausifier                            res/vclausify_rel
% 3.12/0.99  --clausifier_options                    --mode clausify
% 3.12/0.99  --stdin                                 false
% 3.12/0.99  --stats_out                             all
% 3.12/0.99  
% 3.12/0.99  ------ General Options
% 3.12/0.99  
% 3.12/0.99  --fof                                   false
% 3.12/0.99  --time_out_real                         305.
% 3.12/0.99  --time_out_virtual                      -1.
% 3.12/0.99  --symbol_type_check                     false
% 3.12/0.99  --clausify_out                          false
% 3.12/0.99  --sig_cnt_out                           false
% 3.12/0.99  --trig_cnt_out                          false
% 3.12/0.99  --trig_cnt_out_tolerance                1.
% 3.12/0.99  --trig_cnt_out_sk_spl                   false
% 3.12/0.99  --abstr_cl_out                          false
% 3.12/0.99  
% 3.12/0.99  ------ Global Options
% 3.12/0.99  
% 3.12/0.99  --schedule                              default
% 3.12/0.99  --add_important_lit                     false
% 3.12/0.99  --prop_solver_per_cl                    1000
% 3.12/0.99  --min_unsat_core                        false
% 3.12/0.99  --soft_assumptions                      false
% 3.12/0.99  --soft_lemma_size                       3
% 3.12/0.99  --prop_impl_unit_size                   0
% 3.12/0.99  --prop_impl_unit                        []
% 3.12/0.99  --share_sel_clauses                     true
% 3.12/0.99  --reset_solvers                         false
% 3.12/0.99  --bc_imp_inh                            [conj_cone]
% 3.12/0.99  --conj_cone_tolerance                   3.
% 3.12/0.99  --extra_neg_conj                        none
% 3.12/0.99  --large_theory_mode                     true
% 3.12/0.99  --prolific_symb_bound                   200
% 3.12/0.99  --lt_threshold                          2000
% 3.12/0.99  --clause_weak_htbl                      true
% 3.12/0.99  --gc_record_bc_elim                     false
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing Options
% 3.12/0.99  
% 3.12/0.99  --preprocessing_flag                    true
% 3.12/0.99  --time_out_prep_mult                    0.1
% 3.12/0.99  --splitting_mode                        input
% 3.12/0.99  --splitting_grd                         true
% 3.12/0.99  --splitting_cvd                         false
% 3.12/0.99  --splitting_cvd_svl                     false
% 3.12/0.99  --splitting_nvd                         32
% 3.12/0.99  --sub_typing                            true
% 3.12/0.99  --prep_gs_sim                           true
% 3.12/0.99  --prep_unflatten                        true
% 3.12/0.99  --prep_res_sim                          true
% 3.12/0.99  --prep_upred                            true
% 3.12/0.99  --prep_sem_filter                       exhaustive
% 3.12/0.99  --prep_sem_filter_out                   false
% 3.12/0.99  --pred_elim                             true
% 3.12/0.99  --res_sim_input                         true
% 3.12/0.99  --eq_ax_congr_red                       true
% 3.12/0.99  --pure_diseq_elim                       true
% 3.12/0.99  --brand_transform                       false
% 3.12/0.99  --non_eq_to_eq                          false
% 3.12/0.99  --prep_def_merge                        true
% 3.12/0.99  --prep_def_merge_prop_impl              false
% 3.12/0.99  --prep_def_merge_mbd                    true
% 3.12/0.99  --prep_def_merge_tr_red                 false
% 3.12/0.99  --prep_def_merge_tr_cl                  false
% 3.12/0.99  --smt_preprocessing                     true
% 3.12/0.99  --smt_ac_axioms                         fast
% 3.12/0.99  --preprocessed_out                      false
% 3.12/0.99  --preprocessed_stats                    false
% 3.12/0.99  
% 3.12/0.99  ------ Abstraction refinement Options
% 3.12/0.99  
% 3.12/0.99  --abstr_ref                             []
% 3.12/0.99  --abstr_ref_prep                        false
% 3.12/0.99  --abstr_ref_until_sat                   false
% 3.12/0.99  --abstr_ref_sig_restrict                funpre
% 3.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.99  --abstr_ref_under                       []
% 3.12/0.99  
% 3.12/0.99  ------ SAT Options
% 3.12/0.99  
% 3.12/0.99  --sat_mode                              false
% 3.12/0.99  --sat_fm_restart_options                ""
% 3.12/0.99  --sat_gr_def                            false
% 3.12/0.99  --sat_epr_types                         true
% 3.12/0.99  --sat_non_cyclic_types                  false
% 3.12/0.99  --sat_finite_models                     false
% 3.12/0.99  --sat_fm_lemmas                         false
% 3.12/0.99  --sat_fm_prep                           false
% 3.12/0.99  --sat_fm_uc_incr                        true
% 3.12/0.99  --sat_out_model                         small
% 3.12/0.99  --sat_out_clauses                       false
% 3.12/0.99  
% 3.12/0.99  ------ QBF Options
% 3.12/0.99  
% 3.12/0.99  --qbf_mode                              false
% 3.12/0.99  --qbf_elim_univ                         false
% 3.12/0.99  --qbf_dom_inst                          none
% 3.12/0.99  --qbf_dom_pre_inst                      false
% 3.12/0.99  --qbf_sk_in                             false
% 3.12/0.99  --qbf_pred_elim                         true
% 3.12/0.99  --qbf_split                             512
% 3.12/0.99  
% 3.12/0.99  ------ BMC1 Options
% 3.12/0.99  
% 3.12/0.99  --bmc1_incremental                      false
% 3.12/0.99  --bmc1_axioms                           reachable_all
% 3.12/0.99  --bmc1_min_bound                        0
% 3.12/0.99  --bmc1_max_bound                        -1
% 3.12/0.99  --bmc1_max_bound_default                -1
% 3.12/0.99  --bmc1_symbol_reachability              true
% 3.12/0.99  --bmc1_property_lemmas                  false
% 3.12/0.99  --bmc1_k_induction                      false
% 3.12/0.99  --bmc1_non_equiv_states                 false
% 3.12/0.99  --bmc1_deadlock                         false
% 3.12/0.99  --bmc1_ucm                              false
% 3.12/0.99  --bmc1_add_unsat_core                   none
% 3.12/0.99  --bmc1_unsat_core_children              false
% 3.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.99  --bmc1_out_stat                         full
% 3.12/0.99  --bmc1_ground_init                      false
% 3.12/0.99  --bmc1_pre_inst_next_state              false
% 3.12/0.99  --bmc1_pre_inst_state                   false
% 3.12/0.99  --bmc1_pre_inst_reach_state             false
% 3.12/0.99  --bmc1_out_unsat_core                   false
% 3.12/0.99  --bmc1_aig_witness_out                  false
% 3.12/0.99  --bmc1_verbose                          false
% 3.12/0.99  --bmc1_dump_clauses_tptp                false
% 3.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.99  --bmc1_dump_file                        -
% 3.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.99  --bmc1_ucm_extend_mode                  1
% 3.12/0.99  --bmc1_ucm_init_mode                    2
% 3.12/0.99  --bmc1_ucm_cone_mode                    none
% 3.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.99  --bmc1_ucm_relax_model                  4
% 3.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.99  --bmc1_ucm_layered_model                none
% 3.12/0.99  --bmc1_ucm_max_lemma_size               10
% 3.12/0.99  
% 3.12/0.99  ------ AIG Options
% 3.12/0.99  
% 3.12/0.99  --aig_mode                              false
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation Options
% 3.12/0.99  
% 3.12/0.99  --instantiation_flag                    true
% 3.12/0.99  --inst_sos_flag                         false
% 3.12/0.99  --inst_sos_phase                        true
% 3.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel_side                     num_symb
% 3.12/0.99  --inst_solver_per_active                1400
% 3.12/0.99  --inst_solver_calls_frac                1.
% 3.12/0.99  --inst_passive_queue_type               priority_queues
% 3.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.99  --inst_passive_queues_freq              [25;2]
% 3.12/0.99  --inst_dismatching                      true
% 3.12/0.99  --inst_eager_unprocessed_to_passive     true
% 3.12/0.99  --inst_prop_sim_given                   true
% 3.12/0.99  --inst_prop_sim_new                     false
% 3.12/0.99  --inst_subs_new                         false
% 3.12/0.99  --inst_eq_res_simp                      false
% 3.12/0.99  --inst_subs_given                       false
% 3.12/0.99  --inst_orphan_elimination               true
% 3.12/0.99  --inst_learning_loop_flag               true
% 3.12/0.99  --inst_learning_start                   3000
% 3.12/0.99  --inst_learning_factor                  2
% 3.12/0.99  --inst_start_prop_sim_after_learn       3
% 3.12/0.99  --inst_sel_renew                        solver
% 3.12/0.99  --inst_lit_activity_flag                true
% 3.12/0.99  --inst_restr_to_given                   false
% 3.12/0.99  --inst_activity_threshold               500
% 3.12/0.99  --inst_out_proof                        true
% 3.12/0.99  
% 3.12/0.99  ------ Resolution Options
% 3.12/0.99  
% 3.12/0.99  --resolution_flag                       true
% 3.12/0.99  --res_lit_sel                           adaptive
% 3.12/0.99  --res_lit_sel_side                      none
% 3.12/0.99  --res_ordering                          kbo
% 3.12/0.99  --res_to_prop_solver                    active
% 3.12/0.99  --res_prop_simpl_new                    false
% 3.12/0.99  --res_prop_simpl_given                  true
% 3.12/0.99  --res_passive_queue_type                priority_queues
% 3.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.99  --res_passive_queues_freq               [15;5]
% 3.12/0.99  --res_forward_subs                      full
% 3.12/0.99  --res_backward_subs                     full
% 3.12/0.99  --res_forward_subs_resolution           true
% 3.12/0.99  --res_backward_subs_resolution          true
% 3.12/0.99  --res_orphan_elimination                true
% 3.12/0.99  --res_time_limit                        2.
% 3.12/0.99  --res_out_proof                         true
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Options
% 3.12/0.99  
% 3.12/0.99  --superposition_flag                    true
% 3.12/0.99  --sup_passive_queue_type                priority_queues
% 3.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.99  --demod_completeness_check              fast
% 3.12/0.99  --demod_use_ground                      true
% 3.12/0.99  --sup_to_prop_solver                    passive
% 3.12/0.99  --sup_prop_simpl_new                    true
% 3.12/0.99  --sup_prop_simpl_given                  true
% 3.12/0.99  --sup_fun_splitting                     false
% 3.12/0.99  --sup_smt_interval                      50000
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Simplification Setup
% 3.12/0.99  
% 3.12/0.99  --sup_indices_passive                   []
% 3.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_full_bw                           [BwDemod]
% 3.12/0.99  --sup_immed_triv                        [TrivRules]
% 3.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_immed_bw_main                     []
% 3.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  
% 3.12/0.99  ------ Combination Options
% 3.12/0.99  
% 3.12/0.99  --comb_res_mult                         3
% 3.12/0.99  --comb_sup_mult                         2
% 3.12/0.99  --comb_inst_mult                        10
% 3.12/0.99  
% 3.12/0.99  ------ Debug Options
% 3.12/0.99  
% 3.12/0.99  --dbg_backtrace                         false
% 3.12/0.99  --dbg_dump_prop_clauses                 false
% 3.12/0.99  --dbg_dump_prop_clauses_file            -
% 3.12/0.99  --dbg_out_stat                          false
% 3.12/0.99  ------ Parsing...
% 3.12/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.12/0.99  ------ Proving...
% 3.12/0.99  ------ Problem Properties 
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  clauses                                 27
% 3.12/0.99  conjectures                             2
% 3.12/0.99  EPR                                     3
% 3.12/0.99  Horn                                    19
% 3.12/0.99  unary                                   7
% 3.12/0.99  binary                                  9
% 3.12/0.99  lits                                    62
% 3.12/0.99  lits eq                                 24
% 3.12/0.99  fd_pure                                 0
% 3.12/0.99  fd_pseudo                               0
% 3.12/0.99  fd_cond                                 0
% 3.12/0.99  fd_pseudo_cond                          8
% 3.12/0.99  AC symbols                              0
% 3.12/0.99  
% 3.12/0.99  ------ Schedule dynamic 5 is on 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  ------ 
% 3.12/0.99  Current options:
% 3.12/0.99  ------ 
% 3.12/0.99  
% 3.12/0.99  ------ Input Options
% 3.12/0.99  
% 3.12/0.99  --out_options                           all
% 3.12/0.99  --tptp_safe_out                         true
% 3.12/0.99  --problem_path                          ""
% 3.12/0.99  --include_path                          ""
% 3.12/0.99  --clausifier                            res/vclausify_rel
% 3.12/0.99  --clausifier_options                    --mode clausify
% 3.12/0.99  --stdin                                 false
% 3.12/0.99  --stats_out                             all
% 3.12/0.99  
% 3.12/0.99  ------ General Options
% 3.12/0.99  
% 3.12/0.99  --fof                                   false
% 3.12/0.99  --time_out_real                         305.
% 3.12/0.99  --time_out_virtual                      -1.
% 3.12/0.99  --symbol_type_check                     false
% 3.12/0.99  --clausify_out                          false
% 3.12/0.99  --sig_cnt_out                           false
% 3.12/0.99  --trig_cnt_out                          false
% 3.12/0.99  --trig_cnt_out_tolerance                1.
% 3.12/0.99  --trig_cnt_out_sk_spl                   false
% 3.12/0.99  --abstr_cl_out                          false
% 3.12/0.99  
% 3.12/0.99  ------ Global Options
% 3.12/0.99  
% 3.12/0.99  --schedule                              default
% 3.12/0.99  --add_important_lit                     false
% 3.12/0.99  --prop_solver_per_cl                    1000
% 3.12/0.99  --min_unsat_core                        false
% 3.12/0.99  --soft_assumptions                      false
% 3.12/0.99  --soft_lemma_size                       3
% 3.12/0.99  --prop_impl_unit_size                   0
% 3.12/0.99  --prop_impl_unit                        []
% 3.12/0.99  --share_sel_clauses                     true
% 3.12/0.99  --reset_solvers                         false
% 3.12/0.99  --bc_imp_inh                            [conj_cone]
% 3.12/0.99  --conj_cone_tolerance                   3.
% 3.12/0.99  --extra_neg_conj                        none
% 3.12/0.99  --large_theory_mode                     true
% 3.12/0.99  --prolific_symb_bound                   200
% 3.12/0.99  --lt_threshold                          2000
% 3.12/0.99  --clause_weak_htbl                      true
% 3.12/0.99  --gc_record_bc_elim                     false
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing Options
% 3.12/0.99  
% 3.12/0.99  --preprocessing_flag                    true
% 3.12/0.99  --time_out_prep_mult                    0.1
% 3.12/0.99  --splitting_mode                        input
% 3.12/0.99  --splitting_grd                         true
% 3.12/0.99  --splitting_cvd                         false
% 3.12/0.99  --splitting_cvd_svl                     false
% 3.12/0.99  --splitting_nvd                         32
% 3.12/0.99  --sub_typing                            true
% 3.12/0.99  --prep_gs_sim                           true
% 3.12/0.99  --prep_unflatten                        true
% 3.12/0.99  --prep_res_sim                          true
% 3.12/0.99  --prep_upred                            true
% 3.12/0.99  --prep_sem_filter                       exhaustive
% 3.12/0.99  --prep_sem_filter_out                   false
% 3.12/0.99  --pred_elim                             true
% 3.12/0.99  --res_sim_input                         true
% 3.12/0.99  --eq_ax_congr_red                       true
% 3.12/0.99  --pure_diseq_elim                       true
% 3.12/0.99  --brand_transform                       false
% 3.12/0.99  --non_eq_to_eq                          false
% 3.12/0.99  --prep_def_merge                        true
% 3.12/0.99  --prep_def_merge_prop_impl              false
% 3.12/0.99  --prep_def_merge_mbd                    true
% 3.12/0.99  --prep_def_merge_tr_red                 false
% 3.12/0.99  --prep_def_merge_tr_cl                  false
% 3.12/0.99  --smt_preprocessing                     true
% 3.12/0.99  --smt_ac_axioms                         fast
% 3.12/0.99  --preprocessed_out                      false
% 3.12/0.99  --preprocessed_stats                    false
% 3.12/0.99  
% 3.12/0.99  ------ Abstraction refinement Options
% 3.12/0.99  
% 3.12/0.99  --abstr_ref                             []
% 3.12/0.99  --abstr_ref_prep                        false
% 3.12/0.99  --abstr_ref_until_sat                   false
% 3.12/0.99  --abstr_ref_sig_restrict                funpre
% 3.12/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.12/0.99  --abstr_ref_under                       []
% 3.12/0.99  
% 3.12/0.99  ------ SAT Options
% 3.12/0.99  
% 3.12/0.99  --sat_mode                              false
% 3.12/0.99  --sat_fm_restart_options                ""
% 3.12/0.99  --sat_gr_def                            false
% 3.12/0.99  --sat_epr_types                         true
% 3.12/0.99  --sat_non_cyclic_types                  false
% 3.12/0.99  --sat_finite_models                     false
% 3.12/0.99  --sat_fm_lemmas                         false
% 3.12/0.99  --sat_fm_prep                           false
% 3.12/0.99  --sat_fm_uc_incr                        true
% 3.12/0.99  --sat_out_model                         small
% 3.12/0.99  --sat_out_clauses                       false
% 3.12/0.99  
% 3.12/0.99  ------ QBF Options
% 3.12/0.99  
% 3.12/0.99  --qbf_mode                              false
% 3.12/0.99  --qbf_elim_univ                         false
% 3.12/0.99  --qbf_dom_inst                          none
% 3.12/0.99  --qbf_dom_pre_inst                      false
% 3.12/0.99  --qbf_sk_in                             false
% 3.12/0.99  --qbf_pred_elim                         true
% 3.12/0.99  --qbf_split                             512
% 3.12/0.99  
% 3.12/0.99  ------ BMC1 Options
% 3.12/0.99  
% 3.12/0.99  --bmc1_incremental                      false
% 3.12/0.99  --bmc1_axioms                           reachable_all
% 3.12/0.99  --bmc1_min_bound                        0
% 3.12/0.99  --bmc1_max_bound                        -1
% 3.12/0.99  --bmc1_max_bound_default                -1
% 3.12/0.99  --bmc1_symbol_reachability              true
% 3.12/0.99  --bmc1_property_lemmas                  false
% 3.12/0.99  --bmc1_k_induction                      false
% 3.12/0.99  --bmc1_non_equiv_states                 false
% 3.12/0.99  --bmc1_deadlock                         false
% 3.12/0.99  --bmc1_ucm                              false
% 3.12/0.99  --bmc1_add_unsat_core                   none
% 3.12/0.99  --bmc1_unsat_core_children              false
% 3.12/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.12/0.99  --bmc1_out_stat                         full
% 3.12/0.99  --bmc1_ground_init                      false
% 3.12/0.99  --bmc1_pre_inst_next_state              false
% 3.12/0.99  --bmc1_pre_inst_state                   false
% 3.12/0.99  --bmc1_pre_inst_reach_state             false
% 3.12/0.99  --bmc1_out_unsat_core                   false
% 3.12/0.99  --bmc1_aig_witness_out                  false
% 3.12/0.99  --bmc1_verbose                          false
% 3.12/0.99  --bmc1_dump_clauses_tptp                false
% 3.12/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.12/0.99  --bmc1_dump_file                        -
% 3.12/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.12/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.12/0.99  --bmc1_ucm_extend_mode                  1
% 3.12/0.99  --bmc1_ucm_init_mode                    2
% 3.12/0.99  --bmc1_ucm_cone_mode                    none
% 3.12/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.12/0.99  --bmc1_ucm_relax_model                  4
% 3.12/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.12/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.12/0.99  --bmc1_ucm_layered_model                none
% 3.12/0.99  --bmc1_ucm_max_lemma_size               10
% 3.12/0.99  
% 3.12/0.99  ------ AIG Options
% 3.12/0.99  
% 3.12/0.99  --aig_mode                              false
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation Options
% 3.12/0.99  
% 3.12/0.99  --instantiation_flag                    true
% 3.12/0.99  --inst_sos_flag                         false
% 3.12/0.99  --inst_sos_phase                        true
% 3.12/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.12/0.99  --inst_lit_sel_side                     none
% 3.12/0.99  --inst_solver_per_active                1400
% 3.12/0.99  --inst_solver_calls_frac                1.
% 3.12/0.99  --inst_passive_queue_type               priority_queues
% 3.12/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.12/0.99  --inst_passive_queues_freq              [25;2]
% 3.12/0.99  --inst_dismatching                      true
% 3.12/0.99  --inst_eager_unprocessed_to_passive     true
% 3.12/0.99  --inst_prop_sim_given                   true
% 3.12/0.99  --inst_prop_sim_new                     false
% 3.12/0.99  --inst_subs_new                         false
% 3.12/0.99  --inst_eq_res_simp                      false
% 3.12/0.99  --inst_subs_given                       false
% 3.12/0.99  --inst_orphan_elimination               true
% 3.12/0.99  --inst_learning_loop_flag               true
% 3.12/0.99  --inst_learning_start                   3000
% 3.12/0.99  --inst_learning_factor                  2
% 3.12/0.99  --inst_start_prop_sim_after_learn       3
% 3.12/0.99  --inst_sel_renew                        solver
% 3.12/0.99  --inst_lit_activity_flag                true
% 3.12/0.99  --inst_restr_to_given                   false
% 3.12/0.99  --inst_activity_threshold               500
% 3.12/0.99  --inst_out_proof                        true
% 3.12/0.99  
% 3.12/0.99  ------ Resolution Options
% 3.12/0.99  
% 3.12/0.99  --resolution_flag                       false
% 3.12/0.99  --res_lit_sel                           adaptive
% 3.12/0.99  --res_lit_sel_side                      none
% 3.12/0.99  --res_ordering                          kbo
% 3.12/0.99  --res_to_prop_solver                    active
% 3.12/0.99  --res_prop_simpl_new                    false
% 3.12/0.99  --res_prop_simpl_given                  true
% 3.12/0.99  --res_passive_queue_type                priority_queues
% 3.12/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.12/0.99  --res_passive_queues_freq               [15;5]
% 3.12/0.99  --res_forward_subs                      full
% 3.12/0.99  --res_backward_subs                     full
% 3.12/0.99  --res_forward_subs_resolution           true
% 3.12/0.99  --res_backward_subs_resolution          true
% 3.12/0.99  --res_orphan_elimination                true
% 3.12/0.99  --res_time_limit                        2.
% 3.12/0.99  --res_out_proof                         true
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Options
% 3.12/0.99  
% 3.12/0.99  --superposition_flag                    true
% 3.12/0.99  --sup_passive_queue_type                priority_queues
% 3.12/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.12/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.12/0.99  --demod_completeness_check              fast
% 3.12/0.99  --demod_use_ground                      true
% 3.12/0.99  --sup_to_prop_solver                    passive
% 3.12/0.99  --sup_prop_simpl_new                    true
% 3.12/0.99  --sup_prop_simpl_given                  true
% 3.12/0.99  --sup_fun_splitting                     false
% 3.12/0.99  --sup_smt_interval                      50000
% 3.12/0.99  
% 3.12/0.99  ------ Superposition Simplification Setup
% 3.12/0.99  
% 3.12/0.99  --sup_indices_passive                   []
% 3.12/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.12/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.12/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_full_bw                           [BwDemod]
% 3.12/0.99  --sup_immed_triv                        [TrivRules]
% 3.12/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.12/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_immed_bw_main                     []
% 3.12/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.12/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.12/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.12/0.99  
% 3.12/0.99  ------ Combination Options
% 3.12/0.99  
% 3.12/0.99  --comb_res_mult                         3
% 3.12/0.99  --comb_sup_mult                         2
% 3.12/0.99  --comb_inst_mult                        10
% 3.12/0.99  
% 3.12/0.99  ------ Debug Options
% 3.12/0.99  
% 3.12/0.99  --dbg_backtrace                         false
% 3.12/0.99  --dbg_dump_prop_clauses                 false
% 3.12/0.99  --dbg_dump_prop_clauses_file            -
% 3.12/0.99  --dbg_out_stat                          false
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  ------ Proving...
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  % SZS status Theorem for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  fof(f9,axiom,(
% 3.12/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f18,plain,(
% 3.12/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.12/0.99    inference(ennf_transformation,[],[f9])).
% 3.12/0.99  
% 3.12/0.99  fof(f31,plain,(
% 3.12/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.12/0.99    inference(nnf_transformation,[],[f18])).
% 3.12/0.99  
% 3.12/0.99  fof(f32,plain,(
% 3.12/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.12/0.99    inference(flattening,[],[f31])).
% 3.12/0.99  
% 3.12/0.99  fof(f33,plain,(
% 3.12/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.12/0.99    inference(rectify,[],[f32])).
% 3.12/0.99  
% 3.12/0.99  fof(f34,plain,(
% 3.12/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f35,plain,(
% 3.12/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 3.12/0.99  
% 3.12/0.99  fof(f57,plain,(
% 3.12/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.12/0.99    inference(cnf_transformation,[],[f35])).
% 3.12/0.99  
% 3.12/0.99  fof(f12,axiom,(
% 3.12/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f67,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f12])).
% 3.12/0.99  
% 3.12/0.99  fof(f84,plain,(
% 3.12/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.12/0.99    inference(definition_unfolding,[],[f57,f67])).
% 3.12/0.99  
% 3.12/0.99  fof(f100,plain,(
% 3.12/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.12/0.99    inference(equality_resolution,[],[f84])).
% 3.12/0.99  
% 3.12/0.99  fof(f13,axiom,(
% 3.12/0.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f36,plain,(
% 3.12/0.99    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.12/0.99    inference(nnf_transformation,[],[f13])).
% 3.12/0.99  
% 3.12/0.99  fof(f69,plain,(
% 3.12/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f10,axiom,(
% 3.12/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f65,plain,(
% 3.12/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f10])).
% 3.12/0.99  
% 3.12/0.99  fof(f11,axiom,(
% 3.12/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f66,plain,(
% 3.12/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f11])).
% 3.12/0.99  
% 3.12/0.99  fof(f72,plain,(
% 3.12/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.12/0.99    inference(definition_unfolding,[],[f66,f67])).
% 3.12/0.99  
% 3.12/0.99  fof(f73,plain,(
% 3.12/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.12/0.99    inference(definition_unfolding,[],[f65,f72])).
% 3.12/0.99  
% 3.12/0.99  fof(f85,plain,(
% 3.12/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.12/0.99    inference(definition_unfolding,[],[f69,f73])).
% 3.12/0.99  
% 3.12/0.99  fof(f14,conjecture,(
% 3.12/0.99    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f15,negated_conjecture,(
% 3.12/0.99    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.12/0.99    inference(negated_conjecture,[],[f14])).
% 3.12/0.99  
% 3.12/0.99  fof(f19,plain,(
% 3.12/0.99    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <~> ~r2_hidden(X0,X1))),
% 3.12/0.99    inference(ennf_transformation,[],[f15])).
% 3.12/0.99  
% 3.12/0.99  fof(f37,plain,(
% 3.12/0.99    ? [X0,X1] : ((r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)))),
% 3.12/0.99    inference(nnf_transformation,[],[f19])).
% 3.12/0.99  
% 3.12/0.99  fof(f38,plain,(
% 3.12/0.99    ? [X0,X1] : ((r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0))) => ((r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)) & (~r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3)))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f39,plain,(
% 3.12/0.99    (r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)) & (~r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3))),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f37,f38])).
% 3.12/0.99  
% 3.12/0.99  fof(f70,plain,(
% 3.12/0.99    ~r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) = k1_tarski(sK3)),
% 3.12/0.99    inference(cnf_transformation,[],[f39])).
% 3.12/0.99  
% 3.12/0.99  fof(f88,plain,(
% 3.12/0.99    ~r2_hidden(sK3,sK4) | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 3.12/0.99    inference(definition_unfolding,[],[f70,f73,f73])).
% 3.12/0.99  
% 3.12/0.99  fof(f58,plain,(
% 3.12/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.12/0.99    inference(cnf_transformation,[],[f35])).
% 3.12/0.99  
% 3.12/0.99  fof(f83,plain,(
% 3.12/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.12/0.99    inference(definition_unfolding,[],[f58,f67])).
% 3.12/0.99  
% 3.12/0.99  fof(f98,plain,(
% 3.12/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.12/0.99    inference(equality_resolution,[],[f83])).
% 3.12/0.99  
% 3.12/0.99  fof(f99,plain,(
% 3.12/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.12/0.99    inference(equality_resolution,[],[f98])).
% 3.12/0.99  
% 3.12/0.99  fof(f3,axiom,(
% 3.12/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.12/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.12/0.99  
% 3.12/0.99  fof(f24,plain,(
% 3.12/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.12/0.99    inference(nnf_transformation,[],[f3])).
% 3.12/0.99  
% 3.12/0.99  fof(f25,plain,(
% 3.12/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.12/0.99    inference(flattening,[],[f24])).
% 3.12/0.99  
% 3.12/0.99  fof(f26,plain,(
% 3.12/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.12/0.99    inference(rectify,[],[f25])).
% 3.12/0.99  
% 3.12/0.99  fof(f27,plain,(
% 3.12/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.12/0.99    introduced(choice_axiom,[])).
% 3.12/0.99  
% 3.12/0.99  fof(f28,plain,(
% 3.12/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.12/0.99  
% 3.12/0.99  fof(f45,plain,(
% 3.12/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.12/0.99    inference(cnf_transformation,[],[f28])).
% 3.12/0.99  
% 3.12/0.99  fof(f90,plain,(
% 3.12/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.12/0.99    inference(equality_resolution,[],[f45])).
% 3.12/0.99  
% 3.12/0.99  fof(f68,plain,(
% 3.12/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 3.12/0.99    inference(cnf_transformation,[],[f36])).
% 3.12/0.99  
% 3.12/0.99  fof(f86,plain,(
% 3.12/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0) )),
% 3.12/0.99    inference(definition_unfolding,[],[f68,f73])).
% 3.12/0.99  
% 3.12/0.99  fof(f49,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f28])).
% 3.12/0.99  
% 3.12/0.99  fof(f47,plain,(
% 3.12/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.12/0.99    inference(cnf_transformation,[],[f28])).
% 3.12/0.99  
% 3.12/0.99  fof(f71,plain,(
% 3.12/0.99    r2_hidden(sK3,sK4) | k4_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)),
% 3.12/0.99    inference(cnf_transformation,[],[f39])).
% 3.12/0.99  
% 3.12/0.99  fof(f87,plain,(
% 3.12/0.99    r2_hidden(sK3,sK4) | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 3.12/0.99    inference(definition_unfolding,[],[f71,f73,f73])).
% 3.12/0.99  
% 3.12/0.99  cnf(c_23,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.12/0.99      | X0 = X1
% 3.12/0.99      | X0 = X2
% 3.12/0.99      | X0 = X3 ),
% 3.12/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_17231,plain,
% 3.12/0.99      ( ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(X0,X0,X1,X2))
% 3.12/0.99      | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X0
% 3.12/0.99      | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X1
% 3.12/0.99      | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = X2 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_17233,plain,
% 3.12/0.99      ( ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.12/0.99      | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_17231]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_564,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_15073,plain,
% 3.12/0.99      ( X0 != X1
% 3.12/0.99      | X0 = sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.12/0.99      | sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != X1 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_564]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_15074,plain,
% 3.12/0.99      ( sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK3
% 3.12/0.99      | sK3 = sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.12/0.99      | sK3 != sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_15073]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_568,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.12/0.99      theory(equality) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2145,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,sK4) | X2 != X0 | sK4 != X1 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_568]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4051,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X1,sK4) | X1 != X0 | sK4 != sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_2145]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_10008,plain,
% 3.12/0.99      ( r2_hidden(X0,sK4)
% 3.12/0.99      | ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.12/0.99      | X0 != sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.12/0.99      | sK4 != sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_4051]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_10010,plain,
% 3.12/0.99      ( ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.12/0.99      | r2_hidden(sK3,sK4)
% 3.12/0.99      | sK4 != sK4
% 3.12/0.99      | sK3 != sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_10008]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_24,plain,
% 3.12/0.99      ( r2_hidden(X0,X1)
% 3.12/0.99      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 3.12/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1121,plain,
% 3.12/0.99      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 3.12/0.99      | r2_hidden(X1,X0) = iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_27,negated_conjecture,
% 3.12/0.99      ( ~ r2_hidden(sK3,sK4)
% 3.12/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.12/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1118,plain,
% 3.12/0.99      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3)
% 3.12/0.99      | r2_hidden(sK3,sK4) != iProver_top ),
% 3.12/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4070,plain,
% 3.12/0.99      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3)
% 3.12/0.99      | k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK4 ),
% 3.12/0.99      inference(superposition,[status(thm)],[c_1121,c_1118]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_37,plain,
% 3.12/0.99      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_22,plain,
% 3.12/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_40,plain,
% 3.12/0.99      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1472,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1)
% 3.12/0.99      | r2_hidden(X2,k4_xboole_0(X3,X4))
% 3.12/0.99      | X2 != X0
% 3.12/0.99      | k4_xboole_0(X3,X4) != X1 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_568]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1574,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.12/0.99      | r2_hidden(X1,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 3.12/0.99      | X1 != X0
% 3.12/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1472]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1576,plain,
% 3.12/0.99      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.12/0.99      | r2_hidden(sK3,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 3.12/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3)
% 3.12/0.99      | sK3 != sK3 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1574]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_9,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.12/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1999,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 3.12/0.99      | ~ r2_hidden(X0,sK4) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2001,plain,
% 3.12/0.99      ( ~ r2_hidden(sK3,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 3.12/0.99      | ~ r2_hidden(sK3,sK4) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_1999]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2047,plain,
% 3.12/0.99      ( r2_hidden(X0,sK4)
% 3.12/0.99      | k4_xboole_0(sK4,k2_enumset1(X0,X0,X0,X0)) = sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_2049,plain,
% 3.12/0.99      ( r2_hidden(sK3,sK4)
% 3.12/0.99      | k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_2047]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4707,plain,
% 3.12/0.99      ( k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK4 ),
% 3.12/0.99      inference(global_propositional_subsumption,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_4070,c_37,c_40,c_1576,c_2001,c_2049]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_563,plain,( X0 = X0 ),theory(equality) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_4052,plain,
% 3.12/0.99      ( sK4 = sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_563]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_25,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,X1)
% 3.12/0.99      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) != X1 ),
% 3.12/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3940,plain,
% 3.12/0.99      ( ~ r2_hidden(X0,sK4)
% 3.12/0.99      | k4_xboole_0(sK4,k2_enumset1(X0,X0,X0,X0)) != sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_3942,plain,
% 3.12/0.99      ( ~ r2_hidden(sK3,sK4)
% 3.12/0.99      | k4_xboole_0(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != sK4 ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_3940]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_5,plain,
% 3.12/0.99      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 3.12/0.99      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 3.12/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.12/0.99      | k4_xboole_0(X0,X1) = X2 ),
% 3.12/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1400,plain,
% 3.12/0.99      ( ~ r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.12/0.99      | r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.12/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_7,plain,
% 3.12/0.99      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.12/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.12/0.99      | k4_xboole_0(X0,X1) = X2 ),
% 3.12/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_1392,plain,
% 3.12/0.99      ( r2_hidden(sK1(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.12/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.12/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(c_26,negated_conjecture,
% 3.12/0.99      ( r2_hidden(sK3,sK4)
% 3.12/0.99      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.12/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.12/0.99  
% 3.12/0.99  cnf(contradiction,plain,
% 3.12/0.99      ( $false ),
% 3.12/0.99      inference(minisat,
% 3.12/0.99                [status(thm)],
% 3.12/0.99                [c_17233,c_15074,c_10010,c_4707,c_4052,c_3942,c_1400,
% 3.12/0.99                 c_1392,c_40,c_37,c_26]) ).
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.12/0.99  
% 3.12/0.99  ------                               Statistics
% 3.12/0.99  
% 3.12/0.99  ------ General
% 3.12/0.99  
% 3.12/0.99  abstr_ref_over_cycles:                  0
% 3.12/0.99  abstr_ref_under_cycles:                 0
% 3.12/0.99  gc_basic_clause_elim:                   0
% 3.12/0.99  forced_gc_time:                         0
% 3.12/0.99  parsing_time:                           0.009
% 3.12/0.99  unif_index_cands_time:                  0.
% 3.12/0.99  unif_index_add_time:                    0.
% 3.12/0.99  orderings_time:                         0.
% 3.12/0.99  out_proof_time:                         0.009
% 3.12/0.99  total_time:                             0.46
% 3.12/0.99  num_of_symbols:                         41
% 3.12/0.99  num_of_terms:                           24213
% 3.12/0.99  
% 3.12/0.99  ------ Preprocessing
% 3.12/0.99  
% 3.12/0.99  num_of_splits:                          0
% 3.12/0.99  num_of_split_atoms:                     0
% 3.12/0.99  num_of_reused_defs:                     0
% 3.12/0.99  num_eq_ax_congr_red:                    33
% 3.12/0.99  num_of_sem_filtered_clauses:            1
% 3.12/0.99  num_of_subtypes:                        0
% 3.12/0.99  monotx_restored_types:                  0
% 3.12/0.99  sat_num_of_epr_types:                   0
% 3.12/0.99  sat_num_of_non_cyclic_types:            0
% 3.12/0.99  sat_guarded_non_collapsed_types:        0
% 3.12/0.99  num_pure_diseq_elim:                    0
% 3.12/0.99  simp_replaced_by:                       0
% 3.12/0.99  res_preprocessed:                       123
% 3.12/0.99  prep_upred:                             0
% 3.12/0.99  prep_unflattend:                        0
% 3.12/0.99  smt_new_axioms:                         0
% 3.12/0.99  pred_elim_cands:                        2
% 3.12/0.99  pred_elim:                              0
% 3.12/0.99  pred_elim_cl:                           0
% 3.12/0.99  pred_elim_cycles:                       2
% 3.12/0.99  merged_defs:                            16
% 3.12/0.99  merged_defs_ncl:                        0
% 3.12/0.99  bin_hyper_res:                          16
% 3.12/0.99  prep_cycles:                            4
% 3.12/0.99  pred_elim_time:                         0.
% 3.12/0.99  splitting_time:                         0.
% 3.12/0.99  sem_filter_time:                        0.
% 3.12/0.99  monotx_time:                            0.
% 3.12/0.99  subtype_inf_time:                       0.
% 3.12/0.99  
% 3.12/0.99  ------ Problem properties
% 3.12/0.99  
% 3.12/0.99  clauses:                                27
% 3.12/0.99  conjectures:                            2
% 3.12/0.99  epr:                                    3
% 3.12/0.99  horn:                                   19
% 3.12/0.99  ground:                                 2
% 3.12/0.99  unary:                                  7
% 3.12/0.99  binary:                                 9
% 3.12/0.99  lits:                                   62
% 3.12/0.99  lits_eq:                                24
% 3.12/0.99  fd_pure:                                0
% 3.12/0.99  fd_pseudo:                              0
% 3.12/0.99  fd_cond:                                0
% 3.12/0.99  fd_pseudo_cond:                         8
% 3.12/0.99  ac_symbols:                             0
% 3.12/0.99  
% 3.12/0.99  ------ Propositional Solver
% 3.12/0.99  
% 3.12/0.99  prop_solver_calls:                      28
% 3.12/0.99  prop_fast_solver_calls:                 742
% 3.12/0.99  smt_solver_calls:                       0
% 3.12/0.99  smt_fast_solver_calls:                  0
% 3.12/0.99  prop_num_of_clauses:                    5603
% 3.12/0.99  prop_preprocess_simplified:             14011
% 3.12/0.99  prop_fo_subsumed:                       3
% 3.12/0.99  prop_solver_time:                       0.
% 3.12/0.99  smt_solver_time:                        0.
% 3.12/0.99  smt_fast_solver_time:                   0.
% 3.12/0.99  prop_fast_solver_time:                  0.
% 3.12/0.99  prop_unsat_core_time:                   0.
% 3.12/0.99  
% 3.12/0.99  ------ QBF
% 3.12/0.99  
% 3.12/0.99  qbf_q_res:                              0
% 3.12/0.99  qbf_num_tautologies:                    0
% 3.12/0.99  qbf_prep_cycles:                        0
% 3.12/0.99  
% 3.12/0.99  ------ BMC1
% 3.12/0.99  
% 3.12/0.99  bmc1_current_bound:                     -1
% 3.12/0.99  bmc1_last_solved_bound:                 -1
% 3.12/0.99  bmc1_unsat_core_size:                   -1
% 3.12/0.99  bmc1_unsat_core_parents_size:           -1
% 3.12/0.99  bmc1_merge_next_fun:                    0
% 3.12/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.12/0.99  
% 3.12/0.99  ------ Instantiation
% 3.12/0.99  
% 3.12/0.99  inst_num_of_clauses:                    1426
% 3.12/0.99  inst_num_in_passive:                    906
% 3.12/0.99  inst_num_in_active:                     335
% 3.12/0.99  inst_num_in_unprocessed:                185
% 3.12/0.99  inst_num_of_loops:                      458
% 3.12/0.99  inst_num_of_learning_restarts:          0
% 3.12/0.99  inst_num_moves_active_passive:          120
% 3.12/0.99  inst_lit_activity:                      0
% 3.12/0.99  inst_lit_activity_moves:                0
% 3.12/0.99  inst_num_tautologies:                   0
% 3.12/0.99  inst_num_prop_implied:                  0
% 3.12/0.99  inst_num_existing_simplified:           0
% 3.12/0.99  inst_num_eq_res_simplified:             0
% 3.12/0.99  inst_num_child_elim:                    0
% 3.12/0.99  inst_num_of_dismatching_blockings:      2434
% 3.12/0.99  inst_num_of_non_proper_insts:           1213
% 3.12/0.99  inst_num_of_duplicates:                 0
% 3.12/0.99  inst_inst_num_from_inst_to_res:         0
% 3.12/0.99  inst_dismatching_checking_time:         0.
% 3.12/0.99  
% 3.12/0.99  ------ Resolution
% 3.12/0.99  
% 3.12/0.99  res_num_of_clauses:                     0
% 3.12/0.99  res_num_in_passive:                     0
% 3.12/0.99  res_num_in_active:                      0
% 3.12/0.99  res_num_of_loops:                       127
% 3.12/0.99  res_forward_subset_subsumed:            87
% 3.12/0.99  res_backward_subset_subsumed:           2
% 3.12/0.99  res_forward_subsumed:                   0
% 3.12/0.99  res_backward_subsumed:                  0
% 3.12/0.99  res_forward_subsumption_resolution:     0
% 3.12/0.99  res_backward_subsumption_resolution:    0
% 3.12/0.99  res_clause_to_clause_subsumption:       3949
% 3.12/0.99  res_orphan_elimination:                 0
% 3.12/0.99  res_tautology_del:                      112
% 3.12/0.99  res_num_eq_res_simplified:              0
% 3.12/0.99  res_num_sel_changes:                    0
% 3.12/0.99  res_moves_from_active_to_pass:          0
% 3.12/0.99  
% 3.12/0.99  ------ Superposition
% 3.12/0.99  
% 3.12/0.99  sup_time_total:                         0.
% 3.12/0.99  sup_time_generating:                    0.
% 3.12/0.99  sup_time_sim_full:                      0.
% 3.12/0.99  sup_time_sim_immed:                     0.
% 3.12/0.99  
% 3.12/0.99  sup_num_of_clauses:                     367
% 3.12/0.99  sup_num_in_active:                      82
% 3.12/0.99  sup_num_in_passive:                     285
% 3.12/0.99  sup_num_of_loops:                       90
% 3.12/0.99  sup_fw_superposition:                   681
% 3.12/0.99  sup_bw_superposition:                   842
% 3.12/0.99  sup_immediate_simplified:               729
% 3.12/0.99  sup_given_eliminated:                   2
% 3.12/0.99  comparisons_done:                       0
% 3.12/0.99  comparisons_avoided:                    10
% 3.12/0.99  
% 3.12/0.99  ------ Simplifications
% 3.12/0.99  
% 3.12/0.99  
% 3.12/0.99  sim_fw_subset_subsumed:                 15
% 3.12/0.99  sim_bw_subset_subsumed:                 3
% 3.12/0.99  sim_fw_subsumed:                        136
% 3.12/0.99  sim_bw_subsumed:                        2
% 3.12/0.99  sim_fw_subsumption_res:                 3
% 3.12/0.99  sim_bw_subsumption_res:                 0
% 3.12/0.99  sim_tautology_del:                      35
% 3.12/0.99  sim_eq_tautology_del:                   97
% 3.12/0.99  sim_eq_res_simp:                        1
% 3.12/0.99  sim_fw_demodulated:                     270
% 3.12/0.99  sim_bw_demodulated:                     43
% 3.12/0.99  sim_light_normalised:                   420
% 3.12/0.99  sim_joinable_taut:                      0
% 3.12/0.99  sim_joinable_simp:                      0
% 3.12/0.99  sim_ac_normalised:                      0
% 3.12/0.99  sim_smt_subsumption:                    0
% 3.12/0.99  
%------------------------------------------------------------------------------
