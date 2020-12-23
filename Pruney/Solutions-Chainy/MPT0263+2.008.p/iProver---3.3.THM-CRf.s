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
% DateTime   : Thu Dec  3 11:35:05 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 244 expanded)
%              Number of clauses        :   30 (  45 expanded)
%              Number of leaves         :   14 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  292 (1162 expanded)
%              Number of equality atoms :  150 ( 428 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)
      & ~ r1_xboole_0(k1_tarski(sK3),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)
    & ~ r1_xboole_0(k1_tarski(sK3),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f31])).

fof(f60,plain,(
    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f77,plain,(
    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f60,f43,f62,f62])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f88,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ~ r1_xboole_0(k1_tarski(sK3),sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_22,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2711,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_3,c_22])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3452,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_2711,c_19])).

cnf(c_465,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3730,plain,
    ( X0 != sK3
    | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
    inference(resolution,[status(thm)],[c_3452,c_465])).

cnf(c_467,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_464,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1829,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_467,c_464])).

cnf(c_4069,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),X1)
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_3730,c_1829])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_161,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_23,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_299,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
    | k4_xboole_0(X0,X1) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_23])).

cnf(c_300,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_2727,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_3,c_300])).

cnf(c_3457,plain,
    ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_2727,c_19])).

cnf(c_9258,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),X0)
    | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0) ),
    inference(resolution,[status(thm)],[c_4069,c_3457])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5552,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(resolution,[status(thm)],[c_1,c_2711])).

cnf(c_1063,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1118,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5741,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5552,c_22,c_1063,c_1118])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5754,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
    inference(resolution,[status(thm)],[c_5741,c_5])).

cnf(c_15143,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
    inference(resolution,[status(thm)],[c_9258,c_5754])).

cnf(c_1149,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1066,plain,
    ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15143,c_1149,c_1066,c_300])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.87/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.98  
% 3.87/0.98  ------  iProver source info
% 3.87/0.98  
% 3.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.98  git: non_committed_changes: false
% 3.87/0.98  git: last_make_outside_of_git: false
% 3.87/0.98  
% 3.87/0.98  ------ 
% 3.87/0.98  ------ Parsing...
% 3.87/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.98  ------ Proving...
% 3.87/0.98  ------ Problem Properties 
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  clauses                                 23
% 3.87/0.98  conjectures                             1
% 3.87/0.98  EPR                                     0
% 3.87/0.98  Horn                                    15
% 3.87/0.98  unary                                   8
% 3.87/0.98  binary                                  4
% 3.87/0.98  lits                                    53
% 3.87/0.98  lits eq                                 30
% 3.87/0.98  fd_pure                                 0
% 3.87/0.98  fd_pseudo                               0
% 3.87/0.98  fd_cond                                 0
% 3.87/0.98  fd_pseudo_cond                          9
% 3.87/0.98  AC symbols                              0
% 3.87/0.98  
% 3.87/0.98  ------ Input Options Time Limit: Unbounded
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  ------ 
% 3.87/0.98  Current options:
% 3.87/0.98  ------ 
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  ------ Proving...
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  % SZS status Theorem for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  fof(f2,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f17,plain,(
% 3.87/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.87/0.98    inference(nnf_transformation,[],[f2])).
% 3.87/0.98  
% 3.87/0.98  fof(f18,plain,(
% 3.87/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.87/0.98    inference(flattening,[],[f17])).
% 3.87/0.98  
% 3.87/0.98  fof(f19,plain,(
% 3.87/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.87/0.98    inference(rectify,[],[f18])).
% 3.87/0.98  
% 3.87/0.98  fof(f20,plain,(
% 3.87/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f21,plain,(
% 3.87/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.87/0.98  
% 3.87/0.98  fof(f37,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f21])).
% 3.87/0.98  
% 3.87/0.98  fof(f12,conjecture,(
% 3.87/0.98    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f13,negated_conjecture,(
% 3.87/0.98    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 3.87/0.98    inference(negated_conjecture,[],[f12])).
% 3.87/0.98  
% 3.87/0.98  fof(f16,plain,(
% 3.87/0.98    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.87/0.98    inference(ennf_transformation,[],[f13])).
% 3.87/0.98  
% 3.87/0.98  fof(f31,plain,(
% 3.87/0.98    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) & ~r1_xboole_0(k1_tarski(sK3),sK4))),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f32,plain,(
% 3.87/0.98    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3) & ~r1_xboole_0(k1_tarski(sK3),sK4)),
% 3.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f31])).
% 3.87/0.98  
% 3.87/0.98  fof(f60,plain,(
% 3.87/0.98    k3_xboole_0(k1_tarski(sK3),sK4) != k1_tarski(sK3)),
% 3.87/0.98    inference(cnf_transformation,[],[f32])).
% 3.87/0.98  
% 3.87/0.98  fof(f5,axiom,(
% 3.87/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f43,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f5])).
% 3.87/0.98  
% 3.87/0.98  fof(f8,axiom,(
% 3.87/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f54,plain,(
% 3.87/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f8])).
% 3.87/0.98  
% 3.87/0.98  fof(f9,axiom,(
% 3.87/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f55,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f9])).
% 3.87/0.98  
% 3.87/0.98  fof(f10,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f56,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f10])).
% 3.87/0.98  
% 3.87/0.98  fof(f61,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.87/0.98    inference(definition_unfolding,[],[f55,f56])).
% 3.87/0.98  
% 3.87/0.98  fof(f62,plain,(
% 3.87/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.87/0.98    inference(definition_unfolding,[],[f54,f61])).
% 3.87/0.98  
% 3.87/0.98  fof(f77,plain,(
% 3.87/0.98    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3)),
% 3.87/0.98    inference(definition_unfolding,[],[f60,f43,f62,f62])).
% 3.87/0.98  
% 3.87/0.98  fof(f7,axiom,(
% 3.87/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f14,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.87/0.98    inference(ennf_transformation,[],[f7])).
% 3.87/0.98  
% 3.87/0.98  fof(f24,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.87/0.98    inference(nnf_transformation,[],[f14])).
% 3.87/0.98  
% 3.87/0.98  fof(f25,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.87/0.98    inference(flattening,[],[f24])).
% 3.87/0.98  
% 3.87/0.98  fof(f26,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.87/0.98    inference(rectify,[],[f25])).
% 3.87/0.98  
% 3.87/0.98  fof(f27,plain,(
% 3.87/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f28,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 3.87/0.98  
% 3.87/0.98  fof(f46,plain,(
% 3.87/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.87/0.98    inference(cnf_transformation,[],[f28])).
% 3.87/0.98  
% 3.87/0.98  fof(f74,plain,(
% 3.87/0.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.87/0.98    inference(definition_unfolding,[],[f46,f56])).
% 3.87/0.98  
% 3.87/0.98  fof(f88,plain,(
% 3.87/0.98    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.87/0.98    inference(equality_resolution,[],[f74])).
% 3.87/0.98  
% 3.87/0.98  fof(f6,axiom,(
% 3.87/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.87/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f23,plain,(
% 3.87/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.87/0.98    inference(nnf_transformation,[],[f6])).
% 3.87/0.98  
% 3.87/0.98  fof(f45,plain,(
% 3.87/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.87/0.98    inference(cnf_transformation,[],[f23])).
% 3.87/0.98  
% 3.87/0.98  fof(f59,plain,(
% 3.87/0.98    ~r1_xboole_0(k1_tarski(sK3),sK4)),
% 3.87/0.98    inference(cnf_transformation,[],[f32])).
% 3.87/0.98  
% 3.87/0.98  fof(f78,plain,(
% 3.87/0.98    ~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)),
% 3.87/0.98    inference(definition_unfolding,[],[f59,f62])).
% 3.87/0.98  
% 3.87/0.98  fof(f39,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f21])).
% 3.87/0.98  
% 3.87/0.98  fof(f35,plain,(
% 3.87/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.87/0.98    inference(cnf_transformation,[],[f21])).
% 3.87/0.98  
% 3.87/0.98  fof(f80,plain,(
% 3.87/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.87/0.98    inference(equality_resolution,[],[f35])).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3,plain,
% 3.87/0.98      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.87/0.98      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.87/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.87/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_22,negated_conjecture,
% 3.87/0.98      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.87/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2711,plain,
% 3.87/0.98      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_3,c_22]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_19,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.87/0.98      | X0 = X1
% 3.87/0.98      | X0 = X2
% 3.87/0.98      | X0 = X3 ),
% 3.87/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3452,plain,
% 3.87/0.98      ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_2711,c_19]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_465,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3730,plain,
% 3.87/0.98      ( X0 != sK3
% 3.87/0.98      | sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = X0 ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_3452,c_465]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_467,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.87/0.98      theory(equality) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_464,plain,( X0 = X0 ),theory(equality) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1829,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_467,c_464]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_4069,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,X1)
% 3.87/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),X1)
% 3.87/0.98      | X0 != sK3 ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_3730,c_1829]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10,plain,
% 3.87/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_161,plain,
% 3.87/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.87/0.98      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_23,negated_conjecture,
% 3.87/0.98      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) ),
% 3.87/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_299,plain,
% 3.87/0.98      ( k2_enumset1(sK3,sK3,sK3,sK3) != X0
% 3.87/0.98      | k4_xboole_0(X0,X1) != X0
% 3.87/0.98      | sK4 != X1 ),
% 3.87/0.98      inference(resolution_lifted,[status(thm)],[c_161,c_23]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_300,plain,
% 3.87/0.98      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) != k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.87/0.98      inference(unflattening,[status(thm)],[c_299]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2727,plain,
% 3.87/0.98      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_3,c_300]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3457,plain,
% 3.87/0.98      ( sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = sK3 ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_2727,c_19]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9258,plain,
% 3.87/0.98      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),X0)
% 3.87/0.98      | ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),X0) ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_4069,c_3457]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1,plain,
% 3.87/0.98      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.87/0.98      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.87/0.98      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.87/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 3.87/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_5552,plain,
% 3.87/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.87/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 3.87/0.98      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_1,c_2711]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1063,plain,
% 3.87/0.98      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.87/0.98      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.87/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1118,plain,
% 3.87/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.87/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4))
% 3.87/0.98      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.87/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_5741,plain,
% 3.87/0.98      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4)) ),
% 3.87/0.98      inference(global_propositional_subsumption,
% 3.87/0.98                [status(thm)],
% 3.87/0.98                [c_5552,c_22,c_1063,c_1118]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_5,plain,
% 3.87/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.87/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_5754,plain,
% 3.87/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4),k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_5741,c_5]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_15143,plain,
% 3.87/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4) ),
% 3.87/0.98      inference(resolution,[status(thm)],[c_9258,c_5754]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1149,plain,
% 3.87/0.98      ( ~ r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.87/0.98      | r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),sK4)
% 3.87/0.98      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.87/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1066,plain,
% 3.87/0.98      ( r2_hidden(sK0(k2_enumset1(sK3,sK3,sK3,sK3),sK4,k2_enumset1(sK3,sK3,sK3,sK3)),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.87/0.98      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),sK4) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.87/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(contradiction,plain,
% 3.87/0.98      ( $false ),
% 3.87/0.98      inference(minisat,[status(thm)],[c_15143,c_1149,c_1066,c_300]) ).
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  ------                               Statistics
% 3.87/0.98  
% 3.87/0.98  ------ Selected
% 3.87/0.98  
% 3.87/0.98  total_time:                             0.479
% 3.87/0.98  
%------------------------------------------------------------------------------
