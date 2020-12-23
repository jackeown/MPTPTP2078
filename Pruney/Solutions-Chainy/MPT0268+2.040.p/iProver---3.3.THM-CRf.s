%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:38 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  131 (1020 expanded)
%              Number of clauses        :   63 ( 186 expanded)
%              Number of leaves         :   17 ( 262 expanded)
%              Depth                    :   18
%              Number of atoms          :  506 (5116 expanded)
%              Number of equality atoms :  245 (2382 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

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
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f54,f60])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
   => ( ( r2_hidden(sK5,sK4)
        | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
      & ( ~ r2_hidden(sK5,sK4)
        | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ( r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
    & ( ~ r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f40])).

fof(f76,plain,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f96,plain,
    ( r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4 ),
    inference(definition_unfolding,[],[f76,f60,f78])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f62,f72])).

fof(f112,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f93])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f110,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f92])).

fof(f111,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f110])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f83])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f55,f60])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f73,f60,f78,f78])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f60,f78,f78])).

fof(f75,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
    inference(definition_unfolding,[],[f75,f60,f78])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f47])).

cnf(c_9,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X0)
    | ~ r2_hidden(sK2(X0,X1,X2),X2)
    | r2_hidden(sK2(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0,X1,X2),X0)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_6042,plain,
    ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
    | r2_hidden(sK5,sK4) ),
    inference(resolution,[status(thm)],[c_11,c_29])).

cnf(c_9423,plain,
    ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
    | r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
    inference(resolution,[status(thm)],[c_9,c_6042])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_40,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_25,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_43,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1626,plain,
    ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1669,plain,
    ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_643,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1911,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | X2 != X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_7978,plain,
    ( r2_hidden(X0,k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r2_hidden(X1,sK4)
    | X0 != X1
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4 ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_7980,plain,
    ( r2_hidden(sK5,k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
    | ~ r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7978])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_8835,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(X0,k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8837,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK5,k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
    inference(instantiation,[status(thm)],[c_8835])).

cnf(c_9426,plain,
    ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),k2_enumset1(sK5,sK5,sK5,sK5))
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9423,c_29,c_40,c_43,c_1626,c_1669,c_7980,c_8837])).

cnf(c_9430,plain,
    ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9426,c_29,c_40,c_43,c_1626,c_1669,c_7980,c_8837])).

cnf(c_9703,plain,
    ( sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4) = sK5 ),
    inference(resolution,[status(thm)],[c_9430,c_26])).

cnf(c_642,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_641,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2587,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_642,c_641])).

cnf(c_9706,plain,
    ( sK5 = sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
    inference(resolution,[status(thm)],[c_9703,c_2587])).

cnf(c_3321,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_643,c_641])).

cnf(c_9992,plain,
    ( ~ r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),X0)
    | r2_hidden(sK5,X0) ),
    inference(resolution,[status(thm)],[c_9706,c_3321])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK2(X0,X1,X2),X1)
    | r2_hidden(sK2(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_9701,plain,
    ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
    inference(resolution,[status(thm)],[c_9430,c_10])).

cnf(c_9717,plain,
    ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9701,c_29,c_40,c_43,c_1626,c_7980,c_8837])).

cnf(c_10801,plain,
    ( r2_hidden(sK5,sK4) ),
    inference(resolution,[status(thm)],[c_9992,c_9717])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1307,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1306,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_18,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1285,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1811,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1285])).

cnf(c_4069,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_1811])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1286,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1283,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3223,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)
    | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
    inference(superposition,[status(thm)],[c_1286,c_1283])).

cnf(c_1298,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4205,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
    | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3223,c_1298])).

cnf(c_9281,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0) = k1_xboole_0
    | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),X0,k1_xboole_0),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4069,c_4205])).

cnf(c_9348,plain,
    ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0) = k1_xboole_0
    | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),X0,k1_xboole_0),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9281,c_29,c_40,c_43,c_7980,c_8837])).

cnf(c_9357,plain,
    ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = k1_xboole_0
    | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1307,c_9348])).

cnf(c_4446,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0) = X1
    | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),X0,X1),X1) = iProver_top
    | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),X0,X1),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_4205])).

cnf(c_5640,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = X0
    | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),sK4,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1307,c_4446])).

cnf(c_7245,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
    | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5640,c_1811])).

cnf(c_9629,plain,
    ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9357,c_29,c_40,c_43,c_7245,c_7980,c_8837])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1305,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9655,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9629,c_1305])).

cnf(c_9687,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9655])).

cnf(c_1813,plain,
    ( r2_hidden(sK5,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1811])).

cnf(c_42,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_44,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_32,plain,
    ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10801,c_9687,c_1813,c_44,c_32,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:59:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.42/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.00  
% 3.42/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.42/1.00  
% 3.42/1.00  ------  iProver source info
% 3.42/1.00  
% 3.42/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.42/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.42/1.00  git: non_committed_changes: false
% 3.42/1.00  git: last_make_outside_of_git: false
% 3.42/1.00  
% 3.42/1.00  ------ 
% 3.42/1.00  ------ Parsing...
% 3.42/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.42/1.00  
% 3.42/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.42/1.00  
% 3.42/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.42/1.00  
% 3.42/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.42/1.00  ------ Proving...
% 3.42/1.00  ------ Problem Properties 
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  clauses                                 30
% 3.42/1.00  conjectures                             2
% 3.42/1.00  EPR                                     3
% 3.42/1.00  Horn                                    20
% 3.42/1.00  unary                                   5
% 3.42/1.00  binary                                  10
% 3.42/1.00  lits                                    75
% 3.42/1.00  lits eq                                 25
% 3.42/1.00  fd_pure                                 0
% 3.42/1.00  fd_pseudo                               0
% 3.42/1.00  fd_cond                                 0
% 3.42/1.00  fd_pseudo_cond                          11
% 3.42/1.00  AC symbols                              0
% 3.42/1.00  
% 3.42/1.00  ------ Input Options Time Limit: Unbounded
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  ------ 
% 3.42/1.00  Current options:
% 3.42/1.00  ------ 
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  ------ Proving...
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  % SZS status Theorem for theBenchmark.p
% 3.42/1.00  
% 3.42/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.42/1.00  
% 3.42/1.00  fof(f3,axiom,(
% 3.42/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f26,plain,(
% 3.42/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.42/1.00    inference(nnf_transformation,[],[f3])).
% 3.42/1.00  
% 3.42/1.00  fof(f27,plain,(
% 3.42/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.42/1.00    inference(flattening,[],[f26])).
% 3.42/1.00  
% 3.42/1.00  fof(f28,plain,(
% 3.42/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.42/1.00    inference(rectify,[],[f27])).
% 3.42/1.00  
% 3.42/1.00  fof(f29,plain,(
% 3.42/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f30,plain,(
% 3.42/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.42/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 3.42/1.00  
% 3.42/1.00  fof(f56,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f30])).
% 3.42/1.00  
% 3.42/1.00  fof(f5,axiom,(
% 3.42/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f60,plain,(
% 3.42/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.42/1.00    inference(cnf_transformation,[],[f5])).
% 3.42/1.00  
% 3.42/1.00  fof(f79,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.42/1.00    inference(definition_unfolding,[],[f56,f60])).
% 3.42/1.00  
% 3.42/1.00  fof(f54,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f30])).
% 3.42/1.00  
% 3.42/1.00  fof(f81,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.42/1.00    inference(definition_unfolding,[],[f54,f60])).
% 3.42/1.00  
% 3.42/1.00  fof(f12,conjecture,(
% 3.42/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f13,negated_conjecture,(
% 3.42/1.00    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.42/1.00    inference(negated_conjecture,[],[f12])).
% 3.42/1.00  
% 3.42/1.00  fof(f16,plain,(
% 3.42/1.00    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.42/1.00    inference(ennf_transformation,[],[f13])).
% 3.42/1.00  
% 3.42/1.00  fof(f39,plain,(
% 3.42/1.00    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.42/1.00    inference(nnf_transformation,[],[f16])).
% 3.42/1.00  
% 3.42/1.00  fof(f40,plain,(
% 3.42/1.00    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4))),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f41,plain,(
% 3.42/1.00    (r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4)),
% 3.42/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f39,f40])).
% 3.42/1.00  
% 3.42/1.00  fof(f76,plain,(
% 3.42/1.00    r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4),
% 3.42/1.00    inference(cnf_transformation,[],[f41])).
% 3.42/1.00  
% 3.42/1.00  fof(f8,axiom,(
% 3.42/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f70,plain,(
% 3.42/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f8])).
% 3.42/1.00  
% 3.42/1.00  fof(f9,axiom,(
% 3.42/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f71,plain,(
% 3.42/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f9])).
% 3.42/1.00  
% 3.42/1.00  fof(f10,axiom,(
% 3.42/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f72,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f10])).
% 3.42/1.00  
% 3.42/1.00  fof(f77,plain,(
% 3.42/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.42/1.00    inference(definition_unfolding,[],[f71,f72])).
% 3.42/1.00  
% 3.42/1.00  fof(f78,plain,(
% 3.42/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.42/1.00    inference(definition_unfolding,[],[f70,f77])).
% 3.42/1.00  
% 3.42/1.00  fof(f96,plain,(
% 3.42/1.00    r2_hidden(sK5,sK4) | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4),
% 3.42/1.00    inference(definition_unfolding,[],[f76,f60,f78])).
% 3.42/1.00  
% 3.42/1.00  fof(f7,axiom,(
% 3.42/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f15,plain,(
% 3.42/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.42/1.00    inference(ennf_transformation,[],[f7])).
% 3.42/1.00  
% 3.42/1.00  fof(f33,plain,(
% 3.42/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.42/1.00    inference(nnf_transformation,[],[f15])).
% 3.42/1.00  
% 3.42/1.00  fof(f34,plain,(
% 3.42/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.42/1.00    inference(flattening,[],[f33])).
% 3.42/1.00  
% 3.42/1.00  fof(f35,plain,(
% 3.42/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.42/1.00    inference(rectify,[],[f34])).
% 3.42/1.00  
% 3.42/1.00  fof(f36,plain,(
% 3.42/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f37,plain,(
% 3.42/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.42/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 3.42/1.00  
% 3.42/1.00  fof(f62,plain,(
% 3.42/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.42/1.00    inference(cnf_transformation,[],[f37])).
% 3.42/1.00  
% 3.42/1.00  fof(f93,plain,(
% 3.42/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.42/1.00    inference(definition_unfolding,[],[f62,f72])).
% 3.42/1.00  
% 3.42/1.00  fof(f112,plain,(
% 3.42/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.42/1.00    inference(equality_resolution,[],[f93])).
% 3.42/1.00  
% 3.42/1.00  fof(f63,plain,(
% 3.42/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.42/1.00    inference(cnf_transformation,[],[f37])).
% 3.42/1.00  
% 3.42/1.00  fof(f92,plain,(
% 3.42/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.42/1.00    inference(definition_unfolding,[],[f63,f72])).
% 3.42/1.00  
% 3.42/1.00  fof(f110,plain,(
% 3.42/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.42/1.00    inference(equality_resolution,[],[f92])).
% 3.42/1.00  
% 3.42/1.00  fof(f111,plain,(
% 3.42/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.42/1.00    inference(equality_resolution,[],[f110])).
% 3.42/1.00  
% 3.42/1.00  fof(f52,plain,(
% 3.42/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.42/1.00    inference(cnf_transformation,[],[f30])).
% 3.42/1.00  
% 3.42/1.00  fof(f83,plain,(
% 3.42/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 3.42/1.00    inference(definition_unfolding,[],[f52,f60])).
% 3.42/1.00  
% 3.42/1.00  fof(f102,plain,(
% 3.42/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.42/1.00    inference(equality_resolution,[],[f83])).
% 3.42/1.00  
% 3.42/1.00  fof(f55,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f30])).
% 3.42/1.00  
% 3.42/1.00  fof(f80,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 3.42/1.00    inference(definition_unfolding,[],[f55,f60])).
% 3.42/1.00  
% 3.42/1.00  fof(f2,axiom,(
% 3.42/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f21,plain,(
% 3.42/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.42/1.00    inference(nnf_transformation,[],[f2])).
% 3.42/1.00  
% 3.42/1.00  fof(f22,plain,(
% 3.42/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.42/1.00    inference(flattening,[],[f21])).
% 3.42/1.00  
% 3.42/1.00  fof(f23,plain,(
% 3.42/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.42/1.00    inference(rectify,[],[f22])).
% 3.42/1.00  
% 3.42/1.00  fof(f24,plain,(
% 3.42/1.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.42/1.00    introduced(choice_axiom,[])).
% 3.42/1.00  
% 3.42/1.00  fof(f25,plain,(
% 3.42/1.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.42/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 3.42/1.00  
% 3.42/1.00  fof(f49,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f25])).
% 3.42/1.00  
% 3.42/1.00  fof(f48,plain,(
% 3.42/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f25])).
% 3.42/1.00  
% 3.42/1.00  fof(f6,axiom,(
% 3.42/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f61,plain,(
% 3.42/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.42/1.00    inference(cnf_transformation,[],[f6])).
% 3.42/1.00  
% 3.42/1.00  fof(f85,plain,(
% 3.42/1.00    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.42/1.00    inference(definition_unfolding,[],[f61,f60])).
% 3.42/1.00  
% 3.42/1.00  fof(f11,axiom,(
% 3.42/1.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) <=> ~r2_hidden(X0,X1))),
% 3.42/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.00  
% 3.42/1.00  fof(f38,plain,(
% 3.42/1.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)))),
% 3.42/1.00    inference(nnf_transformation,[],[f11])).
% 3.42/1.00  
% 3.42/1.00  fof(f73,plain,(
% 3.42/1.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f38])).
% 3.42/1.00  
% 3.42/1.00  fof(f95,plain,(
% 3.42/1.00    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0)) )),
% 3.42/1.00    inference(definition_unfolding,[],[f73,f60,f78,f78])).
% 3.42/1.00  
% 3.42/1.00  fof(f74,plain,(
% 3.42/1.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r2_hidden(X0,X1)) )),
% 3.42/1.00    inference(cnf_transformation,[],[f38])).
% 3.42/1.00  
% 3.42/1.00  fof(f94,plain,(
% 3.42/1.00    ( ! [X0,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) | r2_hidden(X0,X1)) )),
% 3.42/1.00    inference(definition_unfolding,[],[f74,f60,f78,f78])).
% 3.42/1.00  
% 3.42/1.00  fof(f75,plain,(
% 3.42/1.00    ~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4),
% 3.42/1.00    inference(cnf_transformation,[],[f41])).
% 3.42/1.00  
% 3.42/1.00  fof(f97,plain,(
% 3.42/1.00    ~r2_hidden(sK5,sK4) | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4),
% 3.42/1.00    inference(definition_unfolding,[],[f75,f60,f78])).
% 3.42/1.00  
% 3.42/1.00  fof(f47,plain,(
% 3.42/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 3.42/1.00    inference(cnf_transformation,[],[f25])).
% 3.42/1.00  
% 3.42/1.00  fof(f98,plain,(
% 3.42/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.42/1.00    inference(equality_resolution,[],[f47])).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9,plain,
% 3.42/1.00      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
% 3.42/1.00      | ~ r2_hidden(sK2(X0,X1,X2),X2)
% 3.42/1.00      | r2_hidden(sK2(X0,X1,X2),X1)
% 3.42/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.42/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_11,plain,
% 3.42/1.00      ( r2_hidden(sK2(X0,X1,X2),X0)
% 3.42/1.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.42/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.42/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_29,negated_conjecture,
% 3.42/1.00      ( r2_hidden(sK5,sK4)
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4 ),
% 3.42/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_6042,plain,
% 3.42/1.00      ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
% 3.42/1.00      | r2_hidden(sK5,sK4) ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_11,c_29]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9423,plain,
% 3.42/1.00      ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.42/1.00      | ~ r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
% 3.42/1.00      | r2_hidden(sK5,sK4)
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_9,c_6042]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_26,plain,
% 3.42/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.42/1.00      | X0 = X1
% 3.42/1.00      | X0 = X2
% 3.42/1.00      | X0 = X3 ),
% 3.42/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_40,plain,
% 3.42/1.00      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_25,plain,
% 3.42/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.42/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_43,plain,
% 3.42/1.00      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1626,plain,
% 3.42/1.00      ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1669,plain,
% 3.42/1.00      ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.42/1.00      | ~ r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_643,plain,
% 3.42/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.42/1.00      theory(equality) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1911,plain,
% 3.42/1.00      ( ~ r2_hidden(X0,X1)
% 3.42/1.00      | r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
% 3.42/1.00      | X2 != X0
% 3.42/1.00      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != X1 ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_643]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7978,plain,
% 3.42/1.00      ( r2_hidden(X0,k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
% 3.42/1.00      | ~ r2_hidden(X1,sK4)
% 3.42/1.00      | X0 != X1
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4 ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_1911]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7980,plain,
% 3.42/1.00      ( r2_hidden(sK5,k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))))
% 3.42/1.00      | ~ r2_hidden(sK5,sK4)
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4
% 3.42/1.00      | sK5 != sK5 ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_7978]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_13,plain,
% 3.42/1.00      ( ~ r2_hidden(X0,X1)
% 3.42/1.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 3.42/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_8835,plain,
% 3.42/1.00      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.42/1.00      | ~ r2_hidden(X0,k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_8837,plain,
% 3.42/1.00      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 3.42/1.00      | ~ r2_hidden(sK5,k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5)))) ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_8835]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9426,plain,
% 3.42/1.00      ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),k2_enumset1(sK5,sK5,sK5,sK5))
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_9423,c_29,c_40,c_43,c_1626,c_1669,c_7980,c_8837]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9430,plain,
% 3.42/1.00      ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_9426,c_29,c_40,c_43,c_1626,c_1669,c_7980,c_8837]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9703,plain,
% 3.42/1.00      ( sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4) = sK5 ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_9430,c_26]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_642,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_641,plain,( X0 = X0 ),theory(equality) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_2587,plain,
% 3.42/1.00      ( X0 != X1 | X1 = X0 ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_642,c_641]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9706,plain,
% 3.42/1.00      ( sK5 = sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_9703,c_2587]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3321,plain,
% 3.42/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_643,c_641]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9992,plain,
% 3.42/1.00      ( ~ r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),X0)
% 3.42/1.00      | r2_hidden(sK5,X0) ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_9706,c_3321]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_10,plain,
% 3.42/1.00      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
% 3.42/1.00      | r2_hidden(sK2(X0,X1,X2),X2)
% 3.42/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 3.42/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9701,plain,
% 3.42/1.00      ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4)
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_9430,c_10]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9717,plain,
% 3.42/1.00      ( r2_hidden(sK2(sK4,k2_enumset1(sK5,sK5,sK5,sK5),sK4),sK4) ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_9701,c_29,c_40,c_43,c_1626,c_7980,c_8837]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_10801,plain,
% 3.42/1.00      ( r2_hidden(sK5,sK4) ),
% 3.42/1.00      inference(resolution,[status(thm)],[c_9992,c_9717]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_4,plain,
% 3.42/1.00      ( r2_hidden(sK1(X0,X1,X2),X1)
% 3.42/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.42/1.00      | k3_xboole_0(X0,X1) = X2 ),
% 3.42/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1307,plain,
% 3.42/1.00      ( k3_xboole_0(X0,X1) = X2
% 3.42/1.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top
% 3.42/1.00      | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_5,plain,
% 3.42/1.00      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.42/1.00      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.42/1.00      | k3_xboole_0(X0,X1) = X2 ),
% 3.42/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1306,plain,
% 3.42/1.00      ( k3_xboole_0(X0,X1) = X2
% 3.42/1.00      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 3.42/1.00      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_18,plain,
% 3.42/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.42/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_28,plain,
% 3.42/1.00      ( ~ r2_hidden(X0,X1)
% 3.42/1.00      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1285,plain,
% 3.42/1.00      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) != k2_enumset1(X0,X0,X0,X0)
% 3.42/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1811,plain,
% 3.42/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_18,c_1285]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_4069,plain,
% 3.42/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.42/1.00      | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_1306,c_1811]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_27,plain,
% 3.42/1.00      ( r2_hidden(X0,X1)
% 3.42/1.00      | k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0) ),
% 3.42/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1286,plain,
% 3.42/1.00      ( k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) = k2_enumset1(X0,X0,X0,X0)
% 3.42/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_30,negated_conjecture,
% 3.42/1.00      ( ~ r2_hidden(sK5,sK4)
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
% 3.42/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1283,plain,
% 3.42/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
% 3.42/1.00      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_3223,plain,
% 3.42/1.00      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4)) = k2_enumset1(sK5,sK5,sK5,sK5)
% 3.42/1.00      | k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4 ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_1286,c_1283]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1298,plain,
% 3.42/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.42/1.00      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_4205,plain,
% 3.42/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
% 3.42/1.00      | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 3.42/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_3223,c_1298]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9281,plain,
% 3.42/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
% 3.42/1.00      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0) = k1_xboole_0
% 3.42/1.00      | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),X0,k1_xboole_0),sK4) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_4069,c_4205]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9348,plain,
% 3.42/1.00      ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0) = k1_xboole_0
% 3.42/1.00      | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),X0,k1_xboole_0),sK4) != iProver_top ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_9281,c_29,c_40,c_43,c_7980,c_8837]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9357,plain,
% 3.42/1.00      ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = k1_xboole_0
% 3.42/1.00      | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_1307,c_9348]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_4446,plain,
% 3.42/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
% 3.42/1.00      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),X0) = X1
% 3.42/1.00      | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),X0,X1),X1) = iProver_top
% 3.42/1.00      | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),X0,X1),sK4) != iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_1306,c_4205]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_5640,plain,
% 3.42/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
% 3.42/1.00      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = X0
% 3.42/1.00      | r2_hidden(sK1(k2_enumset1(sK5,sK5,sK5,sK5),sK4,X0),X0) = iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_1307,c_4446]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_7245,plain,
% 3.42/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) = sK4
% 3.42/1.00      | k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = k1_xboole_0 ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_5640,c_1811]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9629,plain,
% 3.42/1.00      ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) = k1_xboole_0 ),
% 3.42/1.00      inference(global_propositional_subsumption,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_9357,c_29,c_40,c_43,c_7245,c_7980,c_8837]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_6,plain,
% 3.42/1.00      ( ~ r2_hidden(X0,X1)
% 3.42/1.00      | ~ r2_hidden(X0,X2)
% 3.42/1.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.42/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1305,plain,
% 3.42/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.42/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.42/1.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9655,plain,
% 3.42/1.00      ( r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 3.42/1.00      | r2_hidden(X0,sK4) != iProver_top
% 3.42/1.00      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.42/1.00      inference(superposition,[status(thm)],[c_9629,c_1305]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_9687,plain,
% 3.42/1.00      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 3.42/1.00      | r2_hidden(sK5,sK4) != iProver_top
% 3.42/1.00      | r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_9655]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_1813,plain,
% 3.42/1.00      ( r2_hidden(sK5,k1_xboole_0) != iProver_top ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_1811]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_42,plain,
% 3.42/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_44,plain,
% 3.42/1.00      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 3.42/1.00      inference(instantiation,[status(thm)],[c_42]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(c_32,plain,
% 3.42/1.00      ( k5_xboole_0(sK4,k3_xboole_0(sK4,k2_enumset1(sK5,sK5,sK5,sK5))) != sK4
% 3.42/1.00      | r2_hidden(sK5,sK4) = iProver_top ),
% 3.42/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.42/1.00  
% 3.42/1.00  cnf(contradiction,plain,
% 3.42/1.00      ( $false ),
% 3.42/1.00      inference(minisat,
% 3.42/1.00                [status(thm)],
% 3.42/1.00                [c_10801,c_9687,c_1813,c_44,c_32,c_30]) ).
% 3.42/1.00  
% 3.42/1.00  
% 3.42/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.42/1.00  
% 3.42/1.00  ------                               Statistics
% 3.42/1.00  
% 3.42/1.00  ------ Selected
% 3.42/1.00  
% 3.42/1.00  total_time:                             0.336
% 3.42/1.00  
%------------------------------------------------------------------------------
