%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:43 EST 2020

% Result     : Theorem 15.52s
% Output     : CNFRefutation 15.52s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 180 expanded)
%              Number of clauses        :   36 (  40 expanded)
%              Number of leaves         :   20 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  373 ( 584 expanded)
%              Number of equality atoms :  166 ( 289 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f24])).

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
    inference(flattening,[],[f34])).

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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f79])).

fof(f100,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f92])).

fof(f101,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f100])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f86,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f71,f79])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f81])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK3,sK4)
      & r1_tarski(k2_xboole_0(k1_tarski(sK3),sK4),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r2_hidden(sK3,sK4)
    & r1_tarski(k2_xboole_0(k1_tarski(sK3),sK4),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f39])).

fof(f76,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK3),sK4),sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f96,plain,(
    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)),sK4) ),
    inference(definition_unfolding,[],[f76,f81,f82])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f79])).

fof(f104,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f94])).

fof(f105,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k4_enumset1(X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f104])).

fof(f77,plain,(
    ~ r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_24,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_51845,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_51853,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_51846,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_51848,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_52251,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_51846,c_51848])).

cnf(c_11,negated_conjecture,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_51850,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_52707,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X3))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_52251,c_51850])).

cnf(c_52724,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_51853,c_52707])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_51856,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_52835,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_52724,c_51856])).

cnf(c_52898,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_51845,c_52835])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_51854,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_304,plain,
    ( k3_xboole_0(X0,X1) = X0
    | k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_305,plain,
    ( k3_xboole_0(k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)),sK4) = k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_51997,plain,
    ( k3_xboole_0(sK4,k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
    inference(superposition,[status(thm)],[c_305,c_0])).

cnf(c_52017,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_51846,c_51850])).

cnf(c_52047,plain,
    ( r2_hidden(X0,k5_xboole_0(sK4,k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)))) != iProver_top
    | r2_hidden(X0,k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_51997,c_52017])).

cnf(c_52497,plain,
    ( r2_hidden(X0,k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_51854,c_52047])).

cnf(c_53150,plain,
    ( r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_52898,c_52497])).

cnf(c_53167,plain,
    ( r2_hidden(sK3,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53150])).

cnf(c_26,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_41,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_43,plain,
    ( r2_hidden(sK3,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_31,plain,
    ( r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53167,c_43,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.52/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.52/2.50  
% 15.52/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.52/2.50  
% 15.52/2.50  ------  iProver source info
% 15.52/2.50  
% 15.52/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.52/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.52/2.50  git: non_committed_changes: false
% 15.52/2.50  git: last_make_outside_of_git: false
% 15.52/2.50  
% 15.52/2.50  ------ 
% 15.52/2.50  ------ Parsing...
% 15.52/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  ------ Proving...
% 15.52/2.50  ------ Problem Properties 
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  clauses                                 29
% 15.52/2.50  conjectures                             3
% 15.52/2.50  EPR                                     2
% 15.52/2.50  Horn                                    20
% 15.52/2.50  unary                                   8
% 15.52/2.50  binary                                  6
% 15.52/2.50  lits                                    69
% 15.52/2.50  lits eq                                 19
% 15.52/2.50  fd_pure                                 0
% 15.52/2.50  fd_pseudo                               0
% 15.52/2.50  fd_cond                                 0
% 15.52/2.50  fd_pseudo_cond                          7
% 15.52/2.50  AC symbols                              0
% 15.52/2.50  
% 15.52/2.50  ------ Input Options Time Limit: Unbounded
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 15.52/2.50  Current options:
% 15.52/2.50  ------ 
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing...
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing...
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing...
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing...
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.52/2.50  
% 15.52/2.50  ------ Proving...
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  % SZS status Theorem for theBenchmark.p
% 15.52/2.50  
% 15.52/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.52/2.50  
% 15.52/2.50  fof(f10,axiom,(
% 15.52/2.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f24,plain,(
% 15.52/2.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 15.52/2.50    inference(ennf_transformation,[],[f10])).
% 15.52/2.50  
% 15.52/2.50  fof(f34,plain,(
% 15.52/2.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.52/2.50    inference(nnf_transformation,[],[f24])).
% 15.52/2.50  
% 15.52/2.50  fof(f35,plain,(
% 15.52/2.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.52/2.50    inference(flattening,[],[f34])).
% 15.52/2.50  
% 15.52/2.50  fof(f36,plain,(
% 15.52/2.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.52/2.50    inference(rectify,[],[f35])).
% 15.52/2.50  
% 15.52/2.50  fof(f37,plain,(
% 15.52/2.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 15.52/2.50    introduced(choice_axiom,[])).
% 15.52/2.50  
% 15.52/2.50  fof(f38,plain,(
% 15.52/2.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 15.52/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 15.52/2.50  
% 15.52/2.50  fof(f65,plain,(
% 15.52/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.52/2.50    inference(cnf_transformation,[],[f38])).
% 15.52/2.50  
% 15.52/2.50  fof(f13,axiom,(
% 15.52/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f72,plain,(
% 15.52/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f13])).
% 15.52/2.50  
% 15.52/2.50  fof(f14,axiom,(
% 15.52/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f73,plain,(
% 15.52/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f14])).
% 15.52/2.50  
% 15.52/2.50  fof(f15,axiom,(
% 15.52/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f74,plain,(
% 15.52/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f15])).
% 15.52/2.50  
% 15.52/2.50  fof(f78,plain,(
% 15.52/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 15.52/2.50    inference(definition_unfolding,[],[f73,f74])).
% 15.52/2.50  
% 15.52/2.50  fof(f79,plain,(
% 15.52/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 15.52/2.50    inference(definition_unfolding,[],[f72,f78])).
% 15.52/2.50  
% 15.52/2.50  fof(f92,plain,(
% 15.52/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 15.52/2.50    inference(definition_unfolding,[],[f65,f79])).
% 15.52/2.50  
% 15.52/2.50  fof(f100,plain,(
% 15.52/2.50    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3) )),
% 15.52/2.50    inference(equality_resolution,[],[f92])).
% 15.52/2.50  
% 15.52/2.50  fof(f101,plain,(
% 15.52/2.50    ( ! [X0,X5,X1] : (r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5))) )),
% 15.52/2.50    inference(equality_resolution,[],[f100])).
% 15.52/2.50  
% 15.52/2.50  fof(f3,axiom,(
% 15.52/2.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f20,plain,(
% 15.52/2.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 15.52/2.50    inference(ennf_transformation,[],[f3])).
% 15.52/2.50  
% 15.52/2.50  fof(f31,plain,(
% 15.52/2.50    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 15.52/2.50    inference(nnf_transformation,[],[f20])).
% 15.52/2.50  
% 15.52/2.50  fof(f50,plain,(
% 15.52/2.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f31])).
% 15.52/2.50  
% 15.52/2.50  fof(f8,axiom,(
% 15.52/2.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f60,plain,(
% 15.52/2.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f8])).
% 15.52/2.50  
% 15.52/2.50  fof(f5,axiom,(
% 15.52/2.50    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f55,plain,(
% 15.52/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f5])).
% 15.52/2.50  
% 15.52/2.50  fof(f86,plain,(
% 15.52/2.50    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 15.52/2.50    inference(definition_unfolding,[],[f60,f55])).
% 15.52/2.50  
% 15.52/2.50  fof(f7,axiom,(
% 15.52/2.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f23,plain,(
% 15.52/2.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 15.52/2.50    inference(ennf_transformation,[],[f7])).
% 15.52/2.50  
% 15.52/2.50  fof(f58,plain,(
% 15.52/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f23])).
% 15.52/2.50  
% 15.52/2.50  fof(f16,axiom,(
% 15.52/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f75,plain,(
% 15.52/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.52/2.50    inference(cnf_transformation,[],[f16])).
% 15.52/2.50  
% 15.52/2.50  fof(f12,axiom,(
% 15.52/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f71,plain,(
% 15.52/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f12])).
% 15.52/2.50  
% 15.52/2.50  fof(f80,plain,(
% 15.52/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 15.52/2.50    inference(definition_unfolding,[],[f71,f79])).
% 15.52/2.50  
% 15.52/2.50  fof(f81,plain,(
% 15.52/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 15.52/2.50    inference(definition_unfolding,[],[f75,f80])).
% 15.52/2.50  
% 15.52/2.50  fof(f84,plain,(
% 15.52/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) | r1_xboole_0(X0,X1)) )),
% 15.52/2.50    inference(definition_unfolding,[],[f58,f81])).
% 15.52/2.50  
% 15.52/2.50  fof(f4,axiom,(
% 15.52/2.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f19,plain,(
% 15.52/2.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.52/2.50    inference(rectify,[],[f4])).
% 15.52/2.50  
% 15.52/2.50  fof(f21,plain,(
% 15.52/2.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 15.52/2.50    inference(ennf_transformation,[],[f19])).
% 15.52/2.50  
% 15.52/2.50  fof(f32,plain,(
% 15.52/2.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 15.52/2.50    introduced(choice_axiom,[])).
% 15.52/2.50  
% 15.52/2.50  fof(f33,plain,(
% 15.52/2.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 15.52/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f32])).
% 15.52/2.50  
% 15.52/2.50  fof(f54,plain,(
% 15.52/2.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f33])).
% 15.52/2.50  
% 15.52/2.50  fof(f2,axiom,(
% 15.52/2.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f26,plain,(
% 15.52/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.52/2.50    inference(nnf_transformation,[],[f2])).
% 15.52/2.50  
% 15.52/2.50  fof(f27,plain,(
% 15.52/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.52/2.50    inference(flattening,[],[f26])).
% 15.52/2.50  
% 15.52/2.50  fof(f28,plain,(
% 15.52/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.52/2.50    inference(rectify,[],[f27])).
% 15.52/2.50  
% 15.52/2.50  fof(f29,plain,(
% 15.52/2.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 15.52/2.50    introduced(choice_axiom,[])).
% 15.52/2.50  
% 15.52/2.50  fof(f30,plain,(
% 15.52/2.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 15.52/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 15.52/2.50  
% 15.52/2.50  fof(f43,plain,(
% 15.52/2.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 15.52/2.50    inference(cnf_transformation,[],[f30])).
% 15.52/2.50  
% 15.52/2.50  fof(f98,plain,(
% 15.52/2.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 15.52/2.50    inference(equality_resolution,[],[f43])).
% 15.52/2.50  
% 15.52/2.50  fof(f51,plain,(
% 15.52/2.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f31])).
% 15.52/2.50  
% 15.52/2.50  fof(f6,axiom,(
% 15.52/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f22,plain,(
% 15.52/2.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.52/2.50    inference(ennf_transformation,[],[f6])).
% 15.52/2.50  
% 15.52/2.50  fof(f56,plain,(
% 15.52/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f22])).
% 15.52/2.50  
% 15.52/2.50  fof(f17,conjecture,(
% 15.52/2.50    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f18,negated_conjecture,(
% 15.52/2.50    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 15.52/2.50    inference(negated_conjecture,[],[f17])).
% 15.52/2.50  
% 15.52/2.50  fof(f25,plain,(
% 15.52/2.50    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 15.52/2.50    inference(ennf_transformation,[],[f18])).
% 15.52/2.50  
% 15.52/2.50  fof(f39,plain,(
% 15.52/2.50    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK3,sK4) & r1_tarski(k2_xboole_0(k1_tarski(sK3),sK4),sK4))),
% 15.52/2.50    introduced(choice_axiom,[])).
% 15.52/2.50  
% 15.52/2.50  fof(f40,plain,(
% 15.52/2.50    ~r2_hidden(sK3,sK4) & r1_tarski(k2_xboole_0(k1_tarski(sK3),sK4),sK4)),
% 15.52/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f25,f39])).
% 15.52/2.50  
% 15.52/2.50  fof(f76,plain,(
% 15.52/2.50    r1_tarski(k2_xboole_0(k1_tarski(sK3),sK4),sK4)),
% 15.52/2.50    inference(cnf_transformation,[],[f40])).
% 15.52/2.50  
% 15.52/2.50  fof(f11,axiom,(
% 15.52/2.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f70,plain,(
% 15.52/2.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f11])).
% 15.52/2.50  
% 15.52/2.50  fof(f82,plain,(
% 15.52/2.50    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 15.52/2.50    inference(definition_unfolding,[],[f70,f80])).
% 15.52/2.50  
% 15.52/2.50  fof(f96,plain,(
% 15.52/2.50    r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)),sK4)),
% 15.52/2.50    inference(definition_unfolding,[],[f76,f81,f82])).
% 15.52/2.50  
% 15.52/2.50  fof(f1,axiom,(
% 15.52/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.52/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.52/2.50  
% 15.52/2.50  fof(f41,plain,(
% 15.52/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.52/2.50    inference(cnf_transformation,[],[f1])).
% 15.52/2.50  
% 15.52/2.50  fof(f63,plain,(
% 15.52/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 15.52/2.50    inference(cnf_transformation,[],[f38])).
% 15.52/2.50  
% 15.52/2.50  fof(f94,plain,(
% 15.52/2.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 15.52/2.50    inference(definition_unfolding,[],[f63,f79])).
% 15.52/2.50  
% 15.52/2.50  fof(f104,plain,(
% 15.52/2.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X5,X5,X5,X5,X1,X2) != X3) )),
% 15.52/2.50    inference(equality_resolution,[],[f94])).
% 15.52/2.50  
% 15.52/2.50  fof(f105,plain,(
% 15.52/2.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k4_enumset1(X5,X5,X5,X5,X1,X2))) )),
% 15.52/2.50    inference(equality_resolution,[],[f104])).
% 15.52/2.50  
% 15.52/2.50  fof(f77,plain,(
% 15.52/2.50    ~r2_hidden(sK3,sK4)),
% 15.52/2.50    inference(cnf_transformation,[],[f40])).
% 15.52/2.50  
% 15.52/2.50  cnf(c_24,plain,
% 15.52/2.50      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
% 15.52/2.50      inference(cnf_transformation,[],[f101]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_51845,plain,
% 15.52/2.50      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_8,plain,
% 15.52/2.50      ( ~ r2_hidden(X0,X1)
% 15.52/2.50      | r2_hidden(X0,X2)
% 15.52/2.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 15.52/2.50      inference(cnf_transformation,[],[f50]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_51853,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.52/2.50      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_18,plain,
% 15.52/2.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 15.52/2.50      inference(cnf_transformation,[],[f86]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_51846,plain,
% 15.52/2.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_16,plain,
% 15.52/2.50      ( r1_xboole_0(X0,X1)
% 15.52/2.50      | ~ r1_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) ),
% 15.52/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_51848,plain,
% 15.52/2.50      ( r1_xboole_0(X0,X1) = iProver_top
% 15.52/2.50      | r1_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) != iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_52251,plain,
% 15.52/2.50      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))),X1) = iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_51846,c_51848]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_11,negated_conjecture,
% 15.52/2.50      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 15.52/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_51850,plain,
% 15.52/2.50      ( r1_xboole_0(X0,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X2,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X2,X0) != iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_52707,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X3))))) != iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_52251,c_51850]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_52724,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X0,X2) != iProver_top
% 15.52/2.50      | r2_hidden(X0,k3_xboole_0(X1,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3)))) = iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_51853,c_52707]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_5,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 15.52/2.50      inference(cnf_transformation,[],[f98]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_51856,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) = iProver_top
% 15.52/2.50      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_52835,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X0,X2) != iProver_top
% 15.52/2.50      | r2_hidden(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X3))) = iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_52724,c_51856]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_52898,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_51845,c_52835]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_7,plain,
% 15.52/2.50      ( ~ r2_hidden(X0,X1)
% 15.52/2.50      | r2_hidden(X0,X2)
% 15.52/2.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 15.52/2.50      inference(cnf_transformation,[],[f51]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_51854,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.52/2.50      | r2_hidden(X0,k5_xboole_0(X2,X1)) = iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_14,plain,
% 15.52/2.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.52/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_29,negated_conjecture,
% 15.52/2.50      ( r1_tarski(k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)),sK4) ),
% 15.52/2.50      inference(cnf_transformation,[],[f96]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_304,plain,
% 15.52/2.50      ( k3_xboole_0(X0,X1) = X0
% 15.52/2.50      | k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) != X0
% 15.52/2.50      | sK4 != X1 ),
% 15.52/2.50      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_305,plain,
% 15.52/2.50      ( k3_xboole_0(k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)),sK4) = k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
% 15.52/2.50      inference(unflattening,[status(thm)],[c_304]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_0,plain,
% 15.52/2.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.52/2.50      inference(cnf_transformation,[],[f41]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_51997,plain,
% 15.52/2.50      ( k3_xboole_0(sK4,k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))) = k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)) ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_305,c_0]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_52017,plain,
% 15.52/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.52/2.50      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_51846,c_51850]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_52047,plain,
% 15.52/2.50      ( r2_hidden(X0,k5_xboole_0(sK4,k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4)))) != iProver_top
% 15.52/2.50      | r2_hidden(X0,k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))) != iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_51997,c_52017]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_52497,plain,
% 15.52/2.50      ( r2_hidden(X0,k3_tarski(k4_enumset1(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK4))) != iProver_top
% 15.52/2.50      | r2_hidden(X0,sK4) = iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_51854,c_52047]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_53150,plain,
% 15.52/2.50      ( r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 15.52/2.50      | r2_hidden(X0,sK4) = iProver_top ),
% 15.52/2.50      inference(superposition,[status(thm)],[c_52898,c_52497]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_53167,plain,
% 15.52/2.50      ( r2_hidden(sK3,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 15.52/2.50      | r2_hidden(sK3,sK4) = iProver_top ),
% 15.52/2.50      inference(instantiation,[status(thm)],[c_53150]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_26,plain,
% 15.52/2.50      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
% 15.52/2.50      inference(cnf_transformation,[],[f105]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_41,plain,
% 15.52/2.50      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_43,plain,
% 15.52/2.50      ( r2_hidden(sK3,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 15.52/2.50      inference(instantiation,[status(thm)],[c_41]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_28,negated_conjecture,
% 15.52/2.50      ( ~ r2_hidden(sK3,sK4) ),
% 15.52/2.50      inference(cnf_transformation,[],[f77]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(c_31,plain,
% 15.52/2.50      ( r2_hidden(sK3,sK4) != iProver_top ),
% 15.52/2.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.52/2.50  
% 15.52/2.50  cnf(contradiction,plain,
% 15.52/2.50      ( $false ),
% 15.52/2.50      inference(minisat,[status(thm)],[c_53167,c_43,c_31]) ).
% 15.52/2.50  
% 15.52/2.50  
% 15.52/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.52/2.50  
% 15.52/2.50  ------                               Statistics
% 15.52/2.50  
% 15.52/2.50  ------ Selected
% 15.52/2.50  
% 15.52/2.50  total_time:                             1.792
% 15.52/2.50  
%------------------------------------------------------------------------------
