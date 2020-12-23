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
% DateTime   : Thu Dec  3 11:36:25 EST 2020

% Result     : Theorem 39.53s
% Output     : CNFRefutation 39.53s
% Verified   : 
% Statistics : Number of formulae       :  184 (3799 expanded)
%              Number of clauses        :  104 ( 826 expanded)
%              Number of leaves         :   22 ( 972 expanded)
%              Depth                    :   31
%              Number of atoms          :  596 (11098 expanded)
%              Number of equality atoms :  358 (6251 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f32])).

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
    inference(rectify,[],[f33])).

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) = X2
      | sK2(X0,X1,X2,X3) = X1
      | sK2(X0,X1,X2,X3) = X0
      | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) = X2
      | sK2(X0,X1,X2,X3) = X1
      | sK2(X0,X1,X2,X3) = X0
      | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f30])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK4,sK5)
        | ~ r2_hidden(sK3,sK5)
        | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 )
      & ( ( r2_hidden(sK4,sK5)
          & r2_hidden(sK3,sK5) )
        | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r2_hidden(sK4,sK5)
      | ~ r2_hidden(sK3,sK5)
      | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 )
    & ( ( r2_hidden(sK4,sK5)
        & r2_hidden(sK3,sK5) )
      | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f39])).

fof(f72,plain,
    ( r2_hidden(sK4,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f75])).

fof(f87,plain,
    ( r2_hidden(sK4,sK5)
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f72,f54,f76])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) = k4_enumset1(X0,X0,X0,X0,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f76,f76])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f96,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f83])).

fof(f97,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k4_enumset1(X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f75])).

fof(f92,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f93,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f92])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f71,plain,
    ( r2_hidden(sK3,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,
    ( r2_hidden(sK3,sK5)
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f71,f54,f76])).

fof(f73,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK3,sK5)
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f73,f54,f76])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f94,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k4_enumset1(X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f82])).

fof(f95,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f94])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

cnf(c_19,plain,
    ( r2_hidden(sK2(X0,X1,X2,X3),X3)
    | k4_enumset1(X0,X0,X0,X0,X1,X2) = X3
    | sK2(X0,X1,X2,X3) = X2
    | sK2(X0,X1,X2,X3) = X1
    | sK2(X0,X1,X2,X3) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_606,plain,
    ( k4_enumset1(X0,X0,X0,X0,X1,X2) = X3
    | sK2(X0,X1,X2,X3) = X2
    | sK2(X0,X1,X2,X3) = X1
    | sK2(X0,X1,X2,X3) = X0
    | r2_hidden(sK2(X0,X1,X2,X3),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_612,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4051,plain,
    ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_612])).

cnf(c_14,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_51,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4073,plain,
    ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4051,c_51])).

cnf(c_4074,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4073])).

cnf(c_4993,plain,
    ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_xboole_0
    | sK2(X0,X1,X2,k1_xboole_0) = X2
    | sK2(X0,X1,X2,k1_xboole_0) = X1
    | sK2(X0,X1,X2,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_606,c_4074])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_26,negated_conjecture,
    ( r2_hidden(sK4,sK5)
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_599,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1044,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_599])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) = k4_enumset1(X0,X0,X0,X0,X0,X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_601,plain,
    ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) = k4_enumset1(X0,X0,X0,X0,X0,X1)
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1305,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,X0),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_601])).

cnf(c_1458,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_1044,c_1305])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_615,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6128,plain,
    ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1458,c_615])).

cnf(c_7792,plain,
    ( r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6128,c_4074])).

cnf(c_7793,plain,
    ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7792])).

cnf(c_120238,plain,
    ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
    | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
    | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_7793])).

cnf(c_120828,plain,
    ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
    | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
    | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_120238,c_13])).

cnf(c_22,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_37,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_39,plain,
    ( r2_hidden(sK3,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_20,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_605,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_617,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7803,plain,
    ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7793,c_617])).

cnf(c_37248,plain,
    ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_7803])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK3,sK5)
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_598,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1045,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_598])).

cnf(c_1450,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_601])).

cnf(c_2059,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_1045,c_1450])).

cnf(c_6125,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2059,c_615])).

cnf(c_6596,plain,
    ( r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6125,c_4074])).

cnf(c_6597,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6596])).

cnf(c_120241,plain,
    ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
    | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_6597])).

cnf(c_120795,plain,
    ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
    | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_120241,c_13])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(sK3,sK5)
    | ~ r2_hidden(sK4,sK5)
    | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_600,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1046,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_600])).

cnf(c_3714,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2059,c_1046])).

cnf(c_6607,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6597,c_617])).

cnf(c_36055,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_6607])).

cnf(c_21,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_604,plain,
    ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_36056,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_6607])).

cnf(c_121658,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120795,c_3714,c_36055,c_36056])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_618,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_121700,plain,
    ( r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_121658,c_618])).

cnf(c_122262,plain,
    ( r2_hidden(sK3,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_121700])).

cnf(c_2058,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1044,c_1450])).

cnf(c_6126,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2058,c_615])).

cnf(c_6649,plain,
    ( r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6126,c_4074])).

cnf(c_6650,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6649])).

cnf(c_120240,plain,
    ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
    | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k3_xboole_0(sK5,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4993,c_6650])).

cnf(c_120806,plain,
    ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
    | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
    | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_120240,c_13])).

cnf(c_6660,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6650,c_617])).

cnf(c_36676,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_6660])).

cnf(c_122859,plain,
    ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120806,c_39,c_1046,c_2058,c_36676,c_122262])).

cnf(c_122995,plain,
    ( k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_122859,c_0])).

cnf(c_123892,plain,
    ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_122995,c_1046])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_123896,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_123892,c_15])).

cnf(c_123897,plain,
    ( r2_hidden(sK3,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_123896])).

cnf(c_126268,plain,
    ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120828,c_39,c_37248,c_122262,c_123897])).

cnf(c_126273,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = k3_xboole_0(k1_xboole_0,sK5)
    | sK2(sK4,sK4,sK4,k1_xboole_0) = sK4 ),
    inference(superposition,[status(thm)],[c_4993,c_126268])).

cnf(c_1064,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_126416,plain,
    ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | sK2(sK4,sK4,sK4,k1_xboole_0) = sK4 ),
    inference(demodulation,[status(thm)],[c_126273,c_1064])).

cnf(c_603,plain,
    ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_146864,plain,
    ( sK2(sK4,sK4,sK4,k1_xboole_0) = sK4
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_126416,c_603])).

cnf(c_3197,plain,
    ( ~ r2_hidden(sK4,k3_xboole_0(X0,sK5))
    | r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7400,plain,
    ( ~ r2_hidden(sK4,k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,sK4),sK5))
    | r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3197])).

cnf(c_7402,plain,
    ( r2_hidden(sK4,k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,sK4),sK5)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7400])).

cnf(c_7404,plain,
    ( r2_hidden(sK4,k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7402])).

cnf(c_224,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7886,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_8119,plain,
    ( r2_hidden(sK4,k4_enumset1(X0,X0,X0,X0,X1,sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_8120,plain,
    ( r2_hidden(sK4,k4_enumset1(X0,X0,X0,X0,X1,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8119])).

cnf(c_8122,plain,
    ( r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8120])).

cnf(c_225,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3386,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_225,c_224])).

cnf(c_12308,plain,
    ( r2_hidden(sK4,sK5)
    | k1_xboole_0 = k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_3386,c_26])).

cnf(c_12311,plain,
    ( k1_xboole_0 = k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12308])).

cnf(c_846,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_enumset1(X2,X2,X2,X2,X3,X0))
    | r2_hidden(X0,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X0),X1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7300,plain,
    ( ~ r2_hidden(sK4,k4_enumset1(X0,X0,X0,X0,X1,sK4))
    | r2_hidden(sK4,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,sK4),k3_xboole_0(X2,sK5)))
    | r2_hidden(sK4,k3_xboole_0(X2,sK5)) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_51030,plain,
    ( ~ r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))
    | r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)))
    | r2_hidden(sK4,k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_7300])).

cnf(c_51031,plain,
    ( r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5))) = iProver_top
    | r2_hidden(sK4,k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51030])).

cnf(c_227,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_932,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X4,X2),X5))
    | X0 != X2
    | X1 != k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X4,X2),X5) ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_7959,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X0),X3))
    | r2_hidden(X4,k1_xboole_0)
    | X4 != X0
    | k1_xboole_0 != k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X0),X3) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_31683,plain,
    ( r2_hidden(X0,k1_xboole_0)
    | ~ r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)))
    | X0 != sK4
    | k1_xboole_0 != k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_7959])).

cnf(c_86636,plain,
    ( ~ r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)))
    | r2_hidden(sK4,k1_xboole_0)
    | sK4 != sK4
    | k1_xboole_0 != k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_31683])).

cnf(c_86637,plain,
    ( sK4 != sK4
    | k1_xboole_0 != k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5))
    | r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5))) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86636])).

cnf(c_146988,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_146864,c_39,c_7404,c_7886,c_8122,c_12311,c_51031,c_86637,c_122262,c_123897])).

cnf(c_146993,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_146988,c_4074])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.53/5.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.53/5.49  
% 39.53/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.53/5.49  
% 39.53/5.49  ------  iProver source info
% 39.53/5.49  
% 39.53/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.53/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.53/5.49  git: non_committed_changes: false
% 39.53/5.49  git: last_make_outside_of_git: false
% 39.53/5.49  
% 39.53/5.49  ------ 
% 39.53/5.49  ------ Parsing...
% 39.53/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.53/5.49  
% 39.53/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.53/5.49  
% 39.53/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.53/5.49  
% 39.53/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.53/5.49  ------ Proving...
% 39.53/5.49  ------ Problem Properties 
% 39.53/5.49  
% 39.53/5.49  
% 39.53/5.49  clauses                                 28
% 39.53/5.49  conjectures                             3
% 39.53/5.49  EPR                                     1
% 39.53/5.49  Horn                                    18
% 39.53/5.49  unary                                   7
% 39.53/5.49  binary                                  6
% 39.53/5.49  lits                                    68
% 39.53/5.49  lits eq                                 23
% 39.53/5.49  fd_pure                                 0
% 39.53/5.49  fd_pseudo                               0
% 39.53/5.49  fd_cond                                 0
% 39.53/5.49  fd_pseudo_cond                          7
% 39.53/5.49  AC symbols                              0
% 39.53/5.49  
% 39.53/5.49  ------ Input Options Time Limit: Unbounded
% 39.53/5.49  
% 39.53/5.49  
% 39.53/5.49  ------ 
% 39.53/5.49  Current options:
% 39.53/5.49  ------ 
% 39.53/5.49  
% 39.53/5.49  
% 39.53/5.49  
% 39.53/5.49  
% 39.53/5.49  ------ Proving...
% 39.53/5.49  
% 39.53/5.49  
% 39.53/5.49  % SZS status Theorem for theBenchmark.p
% 39.53/5.49  
% 39.53/5.49   Resolution empty clause
% 39.53/5.49  
% 39.53/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.53/5.49  
% 39.53/5.49  fof(f9,axiom,(
% 39.53/5.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f20,plain,(
% 39.53/5.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 39.53/5.49    inference(ennf_transformation,[],[f9])).
% 39.53/5.49  
% 39.53/5.49  fof(f32,plain,(
% 39.53/5.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 39.53/5.49    inference(nnf_transformation,[],[f20])).
% 39.53/5.49  
% 39.53/5.49  fof(f33,plain,(
% 39.53/5.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 39.53/5.49    inference(flattening,[],[f32])).
% 39.53/5.49  
% 39.53/5.49  fof(f34,plain,(
% 39.53/5.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 39.53/5.49    inference(rectify,[],[f33])).
% 39.53/5.49  
% 39.53/5.49  fof(f35,plain,(
% 39.53/5.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 39.53/5.49    introduced(choice_axiom,[])).
% 39.53/5.49  
% 39.53/5.49  fof(f36,plain,(
% 39.53/5.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 39.53/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 39.53/5.49  
% 39.53/5.49  fof(f62,plain,(
% 39.53/5.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f36])).
% 39.53/5.49  
% 39.53/5.49  fof(f11,axiom,(
% 39.53/5.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f67,plain,(
% 39.53/5.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f11])).
% 39.53/5.49  
% 39.53/5.49  fof(f12,axiom,(
% 39.53/5.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f68,plain,(
% 39.53/5.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f12])).
% 39.53/5.49  
% 39.53/5.49  fof(f13,axiom,(
% 39.53/5.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f69,plain,(
% 39.53/5.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f13])).
% 39.53/5.49  
% 39.53/5.49  fof(f74,plain,(
% 39.53/5.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 39.53/5.49    inference(definition_unfolding,[],[f68,f69])).
% 39.53/5.49  
% 39.53/5.49  fof(f75,plain,(
% 39.53/5.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 39.53/5.49    inference(definition_unfolding,[],[f67,f74])).
% 39.53/5.49  
% 39.53/5.49  fof(f80,plain,(
% 39.53/5.49    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X0,X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 39.53/5.49    inference(definition_unfolding,[],[f62,f75])).
% 39.53/5.49  
% 39.53/5.49  fof(f6,axiom,(
% 39.53/5.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f55,plain,(
% 39.53/5.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 39.53/5.49    inference(cnf_transformation,[],[f6])).
% 39.53/5.49  
% 39.53/5.49  fof(f4,axiom,(
% 39.53/5.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f17,plain,(
% 39.53/5.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 39.53/5.49    inference(rectify,[],[f4])).
% 39.53/5.49  
% 39.53/5.49  fof(f19,plain,(
% 39.53/5.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 39.53/5.49    inference(ennf_transformation,[],[f17])).
% 39.53/5.49  
% 39.53/5.49  fof(f30,plain,(
% 39.53/5.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 39.53/5.49    introduced(choice_axiom,[])).
% 39.53/5.49  
% 39.53/5.49  fof(f31,plain,(
% 39.53/5.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 39.53/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f30])).
% 39.53/5.49  
% 39.53/5.49  fof(f53,plain,(
% 39.53/5.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 39.53/5.49    inference(cnf_transformation,[],[f31])).
% 39.53/5.49  
% 39.53/5.49  fof(f7,axiom,(
% 39.53/5.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f56,plain,(
% 39.53/5.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f7])).
% 39.53/5.49  
% 39.53/5.49  fof(f1,axiom,(
% 39.53/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f41,plain,(
% 39.53/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f1])).
% 39.53/5.49  
% 39.53/5.49  fof(f15,conjecture,(
% 39.53/5.49    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f16,negated_conjecture,(
% 39.53/5.49    ~! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 39.53/5.49    inference(negated_conjecture,[],[f15])).
% 39.53/5.49  
% 39.53/5.49  fof(f23,plain,(
% 39.53/5.49    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 39.53/5.49    inference(ennf_transformation,[],[f16])).
% 39.53/5.49  
% 39.53/5.49  fof(f37,plain,(
% 39.53/5.49    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0))),
% 39.53/5.49    inference(nnf_transformation,[],[f23])).
% 39.53/5.49  
% 39.53/5.49  fof(f38,plain,(
% 39.53/5.49    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0))),
% 39.53/5.49    inference(flattening,[],[f37])).
% 39.53/5.49  
% 39.53/5.49  fof(f39,plain,(
% 39.53/5.49    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0)) => ((~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0))),
% 39.53/5.49    introduced(choice_axiom,[])).
% 39.53/5.49  
% 39.53/5.49  fof(f40,plain,(
% 39.53/5.49    (~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0) & ((r2_hidden(sK4,sK5) & r2_hidden(sK3,sK5)) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0)),
% 39.53/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f39])).
% 39.53/5.49  
% 39.53/5.49  fof(f72,plain,(
% 39.53/5.49    r2_hidden(sK4,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0),
% 39.53/5.49    inference(cnf_transformation,[],[f40])).
% 39.53/5.49  
% 39.53/5.49  fof(f5,axiom,(
% 39.53/5.49    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f54,plain,(
% 39.53/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f5])).
% 39.53/5.49  
% 39.53/5.49  fof(f10,axiom,(
% 39.53/5.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f66,plain,(
% 39.53/5.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f10])).
% 39.53/5.49  
% 39.53/5.49  fof(f76,plain,(
% 39.53/5.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 39.53/5.49    inference(definition_unfolding,[],[f66,f75])).
% 39.53/5.49  
% 39.53/5.49  fof(f87,plain,(
% 39.53/5.49    r2_hidden(sK4,sK5) | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0),
% 39.53/5.49    inference(definition_unfolding,[],[f72,f54,f76])).
% 39.53/5.49  
% 39.53/5.49  fof(f14,axiom,(
% 39.53/5.49    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2))),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f21,plain,(
% 39.53/5.49    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 39.53/5.49    inference(ennf_transformation,[],[f14])).
% 39.53/5.49  
% 39.53/5.49  fof(f22,plain,(
% 39.53/5.49    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 39.53/5.49    inference(flattening,[],[f21])).
% 39.53/5.49  
% 39.53/5.49  fof(f70,plain,(
% 39.53/5.49    ( ! [X2,X0,X1] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f22])).
% 39.53/5.49  
% 39.53/5.49  fof(f85,plain,(
% 39.53/5.49    ( ! [X2,X0,X1] : (k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) = k4_enumset1(X0,X0,X0,X0,X0,X2) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 39.53/5.49    inference(definition_unfolding,[],[f70,f76,f76])).
% 39.53/5.49  
% 39.53/5.49  fof(f3,axiom,(
% 39.53/5.49    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f18,plain,(
% 39.53/5.49    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 39.53/5.49    inference(ennf_transformation,[],[f3])).
% 39.53/5.49  
% 39.53/5.49  fof(f29,plain,(
% 39.53/5.49    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 39.53/5.49    inference(nnf_transformation,[],[f18])).
% 39.53/5.49  
% 39.53/5.49  fof(f50,plain,(
% 39.53/5.49    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 39.53/5.49    inference(cnf_transformation,[],[f29])).
% 39.53/5.49  
% 39.53/5.49  fof(f59,plain,(
% 39.53/5.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 39.53/5.49    inference(cnf_transformation,[],[f36])).
% 39.53/5.49  
% 39.53/5.49  fof(f83,plain,(
% 39.53/5.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 39.53/5.49    inference(definition_unfolding,[],[f59,f75])).
% 39.53/5.49  
% 39.53/5.49  fof(f96,plain,(
% 39.53/5.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X5,X5,X5,X5,X1,X2) != X3) )),
% 39.53/5.49    inference(equality_resolution,[],[f83])).
% 39.53/5.49  
% 39.53/5.49  fof(f97,plain,(
% 39.53/5.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k4_enumset1(X5,X5,X5,X5,X1,X2))) )),
% 39.53/5.49    inference(equality_resolution,[],[f96])).
% 39.53/5.49  
% 39.53/5.49  fof(f61,plain,(
% 39.53/5.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 39.53/5.49    inference(cnf_transformation,[],[f36])).
% 39.53/5.49  
% 39.53/5.49  fof(f81,plain,(
% 39.53/5.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 39.53/5.49    inference(definition_unfolding,[],[f61,f75])).
% 39.53/5.49  
% 39.53/5.49  fof(f92,plain,(
% 39.53/5.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k4_enumset1(X0,X0,X0,X0,X1,X5) != X3) )),
% 39.53/5.49    inference(equality_resolution,[],[f81])).
% 39.53/5.49  
% 39.53/5.49  fof(f93,plain,(
% 39.53/5.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X1,X5))) )),
% 39.53/5.49    inference(equality_resolution,[],[f92])).
% 39.53/5.49  
% 39.53/5.49  fof(f2,axiom,(
% 39.53/5.49    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f24,plain,(
% 39.53/5.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 39.53/5.49    inference(nnf_transformation,[],[f2])).
% 39.53/5.49  
% 39.53/5.49  fof(f25,plain,(
% 39.53/5.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 39.53/5.49    inference(flattening,[],[f24])).
% 39.53/5.49  
% 39.53/5.49  fof(f26,plain,(
% 39.53/5.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 39.53/5.49    inference(rectify,[],[f25])).
% 39.53/5.49  
% 39.53/5.49  fof(f27,plain,(
% 39.53/5.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 39.53/5.49    introduced(choice_axiom,[])).
% 39.53/5.49  
% 39.53/5.49  fof(f28,plain,(
% 39.53/5.49    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 39.53/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 39.53/5.49  
% 39.53/5.49  fof(f42,plain,(
% 39.53/5.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 39.53/5.49    inference(cnf_transformation,[],[f28])).
% 39.53/5.49  
% 39.53/5.49  fof(f91,plain,(
% 39.53/5.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 39.53/5.49    inference(equality_resolution,[],[f42])).
% 39.53/5.49  
% 39.53/5.49  fof(f71,plain,(
% 39.53/5.49    r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_xboole_0),
% 39.53/5.49    inference(cnf_transformation,[],[f40])).
% 39.53/5.49  
% 39.53/5.49  fof(f88,plain,(
% 39.53/5.49    r2_hidden(sK3,sK5) | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0),
% 39.53/5.49    inference(definition_unfolding,[],[f71,f54,f76])).
% 39.53/5.49  
% 39.53/5.49  fof(f73,plain,(
% 39.53/5.49    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0),
% 39.53/5.49    inference(cnf_transformation,[],[f40])).
% 39.53/5.49  
% 39.53/5.49  fof(f86,plain,(
% 39.53/5.49    ~r2_hidden(sK4,sK5) | ~r2_hidden(sK3,sK5) | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0),
% 39.53/5.49    inference(definition_unfolding,[],[f73,f54,f76])).
% 39.53/5.49  
% 39.53/5.49  fof(f60,plain,(
% 39.53/5.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 39.53/5.49    inference(cnf_transformation,[],[f36])).
% 39.53/5.49  
% 39.53/5.49  fof(f82,plain,(
% 39.53/5.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k4_enumset1(X0,X0,X0,X0,X1,X2) != X3) )),
% 39.53/5.49    inference(definition_unfolding,[],[f60,f75])).
% 39.53/5.49  
% 39.53/5.49  fof(f94,plain,(
% 39.53/5.49    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k4_enumset1(X0,X0,X0,X0,X5,X2) != X3) )),
% 39.53/5.49    inference(equality_resolution,[],[f82])).
% 39.53/5.49  
% 39.53/5.49  fof(f95,plain,(
% 39.53/5.49    ( ! [X2,X0,X5] : (r2_hidden(X5,k4_enumset1(X0,X0,X0,X0,X5,X2))) )),
% 39.53/5.49    inference(equality_resolution,[],[f94])).
% 39.53/5.49  
% 39.53/5.49  fof(f43,plain,(
% 39.53/5.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 39.53/5.49    inference(cnf_transformation,[],[f28])).
% 39.53/5.49  
% 39.53/5.49  fof(f90,plain,(
% 39.53/5.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 39.53/5.49    inference(equality_resolution,[],[f43])).
% 39.53/5.49  
% 39.53/5.49  fof(f8,axiom,(
% 39.53/5.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 39.53/5.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.53/5.49  
% 39.53/5.49  fof(f57,plain,(
% 39.53/5.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 39.53/5.49    inference(cnf_transformation,[],[f8])).
% 39.53/5.49  
% 39.53/5.49  cnf(c_19,plain,
% 39.53/5.49      ( r2_hidden(sK2(X0,X1,X2,X3),X3)
% 39.53/5.49      | k4_enumset1(X0,X0,X0,X0,X1,X2) = X3
% 39.53/5.49      | sK2(X0,X1,X2,X3) = X2
% 39.53/5.49      | sK2(X0,X1,X2,X3) = X1
% 39.53/5.49      | sK2(X0,X1,X2,X3) = X0 ),
% 39.53/5.49      inference(cnf_transformation,[],[f80]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_606,plain,
% 39.53/5.49      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = X3
% 39.53/5.49      | sK2(X0,X1,X2,X3) = X2
% 39.53/5.49      | sK2(X0,X1,X2,X3) = X1
% 39.53/5.49      | sK2(X0,X1,X2,X3) = X0
% 39.53/5.49      | r2_hidden(sK2(X0,X1,X2,X3),X3) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_13,plain,
% 39.53/5.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 39.53/5.49      inference(cnf_transformation,[],[f55]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_11,plain,
% 39.53/5.49      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 39.53/5.49      inference(cnf_transformation,[],[f53]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_612,plain,
% 39.53/5.49      ( r1_xboole_0(X0,X1) != iProver_top
% 39.53/5.49      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_4051,plain,
% 39.53/5.49      ( r1_xboole_0(X0,k1_xboole_0) != iProver_top
% 39.53/5.49      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_13,c_612]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_14,plain,
% 39.53/5.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 39.53/5.49      inference(cnf_transformation,[],[f56]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_51,plain,
% 39.53/5.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_4073,plain,
% 39.53/5.49      ( r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 39.53/5.49      inference(global_propositional_subsumption,[status(thm)],[c_4051,c_51]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_4074,plain,
% 39.53/5.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 39.53/5.49      inference(renaming,[status(thm)],[c_4073]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_4993,plain,
% 39.53/5.49      ( k4_enumset1(X0,X0,X0,X0,X1,X2) = k1_xboole_0
% 39.53/5.49      | sK2(X0,X1,X2,k1_xboole_0) = X2
% 39.53/5.49      | sK2(X0,X1,X2,k1_xboole_0) = X1
% 39.53/5.49      | sK2(X0,X1,X2,k1_xboole_0) = X0 ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_606,c_4074]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_0,plain,
% 39.53/5.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 39.53/5.49      inference(cnf_transformation,[],[f41]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_26,negated_conjecture,
% 39.53/5.49      ( r2_hidden(sK4,sK5)
% 39.53/5.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
% 39.53/5.49      inference(cnf_transformation,[],[f87]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_599,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
% 39.53/5.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_1044,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 39.53/5.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_0,c_599]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_24,plain,
% 39.53/5.49      ( ~ r2_hidden(X0,X1)
% 39.53/5.49      | ~ r2_hidden(X2,X1)
% 39.53/5.49      | k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) = k4_enumset1(X0,X0,X0,X0,X0,X2) ),
% 39.53/5.49      inference(cnf_transformation,[],[f85]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_601,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) = k4_enumset1(X0,X0,X0,X0,X0,X1)
% 39.53/5.49      | r2_hidden(X0,X2) != iProver_top
% 39.53/5.49      | r2_hidden(X1,X2) != iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_1305,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,X0),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,X0)
% 39.53/5.49      | r2_hidden(X0,sK5) != iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_1044,c_601]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_1458,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_1044,c_1305]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_8,plain,
% 39.53/5.49      ( ~ r2_hidden(X0,X1)
% 39.53/5.49      | r2_hidden(X0,X2)
% 39.53/5.49      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 39.53/5.49      inference(cnf_transformation,[],[f50]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_615,plain,
% 39.53/5.49      ( r2_hidden(X0,X1) != iProver_top
% 39.53/5.49      | r2_hidden(X0,X2) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6128,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_1458,c_615]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7792,plain,
% 39.53/5.49      ( r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) ),
% 39.53/5.49      inference(global_propositional_subsumption,[status(thm)],[c_6128,c_4074]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7793,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
% 39.53/5.49      inference(renaming,[status(thm)],[c_7792]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_120238,plain,
% 39.53/5.49      ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
% 39.53/5.49      | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k1_xboole_0)) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_4993,c_7793]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_120828,plain,
% 39.53/5.49      ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
% 39.53/5.49      | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_120238,c_13]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_22,plain,
% 39.53/5.49      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) ),
% 39.53/5.49      inference(cnf_transformation,[],[f97]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_37,plain,
% 39.53/5.49      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_39,plain,
% 39.53/5.49      ( r2_hidden(sK3,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = iProver_top ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_37]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_20,plain,
% 39.53/5.49      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) ),
% 39.53/5.49      inference(cnf_transformation,[],[f93]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_605,plain,
% 39.53/5.49      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6,plain,
% 39.53/5.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 39.53/5.49      inference(cnf_transformation,[],[f91]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_617,plain,
% 39.53/5.49      ( r2_hidden(X0,X1) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7803,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,sK5) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_7793,c_617]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_37248,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4)
% 39.53/5.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_605,c_7803]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_27,negated_conjecture,
% 39.53/5.49      ( r2_hidden(sK3,sK5)
% 39.53/5.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0 ),
% 39.53/5.49      inference(cnf_transformation,[],[f88]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_598,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = k1_xboole_0
% 39.53/5.49      | r2_hidden(sK3,sK5) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_1045,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 39.53/5.49      | r2_hidden(sK3,sK5) = iProver_top ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_0,c_598]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_1450,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,X0)
% 39.53/5.49      | r2_hidden(X0,sK5) != iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_1045,c_601]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_2059,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_1045,c_1450]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6125,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_2059,c_615]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6596,plain,
% 39.53/5.49      ( r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) ),
% 39.53/5.49      inference(global_propositional_subsumption,[status(thm)],[c_6125,c_4074]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6597,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
% 39.53/5.49      inference(renaming,[status(thm)],[c_6596]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_120241,plain,
% 39.53/5.49      ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
% 39.53/5.49      | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k1_xboole_0)) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_4993,c_6597]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_120795,plain,
% 39.53/5.49      ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
% 39.53/5.49      | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_120241,c_13]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_25,negated_conjecture,
% 39.53/5.49      ( ~ r2_hidden(sK3,sK5)
% 39.53/5.49      | ~ r2_hidden(sK4,sK5)
% 39.53/5.49      | k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
% 39.53/5.49      inference(cnf_transformation,[],[f86]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_600,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != k1_xboole_0
% 39.53/5.49      | r2_hidden(sK3,sK5) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,sK5) != iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_1046,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) != k1_xboole_0
% 39.53/5.49      | r2_hidden(sK3,sK5) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,sK5) != iProver_top ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_0,c_600]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_3714,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
% 39.53/5.49      | r2_hidden(sK3,sK5) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,sK5) != iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_2059,c_1046]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6607,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,sK5) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_6597,c_617]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_36055,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
% 39.53/5.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_605,c_6607]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_21,plain,
% 39.53/5.49      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X0,X2)) ),
% 39.53/5.49      inference(cnf_transformation,[],[f95]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_604,plain,
% 39.53/5.49      ( r2_hidden(X0,k4_enumset1(X1,X1,X1,X1,X0,X2)) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_36056,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)
% 39.53/5.49      | r2_hidden(sK3,sK5) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_604,c_6607]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_121658,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3) ),
% 39.53/5.49      inference(global_propositional_subsumption,
% 39.53/5.49                [status(thm)],
% 39.53/5.49                [c_120795,c_3714,c_36055,c_36056]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_5,plain,
% 39.53/5.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 39.53/5.49      inference(cnf_transformation,[],[f90]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_618,plain,
% 39.53/5.49      ( r2_hidden(X0,X1) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_121700,plain,
% 39.53/5.49      ( r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,sK5) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_121658,c_618]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_122262,plain,
% 39.53/5.49      ( r2_hidden(sK3,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != iProver_top
% 39.53/5.49      | r2_hidden(sK3,sK5) = iProver_top ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_121700]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_2058,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = k1_xboole_0
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_1044,c_1450]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6126,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_2058,c_615]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6649,plain,
% 39.53/5.49      ( r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) ),
% 39.53/5.49      inference(global_propositional_subsumption,[status(thm)],[c_6126,c_4074]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6650,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))) = iProver_top ),
% 39.53/5.49      inference(renaming,[status(thm)],[c_6649]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_120240,plain,
% 39.53/5.49      ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
% 39.53/5.49      | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k3_xboole_0(sK5,k1_xboole_0)) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_4993,c_6650]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_120806,plain,
% 39.53/5.49      ( sK2(sK3,sK3,sK4,k1_xboole_0) = sK3
% 39.53/5.49      | sK2(sK3,sK3,sK4,k1_xboole_0) = sK4
% 39.53/5.49      | k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_120240,c_13]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_6660,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
% 39.53/5.49      | r2_hidden(X0,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(X0,sK5) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_6650,c_617]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_36676,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)
% 39.53/5.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_605,c_6660]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_122859,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) ),
% 39.53/5.49      inference(global_propositional_subsumption,
% 39.53/5.49                [status(thm)],
% 39.53/5.49                [c_120806,c_39,c_1046,c_2058,c_36676,c_122262]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_122995,plain,
% 39.53/5.49      ( k3_xboole_0(sK5,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) = k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4) ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_122859,c_0]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_123892,plain,
% 39.53/5.49      ( k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != k1_xboole_0
% 39.53/5.49      | r2_hidden(sK3,sK5) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,sK5) != iProver_top ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_122995,c_1046]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_15,plain,
% 39.53/5.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.53/5.49      inference(cnf_transformation,[],[f57]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_123896,plain,
% 39.53/5.49      ( k1_xboole_0 != k1_xboole_0
% 39.53/5.49      | r2_hidden(sK3,sK5) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,sK5) != iProver_top ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_123892,c_15]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_123897,plain,
% 39.53/5.49      ( r2_hidden(sK3,sK5) != iProver_top | r2_hidden(sK4,sK5) != iProver_top ),
% 39.53/5.49      inference(equality_resolution_simp,[status(thm)],[c_123896]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_126268,plain,
% 39.53/5.49      ( k3_xboole_0(k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4),sK5) = k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) ),
% 39.53/5.49      inference(global_propositional_subsumption,
% 39.53/5.49                [status(thm)],
% 39.53/5.49                [c_120828,c_39,c_37248,c_122262,c_123897]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_126273,plain,
% 39.53/5.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = k3_xboole_0(k1_xboole_0,sK5)
% 39.53/5.49      | sK2(sK4,sK4,sK4,k1_xboole_0) = sK4 ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_4993,c_126268]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_1064,plain,
% 39.53/5.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_126416,plain,
% 39.53/5.49      ( k4_enumset1(sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 39.53/5.49      | sK2(sK4,sK4,sK4,k1_xboole_0) = sK4 ),
% 39.53/5.49      inference(demodulation,[status(thm)],[c_126273,c_1064]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_603,plain,
% 39.53/5.49      ( r2_hidden(X0,k4_enumset1(X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_146864,plain,
% 39.53/5.49      ( sK2(sK4,sK4,sK4,k1_xboole_0) = sK4
% 39.53/5.49      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(superposition,[status(thm)],[c_126416,c_603]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_3197,plain,
% 39.53/5.49      ( ~ r2_hidden(sK4,k3_xboole_0(X0,sK5)) | r2_hidden(sK4,sK5) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_5]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7400,plain,
% 39.53/5.49      ( ~ r2_hidden(sK4,k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,sK4),sK5))
% 39.53/5.49      | r2_hidden(sK4,sK5) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_3197]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7402,plain,
% 39.53/5.49      ( r2_hidden(sK4,k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,sK4),sK5)) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_7400]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7404,plain,
% 39.53/5.49      ( r2_hidden(sK4,k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_7402]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_224,plain,( X0 = X0 ),theory(equality) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7886,plain,
% 39.53/5.49      ( sK4 = sK4 ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_224]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_8119,plain,
% 39.53/5.49      ( r2_hidden(sK4,k4_enumset1(X0,X0,X0,X0,X1,sK4)) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_20]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_8120,plain,
% 39.53/5.49      ( r2_hidden(sK4,k4_enumset1(X0,X0,X0,X0,X1,sK4)) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_8119]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_8122,plain,
% 39.53/5.49      ( r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) = iProver_top ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_8120]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_225,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_3386,plain,
% 39.53/5.49      ( X0 != X1 | X1 = X0 ),
% 39.53/5.49      inference(resolution,[status(thm)],[c_225,c_224]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_12308,plain,
% 39.53/5.49      ( r2_hidden(sK4,sK5)
% 39.53/5.49      | k1_xboole_0 = k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
% 39.53/5.49      inference(resolution,[status(thm)],[c_3386,c_26]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_12311,plain,
% 39.53/5.49      ( k1_xboole_0 = k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5))
% 39.53/5.49      | r2_hidden(sK4,sK5) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_12308]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_846,plain,
% 39.53/5.49      ( r2_hidden(X0,X1)
% 39.53/5.49      | ~ r2_hidden(X0,k4_enumset1(X2,X2,X2,X2,X3,X0))
% 39.53/5.49      | r2_hidden(X0,k5_xboole_0(k4_enumset1(X2,X2,X2,X2,X3,X0),X1)) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_8]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7300,plain,
% 39.53/5.49      ( ~ r2_hidden(sK4,k4_enumset1(X0,X0,X0,X0,X1,sK4))
% 39.53/5.49      | r2_hidden(sK4,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X1,sK4),k3_xboole_0(X2,sK5)))
% 39.53/5.49      | r2_hidden(sK4,k3_xboole_0(X2,sK5)) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_846]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_51030,plain,
% 39.53/5.49      ( ~ r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4))
% 39.53/5.49      | r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)))
% 39.53/5.49      | r2_hidden(sK4,k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_7300]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_51031,plain,
% 39.53/5.49      ( r2_hidden(sK4,k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4)) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5))) = iProver_top
% 39.53/5.49      | r2_hidden(sK4,k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_51030]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_227,plain,
% 39.53/5.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.53/5.49      theory(equality) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_932,plain,
% 39.53/5.49      ( r2_hidden(X0,X1)
% 39.53/5.49      | ~ r2_hidden(X2,k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X4,X2),X5))
% 39.53/5.49      | X0 != X2
% 39.53/5.49      | X1 != k5_xboole_0(k4_enumset1(X3,X3,X3,X3,X4,X2),X5) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_227]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_7959,plain,
% 39.53/5.49      ( ~ r2_hidden(X0,k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X0),X3))
% 39.53/5.49      | r2_hidden(X4,k1_xboole_0)
% 39.53/5.49      | X4 != X0
% 39.53/5.49      | k1_xboole_0 != k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X2,X0),X3) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_932]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_31683,plain,
% 39.53/5.49      ( r2_hidden(X0,k1_xboole_0)
% 39.53/5.49      | ~ r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)))
% 39.53/5.49      | X0 != sK4
% 39.53/5.49      | k1_xboole_0 != k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_7959]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_86636,plain,
% 39.53/5.49      ( ~ r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)))
% 39.53/5.49      | r2_hidden(sK4,k1_xboole_0)
% 39.53/5.49      | sK4 != sK4
% 39.53/5.49      | k1_xboole_0 != k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5)) ),
% 39.53/5.49      inference(instantiation,[status(thm)],[c_31683]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_86637,plain,
% 39.53/5.49      ( sK4 != sK4
% 39.53/5.49      | k1_xboole_0 != k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5))
% 39.53/5.49      | r2_hidden(sK4,k5_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),k3_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK4),sK5))) != iProver_top
% 39.53/5.49      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(predicate_to_equality,[status(thm)],[c_86636]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_146988,plain,
% 39.53/5.49      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 39.53/5.49      inference(global_propositional_subsumption,
% 39.53/5.49                [status(thm)],
% 39.53/5.49                [c_146864,c_39,c_7404,c_7886,c_8122,c_12311,c_51031,c_86637,
% 39.53/5.49                 c_122262,c_123897]) ).
% 39.53/5.49  
% 39.53/5.49  cnf(c_146993,plain,
% 39.53/5.49      ( $false ),
% 39.53/5.49      inference(forward_subsumption_resolution,[status(thm)],[c_146988,c_4074]) ).
% 39.53/5.49  
% 39.53/5.49  
% 39.53/5.49  % SZS output end CNFRefutation for theBenchmark.p
% 39.53/5.49  
% 39.53/5.49  ------                               Statistics
% 39.53/5.49  
% 39.53/5.49  ------ Selected
% 39.53/5.49  
% 39.53/5.49  total_time:                             4.718
% 39.53/5.49  
%------------------------------------------------------------------------------
