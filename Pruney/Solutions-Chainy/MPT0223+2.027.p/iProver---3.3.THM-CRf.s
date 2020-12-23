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
% DateTime   : Thu Dec  3 11:29:48 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  119 (1615 expanded)
%              Number of clauses        :   46 ( 281 expanded)
%              Number of leaves         :   23 ( 513 expanded)
%              Depth                    :   21
%              Number of atoms          :  305 (2159 expanded)
%              Number of equality atoms :  214 (1785 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f31])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f28,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f42,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK4 != sK5
      & k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( sK4 != sK5
    & k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f42])).

fof(f76,plain,(
    k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f101,plain,(
    k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f76,f79,f79,f79])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f86,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f48,f54])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)),k3_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f54,f71,f79])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f50,f54,f54,f48])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

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
    inference(nnf_transformation,[],[f27])).

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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f102,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f91])).

fof(f103,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f102])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f63,f79])).

fof(f111,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f64,f79])).

fof(f109,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f97])).

fof(f110,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f109])).

fof(f77,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_574,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_25,negated_conjecture,
    ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_206,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X2
    | k5_xboole_0(X4,k3_xboole_0(X4,X3)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_207,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_560,plain,
    ( r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_1021,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_560])).

cnf(c_4477,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1021])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_599,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_5])).

cnf(c_4731,plain,
    ( r2_hidden(X0,k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4477,c_599])).

cnf(c_5212,plain,
    ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_574,c_4731])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)),k3_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1528,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4))) ),
    inference(superposition,[status(thm)],[c_25,c_6])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1534,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_1528,c_8,c_599])).

cnf(c_2364,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0)) = k2_enumset1(sK5,sK5,sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_0,c_1534])).

cnf(c_8407,plain,
    ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0) = k2_enumset1(sK5,sK5,sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_5212,c_2364])).

cnf(c_21244,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK4) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_8407,c_8])).

cnf(c_22304,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK4),k2_enumset1(X0,X0,X0,X0)),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK4),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(sK5,sK5,sK5,X0) ),
    inference(superposition,[status(thm)],[c_21244,c_0])).

cnf(c_22322,plain,
    ( k2_enumset1(sK5,sK5,sK4,X0) = k2_enumset1(sK5,sK5,sK5,X0) ),
    inference(demodulation,[status(thm)],[c_22304,c_0])).

cnf(c_22699,plain,
    ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK4),k2_enumset1(X0,X0,X0,X0)),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK4),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(sK5,sK5,sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_22304,c_22322])).

cnf(c_22700,plain,
    ( k2_enumset1(sK5,sK4,sK4,X0) = k2_enumset1(sK5,sK5,sK4,X0) ),
    inference(demodulation,[status(thm)],[c_22699,c_0,c_22322])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_569,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_22782,plain,
    ( r2_hidden(X0,k2_enumset1(sK5,sK4,sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22700,c_569])).

cnf(c_22837,plain,
    ( r2_hidden(sK4,k2_enumset1(sK5,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_22782])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_562,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22313,plain,
    ( sK5 = X0
    | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21244,c_562])).

cnf(c_22690,plain,
    ( sK5 = X0
    | r2_hidden(X0,k2_enumset1(sK5,sK5,sK4,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22313,c_22322])).

cnf(c_22702,plain,
    ( sK5 = X0
    | r2_hidden(X0,k2_enumset1(sK5,sK4,sK4,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22700,c_22690])).

cnf(c_22717,plain,
    ( sK5 = sK4
    | r2_hidden(sK4,k2_enumset1(sK5,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22702])).

cnf(c_322,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_699,plain,
    ( sK5 != X0
    | sK4 != X0
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_700,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_32,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_29,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_24,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22837,c_22717,c_700,c_32,c_29,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.81/1.46  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.46  
% 7.81/1.46  ------  iProver source info
% 7.81/1.46  
% 7.81/1.46  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.46  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.46  git: non_committed_changes: false
% 7.81/1.46  git: last_make_outside_of_git: false
% 7.81/1.46  
% 7.81/1.46  ------ 
% 7.81/1.46  
% 7.81/1.46  ------ Input Options
% 7.81/1.46  
% 7.81/1.46  --out_options                           all
% 7.81/1.46  --tptp_safe_out                         true
% 7.81/1.46  --problem_path                          ""
% 7.81/1.46  --include_path                          ""
% 7.81/1.46  --clausifier                            res/vclausify_rel
% 7.81/1.46  --clausifier_options                    --mode clausify
% 7.81/1.46  --stdin                                 false
% 7.81/1.46  --stats_out                             all
% 7.81/1.46  
% 7.81/1.46  ------ General Options
% 7.81/1.46  
% 7.81/1.46  --fof                                   false
% 7.81/1.46  --time_out_real                         305.
% 7.81/1.46  --time_out_virtual                      -1.
% 7.81/1.46  --symbol_type_check                     false
% 7.81/1.46  --clausify_out                          false
% 7.81/1.46  --sig_cnt_out                           false
% 7.81/1.46  --trig_cnt_out                          false
% 7.81/1.46  --trig_cnt_out_tolerance                1.
% 7.81/1.46  --trig_cnt_out_sk_spl                   false
% 7.81/1.46  --abstr_cl_out                          false
% 7.81/1.46  
% 7.81/1.46  ------ Global Options
% 7.81/1.46  
% 7.81/1.46  --schedule                              default
% 7.81/1.46  --add_important_lit                     false
% 7.81/1.46  --prop_solver_per_cl                    1000
% 7.81/1.46  --min_unsat_core                        false
% 7.81/1.46  --soft_assumptions                      false
% 7.81/1.46  --soft_lemma_size                       3
% 7.81/1.46  --prop_impl_unit_size                   0
% 7.81/1.46  --prop_impl_unit                        []
% 7.81/1.46  --share_sel_clauses                     true
% 7.81/1.46  --reset_solvers                         false
% 7.81/1.46  --bc_imp_inh                            [conj_cone]
% 7.81/1.46  --conj_cone_tolerance                   3.
% 7.81/1.46  --extra_neg_conj                        none
% 7.81/1.46  --large_theory_mode                     true
% 7.81/1.46  --prolific_symb_bound                   200
% 7.81/1.46  --lt_threshold                          2000
% 7.81/1.46  --clause_weak_htbl                      true
% 7.81/1.46  --gc_record_bc_elim                     false
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing Options
% 7.81/1.46  
% 7.81/1.46  --preprocessing_flag                    true
% 7.81/1.46  --time_out_prep_mult                    0.1
% 7.81/1.46  --splitting_mode                        input
% 7.81/1.46  --splitting_grd                         true
% 7.81/1.46  --splitting_cvd                         false
% 7.81/1.46  --splitting_cvd_svl                     false
% 7.81/1.46  --splitting_nvd                         32
% 7.81/1.46  --sub_typing                            true
% 7.81/1.46  --prep_gs_sim                           true
% 7.81/1.46  --prep_unflatten                        true
% 7.81/1.46  --prep_res_sim                          true
% 7.81/1.46  --prep_upred                            true
% 7.81/1.46  --prep_sem_filter                       exhaustive
% 7.81/1.46  --prep_sem_filter_out                   false
% 7.81/1.46  --pred_elim                             true
% 7.81/1.46  --res_sim_input                         true
% 7.81/1.46  --eq_ax_congr_red                       true
% 7.81/1.46  --pure_diseq_elim                       true
% 7.81/1.46  --brand_transform                       false
% 7.81/1.46  --non_eq_to_eq                          false
% 7.81/1.46  --prep_def_merge                        true
% 7.81/1.46  --prep_def_merge_prop_impl              false
% 7.81/1.46  --prep_def_merge_mbd                    true
% 7.81/1.46  --prep_def_merge_tr_red                 false
% 7.81/1.46  --prep_def_merge_tr_cl                  false
% 7.81/1.46  --smt_preprocessing                     true
% 7.81/1.46  --smt_ac_axioms                         fast
% 7.81/1.46  --preprocessed_out                      false
% 7.81/1.46  --preprocessed_stats                    false
% 7.81/1.46  
% 7.81/1.46  ------ Abstraction refinement Options
% 7.81/1.46  
% 7.81/1.46  --abstr_ref                             []
% 7.81/1.46  --abstr_ref_prep                        false
% 7.81/1.46  --abstr_ref_until_sat                   false
% 7.81/1.46  --abstr_ref_sig_restrict                funpre
% 7.81/1.46  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.46  --abstr_ref_under                       []
% 7.81/1.46  
% 7.81/1.46  ------ SAT Options
% 7.81/1.46  
% 7.81/1.46  --sat_mode                              false
% 7.81/1.46  --sat_fm_restart_options                ""
% 7.81/1.46  --sat_gr_def                            false
% 7.81/1.46  --sat_epr_types                         true
% 7.81/1.46  --sat_non_cyclic_types                  false
% 7.81/1.46  --sat_finite_models                     false
% 7.81/1.46  --sat_fm_lemmas                         false
% 7.81/1.46  --sat_fm_prep                           false
% 7.81/1.46  --sat_fm_uc_incr                        true
% 7.81/1.46  --sat_out_model                         small
% 7.81/1.46  --sat_out_clauses                       false
% 7.81/1.46  
% 7.81/1.46  ------ QBF Options
% 7.81/1.46  
% 7.81/1.46  --qbf_mode                              false
% 7.81/1.46  --qbf_elim_univ                         false
% 7.81/1.46  --qbf_dom_inst                          none
% 7.81/1.46  --qbf_dom_pre_inst                      false
% 7.81/1.46  --qbf_sk_in                             false
% 7.81/1.46  --qbf_pred_elim                         true
% 7.81/1.46  --qbf_split                             512
% 7.81/1.46  
% 7.81/1.46  ------ BMC1 Options
% 7.81/1.46  
% 7.81/1.46  --bmc1_incremental                      false
% 7.81/1.46  --bmc1_axioms                           reachable_all
% 7.81/1.46  --bmc1_min_bound                        0
% 7.81/1.46  --bmc1_max_bound                        -1
% 7.81/1.46  --bmc1_max_bound_default                -1
% 7.81/1.46  --bmc1_symbol_reachability              true
% 7.81/1.46  --bmc1_property_lemmas                  false
% 7.81/1.46  --bmc1_k_induction                      false
% 7.81/1.46  --bmc1_non_equiv_states                 false
% 7.81/1.46  --bmc1_deadlock                         false
% 7.81/1.46  --bmc1_ucm                              false
% 7.81/1.46  --bmc1_add_unsat_core                   none
% 7.81/1.46  --bmc1_unsat_core_children              false
% 7.81/1.46  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.46  --bmc1_out_stat                         full
% 7.81/1.46  --bmc1_ground_init                      false
% 7.81/1.46  --bmc1_pre_inst_next_state              false
% 7.81/1.46  --bmc1_pre_inst_state                   false
% 7.81/1.46  --bmc1_pre_inst_reach_state             false
% 7.81/1.46  --bmc1_out_unsat_core                   false
% 7.81/1.46  --bmc1_aig_witness_out                  false
% 7.81/1.46  --bmc1_verbose                          false
% 7.81/1.46  --bmc1_dump_clauses_tptp                false
% 7.81/1.46  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.46  --bmc1_dump_file                        -
% 7.81/1.46  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.46  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.46  --bmc1_ucm_extend_mode                  1
% 7.81/1.46  --bmc1_ucm_init_mode                    2
% 7.81/1.46  --bmc1_ucm_cone_mode                    none
% 7.81/1.46  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.46  --bmc1_ucm_relax_model                  4
% 7.81/1.46  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.46  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.46  --bmc1_ucm_layered_model                none
% 7.81/1.46  --bmc1_ucm_max_lemma_size               10
% 7.81/1.46  
% 7.81/1.46  ------ AIG Options
% 7.81/1.46  
% 7.81/1.46  --aig_mode                              false
% 7.81/1.46  
% 7.81/1.46  ------ Instantiation Options
% 7.81/1.46  
% 7.81/1.46  --instantiation_flag                    true
% 7.81/1.46  --inst_sos_flag                         false
% 7.81/1.46  --inst_sos_phase                        true
% 7.81/1.46  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.46  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.46  --inst_lit_sel_side                     num_symb
% 7.81/1.46  --inst_solver_per_active                1400
% 7.81/1.46  --inst_solver_calls_frac                1.
% 7.81/1.46  --inst_passive_queue_type               priority_queues
% 7.81/1.46  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.46  --inst_passive_queues_freq              [25;2]
% 7.81/1.46  --inst_dismatching                      true
% 7.81/1.46  --inst_eager_unprocessed_to_passive     true
% 7.81/1.46  --inst_prop_sim_given                   true
% 7.81/1.46  --inst_prop_sim_new                     false
% 7.81/1.46  --inst_subs_new                         false
% 7.81/1.46  --inst_eq_res_simp                      false
% 7.81/1.46  --inst_subs_given                       false
% 7.81/1.46  --inst_orphan_elimination               true
% 7.81/1.46  --inst_learning_loop_flag               true
% 7.81/1.46  --inst_learning_start                   3000
% 7.81/1.46  --inst_learning_factor                  2
% 7.81/1.46  --inst_start_prop_sim_after_learn       3
% 7.81/1.46  --inst_sel_renew                        solver
% 7.81/1.46  --inst_lit_activity_flag                true
% 7.81/1.46  --inst_restr_to_given                   false
% 7.81/1.46  --inst_activity_threshold               500
% 7.81/1.46  --inst_out_proof                        true
% 7.81/1.46  
% 7.81/1.46  ------ Resolution Options
% 7.81/1.46  
% 7.81/1.46  --resolution_flag                       true
% 7.81/1.46  --res_lit_sel                           adaptive
% 7.81/1.46  --res_lit_sel_side                      none
% 7.81/1.46  --res_ordering                          kbo
% 7.81/1.46  --res_to_prop_solver                    active
% 7.81/1.46  --res_prop_simpl_new                    false
% 7.81/1.46  --res_prop_simpl_given                  true
% 7.81/1.46  --res_passive_queue_type                priority_queues
% 7.81/1.46  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.46  --res_passive_queues_freq               [15;5]
% 7.81/1.46  --res_forward_subs                      full
% 7.81/1.46  --res_backward_subs                     full
% 7.81/1.46  --res_forward_subs_resolution           true
% 7.81/1.46  --res_backward_subs_resolution          true
% 7.81/1.46  --res_orphan_elimination                true
% 7.81/1.46  --res_time_limit                        2.
% 7.81/1.46  --res_out_proof                         true
% 7.81/1.46  
% 7.81/1.46  ------ Superposition Options
% 7.81/1.46  
% 7.81/1.46  --superposition_flag                    true
% 7.81/1.46  --sup_passive_queue_type                priority_queues
% 7.81/1.46  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.46  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.46  --demod_completeness_check              fast
% 7.81/1.46  --demod_use_ground                      true
% 7.81/1.46  --sup_to_prop_solver                    passive
% 7.81/1.46  --sup_prop_simpl_new                    true
% 7.81/1.46  --sup_prop_simpl_given                  true
% 7.81/1.46  --sup_fun_splitting                     false
% 7.81/1.46  --sup_smt_interval                      50000
% 7.81/1.46  
% 7.81/1.46  ------ Superposition Simplification Setup
% 7.81/1.46  
% 7.81/1.46  --sup_indices_passive                   []
% 7.81/1.46  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.46  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.46  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.46  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.46  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.46  --sup_full_bw                           [BwDemod]
% 7.81/1.46  --sup_immed_triv                        [TrivRules]
% 7.81/1.46  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.46  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.46  --sup_immed_bw_main                     []
% 7.81/1.46  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.46  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.46  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.46  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.46  
% 7.81/1.46  ------ Combination Options
% 7.81/1.46  
% 7.81/1.46  --comb_res_mult                         3
% 7.81/1.46  --comb_sup_mult                         2
% 7.81/1.46  --comb_inst_mult                        10
% 7.81/1.46  
% 7.81/1.46  ------ Debug Options
% 7.81/1.46  
% 7.81/1.46  --dbg_backtrace                         false
% 7.81/1.46  --dbg_dump_prop_clauses                 false
% 7.81/1.46  --dbg_dump_prop_clauses_file            -
% 7.81/1.46  --dbg_out_stat                          false
% 7.81/1.46  ------ Parsing...
% 7.81/1.46  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.46  ------ Proving...
% 7.81/1.46  ------ Problem Properties 
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  clauses                                 25
% 7.81/1.46  conjectures                             2
% 7.81/1.46  EPR                                     1
% 7.81/1.46  Horn                                    21
% 7.81/1.46  unary                                   15
% 7.81/1.46  binary                                  3
% 7.81/1.46  lits                                    45
% 7.81/1.46  lits eq                                 29
% 7.81/1.46  fd_pure                                 0
% 7.81/1.46  fd_pseudo                               0
% 7.81/1.46  fd_cond                                 1
% 7.81/1.46  fd_pseudo_cond                          6
% 7.81/1.46  AC symbols                              0
% 7.81/1.46  
% 7.81/1.46  ------ Schedule dynamic 5 is on 
% 7.81/1.46  
% 7.81/1.46  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  ------ 
% 7.81/1.46  Current options:
% 7.81/1.46  ------ 
% 7.81/1.46  
% 7.81/1.46  ------ Input Options
% 7.81/1.46  
% 7.81/1.46  --out_options                           all
% 7.81/1.46  --tptp_safe_out                         true
% 7.81/1.46  --problem_path                          ""
% 7.81/1.46  --include_path                          ""
% 7.81/1.46  --clausifier                            res/vclausify_rel
% 7.81/1.46  --clausifier_options                    --mode clausify
% 7.81/1.46  --stdin                                 false
% 7.81/1.46  --stats_out                             all
% 7.81/1.46  
% 7.81/1.46  ------ General Options
% 7.81/1.46  
% 7.81/1.46  --fof                                   false
% 7.81/1.46  --time_out_real                         305.
% 7.81/1.46  --time_out_virtual                      -1.
% 7.81/1.46  --symbol_type_check                     false
% 7.81/1.46  --clausify_out                          false
% 7.81/1.46  --sig_cnt_out                           false
% 7.81/1.46  --trig_cnt_out                          false
% 7.81/1.46  --trig_cnt_out_tolerance                1.
% 7.81/1.46  --trig_cnt_out_sk_spl                   false
% 7.81/1.46  --abstr_cl_out                          false
% 7.81/1.46  
% 7.81/1.46  ------ Global Options
% 7.81/1.46  
% 7.81/1.46  --schedule                              default
% 7.81/1.46  --add_important_lit                     false
% 7.81/1.46  --prop_solver_per_cl                    1000
% 7.81/1.46  --min_unsat_core                        false
% 7.81/1.46  --soft_assumptions                      false
% 7.81/1.46  --soft_lemma_size                       3
% 7.81/1.46  --prop_impl_unit_size                   0
% 7.81/1.46  --prop_impl_unit                        []
% 7.81/1.46  --share_sel_clauses                     true
% 7.81/1.46  --reset_solvers                         false
% 7.81/1.46  --bc_imp_inh                            [conj_cone]
% 7.81/1.46  --conj_cone_tolerance                   3.
% 7.81/1.46  --extra_neg_conj                        none
% 7.81/1.46  --large_theory_mode                     true
% 7.81/1.46  --prolific_symb_bound                   200
% 7.81/1.46  --lt_threshold                          2000
% 7.81/1.46  --clause_weak_htbl                      true
% 7.81/1.46  --gc_record_bc_elim                     false
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing Options
% 7.81/1.46  
% 7.81/1.46  --preprocessing_flag                    true
% 7.81/1.46  --time_out_prep_mult                    0.1
% 7.81/1.46  --splitting_mode                        input
% 7.81/1.46  --splitting_grd                         true
% 7.81/1.46  --splitting_cvd                         false
% 7.81/1.46  --splitting_cvd_svl                     false
% 7.81/1.46  --splitting_nvd                         32
% 7.81/1.46  --sub_typing                            true
% 7.81/1.46  --prep_gs_sim                           true
% 7.81/1.46  --prep_unflatten                        true
% 7.81/1.46  --prep_res_sim                          true
% 7.81/1.46  --prep_upred                            true
% 7.81/1.46  --prep_sem_filter                       exhaustive
% 7.81/1.46  --prep_sem_filter_out                   false
% 7.81/1.46  --pred_elim                             true
% 7.81/1.46  --res_sim_input                         true
% 7.81/1.46  --eq_ax_congr_red                       true
% 7.81/1.46  --pure_diseq_elim                       true
% 7.81/1.46  --brand_transform                       false
% 7.81/1.46  --non_eq_to_eq                          false
% 7.81/1.46  --prep_def_merge                        true
% 7.81/1.46  --prep_def_merge_prop_impl              false
% 7.81/1.46  --prep_def_merge_mbd                    true
% 7.81/1.46  --prep_def_merge_tr_red                 false
% 7.81/1.46  --prep_def_merge_tr_cl                  false
% 7.81/1.46  --smt_preprocessing                     true
% 7.81/1.46  --smt_ac_axioms                         fast
% 7.81/1.46  --preprocessed_out                      false
% 7.81/1.46  --preprocessed_stats                    false
% 7.81/1.46  
% 7.81/1.46  ------ Abstraction refinement Options
% 7.81/1.46  
% 7.81/1.46  --abstr_ref                             []
% 7.81/1.46  --abstr_ref_prep                        false
% 7.81/1.46  --abstr_ref_until_sat                   false
% 7.81/1.46  --abstr_ref_sig_restrict                funpre
% 7.81/1.46  --abstr_ref_af_restrict_to_split_sk     false
% 7.81/1.46  --abstr_ref_under                       []
% 7.81/1.46  
% 7.81/1.46  ------ SAT Options
% 7.81/1.46  
% 7.81/1.46  --sat_mode                              false
% 7.81/1.46  --sat_fm_restart_options                ""
% 7.81/1.46  --sat_gr_def                            false
% 7.81/1.46  --sat_epr_types                         true
% 7.81/1.46  --sat_non_cyclic_types                  false
% 7.81/1.46  --sat_finite_models                     false
% 7.81/1.46  --sat_fm_lemmas                         false
% 7.81/1.46  --sat_fm_prep                           false
% 7.81/1.46  --sat_fm_uc_incr                        true
% 7.81/1.46  --sat_out_model                         small
% 7.81/1.46  --sat_out_clauses                       false
% 7.81/1.46  
% 7.81/1.46  ------ QBF Options
% 7.81/1.46  
% 7.81/1.46  --qbf_mode                              false
% 7.81/1.46  --qbf_elim_univ                         false
% 7.81/1.46  --qbf_dom_inst                          none
% 7.81/1.46  --qbf_dom_pre_inst                      false
% 7.81/1.46  --qbf_sk_in                             false
% 7.81/1.46  --qbf_pred_elim                         true
% 7.81/1.46  --qbf_split                             512
% 7.81/1.46  
% 7.81/1.46  ------ BMC1 Options
% 7.81/1.46  
% 7.81/1.46  --bmc1_incremental                      false
% 7.81/1.46  --bmc1_axioms                           reachable_all
% 7.81/1.46  --bmc1_min_bound                        0
% 7.81/1.46  --bmc1_max_bound                        -1
% 7.81/1.46  --bmc1_max_bound_default                -1
% 7.81/1.46  --bmc1_symbol_reachability              true
% 7.81/1.46  --bmc1_property_lemmas                  false
% 7.81/1.46  --bmc1_k_induction                      false
% 7.81/1.46  --bmc1_non_equiv_states                 false
% 7.81/1.46  --bmc1_deadlock                         false
% 7.81/1.46  --bmc1_ucm                              false
% 7.81/1.46  --bmc1_add_unsat_core                   none
% 7.81/1.46  --bmc1_unsat_core_children              false
% 7.81/1.46  --bmc1_unsat_core_extrapolate_axioms    false
% 7.81/1.46  --bmc1_out_stat                         full
% 7.81/1.46  --bmc1_ground_init                      false
% 7.81/1.46  --bmc1_pre_inst_next_state              false
% 7.81/1.46  --bmc1_pre_inst_state                   false
% 7.81/1.46  --bmc1_pre_inst_reach_state             false
% 7.81/1.46  --bmc1_out_unsat_core                   false
% 7.81/1.46  --bmc1_aig_witness_out                  false
% 7.81/1.46  --bmc1_verbose                          false
% 7.81/1.46  --bmc1_dump_clauses_tptp                false
% 7.81/1.46  --bmc1_dump_unsat_core_tptp             false
% 7.81/1.46  --bmc1_dump_file                        -
% 7.81/1.46  --bmc1_ucm_expand_uc_limit              128
% 7.81/1.46  --bmc1_ucm_n_expand_iterations          6
% 7.81/1.46  --bmc1_ucm_extend_mode                  1
% 7.81/1.46  --bmc1_ucm_init_mode                    2
% 7.81/1.46  --bmc1_ucm_cone_mode                    none
% 7.81/1.46  --bmc1_ucm_reduced_relation_type        0
% 7.81/1.46  --bmc1_ucm_relax_model                  4
% 7.81/1.46  --bmc1_ucm_full_tr_after_sat            true
% 7.81/1.46  --bmc1_ucm_expand_neg_assumptions       false
% 7.81/1.46  --bmc1_ucm_layered_model                none
% 7.81/1.46  --bmc1_ucm_max_lemma_size               10
% 7.81/1.46  
% 7.81/1.46  ------ AIG Options
% 7.81/1.46  
% 7.81/1.46  --aig_mode                              false
% 7.81/1.46  
% 7.81/1.46  ------ Instantiation Options
% 7.81/1.46  
% 7.81/1.46  --instantiation_flag                    true
% 7.81/1.46  --inst_sos_flag                         false
% 7.81/1.46  --inst_sos_phase                        true
% 7.81/1.46  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.81/1.46  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.81/1.46  --inst_lit_sel_side                     none
% 7.81/1.46  --inst_solver_per_active                1400
% 7.81/1.46  --inst_solver_calls_frac                1.
% 7.81/1.46  --inst_passive_queue_type               priority_queues
% 7.81/1.46  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.81/1.46  --inst_passive_queues_freq              [25;2]
% 7.81/1.46  --inst_dismatching                      true
% 7.81/1.46  --inst_eager_unprocessed_to_passive     true
% 7.81/1.46  --inst_prop_sim_given                   true
% 7.81/1.46  --inst_prop_sim_new                     false
% 7.81/1.46  --inst_subs_new                         false
% 7.81/1.46  --inst_eq_res_simp                      false
% 7.81/1.46  --inst_subs_given                       false
% 7.81/1.46  --inst_orphan_elimination               true
% 7.81/1.46  --inst_learning_loop_flag               true
% 7.81/1.46  --inst_learning_start                   3000
% 7.81/1.46  --inst_learning_factor                  2
% 7.81/1.46  --inst_start_prop_sim_after_learn       3
% 7.81/1.46  --inst_sel_renew                        solver
% 7.81/1.46  --inst_lit_activity_flag                true
% 7.81/1.46  --inst_restr_to_given                   false
% 7.81/1.46  --inst_activity_threshold               500
% 7.81/1.46  --inst_out_proof                        true
% 7.81/1.46  
% 7.81/1.46  ------ Resolution Options
% 7.81/1.46  
% 7.81/1.46  --resolution_flag                       false
% 7.81/1.46  --res_lit_sel                           adaptive
% 7.81/1.46  --res_lit_sel_side                      none
% 7.81/1.46  --res_ordering                          kbo
% 7.81/1.46  --res_to_prop_solver                    active
% 7.81/1.46  --res_prop_simpl_new                    false
% 7.81/1.46  --res_prop_simpl_given                  true
% 7.81/1.46  --res_passive_queue_type                priority_queues
% 7.81/1.46  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.81/1.46  --res_passive_queues_freq               [15;5]
% 7.81/1.46  --res_forward_subs                      full
% 7.81/1.46  --res_backward_subs                     full
% 7.81/1.46  --res_forward_subs_resolution           true
% 7.81/1.46  --res_backward_subs_resolution          true
% 7.81/1.46  --res_orphan_elimination                true
% 7.81/1.46  --res_time_limit                        2.
% 7.81/1.46  --res_out_proof                         true
% 7.81/1.46  
% 7.81/1.46  ------ Superposition Options
% 7.81/1.46  
% 7.81/1.46  --superposition_flag                    true
% 7.81/1.46  --sup_passive_queue_type                priority_queues
% 7.81/1.46  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.81/1.46  --sup_passive_queues_freq               [8;1;4]
% 7.81/1.46  --demod_completeness_check              fast
% 7.81/1.46  --demod_use_ground                      true
% 7.81/1.46  --sup_to_prop_solver                    passive
% 7.81/1.46  --sup_prop_simpl_new                    true
% 7.81/1.46  --sup_prop_simpl_given                  true
% 7.81/1.46  --sup_fun_splitting                     false
% 7.81/1.46  --sup_smt_interval                      50000
% 7.81/1.46  
% 7.81/1.46  ------ Superposition Simplification Setup
% 7.81/1.46  
% 7.81/1.46  --sup_indices_passive                   []
% 7.81/1.46  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.46  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.46  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.81/1.46  --sup_full_triv                         [TrivRules;PropSubs]
% 7.81/1.46  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.46  --sup_full_bw                           [BwDemod]
% 7.81/1.46  --sup_immed_triv                        [TrivRules]
% 7.81/1.46  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.81/1.46  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.46  --sup_immed_bw_main                     []
% 7.81/1.46  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.46  --sup_input_triv                        [Unflattening;TrivRules]
% 7.81/1.46  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.81/1.46  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.81/1.46  
% 7.81/1.46  ------ Combination Options
% 7.81/1.46  
% 7.81/1.46  --comb_res_mult                         3
% 7.81/1.46  --comb_sup_mult                         2
% 7.81/1.46  --comb_inst_mult                        10
% 7.81/1.46  
% 7.81/1.46  ------ Debug Options
% 7.81/1.46  
% 7.81/1.46  --dbg_backtrace                         false
% 7.81/1.46  --dbg_dump_prop_clauses                 false
% 7.81/1.46  --dbg_dump_prop_clauses_file            -
% 7.81/1.46  --dbg_out_stat                          false
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  ------ Proving...
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  % SZS status Theorem for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  fof(f3,axiom,(
% 7.81/1.46    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f26,plain,(
% 7.81/1.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 7.81/1.46    inference(ennf_transformation,[],[f3])).
% 7.81/1.46  
% 7.81/1.46  fof(f31,plain,(
% 7.81/1.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f32,plain,(
% 7.81/1.46    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 7.81/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f31])).
% 7.81/1.46  
% 7.81/1.46  fof(f47,plain,(
% 7.81/1.46    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 7.81/1.46    inference(cnf_transformation,[],[f32])).
% 7.81/1.46  
% 7.81/1.46  fof(f22,conjecture,(
% 7.81/1.46    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f23,negated_conjecture,(
% 7.81/1.46    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 7.81/1.46    inference(negated_conjecture,[],[f22])).
% 7.81/1.46  
% 7.81/1.46  fof(f28,plain,(
% 7.81/1.46    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 7.81/1.46    inference(ennf_transformation,[],[f23])).
% 7.81/1.46  
% 7.81/1.46  fof(f42,plain,(
% 7.81/1.46    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK4 != sK5 & k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4))),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f43,plain,(
% 7.81/1.46    sK4 != sK5 & k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 7.81/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f42])).
% 7.81/1.46  
% 7.81/1.46  fof(f76,plain,(
% 7.81/1.46    k3_xboole_0(k1_tarski(sK4),k1_tarski(sK5)) = k1_tarski(sK4)),
% 7.81/1.46    inference(cnf_transformation,[],[f43])).
% 7.81/1.46  
% 7.81/1.46  fof(f15,axiom,(
% 7.81/1.46    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f69,plain,(
% 7.81/1.46    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f15])).
% 7.81/1.46  
% 7.81/1.46  fof(f16,axiom,(
% 7.81/1.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f70,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f16])).
% 7.81/1.46  
% 7.81/1.46  fof(f17,axiom,(
% 7.81/1.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f71,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f17])).
% 7.81/1.46  
% 7.81/1.46  fof(f78,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.81/1.46    inference(definition_unfolding,[],[f70,f71])).
% 7.81/1.46  
% 7.81/1.46  fof(f79,plain,(
% 7.81/1.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.81/1.46    inference(definition_unfolding,[],[f69,f78])).
% 7.81/1.46  
% 7.81/1.46  fof(f101,plain,(
% 7.81/1.46    k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k2_enumset1(sK4,sK4,sK4,sK4)),
% 7.81/1.46    inference(definition_unfolding,[],[f76,f79,f79,f79])).
% 7.81/1.46  
% 7.81/1.46  fof(f1,axiom,(
% 7.81/1.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f44,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f1])).
% 7.81/1.46  
% 7.81/1.46  fof(f2,axiom,(
% 7.81/1.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f24,plain,(
% 7.81/1.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.81/1.46    inference(rectify,[],[f2])).
% 7.81/1.46  
% 7.81/1.46  fof(f25,plain,(
% 7.81/1.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.81/1.46    inference(ennf_transformation,[],[f24])).
% 7.81/1.46  
% 7.81/1.46  fof(f29,plain,(
% 7.81/1.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f30,plain,(
% 7.81/1.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.81/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f29])).
% 7.81/1.46  
% 7.81/1.46  fof(f46,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f30])).
% 7.81/1.46  
% 7.81/1.46  fof(f9,axiom,(
% 7.81/1.46    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f53,plain,(
% 7.81/1.46    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f9])).
% 7.81/1.46  
% 7.81/1.46  fof(f4,axiom,(
% 7.81/1.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f48,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f4])).
% 7.81/1.46  
% 7.81/1.46  fof(f86,plain,(
% 7.81/1.46    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 7.81/1.46    inference(definition_unfolding,[],[f53,f48])).
% 7.81/1.46  
% 7.81/1.46  fof(f7,axiom,(
% 7.81/1.46    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f51,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f7])).
% 7.81/1.46  
% 7.81/1.46  fof(f10,axiom,(
% 7.81/1.46    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f54,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f10])).
% 7.81/1.46  
% 7.81/1.46  fof(f85,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))))) )),
% 7.81/1.46    inference(definition_unfolding,[],[f51,f48,f54])).
% 7.81/1.46  
% 7.81/1.46  fof(f5,axiom,(
% 7.81/1.46    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f49,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.81/1.46    inference(cnf_transformation,[],[f5])).
% 7.81/1.46  
% 7.81/1.46  fof(f83,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0) )),
% 7.81/1.46    inference(definition_unfolding,[],[f49,f54])).
% 7.81/1.46  
% 7.81/1.46  fof(f14,axiom,(
% 7.81/1.46    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f68,plain,(
% 7.81/1.46    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f14])).
% 7.81/1.46  
% 7.81/1.46  fof(f82,plain,(
% 7.81/1.46    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)),k3_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.81/1.46    inference(definition_unfolding,[],[f68,f54,f71,f79])).
% 7.81/1.46  
% 7.81/1.46  fof(f6,axiom,(
% 7.81/1.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f50,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f6])).
% 7.81/1.46  
% 7.81/1.46  fof(f84,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 7.81/1.46    inference(definition_unfolding,[],[f50,f54,f54,f48])).
% 7.81/1.46  
% 7.81/1.46  fof(f8,axiom,(
% 7.81/1.46    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f52,plain,(
% 7.81/1.46    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.81/1.46    inference(cnf_transformation,[],[f8])).
% 7.81/1.46  
% 7.81/1.46  fof(f11,axiom,(
% 7.81/1.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f27,plain,(
% 7.81/1.46    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.81/1.46    inference(ennf_transformation,[],[f11])).
% 7.81/1.46  
% 7.81/1.46  fof(f33,plain,(
% 7.81/1.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.81/1.46    inference(nnf_transformation,[],[f27])).
% 7.81/1.46  
% 7.81/1.46  fof(f34,plain,(
% 7.81/1.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.81/1.46    inference(flattening,[],[f33])).
% 7.81/1.46  
% 7.81/1.46  fof(f35,plain,(
% 7.81/1.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.81/1.46    inference(rectify,[],[f34])).
% 7.81/1.46  
% 7.81/1.46  fof(f36,plain,(
% 7.81/1.46    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f37,plain,(
% 7.81/1.46    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.81/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 7.81/1.46  
% 7.81/1.46  fof(f58,plain,(
% 7.81/1.46    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.81/1.46    inference(cnf_transformation,[],[f37])).
% 7.81/1.46  
% 7.81/1.46  fof(f91,plain,(
% 7.81/1.46    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.81/1.46    inference(definition_unfolding,[],[f58,f71])).
% 7.81/1.46  
% 7.81/1.46  fof(f102,plain,(
% 7.81/1.46    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 7.81/1.46    inference(equality_resolution,[],[f91])).
% 7.81/1.46  
% 7.81/1.46  fof(f103,plain,(
% 7.81/1.46    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 7.81/1.46    inference(equality_resolution,[],[f102])).
% 7.81/1.46  
% 7.81/1.46  fof(f12,axiom,(
% 7.81/1.46    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f38,plain,(
% 7.81/1.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.81/1.46    inference(nnf_transformation,[],[f12])).
% 7.81/1.46  
% 7.81/1.46  fof(f39,plain,(
% 7.81/1.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.81/1.46    inference(rectify,[],[f38])).
% 7.81/1.46  
% 7.81/1.46  fof(f40,plain,(
% 7.81/1.46    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f41,plain,(
% 7.81/1.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.81/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 7.81/1.46  
% 7.81/1.46  fof(f63,plain,(
% 7.81/1.46    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.81/1.46    inference(cnf_transformation,[],[f41])).
% 7.81/1.46  
% 7.81/1.46  fof(f98,plain,(
% 7.81/1.46    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.81/1.46    inference(definition_unfolding,[],[f63,f79])).
% 7.81/1.46  
% 7.81/1.46  fof(f111,plain,(
% 7.81/1.46    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.81/1.46    inference(equality_resolution,[],[f98])).
% 7.81/1.46  
% 7.81/1.46  fof(f64,plain,(
% 7.81/1.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.81/1.46    inference(cnf_transformation,[],[f41])).
% 7.81/1.46  
% 7.81/1.46  fof(f97,plain,(
% 7.81/1.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.81/1.46    inference(definition_unfolding,[],[f64,f79])).
% 7.81/1.46  
% 7.81/1.46  fof(f109,plain,(
% 7.81/1.46    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 7.81/1.46    inference(equality_resolution,[],[f97])).
% 7.81/1.46  
% 7.81/1.46  fof(f110,plain,(
% 7.81/1.46    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 7.81/1.46    inference(equality_resolution,[],[f109])).
% 7.81/1.46  
% 7.81/1.46  fof(f77,plain,(
% 7.81/1.46    sK4 != sK5),
% 7.81/1.46    inference(cnf_transformation,[],[f43])).
% 7.81/1.46  
% 7.81/1.46  cnf(c_4,plain,
% 7.81/1.46      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f47]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_574,plain,
% 7.81/1.46      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_25,negated_conjecture,
% 7.81/1.46      ( k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK5,sK5,sK5,sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.81/1.46      inference(cnf_transformation,[],[f101]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1,plain,
% 7.81/1.46      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f44]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2,plain,
% 7.81/1.46      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 7.81/1.46      inference(cnf_transformation,[],[f46]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_9,plain,
% 7.81/1.46      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 7.81/1.46      inference(cnf_transformation,[],[f86]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_206,plain,
% 7.81/1.46      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 7.81/1.46      | X3 != X2
% 7.81/1.46      | k5_xboole_0(X4,k3_xboole_0(X4,X3)) != X1 ),
% 7.81/1.46      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_207,plain,
% 7.81/1.46      ( ~ r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) ),
% 7.81/1.46      inference(unflattening,[status(thm)],[c_206]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_560,plain,
% 7.81/1.46      ( r2_hidden(X0,k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1021,plain,
% 7.81/1.46      ( r2_hidden(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_1,c_560]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_4477,plain,
% 7.81/1.46      ( r2_hidden(X0,k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_25,c_1021]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_7,plain,
% 7.81/1.46      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f85]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5,plain,
% 7.81/1.46      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = X0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f83]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_599,plain,
% 7.81/1.46      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_7,c_5]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_4731,plain,
% 7.81/1.46      ( r2_hidden(X0,k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0)) != iProver_top ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_4477,c_599]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5212,plain,
% 7.81/1.46      ( k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0) = k1_xboole_0 ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_574,c_4731]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_0,plain,
% 7.81/1.46      ( k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)),k3_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) = k2_enumset1(X0,X1,X2,X3) ),
% 7.81/1.46      inference(cnf_transformation,[],[f82]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_6,plain,
% 7.81/1.46      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.81/1.46      inference(cnf_transformation,[],[f84]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1528,plain,
% 7.81/1.46      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4))),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))) = k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4))) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_25,c_6]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_8,plain,
% 7.81/1.46      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.81/1.46      inference(cnf_transformation,[],[f52]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1534,plain,
% 7.81/1.46      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4))) = k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0)) ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_1528,c_8,c_599]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2364,plain,
% 7.81/1.46      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0)) = k2_enumset1(sK5,sK5,sK5,sK4) ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_0,c_1534]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_8407,plain,
% 7.81/1.46      ( k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),k1_xboole_0) = k2_enumset1(sK5,sK5,sK5,sK4) ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_5212,c_2364]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_21244,plain,
% 7.81/1.46      ( k2_enumset1(sK5,sK5,sK5,sK4) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_8407,c_8]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22304,plain,
% 7.81/1.46      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK4),k2_enumset1(X0,X0,X0,X0)),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK4),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(sK5,sK5,sK5,X0) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_21244,c_0]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22322,plain,
% 7.81/1.46      ( k2_enumset1(sK5,sK5,sK4,X0) = k2_enumset1(sK5,sK5,sK5,X0) ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_22304,c_0]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22699,plain,
% 7.81/1.46      ( k5_xboole_0(k5_xboole_0(k2_enumset1(sK5,sK5,sK5,sK4),k2_enumset1(X0,X0,X0,X0)),k3_xboole_0(k2_enumset1(sK5,sK5,sK5,sK4),k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(sK5,sK5,sK4,X0) ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_22304,c_22322]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22700,plain,
% 7.81/1.46      ( k2_enumset1(sK5,sK4,sK4,X0) = k2_enumset1(sK5,sK5,sK4,X0) ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_22699,c_0,c_22322]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_14,plain,
% 7.81/1.46      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 7.81/1.46      inference(cnf_transformation,[],[f103]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_569,plain,
% 7.81/1.46      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22782,plain,
% 7.81/1.46      ( r2_hidden(X0,k2_enumset1(sK5,sK4,sK4,X0)) = iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_22700,c_569]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22837,plain,
% 7.81/1.46      ( r2_hidden(sK4,k2_enumset1(sK5,sK4,sK4,sK4)) = iProver_top ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_22782]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_21,plain,
% 7.81/1.46      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.81/1.46      inference(cnf_transformation,[],[f111]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_562,plain,
% 7.81/1.46      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22313,plain,
% 7.81/1.46      ( sK5 = X0
% 7.81/1.46      | r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK4)) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_21244,c_562]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22690,plain,
% 7.81/1.46      ( sK5 = X0
% 7.81/1.46      | r2_hidden(X0,k2_enumset1(sK5,sK5,sK4,sK4)) != iProver_top ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_22313,c_22322]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22702,plain,
% 7.81/1.46      ( sK5 = X0
% 7.81/1.46      | r2_hidden(X0,k2_enumset1(sK5,sK4,sK4,sK4)) != iProver_top ),
% 7.81/1.46      inference(demodulation,[status(thm)],[c_22700,c_22690]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22717,plain,
% 7.81/1.46      ( sK5 = sK4
% 7.81/1.46      | r2_hidden(sK4,k2_enumset1(sK5,sK4,sK4,sK4)) != iProver_top ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_22702]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_322,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_699,plain,
% 7.81/1.46      ( sK5 != X0 | sK4 != X0 | sK4 = sK5 ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_322]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_700,plain,
% 7.81/1.46      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_699]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_20,plain,
% 7.81/1.46      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 7.81/1.46      inference(cnf_transformation,[],[f110]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_32,plain,
% 7.81/1.46      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_20]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_29,plain,
% 7.81/1.46      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_21]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_24,negated_conjecture,
% 7.81/1.46      ( sK4 != sK5 ),
% 7.81/1.46      inference(cnf_transformation,[],[f77]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(contradiction,plain,
% 7.81/1.46      ( $false ),
% 7.81/1.46      inference(minisat,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_22837,c_22717,c_700,c_32,c_29,c_24]) ).
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  ------                               Statistics
% 7.81/1.46  
% 7.81/1.46  ------ General
% 7.81/1.46  
% 7.81/1.46  abstr_ref_over_cycles:                  0
% 7.81/1.46  abstr_ref_under_cycles:                 0
% 7.81/1.46  gc_basic_clause_elim:                   0
% 7.81/1.46  forced_gc_time:                         0
% 7.81/1.46  parsing_time:                           0.009
% 7.81/1.46  unif_index_cands_time:                  0.
% 7.81/1.46  unif_index_add_time:                    0.
% 7.81/1.46  orderings_time:                         0.
% 7.81/1.46  out_proof_time:                         0.008
% 7.81/1.46  total_time:                             0.74
% 7.81/1.46  num_of_symbols:                         44
% 7.81/1.46  num_of_terms:                           31623
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing
% 7.81/1.46  
% 7.81/1.46  num_of_splits:                          0
% 7.81/1.46  num_of_split_atoms:                     0
% 7.81/1.46  num_of_reused_defs:                     0
% 7.81/1.46  num_eq_ax_congr_red:                    52
% 7.81/1.46  num_of_sem_filtered_clauses:            1
% 7.81/1.46  num_of_subtypes:                        0
% 7.81/1.46  monotx_restored_types:                  0
% 7.81/1.46  sat_num_of_epr_types:                   0
% 7.81/1.46  sat_num_of_non_cyclic_types:            0
% 7.81/1.46  sat_guarded_non_collapsed_types:        0
% 7.81/1.46  num_pure_diseq_elim:                    0
% 7.81/1.46  simp_replaced_by:                       0
% 7.81/1.46  res_preprocessed:                       114
% 7.81/1.46  prep_upred:                             0
% 7.81/1.46  prep_unflattend:                        4
% 7.81/1.46  smt_new_axioms:                         0
% 7.81/1.46  pred_elim_cands:                        1
% 7.81/1.46  pred_elim:                              1
% 7.81/1.46  pred_elim_cl:                           1
% 7.81/1.46  pred_elim_cycles:                       3
% 7.81/1.46  merged_defs:                            0
% 7.81/1.46  merged_defs_ncl:                        0
% 7.81/1.46  bin_hyper_res:                          0
% 7.81/1.46  prep_cycles:                            4
% 7.81/1.46  pred_elim_time:                         0.001
% 7.81/1.46  splitting_time:                         0.
% 7.81/1.46  sem_filter_time:                        0.
% 7.81/1.46  monotx_time:                            0.
% 7.81/1.46  subtype_inf_time:                       0.
% 7.81/1.46  
% 7.81/1.46  ------ Problem properties
% 7.81/1.46  
% 7.81/1.46  clauses:                                25
% 7.81/1.46  conjectures:                            2
% 7.81/1.46  epr:                                    1
% 7.81/1.46  horn:                                   21
% 7.81/1.46  ground:                                 2
% 7.81/1.46  unary:                                  15
% 7.81/1.46  binary:                                 3
% 7.81/1.46  lits:                                   45
% 7.81/1.46  lits_eq:                                29
% 7.81/1.46  fd_pure:                                0
% 7.81/1.46  fd_pseudo:                              0
% 7.81/1.46  fd_cond:                                1
% 7.81/1.46  fd_pseudo_cond:                         6
% 7.81/1.46  ac_symbols:                             0
% 7.81/1.46  
% 7.81/1.46  ------ Propositional Solver
% 7.81/1.46  
% 7.81/1.46  prop_solver_calls:                      30
% 7.81/1.46  prop_fast_solver_calls:                 636
% 7.81/1.46  smt_solver_calls:                       0
% 7.81/1.46  smt_fast_solver_calls:                  0
% 7.81/1.46  prop_num_of_clauses:                    8415
% 7.81/1.46  prop_preprocess_simplified:             17546
% 7.81/1.46  prop_fo_subsumed:                       8
% 7.81/1.46  prop_solver_time:                       0.
% 7.81/1.46  smt_solver_time:                        0.
% 7.81/1.46  smt_fast_solver_time:                   0.
% 7.81/1.46  prop_fast_solver_time:                  0.
% 7.81/1.46  prop_unsat_core_time:                   0.
% 7.81/1.46  
% 7.81/1.46  ------ QBF
% 7.81/1.46  
% 7.81/1.46  qbf_q_res:                              0
% 7.81/1.46  qbf_num_tautologies:                    0
% 7.81/1.46  qbf_prep_cycles:                        0
% 7.81/1.46  
% 7.81/1.46  ------ BMC1
% 7.81/1.46  
% 7.81/1.46  bmc1_current_bound:                     -1
% 7.81/1.46  bmc1_last_solved_bound:                 -1
% 7.81/1.46  bmc1_unsat_core_size:                   -1
% 7.81/1.46  bmc1_unsat_core_parents_size:           -1
% 7.81/1.46  bmc1_merge_next_fun:                    0
% 7.81/1.46  bmc1_unsat_core_clauses_time:           0.
% 7.81/1.46  
% 7.81/1.46  ------ Instantiation
% 7.81/1.46  
% 7.81/1.46  inst_num_of_clauses:                    2448
% 7.81/1.46  inst_num_in_passive:                    774
% 7.81/1.46  inst_num_in_active:                     576
% 7.81/1.46  inst_num_in_unprocessed:                1098
% 7.81/1.46  inst_num_of_loops:                      620
% 7.81/1.46  inst_num_of_learning_restarts:          0
% 7.81/1.46  inst_num_moves_active_passive:          43
% 7.81/1.46  inst_lit_activity:                      0
% 7.81/1.46  inst_lit_activity_moves:                0
% 7.81/1.46  inst_num_tautologies:                   0
% 7.81/1.46  inst_num_prop_implied:                  0
% 7.81/1.46  inst_num_existing_simplified:           0
% 7.81/1.46  inst_num_eq_res_simplified:             0
% 7.81/1.46  inst_num_child_elim:                    0
% 7.81/1.46  inst_num_of_dismatching_blockings:      3068
% 7.81/1.46  inst_num_of_non_proper_insts:           3346
% 7.81/1.46  inst_num_of_duplicates:                 0
% 7.81/1.46  inst_inst_num_from_inst_to_res:         0
% 7.81/1.46  inst_dismatching_checking_time:         0.
% 7.81/1.46  
% 7.81/1.46  ------ Resolution
% 7.81/1.46  
% 7.81/1.46  res_num_of_clauses:                     0
% 7.81/1.46  res_num_in_passive:                     0
% 7.81/1.46  res_num_in_active:                      0
% 7.81/1.46  res_num_of_loops:                       118
% 7.81/1.46  res_forward_subset_subsumed:            515
% 7.81/1.46  res_backward_subset_subsumed:           0
% 7.81/1.46  res_forward_subsumed:                   0
% 7.81/1.46  res_backward_subsumed:                  0
% 7.81/1.46  res_forward_subsumption_resolution:     0
% 7.81/1.46  res_backward_subsumption_resolution:    0
% 7.81/1.46  res_clause_to_clause_subsumption:       2101
% 7.81/1.46  res_orphan_elimination:                 0
% 7.81/1.46  res_tautology_del:                      46
% 7.81/1.46  res_num_eq_res_simplified:              0
% 7.81/1.46  res_num_sel_changes:                    0
% 7.81/1.46  res_moves_from_active_to_pass:          0
% 7.81/1.46  
% 7.81/1.46  ------ Superposition
% 7.81/1.46  
% 7.81/1.46  sup_time_total:                         0.
% 7.81/1.46  sup_time_generating:                    0.
% 7.81/1.46  sup_time_sim_full:                      0.
% 7.81/1.46  sup_time_sim_immed:                     0.
% 7.81/1.46  
% 7.81/1.46  sup_num_of_clauses:                     544
% 7.81/1.46  sup_num_in_active:                      55
% 7.81/1.46  sup_num_in_passive:                     489
% 7.81/1.46  sup_num_of_loops:                       123
% 7.81/1.46  sup_fw_superposition:                   656
% 7.81/1.46  sup_bw_superposition:                   614
% 7.81/1.46  sup_immediate_simplified:               465
% 7.81/1.46  sup_given_eliminated:                   29
% 7.81/1.46  comparisons_done:                       0
% 7.81/1.46  comparisons_avoided:                    14
% 7.81/1.46  
% 7.81/1.46  ------ Simplifications
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  sim_fw_subset_subsumed:                 33
% 7.81/1.46  sim_bw_subset_subsumed:                 44
% 7.81/1.46  sim_fw_subsumed:                        26
% 7.81/1.46  sim_bw_subsumed:                        3
% 7.81/1.46  sim_fw_subsumption_res:                 0
% 7.81/1.46  sim_bw_subsumption_res:                 0
% 7.81/1.46  sim_tautology_del:                      0
% 7.81/1.46  sim_eq_tautology_del:                   41
% 7.81/1.46  sim_eq_res_simp:                        0
% 7.81/1.46  sim_fw_demodulated:                     588
% 7.81/1.46  sim_bw_demodulated:                     111
% 7.81/1.46  sim_light_normalised:                   128
% 7.81/1.46  sim_joinable_taut:                      0
% 7.81/1.46  sim_joinable_simp:                      0
% 7.81/1.46  sim_ac_normalised:                      0
% 7.81/1.46  sim_smt_subsumption:                    0
% 7.81/1.46  
%------------------------------------------------------------------------------
