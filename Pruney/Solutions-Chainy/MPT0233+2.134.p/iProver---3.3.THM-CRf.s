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
% DateTime   : Thu Dec  3 11:31:32 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 272 expanded)
%              Number of clauses        :   43 (  63 expanded)
%              Number of leaves         :   20 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          :  318 ( 505 expanded)
%              Number of equality atoms :  232 ( 407 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f76,f68])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK2 != sK5
      & sK2 != sK4
      & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( sK2 != sK5
    & sK2 != sK4
    & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f41])).

fof(f77,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f84,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f50,f68])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f50,f68,f80])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(definition_unfolding,[],[f67,f50,f80,f68,f81])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f69,f80])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f29])).

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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f54,f80])).

fof(f102,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))) != X3 ) ),
    inference(equality_resolution,[],[f93])).

fof(f103,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))) ),
    inference(equality_resolution,[],[f102])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f79,plain,(
    sK2 != sK5 ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1278,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1277,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1294,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3424,plain,
    ( r1_tarski(X0,k2_tarski(sK4,sK5)) = iProver_top
    | r1_tarski(X0,k2_tarski(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_1294])).

cnf(c_3740,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_3424])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1293,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3745,plain,
    ( k4_xboole_0(k2_tarski(sK2,sK2),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5))) = k2_tarski(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_3740,c_1293])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3785,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK2,sK2)) = k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_3745,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1698,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1708,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1698,c_6])).

cnf(c_1700,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_1702,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1700,c_5])).

cnf(c_1709,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1708,c_1702])).

cnf(c_3787,plain,
    ( k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3785,c_1709])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1697,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_1713,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1697,c_1709])).

cnf(c_21,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2827,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))),k2_tarski(X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k1_xboole_0),k4_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X0),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_1713,c_21])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2840,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k1_xboole_0),k4_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X0),k1_xboole_0))) = k2_tarski(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2827,c_1])).

cnf(c_2841,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2840,c_6])).

cnf(c_2829,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_21])).

cnf(c_2842,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(demodulation,[status(thm)],[c_2841,c_2829])).

cnf(c_11,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1288,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18599,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2842,c_1288])).

cnf(c_19347,plain,
    ( r2_hidden(sK2,k5_xboole_0(k2_tarski(sK4,sK5),k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3787,c_18599])).

cnf(c_19351,plain,
    ( r2_hidden(sK2,k2_tarski(sK4,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_19347,c_6])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1969,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK4,X1))
    | X0 = X1
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3297,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK4,sK5))
    | sK2 = sK4
    | sK2 = sK5 ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_3298,plain,
    ( sK2 = sK4
    | sK2 = sK5
    | r2_hidden(sK2,k2_tarski(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3297])).

cnf(c_26,negated_conjecture,
    ( sK2 != sK5 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_27,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f78])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19351,c_3298,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:35:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.08/1.54  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/1.54  
% 7.08/1.54  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.08/1.54  
% 7.08/1.54  ------  iProver source info
% 7.08/1.54  
% 7.08/1.54  git: date: 2020-06-30 10:37:57 +0100
% 7.08/1.54  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.08/1.54  git: non_committed_changes: false
% 7.08/1.54  git: last_make_outside_of_git: false
% 7.08/1.54  
% 7.08/1.54  ------ 
% 7.08/1.54  
% 7.08/1.54  ------ Input Options
% 7.08/1.54  
% 7.08/1.54  --out_options                           all
% 7.08/1.54  --tptp_safe_out                         true
% 7.08/1.54  --problem_path                          ""
% 7.08/1.54  --include_path                          ""
% 7.08/1.54  --clausifier                            res/vclausify_rel
% 7.08/1.54  --clausifier_options                    --mode clausify
% 7.08/1.54  --stdin                                 false
% 7.08/1.54  --stats_out                             all
% 7.08/1.54  
% 7.08/1.54  ------ General Options
% 7.08/1.54  
% 7.08/1.54  --fof                                   false
% 7.08/1.54  --time_out_real                         305.
% 7.08/1.54  --time_out_virtual                      -1.
% 7.08/1.54  --symbol_type_check                     false
% 7.08/1.54  --clausify_out                          false
% 7.08/1.54  --sig_cnt_out                           false
% 7.08/1.54  --trig_cnt_out                          false
% 7.08/1.54  --trig_cnt_out_tolerance                1.
% 7.08/1.54  --trig_cnt_out_sk_spl                   false
% 7.08/1.54  --abstr_cl_out                          false
% 7.08/1.54  
% 7.08/1.54  ------ Global Options
% 7.08/1.54  
% 7.08/1.54  --schedule                              default
% 7.08/1.54  --add_important_lit                     false
% 7.08/1.54  --prop_solver_per_cl                    1000
% 7.08/1.54  --min_unsat_core                        false
% 7.08/1.54  --soft_assumptions                      false
% 7.08/1.54  --soft_lemma_size                       3
% 7.08/1.54  --prop_impl_unit_size                   0
% 7.08/1.54  --prop_impl_unit                        []
% 7.08/1.54  --share_sel_clauses                     true
% 7.08/1.54  --reset_solvers                         false
% 7.08/1.54  --bc_imp_inh                            [conj_cone]
% 7.08/1.54  --conj_cone_tolerance                   3.
% 7.08/1.54  --extra_neg_conj                        none
% 7.08/1.54  --large_theory_mode                     true
% 7.08/1.54  --prolific_symb_bound                   200
% 7.08/1.54  --lt_threshold                          2000
% 7.08/1.54  --clause_weak_htbl                      true
% 7.08/1.54  --gc_record_bc_elim                     false
% 7.08/1.54  
% 7.08/1.54  ------ Preprocessing Options
% 7.08/1.54  
% 7.08/1.54  --preprocessing_flag                    true
% 7.08/1.54  --time_out_prep_mult                    0.1
% 7.08/1.54  --splitting_mode                        input
% 7.08/1.54  --splitting_grd                         true
% 7.08/1.54  --splitting_cvd                         false
% 7.08/1.54  --splitting_cvd_svl                     false
% 7.08/1.54  --splitting_nvd                         32
% 7.08/1.54  --sub_typing                            true
% 7.08/1.54  --prep_gs_sim                           true
% 7.08/1.54  --prep_unflatten                        true
% 7.08/1.54  --prep_res_sim                          true
% 7.08/1.54  --prep_upred                            true
% 7.08/1.54  --prep_sem_filter                       exhaustive
% 7.08/1.54  --prep_sem_filter_out                   false
% 7.08/1.54  --pred_elim                             true
% 7.08/1.54  --res_sim_input                         true
% 7.08/1.54  --eq_ax_congr_red                       true
% 7.08/1.54  --pure_diseq_elim                       true
% 7.08/1.54  --brand_transform                       false
% 7.08/1.54  --non_eq_to_eq                          false
% 7.08/1.54  --prep_def_merge                        true
% 7.08/1.54  --prep_def_merge_prop_impl              false
% 7.08/1.54  --prep_def_merge_mbd                    true
% 7.08/1.54  --prep_def_merge_tr_red                 false
% 7.08/1.54  --prep_def_merge_tr_cl                  false
% 7.08/1.54  --smt_preprocessing                     true
% 7.08/1.54  --smt_ac_axioms                         fast
% 7.08/1.54  --preprocessed_out                      false
% 7.08/1.54  --preprocessed_stats                    false
% 7.08/1.54  
% 7.08/1.54  ------ Abstraction refinement Options
% 7.08/1.54  
% 7.08/1.54  --abstr_ref                             []
% 7.08/1.54  --abstr_ref_prep                        false
% 7.08/1.54  --abstr_ref_until_sat                   false
% 7.08/1.54  --abstr_ref_sig_restrict                funpre
% 7.08/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 7.08/1.54  --abstr_ref_under                       []
% 7.08/1.54  
% 7.08/1.54  ------ SAT Options
% 7.08/1.54  
% 7.08/1.54  --sat_mode                              false
% 7.08/1.54  --sat_fm_restart_options                ""
% 7.08/1.54  --sat_gr_def                            false
% 7.08/1.54  --sat_epr_types                         true
% 7.08/1.54  --sat_non_cyclic_types                  false
% 7.08/1.54  --sat_finite_models                     false
% 7.08/1.54  --sat_fm_lemmas                         false
% 7.08/1.54  --sat_fm_prep                           false
% 7.08/1.54  --sat_fm_uc_incr                        true
% 7.08/1.54  --sat_out_model                         small
% 7.08/1.54  --sat_out_clauses                       false
% 7.08/1.54  
% 7.08/1.54  ------ QBF Options
% 7.08/1.54  
% 7.08/1.54  --qbf_mode                              false
% 7.08/1.54  --qbf_elim_univ                         false
% 7.08/1.54  --qbf_dom_inst                          none
% 7.08/1.54  --qbf_dom_pre_inst                      false
% 7.08/1.54  --qbf_sk_in                             false
% 7.08/1.54  --qbf_pred_elim                         true
% 7.08/1.54  --qbf_split                             512
% 7.08/1.54  
% 7.08/1.54  ------ BMC1 Options
% 7.08/1.54  
% 7.08/1.54  --bmc1_incremental                      false
% 7.08/1.54  --bmc1_axioms                           reachable_all
% 7.08/1.54  --bmc1_min_bound                        0
% 7.08/1.54  --bmc1_max_bound                        -1
% 7.08/1.54  --bmc1_max_bound_default                -1
% 7.08/1.54  --bmc1_symbol_reachability              true
% 7.08/1.54  --bmc1_property_lemmas                  false
% 7.08/1.54  --bmc1_k_induction                      false
% 7.08/1.54  --bmc1_non_equiv_states                 false
% 7.08/1.54  --bmc1_deadlock                         false
% 7.08/1.54  --bmc1_ucm                              false
% 7.08/1.54  --bmc1_add_unsat_core                   none
% 7.08/1.54  --bmc1_unsat_core_children              false
% 7.08/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 7.08/1.54  --bmc1_out_stat                         full
% 7.08/1.54  --bmc1_ground_init                      false
% 7.08/1.54  --bmc1_pre_inst_next_state              false
% 7.08/1.54  --bmc1_pre_inst_state                   false
% 7.08/1.54  --bmc1_pre_inst_reach_state             false
% 7.08/1.54  --bmc1_out_unsat_core                   false
% 7.08/1.54  --bmc1_aig_witness_out                  false
% 7.08/1.54  --bmc1_verbose                          false
% 7.08/1.54  --bmc1_dump_clauses_tptp                false
% 7.08/1.54  --bmc1_dump_unsat_core_tptp             false
% 7.08/1.54  --bmc1_dump_file                        -
% 7.08/1.54  --bmc1_ucm_expand_uc_limit              128
% 7.08/1.54  --bmc1_ucm_n_expand_iterations          6
% 7.08/1.54  --bmc1_ucm_extend_mode                  1
% 7.08/1.54  --bmc1_ucm_init_mode                    2
% 7.08/1.54  --bmc1_ucm_cone_mode                    none
% 7.08/1.54  --bmc1_ucm_reduced_relation_type        0
% 7.08/1.54  --bmc1_ucm_relax_model                  4
% 7.08/1.54  --bmc1_ucm_full_tr_after_sat            true
% 7.08/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 7.08/1.54  --bmc1_ucm_layered_model                none
% 7.08/1.54  --bmc1_ucm_max_lemma_size               10
% 7.08/1.54  
% 7.08/1.54  ------ AIG Options
% 7.08/1.54  
% 7.08/1.54  --aig_mode                              false
% 7.08/1.54  
% 7.08/1.54  ------ Instantiation Options
% 7.08/1.54  
% 7.08/1.54  --instantiation_flag                    true
% 7.08/1.54  --inst_sos_flag                         false
% 7.08/1.54  --inst_sos_phase                        true
% 7.08/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.08/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.08/1.54  --inst_lit_sel_side                     num_symb
% 7.08/1.54  --inst_solver_per_active                1400
% 7.08/1.54  --inst_solver_calls_frac                1.
% 7.08/1.54  --inst_passive_queue_type               priority_queues
% 7.08/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.08/1.54  --inst_passive_queues_freq              [25;2]
% 7.08/1.54  --inst_dismatching                      true
% 7.08/1.54  --inst_eager_unprocessed_to_passive     true
% 7.08/1.54  --inst_prop_sim_given                   true
% 7.08/1.54  --inst_prop_sim_new                     false
% 7.08/1.54  --inst_subs_new                         false
% 7.08/1.54  --inst_eq_res_simp                      false
% 7.08/1.54  --inst_subs_given                       false
% 7.08/1.54  --inst_orphan_elimination               true
% 7.08/1.54  --inst_learning_loop_flag               true
% 7.08/1.54  --inst_learning_start                   3000
% 7.08/1.54  --inst_learning_factor                  2
% 7.08/1.54  --inst_start_prop_sim_after_learn       3
% 7.08/1.54  --inst_sel_renew                        solver
% 7.08/1.54  --inst_lit_activity_flag                true
% 7.08/1.54  --inst_restr_to_given                   false
% 7.08/1.54  --inst_activity_threshold               500
% 7.08/1.54  --inst_out_proof                        true
% 7.08/1.54  
% 7.08/1.54  ------ Resolution Options
% 7.08/1.54  
% 7.08/1.54  --resolution_flag                       true
% 7.08/1.54  --res_lit_sel                           adaptive
% 7.08/1.54  --res_lit_sel_side                      none
% 7.08/1.54  --res_ordering                          kbo
% 7.08/1.54  --res_to_prop_solver                    active
% 7.08/1.54  --res_prop_simpl_new                    false
% 7.08/1.54  --res_prop_simpl_given                  true
% 7.08/1.54  --res_passive_queue_type                priority_queues
% 7.08/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.08/1.54  --res_passive_queues_freq               [15;5]
% 7.08/1.54  --res_forward_subs                      full
% 7.08/1.54  --res_backward_subs                     full
% 7.08/1.54  --res_forward_subs_resolution           true
% 7.08/1.54  --res_backward_subs_resolution          true
% 7.08/1.54  --res_orphan_elimination                true
% 7.08/1.54  --res_time_limit                        2.
% 7.08/1.54  --res_out_proof                         true
% 7.08/1.54  
% 7.08/1.54  ------ Superposition Options
% 7.08/1.54  
% 7.08/1.54  --superposition_flag                    true
% 7.08/1.54  --sup_passive_queue_type                priority_queues
% 7.08/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.08/1.54  --sup_passive_queues_freq               [8;1;4]
% 7.08/1.54  --demod_completeness_check              fast
% 7.08/1.54  --demod_use_ground                      true
% 7.08/1.54  --sup_to_prop_solver                    passive
% 7.08/1.54  --sup_prop_simpl_new                    true
% 7.08/1.54  --sup_prop_simpl_given                  true
% 7.08/1.54  --sup_fun_splitting                     false
% 7.08/1.54  --sup_smt_interval                      50000
% 7.08/1.54  
% 7.08/1.54  ------ Superposition Simplification Setup
% 7.08/1.54  
% 7.08/1.54  --sup_indices_passive                   []
% 7.08/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 7.08/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.54  --sup_full_bw                           [BwDemod]
% 7.08/1.54  --sup_immed_triv                        [TrivRules]
% 7.08/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.54  --sup_immed_bw_main                     []
% 7.08/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 7.08/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.54  
% 7.08/1.54  ------ Combination Options
% 7.08/1.54  
% 7.08/1.54  --comb_res_mult                         3
% 7.08/1.54  --comb_sup_mult                         2
% 7.08/1.54  --comb_inst_mult                        10
% 7.08/1.54  
% 7.08/1.54  ------ Debug Options
% 7.08/1.54  
% 7.08/1.54  --dbg_backtrace                         false
% 7.08/1.54  --dbg_dump_prop_clauses                 false
% 7.08/1.54  --dbg_dump_prop_clauses_file            -
% 7.08/1.54  --dbg_out_stat                          false
% 7.08/1.54  ------ Parsing...
% 7.08/1.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.08/1.54  
% 7.08/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.08/1.54  
% 7.08/1.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.08/1.54  
% 7.08/1.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.08/1.54  ------ Proving...
% 7.08/1.54  ------ Problem Properties 
% 7.08/1.54  
% 7.08/1.54  
% 7.08/1.54  clauses                                 29
% 7.08/1.54  conjectures                             3
% 7.08/1.54  EPR                                     3
% 7.08/1.54  Horn                                    25
% 7.08/1.54  unary                                   18
% 7.08/1.54  binary                                  1
% 7.08/1.54  lits                                    54
% 7.08/1.54  lits eq                                 34
% 7.08/1.54  fd_pure                                 0
% 7.08/1.54  fd_pseudo                               0
% 7.08/1.54  fd_cond                                 0
% 7.08/1.54  fd_pseudo_cond                          7
% 7.08/1.54  AC symbols                              0
% 7.08/1.54  
% 7.08/1.54  ------ Schedule dynamic 5 is on 
% 7.08/1.54  
% 7.08/1.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.08/1.54  
% 7.08/1.54  
% 7.08/1.54  ------ 
% 7.08/1.54  Current options:
% 7.08/1.54  ------ 
% 7.08/1.54  
% 7.08/1.54  ------ Input Options
% 7.08/1.54  
% 7.08/1.54  --out_options                           all
% 7.08/1.54  --tptp_safe_out                         true
% 7.08/1.54  --problem_path                          ""
% 7.08/1.54  --include_path                          ""
% 7.08/1.54  --clausifier                            res/vclausify_rel
% 7.08/1.54  --clausifier_options                    --mode clausify
% 7.08/1.54  --stdin                                 false
% 7.08/1.54  --stats_out                             all
% 7.08/1.54  
% 7.08/1.54  ------ General Options
% 7.08/1.54  
% 7.08/1.54  --fof                                   false
% 7.08/1.54  --time_out_real                         305.
% 7.08/1.54  --time_out_virtual                      -1.
% 7.08/1.54  --symbol_type_check                     false
% 7.08/1.54  --clausify_out                          false
% 7.08/1.54  --sig_cnt_out                           false
% 7.08/1.54  --trig_cnt_out                          false
% 7.08/1.54  --trig_cnt_out_tolerance                1.
% 7.08/1.54  --trig_cnt_out_sk_spl                   false
% 7.08/1.54  --abstr_cl_out                          false
% 7.08/1.54  
% 7.08/1.54  ------ Global Options
% 7.08/1.54  
% 7.08/1.54  --schedule                              default
% 7.08/1.54  --add_important_lit                     false
% 7.08/1.54  --prop_solver_per_cl                    1000
% 7.08/1.54  --min_unsat_core                        false
% 7.08/1.54  --soft_assumptions                      false
% 7.08/1.54  --soft_lemma_size                       3
% 7.08/1.54  --prop_impl_unit_size                   0
% 7.08/1.54  --prop_impl_unit                        []
% 7.08/1.54  --share_sel_clauses                     true
% 7.08/1.54  --reset_solvers                         false
% 7.08/1.54  --bc_imp_inh                            [conj_cone]
% 7.08/1.54  --conj_cone_tolerance                   3.
% 7.08/1.54  --extra_neg_conj                        none
% 7.08/1.54  --large_theory_mode                     true
% 7.08/1.54  --prolific_symb_bound                   200
% 7.08/1.54  --lt_threshold                          2000
% 7.08/1.54  --clause_weak_htbl                      true
% 7.08/1.54  --gc_record_bc_elim                     false
% 7.08/1.54  
% 7.08/1.54  ------ Preprocessing Options
% 7.08/1.54  
% 7.08/1.54  --preprocessing_flag                    true
% 7.08/1.54  --time_out_prep_mult                    0.1
% 7.08/1.54  --splitting_mode                        input
% 7.08/1.54  --splitting_grd                         true
% 7.08/1.54  --splitting_cvd                         false
% 7.08/1.54  --splitting_cvd_svl                     false
% 7.08/1.54  --splitting_nvd                         32
% 7.08/1.54  --sub_typing                            true
% 7.08/1.54  --prep_gs_sim                           true
% 7.08/1.54  --prep_unflatten                        true
% 7.08/1.54  --prep_res_sim                          true
% 7.08/1.54  --prep_upred                            true
% 7.08/1.54  --prep_sem_filter                       exhaustive
% 7.08/1.54  --prep_sem_filter_out                   false
% 7.08/1.54  --pred_elim                             true
% 7.08/1.54  --res_sim_input                         true
% 7.08/1.54  --eq_ax_congr_red                       true
% 7.08/1.54  --pure_diseq_elim                       true
% 7.08/1.54  --brand_transform                       false
% 7.08/1.54  --non_eq_to_eq                          false
% 7.08/1.54  --prep_def_merge                        true
% 7.08/1.54  --prep_def_merge_prop_impl              false
% 7.08/1.54  --prep_def_merge_mbd                    true
% 7.08/1.54  --prep_def_merge_tr_red                 false
% 7.08/1.54  --prep_def_merge_tr_cl                  false
% 7.08/1.54  --smt_preprocessing                     true
% 7.08/1.54  --smt_ac_axioms                         fast
% 7.08/1.54  --preprocessed_out                      false
% 7.08/1.54  --preprocessed_stats                    false
% 7.08/1.54  
% 7.08/1.54  ------ Abstraction refinement Options
% 7.08/1.54  
% 7.08/1.54  --abstr_ref                             []
% 7.08/1.54  --abstr_ref_prep                        false
% 7.08/1.54  --abstr_ref_until_sat                   false
% 7.08/1.54  --abstr_ref_sig_restrict                funpre
% 7.08/1.54  --abstr_ref_af_restrict_to_split_sk     false
% 7.08/1.54  --abstr_ref_under                       []
% 7.08/1.54  
% 7.08/1.54  ------ SAT Options
% 7.08/1.54  
% 7.08/1.54  --sat_mode                              false
% 7.08/1.54  --sat_fm_restart_options                ""
% 7.08/1.54  --sat_gr_def                            false
% 7.08/1.54  --sat_epr_types                         true
% 7.08/1.54  --sat_non_cyclic_types                  false
% 7.08/1.54  --sat_finite_models                     false
% 7.08/1.54  --sat_fm_lemmas                         false
% 7.08/1.54  --sat_fm_prep                           false
% 7.08/1.54  --sat_fm_uc_incr                        true
% 7.08/1.54  --sat_out_model                         small
% 7.08/1.54  --sat_out_clauses                       false
% 7.08/1.54  
% 7.08/1.54  ------ QBF Options
% 7.08/1.54  
% 7.08/1.54  --qbf_mode                              false
% 7.08/1.54  --qbf_elim_univ                         false
% 7.08/1.54  --qbf_dom_inst                          none
% 7.08/1.54  --qbf_dom_pre_inst                      false
% 7.08/1.54  --qbf_sk_in                             false
% 7.08/1.54  --qbf_pred_elim                         true
% 7.08/1.54  --qbf_split                             512
% 7.08/1.54  
% 7.08/1.54  ------ BMC1 Options
% 7.08/1.54  
% 7.08/1.54  --bmc1_incremental                      false
% 7.08/1.54  --bmc1_axioms                           reachable_all
% 7.08/1.54  --bmc1_min_bound                        0
% 7.08/1.54  --bmc1_max_bound                        -1
% 7.08/1.54  --bmc1_max_bound_default                -1
% 7.08/1.54  --bmc1_symbol_reachability              true
% 7.08/1.54  --bmc1_property_lemmas                  false
% 7.08/1.54  --bmc1_k_induction                      false
% 7.08/1.54  --bmc1_non_equiv_states                 false
% 7.08/1.54  --bmc1_deadlock                         false
% 7.08/1.54  --bmc1_ucm                              false
% 7.08/1.54  --bmc1_add_unsat_core                   none
% 7.08/1.54  --bmc1_unsat_core_children              false
% 7.08/1.54  --bmc1_unsat_core_extrapolate_axioms    false
% 7.08/1.54  --bmc1_out_stat                         full
% 7.08/1.54  --bmc1_ground_init                      false
% 7.08/1.54  --bmc1_pre_inst_next_state              false
% 7.08/1.54  --bmc1_pre_inst_state                   false
% 7.08/1.54  --bmc1_pre_inst_reach_state             false
% 7.08/1.54  --bmc1_out_unsat_core                   false
% 7.08/1.54  --bmc1_aig_witness_out                  false
% 7.08/1.54  --bmc1_verbose                          false
% 7.08/1.54  --bmc1_dump_clauses_tptp                false
% 7.08/1.54  --bmc1_dump_unsat_core_tptp             false
% 7.08/1.54  --bmc1_dump_file                        -
% 7.08/1.54  --bmc1_ucm_expand_uc_limit              128
% 7.08/1.54  --bmc1_ucm_n_expand_iterations          6
% 7.08/1.54  --bmc1_ucm_extend_mode                  1
% 7.08/1.54  --bmc1_ucm_init_mode                    2
% 7.08/1.54  --bmc1_ucm_cone_mode                    none
% 7.08/1.54  --bmc1_ucm_reduced_relation_type        0
% 7.08/1.54  --bmc1_ucm_relax_model                  4
% 7.08/1.54  --bmc1_ucm_full_tr_after_sat            true
% 7.08/1.54  --bmc1_ucm_expand_neg_assumptions       false
% 7.08/1.54  --bmc1_ucm_layered_model                none
% 7.08/1.54  --bmc1_ucm_max_lemma_size               10
% 7.08/1.54  
% 7.08/1.54  ------ AIG Options
% 7.08/1.54  
% 7.08/1.54  --aig_mode                              false
% 7.08/1.54  
% 7.08/1.54  ------ Instantiation Options
% 7.08/1.54  
% 7.08/1.54  --instantiation_flag                    true
% 7.08/1.54  --inst_sos_flag                         false
% 7.08/1.54  --inst_sos_phase                        true
% 7.08/1.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.08/1.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.08/1.54  --inst_lit_sel_side                     none
% 7.08/1.54  --inst_solver_per_active                1400
% 7.08/1.54  --inst_solver_calls_frac                1.
% 7.08/1.54  --inst_passive_queue_type               priority_queues
% 7.08/1.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.08/1.54  --inst_passive_queues_freq              [25;2]
% 7.08/1.54  --inst_dismatching                      true
% 7.08/1.54  --inst_eager_unprocessed_to_passive     true
% 7.08/1.54  --inst_prop_sim_given                   true
% 7.08/1.54  --inst_prop_sim_new                     false
% 7.08/1.54  --inst_subs_new                         false
% 7.08/1.54  --inst_eq_res_simp                      false
% 7.08/1.54  --inst_subs_given                       false
% 7.08/1.54  --inst_orphan_elimination               true
% 7.08/1.54  --inst_learning_loop_flag               true
% 7.08/1.54  --inst_learning_start                   3000
% 7.08/1.54  --inst_learning_factor                  2
% 7.08/1.54  --inst_start_prop_sim_after_learn       3
% 7.08/1.54  --inst_sel_renew                        solver
% 7.08/1.54  --inst_lit_activity_flag                true
% 7.08/1.54  --inst_restr_to_given                   false
% 7.08/1.54  --inst_activity_threshold               500
% 7.08/1.54  --inst_out_proof                        true
% 7.08/1.54  
% 7.08/1.54  ------ Resolution Options
% 7.08/1.54  
% 7.08/1.54  --resolution_flag                       false
% 7.08/1.54  --res_lit_sel                           adaptive
% 7.08/1.54  --res_lit_sel_side                      none
% 7.08/1.54  --res_ordering                          kbo
% 7.08/1.54  --res_to_prop_solver                    active
% 7.08/1.54  --res_prop_simpl_new                    false
% 7.08/1.54  --res_prop_simpl_given                  true
% 7.08/1.54  --res_passive_queue_type                priority_queues
% 7.08/1.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.08/1.54  --res_passive_queues_freq               [15;5]
% 7.08/1.54  --res_forward_subs                      full
% 7.08/1.54  --res_backward_subs                     full
% 7.08/1.54  --res_forward_subs_resolution           true
% 7.08/1.54  --res_backward_subs_resolution          true
% 7.08/1.54  --res_orphan_elimination                true
% 7.08/1.54  --res_time_limit                        2.
% 7.08/1.54  --res_out_proof                         true
% 7.08/1.54  
% 7.08/1.54  ------ Superposition Options
% 7.08/1.54  
% 7.08/1.54  --superposition_flag                    true
% 7.08/1.54  --sup_passive_queue_type                priority_queues
% 7.08/1.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.08/1.54  --sup_passive_queues_freq               [8;1;4]
% 7.08/1.54  --demod_completeness_check              fast
% 7.08/1.54  --demod_use_ground                      true
% 7.08/1.54  --sup_to_prop_solver                    passive
% 7.08/1.54  --sup_prop_simpl_new                    true
% 7.08/1.54  --sup_prop_simpl_given                  true
% 7.08/1.54  --sup_fun_splitting                     false
% 7.08/1.54  --sup_smt_interval                      50000
% 7.08/1.54  
% 7.08/1.54  ------ Superposition Simplification Setup
% 7.08/1.54  
% 7.08/1.54  --sup_indices_passive                   []
% 7.08/1.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.54  --sup_full_triv                         [TrivRules;PropSubs]
% 7.08/1.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.54  --sup_full_bw                           [BwDemod]
% 7.08/1.54  --sup_immed_triv                        [TrivRules]
% 7.08/1.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.54  --sup_immed_bw_main                     []
% 7.08/1.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.54  --sup_input_triv                        [Unflattening;TrivRules]
% 7.08/1.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.54  
% 7.08/1.54  ------ Combination Options
% 7.08/1.54  
% 7.08/1.54  --comb_res_mult                         3
% 7.08/1.54  --comb_sup_mult                         2
% 7.08/1.54  --comb_inst_mult                        10
% 7.08/1.54  
% 7.08/1.54  ------ Debug Options
% 7.08/1.54  
% 7.08/1.54  --dbg_backtrace                         false
% 7.08/1.54  --dbg_dump_prop_clauses                 false
% 7.08/1.54  --dbg_dump_prop_clauses_file            -
% 7.08/1.54  --dbg_out_stat                          false
% 7.08/1.54  
% 7.08/1.54  
% 7.08/1.54  
% 7.08/1.54  
% 7.08/1.54  ------ Proving...
% 7.08/1.54  
% 7.08/1.54  
% 7.08/1.54  % SZS status Theorem for theBenchmark.p
% 7.08/1.54  
% 7.08/1.54  % SZS output start CNFRefutation for theBenchmark.p
% 7.08/1.54  
% 7.08/1.54  fof(f22,axiom,(
% 7.08/1.54    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f76,plain,(
% 7.08/1.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 7.08/1.54    inference(cnf_transformation,[],[f22])).
% 7.08/1.54  
% 7.08/1.54  fof(f14,axiom,(
% 7.08/1.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f68,plain,(
% 7.08/1.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.08/1.54    inference(cnf_transformation,[],[f14])).
% 7.08/1.54  
% 7.08/1.54  fof(f101,plain,(
% 7.08/1.54    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 7.08/1.54    inference(definition_unfolding,[],[f76,f68])).
% 7.08/1.54  
% 7.08/1.54  fof(f23,conjecture,(
% 7.08/1.54    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f24,negated_conjecture,(
% 7.08/1.54    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.08/1.54    inference(negated_conjecture,[],[f23])).
% 7.08/1.54  
% 7.08/1.54  fof(f30,plain,(
% 7.08/1.54    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.08/1.54    inference(ennf_transformation,[],[f24])).
% 7.08/1.54  
% 7.08/1.54  fof(f41,plain,(
% 7.08/1.54    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))),
% 7.08/1.54    introduced(choice_axiom,[])).
% 7.08/1.54  
% 7.08/1.54  fof(f42,plain,(
% 7.08/1.54    sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 7.08/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f30,f41])).
% 7.08/1.54  
% 7.08/1.54  fof(f77,plain,(
% 7.08/1.54    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 7.08/1.54    inference(cnf_transformation,[],[f42])).
% 7.08/1.54  
% 7.08/1.54  fof(f3,axiom,(
% 7.08/1.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f26,plain,(
% 7.08/1.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.08/1.54    inference(ennf_transformation,[],[f3])).
% 7.08/1.54  
% 7.08/1.54  fof(f27,plain,(
% 7.08/1.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.08/1.54    inference(flattening,[],[f26])).
% 7.08/1.54  
% 7.08/1.54  fof(f45,plain,(
% 7.08/1.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.08/1.54    inference(cnf_transformation,[],[f27])).
% 7.08/1.54  
% 7.08/1.54  fof(f4,axiom,(
% 7.08/1.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f28,plain,(
% 7.08/1.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.08/1.54    inference(ennf_transformation,[],[f4])).
% 7.08/1.54  
% 7.08/1.54  fof(f46,plain,(
% 7.08/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.08/1.54    inference(cnf_transformation,[],[f28])).
% 7.08/1.54  
% 7.08/1.54  fof(f6,axiom,(
% 7.08/1.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f48,plain,(
% 7.08/1.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.08/1.54    inference(cnf_transformation,[],[f6])).
% 7.08/1.54  
% 7.08/1.54  fof(f87,plain,(
% 7.08/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.08/1.54    inference(definition_unfolding,[],[f46,f48])).
% 7.08/1.54  
% 7.08/1.54  fof(f2,axiom,(
% 7.08/1.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f44,plain,(
% 7.08/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.08/1.54    inference(cnf_transformation,[],[f2])).
% 7.08/1.54  
% 7.08/1.54  fof(f84,plain,(
% 7.08/1.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.08/1.54    inference(definition_unfolding,[],[f44,f48])).
% 7.08/1.54  
% 7.08/1.54  fof(f5,axiom,(
% 7.08/1.54    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f47,plain,(
% 7.08/1.54    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.08/1.54    inference(cnf_transformation,[],[f5])).
% 7.08/1.54  
% 7.08/1.54  fof(f88,plain,(
% 7.08/1.54    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.08/1.54    inference(definition_unfolding,[],[f47,f48])).
% 7.08/1.54  
% 7.08/1.54  fof(f7,axiom,(
% 7.08/1.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f49,plain,(
% 7.08/1.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.08/1.54    inference(cnf_transformation,[],[f7])).
% 7.08/1.54  
% 7.08/1.54  fof(f1,axiom,(
% 7.08/1.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f25,plain,(
% 7.08/1.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.08/1.54    inference(rectify,[],[f1])).
% 7.08/1.54  
% 7.08/1.54  fof(f43,plain,(
% 7.08/1.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.08/1.54    inference(cnf_transformation,[],[f25])).
% 7.08/1.54  
% 7.08/1.54  fof(f86,plain,(
% 7.08/1.54    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.08/1.54    inference(definition_unfolding,[],[f43,f48])).
% 7.08/1.54  
% 7.08/1.54  fof(f13,axiom,(
% 7.08/1.54    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f67,plain,(
% 7.08/1.54    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.08/1.54    inference(cnf_transformation,[],[f13])).
% 7.08/1.54  
% 7.08/1.54  fof(f12,axiom,(
% 7.08/1.54    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f66,plain,(
% 7.08/1.54    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.08/1.54    inference(cnf_transformation,[],[f12])).
% 7.08/1.54  
% 7.08/1.54  fof(f11,axiom,(
% 7.08/1.54    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f65,plain,(
% 7.08/1.54    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 7.08/1.54    inference(cnf_transformation,[],[f11])).
% 7.08/1.54  
% 7.08/1.54  fof(f8,axiom,(
% 7.08/1.54    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f50,plain,(
% 7.08/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.08/1.54    inference(cnf_transformation,[],[f8])).
% 7.08/1.54  
% 7.08/1.54  fof(f80,plain,(
% 7.08/1.54    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k1_enumset1(X0,X1,X2)) )),
% 7.08/1.54    inference(definition_unfolding,[],[f65,f50,f68])).
% 7.08/1.54  
% 7.08/1.54  fof(f81,plain,(
% 7.08/1.54    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.08/1.54    inference(definition_unfolding,[],[f66,f50,f68,f80])).
% 7.08/1.54  
% 7.08/1.54  fof(f97,plain,(
% 7.08/1.54    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))) )),
% 7.08/1.54    inference(definition_unfolding,[],[f67,f50,f80,f68,f81])).
% 7.08/1.54  
% 7.08/1.54  fof(f15,axiom,(
% 7.08/1.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f69,plain,(
% 7.08/1.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.08/1.54    inference(cnf_transformation,[],[f15])).
% 7.08/1.54  
% 7.08/1.54  fof(f85,plain,(
% 7.08/1.54    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1)) )),
% 7.08/1.54    inference(definition_unfolding,[],[f69,f80])).
% 7.08/1.54  
% 7.08/1.54  fof(f9,axiom,(
% 7.08/1.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f29,plain,(
% 7.08/1.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.08/1.54    inference(ennf_transformation,[],[f9])).
% 7.08/1.54  
% 7.08/1.54  fof(f31,plain,(
% 7.08/1.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.08/1.54    inference(nnf_transformation,[],[f29])).
% 7.08/1.54  
% 7.08/1.54  fof(f32,plain,(
% 7.08/1.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.08/1.54    inference(flattening,[],[f31])).
% 7.08/1.54  
% 7.08/1.54  fof(f33,plain,(
% 7.08/1.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.08/1.54    inference(rectify,[],[f32])).
% 7.08/1.54  
% 7.08/1.54  fof(f34,plain,(
% 7.08/1.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 7.08/1.54    introduced(choice_axiom,[])).
% 7.08/1.54  
% 7.08/1.54  fof(f35,plain,(
% 7.08/1.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.08/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 7.08/1.54  
% 7.08/1.54  fof(f54,plain,(
% 7.08/1.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.08/1.54    inference(cnf_transformation,[],[f35])).
% 7.08/1.54  
% 7.08/1.54  fof(f93,plain,(
% 7.08/1.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3) )),
% 7.08/1.54    inference(definition_unfolding,[],[f54,f80])).
% 7.08/1.54  
% 7.08/1.54  fof(f102,plain,(
% 7.08/1.54    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))) != X3) )),
% 7.08/1.54    inference(equality_resolution,[],[f93])).
% 7.08/1.54  
% 7.08/1.54  fof(f103,plain,(
% 7.08/1.54    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))))) )),
% 7.08/1.54    inference(equality_resolution,[],[f102])).
% 7.08/1.54  
% 7.08/1.54  fof(f10,axiom,(
% 7.08/1.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.08/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.54  
% 7.08/1.54  fof(f36,plain,(
% 7.08/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.08/1.54    inference(nnf_transformation,[],[f10])).
% 7.08/1.54  
% 7.08/1.54  fof(f37,plain,(
% 7.08/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.08/1.54    inference(flattening,[],[f36])).
% 7.08/1.54  
% 7.08/1.54  fof(f38,plain,(
% 7.08/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.08/1.54    inference(rectify,[],[f37])).
% 7.08/1.54  
% 7.08/1.54  fof(f39,plain,(
% 7.08/1.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.08/1.54    introduced(choice_axiom,[])).
% 7.08/1.54  
% 7.08/1.54  fof(f40,plain,(
% 7.08/1.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.08/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 7.08/1.54  
% 7.08/1.54  fof(f59,plain,(
% 7.08/1.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.08/1.54    inference(cnf_transformation,[],[f40])).
% 7.08/1.54  
% 7.08/1.54  fof(f113,plain,(
% 7.08/1.54    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 7.08/1.54    inference(equality_resolution,[],[f59])).
% 7.08/1.54  
% 7.08/1.54  fof(f79,plain,(
% 7.08/1.54    sK2 != sK5),
% 7.08/1.54    inference(cnf_transformation,[],[f42])).
% 7.08/1.54  
% 7.08/1.54  fof(f78,plain,(
% 7.08/1.54    sK2 != sK4),
% 7.08/1.54    inference(cnf_transformation,[],[f42])).
% 7.08/1.54  
% 7.08/1.54  cnf(c_25,plain,
% 7.08/1.54      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
% 7.08/1.54      inference(cnf_transformation,[],[f101]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1278,plain,
% 7.08/1.54      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
% 7.08/1.54      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_28,negated_conjecture,
% 7.08/1.54      ( r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
% 7.08/1.54      inference(cnf_transformation,[],[f77]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1277,plain,
% 7.08/1.54      ( r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) = iProver_top ),
% 7.08/1.54      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_3,plain,
% 7.08/1.54      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.08/1.54      inference(cnf_transformation,[],[f45]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1294,plain,
% 7.08/1.54      ( r1_tarski(X0,X1) != iProver_top
% 7.08/1.54      | r1_tarski(X2,X0) != iProver_top
% 7.08/1.54      | r1_tarski(X2,X1) = iProver_top ),
% 7.08/1.54      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_3424,plain,
% 7.08/1.54      ( r1_tarski(X0,k2_tarski(sK4,sK5)) = iProver_top
% 7.08/1.54      | r1_tarski(X0,k2_tarski(sK2,sK3)) != iProver_top ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_1277,c_1294]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_3740,plain,
% 7.08/1.54      ( r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) = iProver_top ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_1278,c_3424]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_4,plain,
% 7.08/1.54      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.08/1.54      inference(cnf_transformation,[],[f87]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1293,plain,
% 7.08/1.54      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.08/1.54      | r1_tarski(X0,X1) != iProver_top ),
% 7.08/1.54      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_3745,plain,
% 7.08/1.54      ( k4_xboole_0(k2_tarski(sK2,sK2),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5))) = k2_tarski(sK2,sK2) ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_3740,c_1293]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_0,plain,
% 7.08/1.54      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.08/1.54      inference(cnf_transformation,[],[f84]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_3785,plain,
% 7.08/1.54      ( k5_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK2,sK2)) = k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_3745,c_0]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_5,plain,
% 7.08/1.54      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.08/1.54      inference(cnf_transformation,[],[f88]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1698,plain,
% 7.08/1.54      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_6,plain,
% 7.08/1.54      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.08/1.54      inference(cnf_transformation,[],[f49]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1708,plain,
% 7.08/1.54      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.08/1.54      inference(light_normalisation,[status(thm)],[c_1698,c_6]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1700,plain,
% 7.08/1.54      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1702,plain,
% 7.08/1.54      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.08/1.54      inference(light_normalisation,[status(thm)],[c_1700,c_5]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1709,plain,
% 7.08/1.54      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.08/1.54      inference(demodulation,[status(thm)],[c_1708,c_1702]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_3787,plain,
% 7.08/1.54      ( k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) = k1_xboole_0 ),
% 7.08/1.54      inference(demodulation,[status(thm)],[c_3785,c_1709]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_2,plain,
% 7.08/1.54      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.08/1.54      inference(cnf_transformation,[],[f86]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1697,plain,
% 7.08/1.54      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1713,plain,
% 7.08/1.54      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.08/1.54      inference(light_normalisation,[status(thm)],[c_1697,c_1709]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_21,plain,
% 7.08/1.54      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))),k2_tarski(X0,X0))) ),
% 7.08/1.54      inference(cnf_transformation,[],[f97]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_2827,plain,
% 7.08/1.54      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))),k2_tarski(X0,X0))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k1_xboole_0),k4_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X0),k1_xboole_0))) ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_1713,c_21]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1,plain,
% 7.08/1.54      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
% 7.08/1.54      inference(cnf_transformation,[],[f85]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_2840,plain,
% 7.08/1.54      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k1_xboole_0),k4_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X0),k1_xboole_0))) = k2_tarski(X0,X1) ),
% 7.08/1.54      inference(light_normalisation,[status(thm)],[c_2827,c_1]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_2841,plain,
% 7.08/1.54      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
% 7.08/1.54      inference(demodulation,[status(thm)],[c_2840,c_6]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_2829,plain,
% 7.08/1.54      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))),k4_xboole_0(k2_tarski(X2,X2),k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_1,c_21]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_2842,plain,
% 7.08/1.54      ( k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
% 7.08/1.54      inference(demodulation,[status(thm)],[c_2841,c_2829]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_11,plain,
% 7.08/1.54      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1)))) ),
% 7.08/1.54      inference(cnf_transformation,[],[f103]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1288,plain,
% 7.08/1.54      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1)))) = iProver_top ),
% 7.08/1.54      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_18599,plain,
% 7.08/1.54      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X2)))) = iProver_top ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_2842,c_1288]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_19347,plain,
% 7.08/1.54      ( r2_hidden(sK2,k5_xboole_0(k2_tarski(sK4,sK5),k1_xboole_0)) = iProver_top ),
% 7.08/1.54      inference(superposition,[status(thm)],[c_3787,c_18599]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_19351,plain,
% 7.08/1.54      ( r2_hidden(sK2,k2_tarski(sK4,sK5)) = iProver_top ),
% 7.08/1.54      inference(demodulation,[status(thm)],[c_19347,c_6]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_20,plain,
% 7.08/1.54      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.08/1.54      inference(cnf_transformation,[],[f113]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_1969,plain,
% 7.08/1.54      ( ~ r2_hidden(X0,k2_tarski(sK4,X1)) | X0 = X1 | X0 = sK4 ),
% 7.08/1.54      inference(instantiation,[status(thm)],[c_20]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_3297,plain,
% 7.08/1.54      ( ~ r2_hidden(sK2,k2_tarski(sK4,sK5)) | sK2 = sK4 | sK2 = sK5 ),
% 7.08/1.54      inference(instantiation,[status(thm)],[c_1969]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_3298,plain,
% 7.08/1.54      ( sK2 = sK4
% 7.08/1.54      | sK2 = sK5
% 7.08/1.54      | r2_hidden(sK2,k2_tarski(sK4,sK5)) != iProver_top ),
% 7.08/1.54      inference(predicate_to_equality,[status(thm)],[c_3297]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_26,negated_conjecture,
% 7.08/1.54      ( sK2 != sK5 ),
% 7.08/1.54      inference(cnf_transformation,[],[f79]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(c_27,negated_conjecture,
% 7.08/1.54      ( sK2 != sK4 ),
% 7.08/1.54      inference(cnf_transformation,[],[f78]) ).
% 7.08/1.54  
% 7.08/1.54  cnf(contradiction,plain,
% 7.08/1.54      ( $false ),
% 7.08/1.54      inference(minisat,[status(thm)],[c_19351,c_3298,c_26,c_27]) ).
% 7.08/1.54  
% 7.08/1.54  
% 7.08/1.54  % SZS output end CNFRefutation for theBenchmark.p
% 7.08/1.54  
% 7.08/1.54  ------                               Statistics
% 7.08/1.54  
% 7.08/1.54  ------ General
% 7.08/1.54  
% 7.08/1.54  abstr_ref_over_cycles:                  0
% 7.08/1.54  abstr_ref_under_cycles:                 0
% 7.08/1.54  gc_basic_clause_elim:                   0
% 7.08/1.54  forced_gc_time:                         0
% 7.08/1.54  parsing_time:                           0.018
% 7.08/1.54  unif_index_cands_time:                  0.
% 7.08/1.54  unif_index_add_time:                    0.
% 7.08/1.54  orderings_time:                         0.
% 7.08/1.54  out_proof_time:                         0.014
% 7.08/1.54  total_time:                             0.807
% 7.08/1.54  num_of_symbols:                         44
% 7.08/1.54  num_of_terms:                           21529
% 7.08/1.54  
% 7.08/1.54  ------ Preprocessing
% 7.08/1.54  
% 7.08/1.54  num_of_splits:                          0
% 7.08/1.54  num_of_split_atoms:                     0
% 7.08/1.54  num_of_reused_defs:                     0
% 7.08/1.54  num_eq_ax_congr_red:                    30
% 7.08/1.54  num_of_sem_filtered_clauses:            1
% 7.08/1.54  num_of_subtypes:                        0
% 7.08/1.54  monotx_restored_types:                  0
% 7.08/1.54  sat_num_of_epr_types:                   0
% 7.08/1.54  sat_num_of_non_cyclic_types:            0
% 7.08/1.54  sat_guarded_non_collapsed_types:        0
% 7.08/1.54  num_pure_diseq_elim:                    0
% 7.08/1.54  simp_replaced_by:                       0
% 7.08/1.54  res_preprocessed:                       102
% 7.08/1.54  prep_upred:                             0
% 7.08/1.54  prep_unflattend:                        48
% 7.08/1.54  smt_new_axioms:                         0
% 7.08/1.54  pred_elim_cands:                        2
% 7.08/1.54  pred_elim:                              0
% 7.08/1.54  pred_elim_cl:                           0
% 7.08/1.54  pred_elim_cycles:                       1
% 7.08/1.54  merged_defs:                            0
% 7.08/1.54  merged_defs_ncl:                        0
% 7.08/1.54  bin_hyper_res:                          0
% 7.08/1.54  prep_cycles:                            3
% 7.08/1.54  pred_elim_time:                         0.014
% 7.08/1.54  splitting_time:                         0.
% 7.08/1.54  sem_filter_time:                        0.
% 7.08/1.54  monotx_time:                            0.
% 7.08/1.54  subtype_inf_time:                       0.
% 7.08/1.54  
% 7.08/1.54  ------ Problem properties
% 7.08/1.54  
% 7.08/1.54  clauses:                                29
% 7.08/1.54  conjectures:                            3
% 7.08/1.54  epr:                                    3
% 7.08/1.54  horn:                                   25
% 7.08/1.54  ground:                                 3
% 7.08/1.54  unary:                                  18
% 7.08/1.54  binary:                                 1
% 7.08/1.54  lits:                                   54
% 7.08/1.54  lits_eq:                                34
% 7.08/1.54  fd_pure:                                0
% 7.08/1.54  fd_pseudo:                              0
% 7.08/1.54  fd_cond:                                0
% 7.08/1.54  fd_pseudo_cond:                         7
% 7.08/1.54  ac_symbols:                             0
% 7.08/1.54  
% 7.08/1.54  ------ Propositional Solver
% 7.08/1.54  
% 7.08/1.54  prop_solver_calls:                      25
% 7.08/1.54  prop_fast_solver_calls:                 714
% 7.08/1.54  smt_solver_calls:                       0
% 7.08/1.54  smt_fast_solver_calls:                  0
% 7.08/1.54  prop_num_of_clauses:                    5670
% 7.08/1.54  prop_preprocess_simplified:             13939
% 7.08/1.54  prop_fo_subsumed:                       0
% 7.08/1.54  prop_solver_time:                       0.
% 7.08/1.54  smt_solver_time:                        0.
% 7.08/1.54  smt_fast_solver_time:                   0.
% 7.08/1.54  prop_fast_solver_time:                  0.
% 7.08/1.54  prop_unsat_core_time:                   0.
% 7.08/1.54  
% 7.08/1.54  ------ QBF
% 7.08/1.54  
% 7.08/1.54  qbf_q_res:                              0
% 7.08/1.54  qbf_num_tautologies:                    0
% 7.08/1.54  qbf_prep_cycles:                        0
% 7.08/1.54  
% 7.08/1.54  ------ BMC1
% 7.08/1.54  
% 7.08/1.54  bmc1_current_bound:                     -1
% 7.08/1.54  bmc1_last_solved_bound:                 -1
% 7.08/1.54  bmc1_unsat_core_size:                   -1
% 7.08/1.54  bmc1_unsat_core_parents_size:           -1
% 7.08/1.54  bmc1_merge_next_fun:                    0
% 7.08/1.54  bmc1_unsat_core_clauses_time:           0.
% 7.08/1.54  
% 7.08/1.54  ------ Instantiation
% 7.08/1.54  
% 7.08/1.54  inst_num_of_clauses:                    1785
% 7.08/1.54  inst_num_in_passive:                    958
% 7.08/1.54  inst_num_in_active:                     534
% 7.08/1.54  inst_num_in_unprocessed:                293
% 7.08/1.54  inst_num_of_loops:                      550
% 7.08/1.54  inst_num_of_learning_restarts:          0
% 7.08/1.54  inst_num_moves_active_passive:          15
% 7.08/1.54  inst_lit_activity:                      0
% 7.08/1.54  inst_lit_activity_moves:                0
% 7.08/1.54  inst_num_tautologies:                   0
% 7.08/1.54  inst_num_prop_implied:                  0
% 7.08/1.54  inst_num_existing_simplified:           0
% 7.08/1.54  inst_num_eq_res_simplified:             0
% 7.08/1.54  inst_num_child_elim:                    0
% 7.08/1.54  inst_num_of_dismatching_blockings:      1844
% 7.08/1.54  inst_num_of_non_proper_insts:           1542
% 7.08/1.54  inst_num_of_duplicates:                 0
% 7.08/1.54  inst_inst_num_from_inst_to_res:         0
% 7.08/1.54  inst_dismatching_checking_time:         0.
% 7.08/1.54  
% 7.08/1.54  ------ Resolution
% 7.08/1.54  
% 7.08/1.54  res_num_of_clauses:                     0
% 7.08/1.54  res_num_in_passive:                     0
% 7.08/1.54  res_num_in_active:                      0
% 7.08/1.54  res_num_of_loops:                       105
% 7.08/1.54  res_forward_subset_subsumed:            358
% 7.08/1.54  res_backward_subset_subsumed:           0
% 7.08/1.54  res_forward_subsumed:                   0
% 7.08/1.54  res_backward_subsumed:                  0
% 7.08/1.54  res_forward_subsumption_resolution:     0
% 7.08/1.54  res_backward_subsumption_resolution:    0
% 7.08/1.54  res_clause_to_clause_subsumption:       1432
% 7.08/1.54  res_orphan_elimination:                 0
% 7.08/1.54  res_tautology_del:                      28
% 7.08/1.54  res_num_eq_res_simplified:              0
% 7.08/1.54  res_num_sel_changes:                    0
% 7.08/1.54  res_moves_from_active_to_pass:          0
% 7.08/1.54  
% 7.08/1.54  ------ Superposition
% 7.08/1.54  
% 7.08/1.54  sup_time_total:                         0.
% 7.08/1.54  sup_time_generating:                    0.
% 7.08/1.54  sup_time_sim_full:                      0.
% 7.08/1.54  sup_time_sim_immed:                     0.
% 7.08/1.54  
% 7.08/1.54  sup_num_of_clauses:                     199
% 7.08/1.54  sup_num_in_active:                      104
% 7.08/1.54  sup_num_in_passive:                     95
% 7.08/1.54  sup_num_of_loops:                       108
% 7.08/1.54  sup_fw_superposition:                   2181
% 7.08/1.54  sup_bw_superposition:                   2460
% 7.08/1.54  sup_immediate_simplified:               305
% 7.08/1.54  sup_given_eliminated:                   3
% 7.08/1.54  comparisons_done:                       0
% 7.08/1.54  comparisons_avoided:                    9
% 7.08/1.54  
% 7.08/1.54  ------ Simplifications
% 7.08/1.54  
% 7.08/1.54  
% 7.08/1.54  sim_fw_subset_subsumed:                 0
% 7.08/1.54  sim_bw_subset_subsumed:                 0
% 7.08/1.54  sim_fw_subsumed:                        17
% 7.08/1.54  sim_bw_subsumed:                        0
% 7.08/1.54  sim_fw_subsumption_res:                 0
% 7.08/1.54  sim_bw_subsumption_res:                 0
% 7.08/1.54  sim_tautology_del:                      0
% 7.08/1.54  sim_eq_tautology_del:                   105
% 7.08/1.54  sim_eq_res_simp:                        0
% 7.08/1.54  sim_fw_demodulated:                     200
% 7.08/1.54  sim_bw_demodulated:                     8
% 7.08/1.54  sim_light_normalised:                   96
% 7.08/1.54  sim_joinable_taut:                      0
% 7.08/1.54  sim_joinable_simp:                      0
% 7.08/1.54  sim_ac_normalised:                      0
% 7.08/1.54  sim_smt_subsumption:                    0
% 7.08/1.54  
%------------------------------------------------------------------------------
