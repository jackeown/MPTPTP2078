%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:25 EST 2020

% Result     : Theorem 19.45s
% Output     : CNFRefutation 19.45s
% Verified   : 
% Statistics : Number of formulae       :  203 (7741 expanded)
%              Number of clauses        :  132 (1886 expanded)
%              Number of leaves         :   21 (2321 expanded)
%              Depth                    :   28
%              Number of atoms          :  408 (8755 expanded)
%              Number of equality atoms :  274 (8026 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f66])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f64,f74,f66,f77])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f62,f74,f66,f66])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f67,f76])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) )
   => ( ~ r2_hidden(sK2,sK4)
      & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ r2_hidden(sK2,sK4)
    & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f38])).

fof(f72,plain,(
    k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f86,plain,(
    k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))) = k1_enumset1(sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f72,f75,f66,f66])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f81,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k1_enumset1(X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f42,f75])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f74])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(nnf_transformation,[],[f28])).

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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f90,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f89])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f55])).

fof(f92,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f73,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_543,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4622,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_543,c_13])).

cnf(c_4963,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_4622])).

cnf(c_0,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_23,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1235,plain,
    ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_23])).

cnf(c_26,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))) = k1_enumset1(sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_245,negated_conjecture,
    ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))) = k1_enumset1(sK2,sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_26,c_12,c_1])).

cnf(c_1110,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))),X0)) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_245,c_12])).

cnf(c_2895,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))),X0)) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
    inference(demodulation,[status(thm)],[c_1235,c_1110])).

cnf(c_2896,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)))) = k1_enumset1(sK2,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_1235,c_245])).

cnf(c_544,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_5471,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))),k5_xboole_0(sK4,X0)) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2896,c_544])).

cnf(c_1518,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_12,c_1110])).

cnf(c_2893,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)),X0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
    inference(demodulation,[status(thm)],[c_1235,c_1518])).

cnf(c_4132,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))) = k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_13,c_2893])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k1_enumset1(X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_250,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_3,c_12,c_1])).

cnf(c_2,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_525,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_250,c_2,c_13])).

cnf(c_4140,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))) = k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4132,c_525])).

cnf(c_5524,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(sK4,X0)) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_5471,c_4140])).

cnf(c_5583,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_5524,c_1])).

cnf(c_13358,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))),X0),k1_enumset1(sK2,sK2,sK3)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_2895,c_5583])).

cnf(c_1520,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),X1) ),
    inference(superposition,[status(thm)],[c_1110,c_12])).

cnf(c_1769,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))) = k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_13,c_1518])).

cnf(c_1772,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))) = k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1769,c_525])).

cnf(c_2072,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1520,c_1520,c_1772])).

cnf(c_1515,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_1,c_1110])).

cnf(c_2086,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0)) ),
    inference(superposition,[status(thm)],[c_2072,c_1515])).

cnf(c_2087,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0)) ),
    inference(light_normalisation,[status(thm)],[c_2086,c_1772])).

cnf(c_1113,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_13])).

cnf(c_1771,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0)),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),X1) ),
    inference(superposition,[status(thm)],[c_1518,c_12])).

cnf(c_6015,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0))),X1) = k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0),X1)) ),
    inference(superposition,[status(thm)],[c_1113,c_1771])).

cnf(c_2853,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0))) = k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1113,c_1518])).

cnf(c_2863,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0))) = k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2853,c_525])).

cnf(c_6039,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0),X0)) = k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0) ),
    inference(light_normalisation,[status(thm)],[c_6015,c_2863])).

cnf(c_6040,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0)) = k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0) ),
    inference(demodulation,[status(thm)],[c_6039,c_525])).

cnf(c_1517,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_13,c_1110])).

cnf(c_1109,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_13,c_12])).

cnf(c_954,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_525,c_1])).

cnf(c_1117,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1109,c_954])).

cnf(c_1522,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))) = sK4 ),
    inference(demodulation,[status(thm)],[c_1517,c_525,c_1117])).

cnf(c_2101,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_1522,c_1522,c_1772])).

cnf(c_545,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_12,c_1])).

cnf(c_6871,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0)) = k5_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_2101,c_545])).

cnf(c_2102,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0)) = k5_xboole_0(sK4,X0) ),
    inference(superposition,[status(thm)],[c_2101,c_12])).

cnf(c_7002,plain,
    ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0))) = k5_xboole_0(X0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_6871,c_2102,c_6040])).

cnf(c_13426,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0)),k1_enumset1(sK2,sK2,sK3)) = k5_xboole_0(X0,sK4) ),
    inference(light_normalisation,[status(thm)],[c_13358,c_2087,c_4140,c_6040,c_7002])).

cnf(c_17592,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),X0),sK4) = k5_xboole_0(k5_xboole_0(sK4,k1_xboole_0),k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_4963,c_13426])).

cnf(c_5461,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_525,c_544])).

cnf(c_6952,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_545,c_5524])).

cnf(c_5590,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k1_enumset1(sK2,sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_5524,c_543])).

cnf(c_6970,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k5_xboole_0(X1,X0),k1_enumset1(sK2,sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_6952,c_5590])).

cnf(c_6877,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))),X0)) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2896,c_545])).

cnf(c_6999,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0))) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_6877,c_2895,c_4140,c_6040])).

cnf(c_7471,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)),k1_enumset1(sK2,sK2,sK3)) = k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2896,c_6999])).

cnf(c_7536,plain,
    ( k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0)) = k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_7471,c_545])).

cnf(c_7833,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))) = k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_7536,c_1])).

cnf(c_7826,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4963,c_7536])).

cnf(c_6911,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4963,c_545])).

cnf(c_6980,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X2,X1)) = X2 ),
    inference(demodulation,[status(thm)],[c_6911,c_525])).

cnf(c_7859,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)) = sK4 ),
    inference(demodulation,[status(thm)],[c_7826,c_525,c_6980])).

cnf(c_8385,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),sK4) = k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) ),
    inference(light_normalisation,[status(thm)],[c_7833,c_7859])).

cnf(c_5589,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,X0))) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_5524,c_12])).

cnf(c_13492,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,X0)),X1)) = k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),X1) ),
    inference(superposition,[status(thm)],[c_5589,c_12])).

cnf(c_2835,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))),k1_enumset1(sK2,sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_245,c_1113])).

cnf(c_2874,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2835,c_1772])).

cnf(c_3292,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2874,c_12])).

cnf(c_3293,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3292,c_954])).

cnf(c_7483,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3)) = k5_xboole_0(sK4,k5_xboole_0(sK4,sK4)) ),
    inference(superposition,[status(thm)],[c_2101,c_6999])).

cnf(c_7502,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3)) = sK4 ),
    inference(demodulation,[status(thm)],[c_7483,c_1117,c_6040])).

cnf(c_10145,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(sK4,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3293,c_3293,c_7502])).

cnf(c_10180,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,X0),X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_10145,c_12])).

cnf(c_11658,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK4,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_543,c_10180])).

cnf(c_11725,plain,
    ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK4,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_11658,c_12])).

cnf(c_13528,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),X1) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_13492,c_11725])).

cnf(c_17649,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(demodulation,[status(thm)],[c_17592,c_5461,c_6970,c_8385,c_13528])).

cnf(c_17650,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) ),
    inference(light_normalisation,[status(thm)],[c_17649,c_13])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_247,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_12,c_1])).

cnf(c_521,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_71334,plain,
    ( r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17650,c_521])).

cnf(c_71502,plain,
    ( r2_hidden(sK2,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top
    | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_71334])).

cnf(c_11,plain,
    ( r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_246,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X1)))),k5_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_11,c_12,c_1])).

cnf(c_517,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X1)))),k5_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_45095,plain,
    ( r1_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))))),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_517])).

cnf(c_38380,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
    inference(superposition,[status(thm)],[c_12,c_1117])).

cnf(c_45107,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)))) = k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)) ),
    inference(superposition,[status(thm)],[c_1772,c_38380])).

cnf(c_2834,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_1113])).

cnf(c_8690,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X2,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_2834])).

cnf(c_18277,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)))),k5_xboole_0(sK4,k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2896,c_8690])).

cnf(c_18412,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))),k5_xboole_0(sK4,k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18277,c_4140])).

cnf(c_20658,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3))),k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18412,c_1])).

cnf(c_35703,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)))) = k5_xboole_0(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_20658,c_10180])).

cnf(c_35730,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)))) = sK4 ),
    inference(demodulation,[status(thm)],[c_35703,c_525,c_13528])).

cnf(c_45204,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_45107,c_35730])).

cnf(c_45994,plain,
    ( r1_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,sK4)),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_45095,c_45204])).

cnf(c_45995,plain,
    ( r1_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_45994,c_13,c_525])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_520,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_67086,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_45995,c_520])).

cnf(c_67088,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_67086])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1019,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,sK4))
    | r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_41045,plain,
    ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK3))
    | r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4))
    | r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_41046,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41045])).

cnf(c_41048,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_41046])).

cnf(c_19,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_39450,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_39451,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39450])).

cnf(c_2327,plain,
    ( k5_xboole_0(sK4,sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_257,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_598,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k5_xboole_0(X2,sK4))
    | k5_xboole_0(X2,sK4) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_257])).

cnf(c_1258,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k5_xboole_0(sK4,sK4))
    | k5_xboole_0(sK4,sK4) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_1529,plain,
    ( ~ r2_hidden(X0,k1_xboole_0)
    | r2_hidden(sK2,k5_xboole_0(sK4,sK4))
    | k5_xboole_0(sK4,sK4) != k1_xboole_0
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1258])).

cnf(c_1530,plain,
    ( k5_xboole_0(sK4,sK4) != k1_xboole_0
    | sK2 != X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK2,k5_xboole_0(sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1529])).

cnf(c_1532,plain,
    ( k5_xboole_0(sK4,sK4) != k1_xboole_0
    | sK2 != sK2
    | r2_hidden(sK2,k5_xboole_0(sK4,sK4)) = iProver_top
    | r2_hidden(sK2,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_553,plain,
    ( r2_hidden(sK2,X0)
    | ~ r2_hidden(sK2,k5_xboole_0(X0,sK4))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_247])).

cnf(c_821,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK4,sK4))
    | r2_hidden(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_822,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK4,sK4)) != iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_20,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_35,plain,
    ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_32,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_71502,c_67088,c_41048,c_39451,c_2327,c_1532,c_822,c_35,c_32,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:55:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 19.45/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.45/2.98  
% 19.45/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.45/2.98  
% 19.45/2.98  ------  iProver source info
% 19.45/2.98  
% 19.45/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.45/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.45/2.98  git: non_committed_changes: false
% 19.45/2.98  git: last_make_outside_of_git: false
% 19.45/2.98  
% 19.45/2.98  ------ 
% 19.45/2.98  
% 19.45/2.98  ------ Input Options
% 19.45/2.98  
% 19.45/2.98  --out_options                           all
% 19.45/2.98  --tptp_safe_out                         true
% 19.45/2.98  --problem_path                          ""
% 19.45/2.98  --include_path                          ""
% 19.45/2.98  --clausifier                            res/vclausify_rel
% 19.45/2.98  --clausifier_options                    ""
% 19.45/2.98  --stdin                                 false
% 19.45/2.98  --stats_out                             all
% 19.45/2.98  
% 19.45/2.98  ------ General Options
% 19.45/2.98  
% 19.45/2.98  --fof                                   false
% 19.45/2.98  --time_out_real                         305.
% 19.45/2.98  --time_out_virtual                      -1.
% 19.45/2.98  --symbol_type_check                     false
% 19.45/2.98  --clausify_out                          false
% 19.45/2.98  --sig_cnt_out                           false
% 19.45/2.98  --trig_cnt_out                          false
% 19.45/2.98  --trig_cnt_out_tolerance                1.
% 19.45/2.98  --trig_cnt_out_sk_spl                   false
% 19.45/2.98  --abstr_cl_out                          false
% 19.45/2.98  
% 19.45/2.98  ------ Global Options
% 19.45/2.98  
% 19.45/2.98  --schedule                              default
% 19.45/2.98  --add_important_lit                     false
% 19.45/2.98  --prop_solver_per_cl                    1000
% 19.45/2.98  --min_unsat_core                        false
% 19.45/2.98  --soft_assumptions                      false
% 19.45/2.98  --soft_lemma_size                       3
% 19.45/2.98  --prop_impl_unit_size                   0
% 19.45/2.98  --prop_impl_unit                        []
% 19.45/2.98  --share_sel_clauses                     true
% 19.45/2.98  --reset_solvers                         false
% 19.45/2.98  --bc_imp_inh                            [conj_cone]
% 19.45/2.98  --conj_cone_tolerance                   3.
% 19.45/2.98  --extra_neg_conj                        none
% 19.45/2.98  --large_theory_mode                     true
% 19.45/2.98  --prolific_symb_bound                   200
% 19.45/2.98  --lt_threshold                          2000
% 19.45/2.98  --clause_weak_htbl                      true
% 19.45/2.98  --gc_record_bc_elim                     false
% 19.45/2.98  
% 19.45/2.98  ------ Preprocessing Options
% 19.45/2.98  
% 19.45/2.98  --preprocessing_flag                    true
% 19.45/2.98  --time_out_prep_mult                    0.1
% 19.45/2.98  --splitting_mode                        input
% 19.45/2.98  --splitting_grd                         true
% 19.45/2.98  --splitting_cvd                         false
% 19.45/2.98  --splitting_cvd_svl                     false
% 19.45/2.98  --splitting_nvd                         32
% 19.45/2.98  --sub_typing                            true
% 19.45/2.98  --prep_gs_sim                           true
% 19.45/2.98  --prep_unflatten                        true
% 19.45/2.98  --prep_res_sim                          true
% 19.45/2.98  --prep_upred                            true
% 19.45/2.98  --prep_sem_filter                       exhaustive
% 19.45/2.98  --prep_sem_filter_out                   false
% 19.45/2.98  --pred_elim                             true
% 19.45/2.98  --res_sim_input                         true
% 19.45/2.98  --eq_ax_congr_red                       true
% 19.45/2.98  --pure_diseq_elim                       true
% 19.45/2.98  --brand_transform                       false
% 19.45/2.98  --non_eq_to_eq                          false
% 19.45/2.98  --prep_def_merge                        true
% 19.45/2.98  --prep_def_merge_prop_impl              false
% 19.45/2.98  --prep_def_merge_mbd                    true
% 19.45/2.98  --prep_def_merge_tr_red                 false
% 19.45/2.98  --prep_def_merge_tr_cl                  false
% 19.45/2.98  --smt_preprocessing                     true
% 19.45/2.98  --smt_ac_axioms                         fast
% 19.45/2.98  --preprocessed_out                      false
% 19.45/2.98  --preprocessed_stats                    false
% 19.45/2.98  
% 19.45/2.98  ------ Abstraction refinement Options
% 19.45/2.98  
% 19.45/2.98  --abstr_ref                             []
% 19.45/2.98  --abstr_ref_prep                        false
% 19.45/2.98  --abstr_ref_until_sat                   false
% 19.45/2.98  --abstr_ref_sig_restrict                funpre
% 19.45/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.45/2.98  --abstr_ref_under                       []
% 19.45/2.98  
% 19.45/2.98  ------ SAT Options
% 19.45/2.98  
% 19.45/2.98  --sat_mode                              false
% 19.45/2.98  --sat_fm_restart_options                ""
% 19.45/2.98  --sat_gr_def                            false
% 19.45/2.98  --sat_epr_types                         true
% 19.45/2.98  --sat_non_cyclic_types                  false
% 19.45/2.98  --sat_finite_models                     false
% 19.45/2.98  --sat_fm_lemmas                         false
% 19.45/2.98  --sat_fm_prep                           false
% 19.45/2.98  --sat_fm_uc_incr                        true
% 19.45/2.98  --sat_out_model                         small
% 19.45/2.98  --sat_out_clauses                       false
% 19.45/2.98  
% 19.45/2.98  ------ QBF Options
% 19.45/2.98  
% 19.45/2.98  --qbf_mode                              false
% 19.45/2.98  --qbf_elim_univ                         false
% 19.45/2.98  --qbf_dom_inst                          none
% 19.45/2.98  --qbf_dom_pre_inst                      false
% 19.45/2.98  --qbf_sk_in                             false
% 19.45/2.98  --qbf_pred_elim                         true
% 19.45/2.98  --qbf_split                             512
% 19.45/2.98  
% 19.45/2.98  ------ BMC1 Options
% 19.45/2.98  
% 19.45/2.98  --bmc1_incremental                      false
% 19.45/2.98  --bmc1_axioms                           reachable_all
% 19.45/2.98  --bmc1_min_bound                        0
% 19.45/2.98  --bmc1_max_bound                        -1
% 19.45/2.98  --bmc1_max_bound_default                -1
% 19.45/2.98  --bmc1_symbol_reachability              true
% 19.45/2.98  --bmc1_property_lemmas                  false
% 19.45/2.98  --bmc1_k_induction                      false
% 19.45/2.98  --bmc1_non_equiv_states                 false
% 19.45/2.98  --bmc1_deadlock                         false
% 19.45/2.98  --bmc1_ucm                              false
% 19.45/2.98  --bmc1_add_unsat_core                   none
% 19.45/2.98  --bmc1_unsat_core_children              false
% 19.45/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.45/2.98  --bmc1_out_stat                         full
% 19.45/2.98  --bmc1_ground_init                      false
% 19.45/2.98  --bmc1_pre_inst_next_state              false
% 19.45/2.98  --bmc1_pre_inst_state                   false
% 19.45/2.98  --bmc1_pre_inst_reach_state             false
% 19.45/2.98  --bmc1_out_unsat_core                   false
% 19.45/2.98  --bmc1_aig_witness_out                  false
% 19.45/2.98  --bmc1_verbose                          false
% 19.45/2.98  --bmc1_dump_clauses_tptp                false
% 19.45/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.45/2.98  --bmc1_dump_file                        -
% 19.45/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.45/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.45/2.98  --bmc1_ucm_extend_mode                  1
% 19.45/2.98  --bmc1_ucm_init_mode                    2
% 19.45/2.98  --bmc1_ucm_cone_mode                    none
% 19.45/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.45/2.98  --bmc1_ucm_relax_model                  4
% 19.45/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.45/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.45/2.98  --bmc1_ucm_layered_model                none
% 19.45/2.98  --bmc1_ucm_max_lemma_size               10
% 19.45/2.98  
% 19.45/2.98  ------ AIG Options
% 19.45/2.98  
% 19.45/2.98  --aig_mode                              false
% 19.45/2.98  
% 19.45/2.98  ------ Instantiation Options
% 19.45/2.98  
% 19.45/2.98  --instantiation_flag                    true
% 19.45/2.98  --inst_sos_flag                         true
% 19.45/2.98  --inst_sos_phase                        true
% 19.45/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.45/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.45/2.98  --inst_lit_sel_side                     num_symb
% 19.45/2.98  --inst_solver_per_active                1400
% 19.45/2.98  --inst_solver_calls_frac                1.
% 19.45/2.98  --inst_passive_queue_type               priority_queues
% 19.45/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.45/2.98  --inst_passive_queues_freq              [25;2]
% 19.45/2.98  --inst_dismatching                      true
% 19.45/2.98  --inst_eager_unprocessed_to_passive     true
% 19.45/2.98  --inst_prop_sim_given                   true
% 19.45/2.98  --inst_prop_sim_new                     false
% 19.45/2.98  --inst_subs_new                         false
% 19.45/2.98  --inst_eq_res_simp                      false
% 19.45/2.98  --inst_subs_given                       false
% 19.45/2.98  --inst_orphan_elimination               true
% 19.45/2.98  --inst_learning_loop_flag               true
% 19.45/2.98  --inst_learning_start                   3000
% 19.45/2.98  --inst_learning_factor                  2
% 19.45/2.98  --inst_start_prop_sim_after_learn       3
% 19.45/2.98  --inst_sel_renew                        solver
% 19.45/2.98  --inst_lit_activity_flag                true
% 19.45/2.98  --inst_restr_to_given                   false
% 19.45/2.98  --inst_activity_threshold               500
% 19.45/2.98  --inst_out_proof                        true
% 19.45/2.98  
% 19.45/2.98  ------ Resolution Options
% 19.45/2.98  
% 19.45/2.98  --resolution_flag                       true
% 19.45/2.98  --res_lit_sel                           adaptive
% 19.45/2.98  --res_lit_sel_side                      none
% 19.45/2.98  --res_ordering                          kbo
% 19.45/2.98  --res_to_prop_solver                    active
% 19.45/2.98  --res_prop_simpl_new                    false
% 19.45/2.98  --res_prop_simpl_given                  true
% 19.45/2.98  --res_passive_queue_type                priority_queues
% 19.45/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.45/2.98  --res_passive_queues_freq               [15;5]
% 19.45/2.98  --res_forward_subs                      full
% 19.45/2.98  --res_backward_subs                     full
% 19.45/2.98  --res_forward_subs_resolution           true
% 19.45/2.98  --res_backward_subs_resolution          true
% 19.45/2.98  --res_orphan_elimination                true
% 19.45/2.98  --res_time_limit                        2.
% 19.45/2.98  --res_out_proof                         true
% 19.45/2.98  
% 19.45/2.98  ------ Superposition Options
% 19.45/2.98  
% 19.45/2.98  --superposition_flag                    true
% 19.45/2.98  --sup_passive_queue_type                priority_queues
% 19.45/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.45/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.45/2.98  --demod_completeness_check              fast
% 19.45/2.98  --demod_use_ground                      true
% 19.45/2.98  --sup_to_prop_solver                    passive
% 19.45/2.98  --sup_prop_simpl_new                    true
% 19.45/2.98  --sup_prop_simpl_given                  true
% 19.45/2.98  --sup_fun_splitting                     true
% 19.45/2.98  --sup_smt_interval                      50000
% 19.45/2.98  
% 19.45/2.98  ------ Superposition Simplification Setup
% 19.45/2.98  
% 19.45/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.45/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.45/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.45/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.45/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.45/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.45/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.45/2.98  --sup_immed_triv                        [TrivRules]
% 19.45/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.45/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.45/2.98  --sup_immed_bw_main                     []
% 19.45/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.45/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.45/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.45/2.98  --sup_input_bw                          []
% 19.45/2.98  
% 19.45/2.98  ------ Combination Options
% 19.45/2.98  
% 19.45/2.98  --comb_res_mult                         3
% 19.45/2.98  --comb_sup_mult                         2
% 19.45/2.98  --comb_inst_mult                        10
% 19.45/2.98  
% 19.45/2.98  ------ Debug Options
% 19.45/2.98  
% 19.45/2.98  --dbg_backtrace                         false
% 19.45/2.98  --dbg_dump_prop_clauses                 false
% 19.45/2.98  --dbg_dump_prop_clauses_file            -
% 19.45/2.98  --dbg_out_stat                          false
% 19.45/2.98  ------ Parsing...
% 19.45/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.45/2.98  
% 19.45/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.45/2.98  
% 19.45/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.45/2.98  
% 19.45/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.45/2.98  ------ Proving...
% 19.45/2.98  ------ Problem Properties 
% 19.45/2.98  
% 19.45/2.98  
% 19.45/2.98  clauses                                 27
% 19.45/2.98  conjectures                             2
% 19.45/2.98  EPR                                     2
% 19.45/2.98  Horn                                    20
% 19.45/2.98  unary                                   15
% 19.45/2.98  binary                                  2
% 19.45/2.98  lits                                    52
% 19.45/2.98  lits eq                                 23
% 19.45/2.98  fd_pure                                 0
% 19.45/2.98  fd_pseudo                               0
% 19.45/2.98  fd_cond                                 0
% 19.45/2.98  fd_pseudo_cond                          4
% 19.45/2.98  AC symbols                              1
% 19.45/2.98  
% 19.45/2.98  ------ Schedule dynamic 5 is on 
% 19.45/2.98  
% 19.45/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.45/2.98  
% 19.45/2.98  
% 19.45/2.98  ------ 
% 19.45/2.98  Current options:
% 19.45/2.98  ------ 
% 19.45/2.98  
% 19.45/2.98  ------ Input Options
% 19.45/2.98  
% 19.45/2.98  --out_options                           all
% 19.45/2.98  --tptp_safe_out                         true
% 19.45/2.98  --problem_path                          ""
% 19.45/2.98  --include_path                          ""
% 19.45/2.98  --clausifier                            res/vclausify_rel
% 19.45/2.98  --clausifier_options                    ""
% 19.45/2.98  --stdin                                 false
% 19.45/2.98  --stats_out                             all
% 19.45/2.98  
% 19.45/2.98  ------ General Options
% 19.45/2.98  
% 19.45/2.98  --fof                                   false
% 19.45/2.98  --time_out_real                         305.
% 19.45/2.98  --time_out_virtual                      -1.
% 19.45/2.98  --symbol_type_check                     false
% 19.45/2.98  --clausify_out                          false
% 19.45/2.98  --sig_cnt_out                           false
% 19.45/2.98  --trig_cnt_out                          false
% 19.45/2.98  --trig_cnt_out_tolerance                1.
% 19.45/2.98  --trig_cnt_out_sk_spl                   false
% 19.45/2.98  --abstr_cl_out                          false
% 19.45/2.98  
% 19.45/2.98  ------ Global Options
% 19.45/2.98  
% 19.45/2.98  --schedule                              default
% 19.45/2.98  --add_important_lit                     false
% 19.45/2.98  --prop_solver_per_cl                    1000
% 19.45/2.98  --min_unsat_core                        false
% 19.45/2.98  --soft_assumptions                      false
% 19.45/2.98  --soft_lemma_size                       3
% 19.45/2.98  --prop_impl_unit_size                   0
% 19.45/2.98  --prop_impl_unit                        []
% 19.45/2.98  --share_sel_clauses                     true
% 19.45/2.98  --reset_solvers                         false
% 19.45/2.98  --bc_imp_inh                            [conj_cone]
% 19.45/2.98  --conj_cone_tolerance                   3.
% 19.45/2.98  --extra_neg_conj                        none
% 19.45/2.98  --large_theory_mode                     true
% 19.45/2.98  --prolific_symb_bound                   200
% 19.45/2.98  --lt_threshold                          2000
% 19.45/2.98  --clause_weak_htbl                      true
% 19.45/2.98  --gc_record_bc_elim                     false
% 19.45/2.98  
% 19.45/2.98  ------ Preprocessing Options
% 19.45/2.98  
% 19.45/2.98  --preprocessing_flag                    true
% 19.45/2.98  --time_out_prep_mult                    0.1
% 19.45/2.98  --splitting_mode                        input
% 19.45/2.98  --splitting_grd                         true
% 19.45/2.98  --splitting_cvd                         false
% 19.45/2.98  --splitting_cvd_svl                     false
% 19.45/2.98  --splitting_nvd                         32
% 19.45/2.98  --sub_typing                            true
% 19.45/2.98  --prep_gs_sim                           true
% 19.45/2.98  --prep_unflatten                        true
% 19.45/2.98  --prep_res_sim                          true
% 19.45/2.98  --prep_upred                            true
% 19.45/2.98  --prep_sem_filter                       exhaustive
% 19.45/2.98  --prep_sem_filter_out                   false
% 19.45/2.98  --pred_elim                             true
% 19.45/2.98  --res_sim_input                         true
% 19.45/2.98  --eq_ax_congr_red                       true
% 19.45/2.98  --pure_diseq_elim                       true
% 19.45/2.98  --brand_transform                       false
% 19.45/2.98  --non_eq_to_eq                          false
% 19.45/2.98  --prep_def_merge                        true
% 19.45/2.98  --prep_def_merge_prop_impl              false
% 19.45/2.98  --prep_def_merge_mbd                    true
% 19.45/2.98  --prep_def_merge_tr_red                 false
% 19.45/2.98  --prep_def_merge_tr_cl                  false
% 19.45/2.98  --smt_preprocessing                     true
% 19.45/2.98  --smt_ac_axioms                         fast
% 19.45/2.98  --preprocessed_out                      false
% 19.45/2.98  --preprocessed_stats                    false
% 19.45/2.98  
% 19.45/2.98  ------ Abstraction refinement Options
% 19.45/2.98  
% 19.45/2.98  --abstr_ref                             []
% 19.45/2.98  --abstr_ref_prep                        false
% 19.45/2.98  --abstr_ref_until_sat                   false
% 19.45/2.98  --abstr_ref_sig_restrict                funpre
% 19.45/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.45/2.98  --abstr_ref_under                       []
% 19.45/2.98  
% 19.45/2.98  ------ SAT Options
% 19.45/2.98  
% 19.45/2.98  --sat_mode                              false
% 19.45/2.98  --sat_fm_restart_options                ""
% 19.45/2.98  --sat_gr_def                            false
% 19.45/2.98  --sat_epr_types                         true
% 19.45/2.98  --sat_non_cyclic_types                  false
% 19.45/2.98  --sat_finite_models                     false
% 19.45/2.98  --sat_fm_lemmas                         false
% 19.45/2.98  --sat_fm_prep                           false
% 19.45/2.98  --sat_fm_uc_incr                        true
% 19.45/2.98  --sat_out_model                         small
% 19.45/2.98  --sat_out_clauses                       false
% 19.45/2.98  
% 19.45/2.98  ------ QBF Options
% 19.45/2.98  
% 19.45/2.98  --qbf_mode                              false
% 19.45/2.98  --qbf_elim_univ                         false
% 19.45/2.98  --qbf_dom_inst                          none
% 19.45/2.98  --qbf_dom_pre_inst                      false
% 19.45/2.98  --qbf_sk_in                             false
% 19.45/2.98  --qbf_pred_elim                         true
% 19.45/2.98  --qbf_split                             512
% 19.45/2.98  
% 19.45/2.98  ------ BMC1 Options
% 19.45/2.98  
% 19.45/2.98  --bmc1_incremental                      false
% 19.45/2.98  --bmc1_axioms                           reachable_all
% 19.45/2.98  --bmc1_min_bound                        0
% 19.45/2.98  --bmc1_max_bound                        -1
% 19.45/2.98  --bmc1_max_bound_default                -1
% 19.45/2.98  --bmc1_symbol_reachability              true
% 19.45/2.98  --bmc1_property_lemmas                  false
% 19.45/2.98  --bmc1_k_induction                      false
% 19.45/2.98  --bmc1_non_equiv_states                 false
% 19.45/2.98  --bmc1_deadlock                         false
% 19.45/2.98  --bmc1_ucm                              false
% 19.45/2.98  --bmc1_add_unsat_core                   none
% 19.45/2.98  --bmc1_unsat_core_children              false
% 19.45/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.45/2.98  --bmc1_out_stat                         full
% 19.45/2.98  --bmc1_ground_init                      false
% 19.45/2.98  --bmc1_pre_inst_next_state              false
% 19.45/2.98  --bmc1_pre_inst_state                   false
% 19.45/2.98  --bmc1_pre_inst_reach_state             false
% 19.45/2.98  --bmc1_out_unsat_core                   false
% 19.45/2.98  --bmc1_aig_witness_out                  false
% 19.45/2.98  --bmc1_verbose                          false
% 19.45/2.98  --bmc1_dump_clauses_tptp                false
% 19.45/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.45/2.98  --bmc1_dump_file                        -
% 19.45/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.45/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.45/2.98  --bmc1_ucm_extend_mode                  1
% 19.45/2.98  --bmc1_ucm_init_mode                    2
% 19.45/2.98  --bmc1_ucm_cone_mode                    none
% 19.45/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.45/2.98  --bmc1_ucm_relax_model                  4
% 19.45/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.45/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.45/2.98  --bmc1_ucm_layered_model                none
% 19.45/2.98  --bmc1_ucm_max_lemma_size               10
% 19.45/2.98  
% 19.45/2.98  ------ AIG Options
% 19.45/2.98  
% 19.45/2.98  --aig_mode                              false
% 19.45/2.98  
% 19.45/2.98  ------ Instantiation Options
% 19.45/2.98  
% 19.45/2.98  --instantiation_flag                    true
% 19.45/2.98  --inst_sos_flag                         true
% 19.45/2.98  --inst_sos_phase                        true
% 19.45/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.45/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.45/2.98  --inst_lit_sel_side                     none
% 19.45/2.98  --inst_solver_per_active                1400
% 19.45/2.98  --inst_solver_calls_frac                1.
% 19.45/2.98  --inst_passive_queue_type               priority_queues
% 19.45/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.45/2.98  --inst_passive_queues_freq              [25;2]
% 19.45/2.98  --inst_dismatching                      true
% 19.45/2.98  --inst_eager_unprocessed_to_passive     true
% 19.45/2.98  --inst_prop_sim_given                   true
% 19.45/2.98  --inst_prop_sim_new                     false
% 19.45/2.98  --inst_subs_new                         false
% 19.45/2.98  --inst_eq_res_simp                      false
% 19.45/2.98  --inst_subs_given                       false
% 19.45/2.98  --inst_orphan_elimination               true
% 19.45/2.98  --inst_learning_loop_flag               true
% 19.45/2.98  --inst_learning_start                   3000
% 19.45/2.98  --inst_learning_factor                  2
% 19.45/2.98  --inst_start_prop_sim_after_learn       3
% 19.45/2.98  --inst_sel_renew                        solver
% 19.45/2.98  --inst_lit_activity_flag                true
% 19.45/2.98  --inst_restr_to_given                   false
% 19.45/2.98  --inst_activity_threshold               500
% 19.45/2.98  --inst_out_proof                        true
% 19.45/2.98  
% 19.45/2.98  ------ Resolution Options
% 19.45/2.98  
% 19.45/2.98  --resolution_flag                       false
% 19.45/2.98  --res_lit_sel                           adaptive
% 19.45/2.98  --res_lit_sel_side                      none
% 19.45/2.98  --res_ordering                          kbo
% 19.45/2.98  --res_to_prop_solver                    active
% 19.45/2.98  --res_prop_simpl_new                    false
% 19.45/2.98  --res_prop_simpl_given                  true
% 19.45/2.98  --res_passive_queue_type                priority_queues
% 19.45/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.45/2.98  --res_passive_queues_freq               [15;5]
% 19.45/2.98  --res_forward_subs                      full
% 19.45/2.98  --res_backward_subs                     full
% 19.45/2.98  --res_forward_subs_resolution           true
% 19.45/2.98  --res_backward_subs_resolution          true
% 19.45/2.98  --res_orphan_elimination                true
% 19.45/2.98  --res_time_limit                        2.
% 19.45/2.98  --res_out_proof                         true
% 19.45/2.98  
% 19.45/2.98  ------ Superposition Options
% 19.45/2.98  
% 19.45/2.98  --superposition_flag                    true
% 19.45/2.98  --sup_passive_queue_type                priority_queues
% 19.45/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.45/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.45/2.98  --demod_completeness_check              fast
% 19.45/2.98  --demod_use_ground                      true
% 19.45/2.98  --sup_to_prop_solver                    passive
% 19.45/2.98  --sup_prop_simpl_new                    true
% 19.45/2.98  --sup_prop_simpl_given                  true
% 19.45/2.98  --sup_fun_splitting                     true
% 19.45/2.98  --sup_smt_interval                      50000
% 19.45/2.98  
% 19.45/2.98  ------ Superposition Simplification Setup
% 19.45/2.98  
% 19.45/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.45/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.45/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.45/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.45/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.45/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.45/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.45/2.98  --sup_immed_triv                        [TrivRules]
% 19.45/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.45/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.45/2.98  --sup_immed_bw_main                     []
% 19.45/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.45/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.45/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.45/2.98  --sup_input_bw                          []
% 19.45/2.98  
% 19.45/2.98  ------ Combination Options
% 19.45/2.98  
% 19.45/2.98  --comb_res_mult                         3
% 19.45/2.98  --comb_sup_mult                         2
% 19.45/2.98  --comb_inst_mult                        10
% 19.45/2.98  
% 19.45/2.98  ------ Debug Options
% 19.45/2.98  
% 19.45/2.98  --dbg_backtrace                         false
% 19.45/2.98  --dbg_dump_prop_clauses                 false
% 19.45/2.98  --dbg_dump_prop_clauses_file            -
% 19.45/2.98  --dbg_out_stat                          false
% 19.45/2.98  
% 19.45/2.98  
% 19.45/2.98  
% 19.45/2.98  
% 19.45/2.98  ------ Proving...
% 19.45/2.98  
% 19.45/2.98  
% 19.45/2.98  % SZS status Theorem for theBenchmark.p
% 19.45/2.98  
% 19.45/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.45/2.98  
% 19.45/2.98  fof(f1,axiom,(
% 19.45/2.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f40,plain,(
% 19.45/2.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f1])).
% 19.45/2.98  
% 19.45/2.98  fof(f7,axiom,(
% 19.45/2.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f51,plain,(
% 19.45/2.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f7])).
% 19.45/2.98  
% 19.45/2.98  fof(f8,axiom,(
% 19.45/2.98    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f52,plain,(
% 19.45/2.98    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 19.45/2.98    inference(cnf_transformation,[],[f8])).
% 19.45/2.98  
% 19.45/2.98  fof(f13,axiom,(
% 19.45/2.98    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f64,plain,(
% 19.45/2.98    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f13])).
% 19.45/2.98  
% 19.45/2.98  fof(f20,axiom,(
% 19.45/2.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f71,plain,(
% 19.45/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.45/2.98    inference(cnf_transformation,[],[f20])).
% 19.45/2.98  
% 19.45/2.98  fof(f74,plain,(
% 19.45/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 19.45/2.98    inference(definition_unfolding,[],[f71,f66])).
% 19.45/2.98  
% 19.45/2.98  fof(f14,axiom,(
% 19.45/2.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f65,plain,(
% 19.45/2.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f14])).
% 19.45/2.98  
% 19.45/2.98  fof(f15,axiom,(
% 19.45/2.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f66,plain,(
% 19.45/2.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f15])).
% 19.45/2.98  
% 19.45/2.98  fof(f77,plain,(
% 19.45/2.98    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 19.45/2.98    inference(definition_unfolding,[],[f65,f66])).
% 19.45/2.98  
% 19.45/2.98  fof(f79,plain,(
% 19.45/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 19.45/2.98    inference(definition_unfolding,[],[f64,f74,f66,f77])).
% 19.45/2.98  
% 19.45/2.98  fof(f16,axiom,(
% 19.45/2.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f67,plain,(
% 19.45/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f16])).
% 19.45/2.98  
% 19.45/2.98  fof(f11,axiom,(
% 19.45/2.98    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f62,plain,(
% 19.45/2.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f11])).
% 19.45/2.98  
% 19.45/2.98  fof(f76,plain,(
% 19.45/2.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 19.45/2.98    inference(definition_unfolding,[],[f62,f74,f66,f66])).
% 19.45/2.98  
% 19.45/2.98  fof(f84,plain,(
% 19.45/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)))) )),
% 19.45/2.98    inference(definition_unfolding,[],[f67,f76])).
% 19.45/2.98  
% 19.45/2.98  fof(f21,conjecture,(
% 19.45/2.98    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f22,negated_conjecture,(
% 19.45/2.98    ~! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 19.45/2.98    inference(negated_conjecture,[],[f21])).
% 19.45/2.98  
% 19.45/2.98  fof(f29,plain,(
% 19.45/2.98    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))),
% 19.45/2.98    inference(ennf_transformation,[],[f22])).
% 19.45/2.98  
% 19.45/2.98  fof(f38,plain,(
% 19.45/2.98    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)) => (~r2_hidden(sK2,sK4) & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3))),
% 19.45/2.98    introduced(choice_axiom,[])).
% 19.45/2.98  
% 19.45/2.98  fof(f39,plain,(
% 19.45/2.98    ~r2_hidden(sK2,sK4) & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 19.45/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f38])).
% 19.45/2.98  
% 19.45/2.98  fof(f72,plain,(
% 19.45/2.98    k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 19.45/2.98    inference(cnf_transformation,[],[f39])).
% 19.45/2.98  
% 19.45/2.98  fof(f9,axiom,(
% 19.45/2.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f53,plain,(
% 19.45/2.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f9])).
% 19.45/2.98  
% 19.45/2.98  fof(f75,plain,(
% 19.45/2.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 19.45/2.98    inference(definition_unfolding,[],[f53,f74])).
% 19.45/2.98  
% 19.45/2.98  fof(f86,plain,(
% 19.45/2.98    k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))) = k1_enumset1(sK2,sK2,sK3)),
% 19.45/2.98    inference(definition_unfolding,[],[f72,f75,f66,f66])).
% 19.45/2.98  
% 19.45/2.98  fof(f3,axiom,(
% 19.45/2.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f24,plain,(
% 19.45/2.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 19.45/2.98    inference(rectify,[],[f3])).
% 19.45/2.98  
% 19.45/2.98  fof(f42,plain,(
% 19.45/2.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 19.45/2.98    inference(cnf_transformation,[],[f24])).
% 19.45/2.98  
% 19.45/2.98  fof(f81,plain,(
% 19.45/2.98    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k1_enumset1(X0,X0,X0))) = X0) )),
% 19.45/2.98    inference(definition_unfolding,[],[f42,f75])).
% 19.45/2.98  
% 19.45/2.98  fof(f2,axiom,(
% 19.45/2.98    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f23,plain,(
% 19.45/2.98    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 19.45/2.98    inference(rectify,[],[f2])).
% 19.45/2.98  
% 19.45/2.98  fof(f41,plain,(
% 19.45/2.98    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 19.45/2.98    inference(cnf_transformation,[],[f23])).
% 19.45/2.98  
% 19.45/2.98  fof(f80,plain,(
% 19.45/2.98    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 19.45/2.98    inference(definition_unfolding,[],[f41,f74])).
% 19.45/2.98  
% 19.45/2.98  fof(f4,axiom,(
% 19.45/2.98    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f26,plain,(
% 19.45/2.98    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 19.45/2.98    inference(ennf_transformation,[],[f4])).
% 19.45/2.98  
% 19.45/2.98  fof(f30,plain,(
% 19.45/2.98    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 19.45/2.98    inference(nnf_transformation,[],[f26])).
% 19.45/2.98  
% 19.45/2.98  fof(f43,plain,(
% 19.45/2.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 19.45/2.98    inference(cnf_transformation,[],[f30])).
% 19.45/2.98  
% 19.45/2.98  fof(f6,axiom,(
% 19.45/2.98    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f50,plain,(
% 19.45/2.98    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 19.45/2.98    inference(cnf_transformation,[],[f6])).
% 19.45/2.98  
% 19.45/2.98  fof(f82,plain,(
% 19.45/2.98    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))),k5_xboole_0(X0,X1))) )),
% 19.45/2.98    inference(definition_unfolding,[],[f50,f75])).
% 19.45/2.98  
% 19.45/2.98  fof(f5,axiom,(
% 19.45/2.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f25,plain,(
% 19.45/2.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.45/2.98    inference(rectify,[],[f5])).
% 19.45/2.98  
% 19.45/2.98  fof(f27,plain,(
% 19.45/2.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.45/2.98    inference(ennf_transformation,[],[f25])).
% 19.45/2.98  
% 19.45/2.98  fof(f31,plain,(
% 19.45/2.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.45/2.98    introduced(choice_axiom,[])).
% 19.45/2.98  
% 19.45/2.98  fof(f32,plain,(
% 19.45/2.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.45/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f31])).
% 19.45/2.98  
% 19.45/2.98  fof(f49,plain,(
% 19.45/2.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f32])).
% 19.45/2.98  
% 19.45/2.98  fof(f45,plain,(
% 19.45/2.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 19.45/2.98    inference(cnf_transformation,[],[f30])).
% 19.45/2.98  
% 19.45/2.98  fof(f10,axiom,(
% 19.45/2.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 19.45/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.45/2.98  
% 19.45/2.98  fof(f28,plain,(
% 19.45/2.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 19.45/2.98    inference(ennf_transformation,[],[f10])).
% 19.45/2.98  
% 19.45/2.98  fof(f33,plain,(
% 19.45/2.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.45/2.98    inference(nnf_transformation,[],[f28])).
% 19.45/2.98  
% 19.45/2.98  fof(f34,plain,(
% 19.45/2.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.45/2.98    inference(flattening,[],[f33])).
% 19.45/2.98  
% 19.45/2.98  fof(f35,plain,(
% 19.45/2.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.45/2.98    inference(rectify,[],[f34])).
% 19.45/2.98  
% 19.45/2.98  fof(f36,plain,(
% 19.45/2.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 19.45/2.98    introduced(choice_axiom,[])).
% 19.45/2.98  
% 19.45/2.98  fof(f37,plain,(
% 19.45/2.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 19.45/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 19.45/2.98  
% 19.45/2.98  fof(f56,plain,(
% 19.45/2.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 19.45/2.98    inference(cnf_transformation,[],[f37])).
% 19.45/2.98  
% 19.45/2.98  fof(f89,plain,(
% 19.45/2.98    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 19.45/2.98    inference(equality_resolution,[],[f56])).
% 19.45/2.98  
% 19.45/2.98  fof(f90,plain,(
% 19.45/2.98    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 19.45/2.98    inference(equality_resolution,[],[f89])).
% 19.45/2.98  
% 19.45/2.98  fof(f55,plain,(
% 19.45/2.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 19.45/2.98    inference(cnf_transformation,[],[f37])).
% 19.45/2.98  
% 19.45/2.98  fof(f91,plain,(
% 19.45/2.98    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 19.45/2.98    inference(equality_resolution,[],[f55])).
% 19.45/2.98  
% 19.45/2.98  fof(f92,plain,(
% 19.45/2.98    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 19.45/2.98    inference(equality_resolution,[],[f91])).
% 19.45/2.98  
% 19.45/2.98  fof(f54,plain,(
% 19.45/2.98    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 19.45/2.98    inference(cnf_transformation,[],[f37])).
% 19.45/2.98  
% 19.45/2.98  fof(f93,plain,(
% 19.45/2.98    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 19.45/2.98    inference(equality_resolution,[],[f54])).
% 19.45/2.98  
% 19.45/2.98  fof(f73,plain,(
% 19.45/2.98    ~r2_hidden(sK2,sK4)),
% 19.45/2.98    inference(cnf_transformation,[],[f39])).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1,plain,
% 19.45/2.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 19.45/2.98      inference(cnf_transformation,[],[f40]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_12,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.45/2.98      inference(cnf_transformation,[],[f51]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_543,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_13,plain,
% 19.45/2.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 19.45/2.98      inference(cnf_transformation,[],[f52]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_4622,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_543,c_13]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_4963,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X0),X1)) = k1_xboole_0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1,c_4622]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_0,plain,
% 19.45/2.98      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) = k1_enumset1(X0,X1,X2) ),
% 19.45/2.98      inference(cnf_transformation,[],[f79]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_23,plain,
% 19.45/2.98      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) = k1_enumset1(X0,X1,X2) ),
% 19.45/2.98      inference(cnf_transformation,[],[f84]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1235,plain,
% 19.45/2.98      ( k1_enumset1(X0,X1,X1) = k1_enumset1(X0,X0,X1) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_0,c_23]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_26,negated_conjecture,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))) = k1_enumset1(sK2,sK2,sK3) ),
% 19.45/2.98      inference(cnf_transformation,[],[f86]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_245,negated_conjecture,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))) = k1_enumset1(sK2,sK2,sK3) ),
% 19.45/2.98      inference(theory_normalisation,[status(thm)],[c_26,c_12,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1110,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))),X0)) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_245,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2895,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))),X0)) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_1235,c_1110]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2896,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)))) = k1_enumset1(sK2,sK2,sK3) ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_1235,c_245]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_544,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_5471,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))),k5_xboole_0(sK4,X0)) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2896,c_544]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1518,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_12,c_1110]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2893,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)),X0))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_1235,c_1518]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_4132,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))) = k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_13,c_2893]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_3,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k1_enumset1(X0,X0,X0))) = X0 ),
% 19.45/2.98      inference(cnf_transformation,[],[f81]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_250,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X0)))) = X0 ),
% 19.45/2.98      inference(theory_normalisation,[status(thm)],[c_3,c_12,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2,plain,
% 19.45/2.98      ( k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
% 19.45/2.98      inference(cnf_transformation,[],[f80]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_525,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_250,c_2,c_13]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_4140,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))) = k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_4132,c_525]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_5524,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(sK4,X0)) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_5471,c_4140]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_5583,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(sK4,X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_5524,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_13358,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))),X0),k1_enumset1(sK2,sK2,sK3)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2895,c_5583]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1520,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),X1) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1110,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1769,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))) = k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_13,c_1518]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1772,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))) = k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_1769,c_525]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2072,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),X1) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_1520,c_1520,c_1772]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1515,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1,c_1110]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2086,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2072,c_1515]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2087,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0)) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_2086,c_1772]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1113,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) = k1_xboole_0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_12,c_13]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1771,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0)),X1)) = k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),X1) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1518,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6015,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0))),X1) = k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0),X1)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1113,c_1771]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2853,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0))) = k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1113,c_1518]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2863,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),X0))) = k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_2853,c_525]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6039,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_xboole_0),X0)) = k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_6015,c_2863]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6040,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0)) = k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0) ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_6039,c_525]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1517,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))) = k5_xboole_0(sK4,k1_xboole_0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_13,c_1110]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1109,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_13,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_954,plain,
% 19.45/2.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_525,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1117,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_1109,c_954]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1522,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))) = sK4 ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_1517,c_525,c_1117]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2101,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = sK4 ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_1522,c_1522,c_1772]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_545,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_12,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6871,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0)) = k5_xboole_0(X0,sK4) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2101,c_545]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2102,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),X0)) = k5_xboole_0(sK4,X0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2101,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7002,plain,
% 19.45/2.98      ( k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0))) = k5_xboole_0(X0,sK4) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_6871,c_2102,c_6040]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_13426,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0)),k1_enumset1(sK2,sK2,sK3)) = k5_xboole_0(X0,sK4) ),
% 19.45/2.98      inference(light_normalisation,
% 19.45/2.98                [status(thm)],
% 19.45/2.98                [c_13358,c_2087,c_4140,c_6040,c_7002]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_17592,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),X0),sK4) = k5_xboole_0(k5_xboole_0(sK4,k1_xboole_0),k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_4963,c_13426]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_5461,plain,
% 19.45/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_525,c_544]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6952,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,X1))) = k5_xboole_0(k5_xboole_0(X1,X0),k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_545,c_5524]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_5590,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k1_enumset1(sK2,sK2,sK3))) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_5524,c_543]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6970,plain,
% 19.45/2.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k5_xboole_0(X1,X0),k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_6952,c_5590]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6877,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))),X0)) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2896,c_545]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6999,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0))) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(light_normalisation,
% 19.45/2.98                [status(thm)],
% 19.45/2.98                [c_6877,c_2895,c_4140,c_6040]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7471,plain,
% 19.45/2.98      ( k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)),k1_enumset1(sK2,sK2,sK3)) = k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2896,c_6999]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7536,plain,
% 19.45/2.98      ( k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0)) = k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_7471,c_545]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7833,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4))) = k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_7536,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7826,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)),k1_xboole_0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_4963,c_7536]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6911,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X2,X1)) = k5_xboole_0(X2,k1_xboole_0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_4963,c_545]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_6980,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),X0),k5_xboole_0(X2,X1)) = X2 ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_6911,c_525]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7859,plain,
% 19.45/2.98      ( k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)) = sK4 ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_7826,c_525,c_6980]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_8385,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),X0),sK4) = k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_7833,c_7859]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_5589,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,X0))) = k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_5524,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_13492,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,X0)),X1)) = k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),X1) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_5589,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2835,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4))),k1_enumset1(sK2,sK2,sK3))) = k1_xboole_0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_245,c_1113]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2874,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3))) = k1_xboole_0 ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_2835,c_1772]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_3292,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3)),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2874,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_3293,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3)),X0)) = X0 ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_3292,c_954]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7483,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3)) = k5_xboole_0(sK4,k5_xboole_0(sK4,sK4)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2101,c_6999]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7502,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)),k1_enumset1(sK2,sK2,sK3)) = sK4 ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_7483,c_1117,c_6040]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_10145,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(sK4,X0)) = X0 ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_3293,c_3293,c_7502]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_10180,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,X0),X1)) = k5_xboole_0(X0,X1) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_10145,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_11658,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK4,X1)),X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_543,c_10180]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_11725,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK4,X1)),X2)) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_11658,c_12]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_13528,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),X1) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(X0,X1)) ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_13492,c_11725]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_17649,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) ),
% 19.45/2.98      inference(demodulation,
% 19.45/2.98                [status(thm)],
% 19.45/2.98                [c_17592,c_5461,c_6970,c_8385,c_13528]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_17650,plain,
% 19.45/2.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4) ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_17649,c_13]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_7,plain,
% 19.45/2.98      ( r2_hidden(X0,X1)
% 19.45/2.98      | r2_hidden(X0,X2)
% 19.45/2.98      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 19.45/2.98      inference(cnf_transformation,[],[f43]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_247,plain,
% 19.45/2.98      ( r2_hidden(X0,X1)
% 19.45/2.98      | r2_hidden(X0,X2)
% 19.45/2.98      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 19.45/2.98      inference(theory_normalisation,[status(thm)],[c_7,c_12,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_521,plain,
% 19.45/2.98      ( r2_hidden(X0,X1) = iProver_top
% 19.45/2.98      | r2_hidden(X0,X2) = iProver_top
% 19.45/2.98      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 19.45/2.98      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_71334,plain,
% 19.45/2.98      ( r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) != iProver_top
% 19.45/2.98      | r2_hidden(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top
% 19.45/2.98      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_17650,c_521]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_71502,plain,
% 19.45/2.98      ( r2_hidden(sK2,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) != iProver_top
% 19.45/2.98      | r2_hidden(sK2,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top
% 19.45/2.98      | r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_71334]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_11,plain,
% 19.45/2.98      ( r1_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X1))),k5_xboole_0(X0,X1)) ),
% 19.45/2.98      inference(cnf_transformation,[],[f82]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_246,plain,
% 19.45/2.98      ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X1)))),k5_xboole_0(X0,X1)) ),
% 19.45/2.98      inference(theory_normalisation,[status(thm)],[c_11,c_12,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_517,plain,
% 19.45/2.98      ( r1_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k1_enumset1(X0,X0,X1)))),k5_xboole_0(X0,X1)) = iProver_top ),
% 19.45/2.98      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_45095,plain,
% 19.45/2.98      ( r1_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)))))),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1772,c_517]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_38380,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_12,c_1117]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_45107,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)))) = k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1772,c_38380]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2834,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,X2)))) = k1_xboole_0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_12,c_1113]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_8690,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X2,X1)))) = k1_xboole_0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_1,c_2834]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_18277,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),sK4,sK4)))),k5_xboole_0(sK4,k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)))) = k1_xboole_0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_2896,c_8690]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_18412,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))),k5_xboole_0(sK4,k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)))) = k1_xboole_0 ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_18277,c_4140]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_20658,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(sK4,k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3))),k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)))) = k1_xboole_0 ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_18412,c_1]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_35703,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)))) = k5_xboole_0(sK4,k1_xboole_0) ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_20658,c_10180]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_35730,plain,
% 19.45/2.98      ( k5_xboole_0(k5_xboole_0(X0,k1_enumset1(sK2,sK2,sK3)),k5_xboole_0(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3)))) = sK4 ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_35703,c_525,c_13528]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_45204,plain,
% 19.45/2.98      ( k3_tarski(k1_enumset1(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK2,sK2,sK3),sK4)) = sK4 ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_45107,c_35730]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_45994,plain,
% 19.45/2.98      ( r1_xboole_0(k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,sK4)),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top ),
% 19.45/2.98      inference(light_normalisation,[status(thm)],[c_45095,c_45204]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_45995,plain,
% 19.45/2.98      ( r1_xboole_0(k1_enumset1(sK2,sK2,sK3),k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) = iProver_top ),
% 19.45/2.98      inference(demodulation,[status(thm)],[c_45994,c_13,c_525]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_8,plain,
% 19.45/2.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 19.45/2.98      inference(cnf_transformation,[],[f49]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_520,plain,
% 19.45/2.98      ( r1_xboole_0(X0,X1) != iProver_top
% 19.45/2.98      | r2_hidden(X2,X1) != iProver_top
% 19.45/2.98      | r2_hidden(X2,X0) != iProver_top ),
% 19.45/2.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_67086,plain,
% 19.45/2.98      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 19.45/2.98      | r2_hidden(X0,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) != iProver_top ),
% 19.45/2.98      inference(superposition,[status(thm)],[c_45995,c_520]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_67088,plain,
% 19.45/2.98      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 19.45/2.98      | r2_hidden(sK2,k5_xboole_0(sK4,k1_enumset1(sK2,sK2,sK3))) != iProver_top ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_67086]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_5,plain,
% 19.45/2.98      ( ~ r2_hidden(X0,X1)
% 19.45/2.98      | r2_hidden(X0,X2)
% 19.45/2.98      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 19.45/2.98      inference(cnf_transformation,[],[f45]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1019,plain,
% 19.45/2.98      ( ~ r2_hidden(X0,X1)
% 19.45/2.98      | r2_hidden(X0,k5_xboole_0(X1,sK4))
% 19.45/2.98      | r2_hidden(X0,sK4) ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_5]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_41045,plain,
% 19.45/2.98      ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK3))
% 19.45/2.98      | r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4))
% 19.45/2.98      | r2_hidden(X0,sK4) ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_1019]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_41046,plain,
% 19.45/2.98      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 19.45/2.98      | r2_hidden(X0,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = iProver_top
% 19.45/2.98      | r2_hidden(X0,sK4) = iProver_top ),
% 19.45/2.98      inference(predicate_to_equality,[status(thm)],[c_41045]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_41048,plain,
% 19.45/2.98      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) != iProver_top
% 19.45/2.98      | r2_hidden(sK2,k5_xboole_0(k1_enumset1(sK2,sK2,sK3),sK4)) = iProver_top
% 19.45/2.98      | r2_hidden(sK2,sK4) = iProver_top ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_41046]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_19,plain,
% 19.45/2.98      ( r2_hidden(X0,k1_enumset1(X1,X0,X2)) ),
% 19.45/2.98      inference(cnf_transformation,[],[f90]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_39450,plain,
% 19.45/2.98      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_19]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_39451,plain,
% 19.45/2.98      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK3)) = iProver_top ),
% 19.45/2.98      inference(predicate_to_equality,[status(thm)],[c_39450]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_2327,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,sK4) = k1_xboole_0 ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_13]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_257,plain,
% 19.45/2.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.45/2.98      theory(equality) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_598,plain,
% 19.45/2.98      ( ~ r2_hidden(X0,X1)
% 19.45/2.98      | r2_hidden(sK2,k5_xboole_0(X2,sK4))
% 19.45/2.98      | k5_xboole_0(X2,sK4) != X1
% 19.45/2.98      | sK2 != X0 ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_257]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1258,plain,
% 19.45/2.98      ( ~ r2_hidden(X0,X1)
% 19.45/2.98      | r2_hidden(sK2,k5_xboole_0(sK4,sK4))
% 19.45/2.98      | k5_xboole_0(sK4,sK4) != X1
% 19.45/2.98      | sK2 != X0 ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_598]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1529,plain,
% 19.45/2.98      ( ~ r2_hidden(X0,k1_xboole_0)
% 19.45/2.98      | r2_hidden(sK2,k5_xboole_0(sK4,sK4))
% 19.45/2.98      | k5_xboole_0(sK4,sK4) != k1_xboole_0
% 19.45/2.98      | sK2 != X0 ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_1258]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1530,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,sK4) != k1_xboole_0
% 19.45/2.98      | sK2 != X0
% 19.45/2.98      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 19.45/2.98      | r2_hidden(sK2,k5_xboole_0(sK4,sK4)) = iProver_top ),
% 19.45/2.98      inference(predicate_to_equality,[status(thm)],[c_1529]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_1532,plain,
% 19.45/2.98      ( k5_xboole_0(sK4,sK4) != k1_xboole_0
% 19.45/2.98      | sK2 != sK2
% 19.45/2.98      | r2_hidden(sK2,k5_xboole_0(sK4,sK4)) = iProver_top
% 19.45/2.98      | r2_hidden(sK2,k1_xboole_0) != iProver_top ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_1530]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_553,plain,
% 19.45/2.98      ( r2_hidden(sK2,X0)
% 19.45/2.98      | ~ r2_hidden(sK2,k5_xboole_0(X0,sK4))
% 19.45/2.98      | r2_hidden(sK2,sK4) ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_247]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_821,plain,
% 19.45/2.98      ( ~ r2_hidden(sK2,k5_xboole_0(sK4,sK4)) | r2_hidden(sK2,sK4) ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_553]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_822,plain,
% 19.45/2.98      ( r2_hidden(sK2,k5_xboole_0(sK4,sK4)) != iProver_top
% 19.45/2.98      | r2_hidden(sK2,sK4) = iProver_top ),
% 19.45/2.98      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_20,plain,
% 19.45/2.98      ( r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
% 19.45/2.98      inference(cnf_transformation,[],[f92]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_35,plain,
% 19.45/2.98      ( r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_20]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_21,plain,
% 19.45/2.98      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 19.45/2.98      | X0 = X1
% 19.45/2.98      | X0 = X2
% 19.45/2.98      | X0 = X3 ),
% 19.45/2.98      inference(cnf_transformation,[],[f93]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_32,plain,
% 19.45/2.98      ( ~ r2_hidden(sK2,k1_enumset1(sK2,sK2,sK2)) | sK2 = sK2 ),
% 19.45/2.98      inference(instantiation,[status(thm)],[c_21]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_25,negated_conjecture,
% 19.45/2.98      ( ~ r2_hidden(sK2,sK4) ),
% 19.45/2.98      inference(cnf_transformation,[],[f73]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(c_27,plain,
% 19.45/2.98      ( r2_hidden(sK2,sK4) != iProver_top ),
% 19.45/2.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.45/2.98  
% 19.45/2.98  cnf(contradiction,plain,
% 19.45/2.98      ( $false ),
% 19.45/2.98      inference(minisat,
% 19.45/2.98                [status(thm)],
% 19.45/2.98                [c_71502,c_67088,c_41048,c_39451,c_2327,c_1532,c_822,
% 19.45/2.98                 c_35,c_32,c_27]) ).
% 19.45/2.98  
% 19.45/2.98  
% 19.45/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.45/2.98  
% 19.45/2.98  ------                               Statistics
% 19.45/2.98  
% 19.45/2.98  ------ General
% 19.45/2.98  
% 19.45/2.98  abstr_ref_over_cycles:                  0
% 19.45/2.98  abstr_ref_under_cycles:                 0
% 19.45/2.98  gc_basic_clause_elim:                   0
% 19.45/2.98  forced_gc_time:                         0
% 19.45/2.98  parsing_time:                           0.006
% 19.45/2.98  unif_index_cands_time:                  0.
% 19.45/2.98  unif_index_add_time:                    0.
% 19.45/2.98  orderings_time:                         0.
% 19.45/2.98  out_proof_time:                         0.015
% 19.45/2.98  total_time:                             2.174
% 19.45/2.98  num_of_symbols:                         43
% 19.45/2.98  num_of_terms:                           125844
% 19.45/2.98  
% 19.45/2.98  ------ Preprocessing
% 19.45/2.98  
% 19.45/2.98  num_of_splits:                          0
% 19.45/2.98  num_of_split_atoms:                     0
% 19.45/2.98  num_of_reused_defs:                     0
% 19.45/2.98  num_eq_ax_congr_red:                    26
% 19.45/2.98  num_of_sem_filtered_clauses:            1
% 19.45/2.98  num_of_subtypes:                        0
% 19.45/2.98  monotx_restored_types:                  0
% 19.45/2.98  sat_num_of_epr_types:                   0
% 19.45/2.98  sat_num_of_non_cyclic_types:            0
% 19.45/2.98  sat_guarded_non_collapsed_types:        0
% 19.45/2.98  num_pure_diseq_elim:                    0
% 19.45/2.98  simp_replaced_by:                       0
% 19.45/2.98  res_preprocessed:                       94
% 19.45/2.98  prep_upred:                             0
% 19.45/2.98  prep_unflattend:                        2
% 19.45/2.98  smt_new_axioms:                         0
% 19.45/2.98  pred_elim_cands:                        2
% 19.45/2.98  pred_elim:                              0
% 19.45/2.98  pred_elim_cl:                           0
% 19.45/2.98  pred_elim_cycles:                       1
% 19.45/2.98  merged_defs:                            0
% 19.45/2.98  merged_defs_ncl:                        0
% 19.45/2.98  bin_hyper_res:                          0
% 19.45/2.98  prep_cycles:                            3
% 19.45/2.98  pred_elim_time:                         0.
% 19.45/2.98  splitting_time:                         0.
% 19.45/2.98  sem_filter_time:                        0.
% 19.45/2.98  monotx_time:                            0.
% 19.45/2.98  subtype_inf_time:                       0.
% 19.45/2.98  
% 19.45/2.98  ------ Problem properties
% 19.45/2.98  
% 19.45/2.98  clauses:                                27
% 19.45/2.98  conjectures:                            2
% 19.45/2.98  epr:                                    2
% 19.45/2.98  horn:                                   20
% 19.45/2.98  ground:                                 2
% 19.45/2.98  unary:                                  15
% 19.45/2.98  binary:                                 2
% 19.45/2.98  lits:                                   52
% 19.45/2.98  lits_eq:                                23
% 19.45/2.98  fd_pure:                                0
% 19.45/2.98  fd_pseudo:                              0
% 19.45/2.98  fd_cond:                                0
% 19.45/2.98  fd_pseudo_cond:                         4
% 19.45/2.98  ac_symbols:                             1
% 19.45/2.98  
% 19.45/2.98  ------ Propositional Solver
% 19.45/2.98  
% 19.45/2.98  prop_solver_calls:                      27
% 19.45/2.98  prop_fast_solver_calls:                 685
% 19.45/2.98  smt_solver_calls:                       0
% 19.45/2.98  smt_fast_solver_calls:                  0
% 19.45/2.98  prop_num_of_clauses:                    15579
% 19.45/2.98  prop_preprocess_simplified:             20345
% 19.45/2.98  prop_fo_subsumed:                       0
% 19.45/2.98  prop_solver_time:                       0.
% 19.45/2.98  smt_solver_time:                        0.
% 19.45/2.98  smt_fast_solver_time:                   0.
% 19.45/2.98  prop_fast_solver_time:                  0.
% 19.45/2.98  prop_unsat_core_time:                   0.001
% 19.45/2.98  
% 19.45/2.98  ------ QBF
% 19.45/2.98  
% 19.45/2.98  qbf_q_res:                              0
% 19.45/2.98  qbf_num_tautologies:                    0
% 19.45/2.98  qbf_prep_cycles:                        0
% 19.45/2.98  
% 19.45/2.98  ------ BMC1
% 19.45/2.98  
% 19.45/2.98  bmc1_current_bound:                     -1
% 19.45/2.98  bmc1_last_solved_bound:                 -1
% 19.45/2.98  bmc1_unsat_core_size:                   -1
% 19.45/2.98  bmc1_unsat_core_parents_size:           -1
% 19.45/2.98  bmc1_merge_next_fun:                    0
% 19.45/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.45/2.98  
% 19.45/2.98  ------ Instantiation
% 19.45/2.98  
% 19.45/2.98  inst_num_of_clauses:                    2327
% 19.45/2.98  inst_num_in_passive:                    885
% 19.45/2.98  inst_num_in_active:                     725
% 19.45/2.98  inst_num_in_unprocessed:                718
% 19.45/2.98  inst_num_of_loops:                      800
% 19.45/2.98  inst_num_of_learning_restarts:          0
% 19.45/2.98  inst_num_moves_active_passive:          73
% 19.45/2.98  inst_lit_activity:                      0
% 19.45/2.98  inst_lit_activity_moves:                0
% 19.45/2.98  inst_num_tautologies:                   0
% 19.45/2.98  inst_num_prop_implied:                  0
% 19.45/2.98  inst_num_existing_simplified:           0
% 19.45/2.98  inst_num_eq_res_simplified:             0
% 19.45/2.98  inst_num_child_elim:                    0
% 19.45/2.98  inst_num_of_dismatching_blockings:      8741
% 19.45/2.98  inst_num_of_non_proper_insts:           6047
% 19.45/2.98  inst_num_of_duplicates:                 0
% 19.45/2.98  inst_inst_num_from_inst_to_res:         0
% 19.45/2.98  inst_dismatching_checking_time:         0.
% 19.45/2.98  
% 19.45/2.98  ------ Resolution
% 19.45/2.98  
% 19.45/2.98  res_num_of_clauses:                     0
% 19.45/2.98  res_num_in_passive:                     0
% 19.45/2.98  res_num_in_active:                      0
% 19.45/2.98  res_num_of_loops:                       97
% 19.45/2.98  res_forward_subset_subsumed:            643
% 19.45/2.98  res_backward_subset_subsumed:           18
% 19.45/2.98  res_forward_subsumed:                   0
% 19.45/2.98  res_backward_subsumed:                  0
% 19.45/2.98  res_forward_subsumption_resolution:     0
% 19.45/2.98  res_backward_subsumption_resolution:    0
% 19.45/2.98  res_clause_to_clause_subsumption:       109390
% 19.45/2.98  res_orphan_elimination:                 0
% 19.45/2.98  res_tautology_del:                      235
% 19.45/2.98  res_num_eq_res_simplified:              0
% 19.45/2.98  res_num_sel_changes:                    0
% 19.45/2.98  res_moves_from_active_to_pass:          0
% 19.45/2.98  
% 19.45/2.98  ------ Superposition
% 19.45/2.98  
% 19.45/2.98  sup_time_total:                         0.
% 19.45/2.98  sup_time_generating:                    0.
% 19.45/2.98  sup_time_sim_full:                      0.
% 19.45/2.98  sup_time_sim_immed:                     0.
% 19.45/2.98  
% 19.45/2.98  sup_num_of_clauses:                     4415
% 19.45/2.98  sup_num_in_active:                      139
% 19.45/2.98  sup_num_in_passive:                     4276
% 19.45/2.98  sup_num_of_loops:                       159
% 19.45/2.98  sup_fw_superposition:                   12391
% 19.45/2.98  sup_bw_superposition:                   9037
% 19.45/2.98  sup_immediate_simplified:               14161
% 19.45/2.98  sup_given_eliminated:                   6
% 19.45/2.98  comparisons_done:                       0
% 19.45/2.98  comparisons_avoided:                    6
% 19.45/2.98  
% 19.45/2.98  ------ Simplifications
% 19.45/2.98  
% 19.45/2.98  
% 19.45/2.98  sim_fw_subset_subsumed:                 2
% 19.45/2.98  sim_bw_subset_subsumed:                 0
% 19.45/2.98  sim_fw_subsumed:                        767
% 19.45/2.98  sim_bw_subsumed:                        100
% 19.45/2.98  sim_fw_subsumption_res:                 0
% 19.45/2.98  sim_bw_subsumption_res:                 0
% 19.45/2.98  sim_tautology_del:                      11
% 19.45/2.98  sim_eq_tautology_del:                   5118
% 19.45/2.98  sim_eq_res_simp:                        0
% 19.45/2.98  sim_fw_demodulated:                     11943
% 19.45/2.98  sim_bw_demodulated:                     216
% 19.45/2.98  sim_light_normalised:                   6817
% 19.45/2.98  sim_joinable_taut:                      501
% 19.45/2.98  sim_joinable_simp:                      0
% 19.45/2.98  sim_ac_normalised:                      0
% 19.45/2.98  sim_smt_subsumption:                    0
% 19.45/2.98  
%------------------------------------------------------------------------------
