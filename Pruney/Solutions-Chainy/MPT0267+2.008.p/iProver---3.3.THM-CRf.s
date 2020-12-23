%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:30 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  124 (4058 expanded)
%              Number of clauses        :   48 ( 361 expanded)
%              Number of leaves         :   19 (1158 expanded)
%              Depth                    :   27
%              Number of atoms          :  389 (10598 expanded)
%              Number of equality atoms :  132 (3652 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f75,f83])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f85])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f86])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f87])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f88])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK3 = sK5
        | ~ r2_hidden(sK3,sK4)
        | ~ r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) )
      & ( ( sK3 != sK5
          & r2_hidden(sK3,sK4) )
        | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( sK3 = sK5
      | ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) )
    & ( ( sK3 != sK5
        & r2_hidden(sK3,sK4) )
      | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f42])).

fof(f80,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f58,f88])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f87])).

fof(f114,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) ),
    inference(definition_unfolding,[],[f80,f90,f91])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f88])).

fof(f116,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f88])).

fof(f115,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f95])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,
    ( sK3 = sK5
    | ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,
    ( sK3 = sK5
    | ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) ),
    inference(definition_unfolding,[],[f82,f90,f91])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f91])).

fof(f127,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f110])).

fof(f81,plain,
    ( sK3 != sK5
    | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f43])).

fof(f113,plain,
    ( sK3 != sK5
    | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) ),
    inference(definition_unfolding,[],[f81,f90,f91])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f91])).

fof(f125,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f109])).

fof(f126,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f125])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1164,plain,
    ( r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_10,c_28])).

cnf(c_1174,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1164,c_10])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1383,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1174,c_4])).

cnf(c_5069,plain,
    ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_5,c_1383])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1277,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_9,c_1164])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1482,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1277,c_3])).

cnf(c_1488,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | r2_hidden(sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1482,c_10])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1780,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1488,c_7])).

cnf(c_5903,plain,
    ( r2_hidden(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5069,c_1488,c_1780])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | ~ r2_hidden(sK3,sK4)
    | sK3 = sK5 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_5914,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | sK3 = sK5 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5903,c_26])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6343,plain,
    ( r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | ~ r2_hidden(sK3,sK4)
    | sK3 = sK5 ),
    inference(resolution,[status(thm)],[c_5914,c_8])).

cnf(c_6358,plain,
    ( r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | sK3 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6343,c_1488,c_1780,c_5069])).

cnf(c_6705,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK3 = sK5 ),
    inference(resolution,[status(thm)],[c_6358,c_9])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1054,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1331,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,k5_xboole_0(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2042,plain,
    ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_7570,plain,
    ( ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK3 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6705,c_1054,c_1488,c_1780,c_2042,c_5069])).

cnf(c_7588,plain,
    ( ~ r2_hidden(sK3,sK4)
    | sK3 = sK5 ),
    inference(resolution,[status(thm)],[c_7570,c_4])).

cnf(c_7594,plain,
    ( sK3 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7588,c_1488,c_1780,c_5069])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1275,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | ~ r2_hidden(sK3,sK4)
    | sK3 != sK5 ),
    inference(resolution,[status(thm)],[c_9,c_27])).

cnf(c_5915,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | sK3 != sK5 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5903,c_1275])).

cnf(c_6353,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK3 != sK5 ),
    inference(resolution,[status(thm)],[c_5915,c_8])).

cnf(c_6709,plain,
    ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK3 != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6353,c_1383])).

cnf(c_6355,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK3 != sK5 ),
    inference(resolution,[status(thm)],[c_5915,c_7])).

cnf(c_6723,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | sK3 != sK5 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6709,c_6355])).

cnf(c_8419,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7594,c_6723])).

cnf(c_12826,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_8419,c_9])).

cnf(c_270,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1425,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_4664,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
    | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_4667,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK3 != sK5 ),
    inference(instantiation,[status(thm)],[c_4664])).

cnf(c_268,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_272,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_23,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_37,plain,
    ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_34,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12826,c_7588,c_5903,c_4667,c_272,c_37,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:24:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.61/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.00  
% 3.61/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/1.00  
% 3.61/1.00  ------  iProver source info
% 3.61/1.00  
% 3.61/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.61/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/1.00  git: non_committed_changes: false
% 3.61/1.00  git: last_make_outside_of_git: false
% 3.61/1.00  
% 3.61/1.00  ------ 
% 3.61/1.00  ------ Parsing...
% 3.61/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/1.00  
% 3.61/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/1.00  ------ Proving...
% 3.61/1.00  ------ Problem Properties 
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  clauses                                 29
% 3.61/1.00  conjectures                             3
% 3.61/1.00  EPR                                     0
% 3.61/1.00  Horn                                    20
% 3.61/1.00  unary                                   8
% 3.61/1.00  binary                                  5
% 3.61/1.00  lits                                    70
% 3.61/1.00  lits eq                                 27
% 3.61/1.00  fd_pure                                 0
% 3.61/1.00  fd_pseudo                               0
% 3.61/1.00  fd_cond                                 0
% 3.61/1.00  fd_pseudo_cond                          9
% 3.61/1.00  AC symbols                              0
% 3.61/1.00  
% 3.61/1.00  ------ Input Options Time Limit: Unbounded
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ 
% 3.61/1.00  Current options:
% 3.61/1.00  ------ 
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  ------ Proving...
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  % SZS status Theorem for theBenchmark.p
% 3.61/1.00  
% 3.61/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/1.00  
% 3.61/1.00  fof(f1,axiom,(
% 3.61/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f25,plain,(
% 3.61/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.61/1.00    inference(nnf_transformation,[],[f1])).
% 3.61/1.00  
% 3.61/1.00  fof(f26,plain,(
% 3.61/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.61/1.00    inference(flattening,[],[f25])).
% 3.61/1.00  
% 3.61/1.00  fof(f27,plain,(
% 3.61/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.61/1.00    inference(rectify,[],[f26])).
% 3.61/1.00  
% 3.61/1.00  fof(f28,plain,(
% 3.61/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.61/1.00    introduced(choice_axiom,[])).
% 3.61/1.00  
% 3.61/1.00  fof(f29,plain,(
% 3.61/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.61/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.61/1.00  
% 3.61/1.00  fof(f44,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.61/1.00    inference(cnf_transformation,[],[f29])).
% 3.61/1.00  
% 3.61/1.00  fof(f17,axiom,(
% 3.61/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f78,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.61/1.00    inference(cnf_transformation,[],[f17])).
% 3.61/1.00  
% 3.61/1.00  fof(f11,axiom,(
% 3.61/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f72,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f11])).
% 3.61/1.00  
% 3.61/1.00  fof(f12,axiom,(
% 3.61/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f73,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f12])).
% 3.61/1.00  
% 3.61/1.00  fof(f13,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f74,plain,(
% 3.61/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f13])).
% 3.61/1.00  
% 3.61/1.00  fof(f14,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f75,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f14])).
% 3.61/1.00  
% 3.61/1.00  fof(f15,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f76,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f15])).
% 3.61/1.00  
% 3.61/1.00  fof(f16,axiom,(
% 3.61/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f77,plain,(
% 3.61/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f16])).
% 3.61/1.00  
% 3.61/1.00  fof(f83,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f76,f77])).
% 3.61/1.00  
% 3.61/1.00  fof(f84,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f75,f83])).
% 3.61/1.00  
% 3.61/1.00  fof(f85,plain,(
% 3.61/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f74,f84])).
% 3.61/1.00  
% 3.61/1.00  fof(f86,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f73,f85])).
% 3.61/1.00  
% 3.61/1.00  fof(f87,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f72,f86])).
% 3.61/1.00  
% 3.61/1.00  fof(f88,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.61/1.00    inference(definition_unfolding,[],[f78,f87])).
% 3.61/1.00  
% 3.61/1.00  fof(f97,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.61/1.00    inference(definition_unfolding,[],[f44,f88])).
% 3.61/1.00  
% 3.61/1.00  fof(f117,plain,(
% 3.61/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.61/1.00    inference(equality_resolution,[],[f97])).
% 3.61/1.00  
% 3.61/1.00  fof(f3,axiom,(
% 3.61/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f22,plain,(
% 3.61/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 3.61/1.00    inference(ennf_transformation,[],[f3])).
% 3.61/1.00  
% 3.61/1.00  fof(f30,plain,(
% 3.61/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 3.61/1.00    inference(nnf_transformation,[],[f22])).
% 3.61/1.00  
% 3.61/1.00  fof(f51,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.61/1.00    inference(cnf_transformation,[],[f30])).
% 3.61/1.00  
% 3.61/1.00  fof(f19,conjecture,(
% 3.61/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f20,negated_conjecture,(
% 3.61/1.00    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.61/1.00    inference(negated_conjecture,[],[f19])).
% 3.61/1.00  
% 3.61/1.00  fof(f24,plain,(
% 3.61/1.00    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.61/1.00    inference(ennf_transformation,[],[f20])).
% 3.61/1.00  
% 3.61/1.00  fof(f40,plain,(
% 3.61/1.00    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.61/1.00    inference(nnf_transformation,[],[f24])).
% 3.61/1.00  
% 3.61/1.00  fof(f41,plain,(
% 3.61/1.00    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.61/1.00    inference(flattening,[],[f40])).
% 3.61/1.00  
% 3.61/1.00  fof(f42,plain,(
% 3.61/1.00    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK3 = sK5 | ~r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))) & ((sK3 != sK5 & r2_hidden(sK3,sK4)) | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))))),
% 3.61/1.00    introduced(choice_axiom,[])).
% 3.61/1.00  
% 3.61/1.00  fof(f43,plain,(
% 3.61/1.00    (sK3 = sK5 | ~r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))) & ((sK3 != sK5 & r2_hidden(sK3,sK4)) | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))))),
% 3.61/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f41,f42])).
% 3.61/1.00  
% 3.61/1.00  fof(f80,plain,(
% 3.61/1.00    r2_hidden(sK3,sK4) | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))),
% 3.61/1.00    inference(cnf_transformation,[],[f43])).
% 3.61/1.00  
% 3.61/1.00  fof(f4,axiom,(
% 3.61/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f55,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f4])).
% 3.61/1.00  
% 3.61/1.00  fof(f7,axiom,(
% 3.61/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f58,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.61/1.00    inference(cnf_transformation,[],[f7])).
% 3.61/1.00  
% 3.61/1.00  fof(f89,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.61/1.00    inference(definition_unfolding,[],[f58,f88])).
% 3.61/1.00  
% 3.61/1.00  fof(f90,plain,(
% 3.61/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f55,f89])).
% 3.61/1.00  
% 3.61/1.00  fof(f10,axiom,(
% 3.61/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f71,plain,(
% 3.61/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f10])).
% 3.61/1.00  
% 3.61/1.00  fof(f91,plain,(
% 3.61/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.61/1.00    inference(definition_unfolding,[],[f71,f87])).
% 3.61/1.00  
% 3.61/1.00  fof(f114,plain,(
% 3.61/1.00    r2_hidden(sK3,sK4) | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))),
% 3.61/1.00    inference(definition_unfolding,[],[f80,f90,f91])).
% 3.61/1.00  
% 3.61/1.00  fof(f45,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.61/1.00    inference(cnf_transformation,[],[f29])).
% 3.61/1.00  
% 3.61/1.00  fof(f96,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.61/1.00    inference(definition_unfolding,[],[f45,f88])).
% 3.61/1.00  
% 3.61/1.00  fof(f116,plain,(
% 3.61/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.61/1.00    inference(equality_resolution,[],[f96])).
% 3.61/1.00  
% 3.61/1.00  fof(f52,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 3.61/1.00    inference(cnf_transformation,[],[f30])).
% 3.61/1.00  
% 3.61/1.00  fof(f46,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.61/1.00    inference(cnf_transformation,[],[f29])).
% 3.61/1.00  
% 3.61/1.00  fof(f95,plain,(
% 3.61/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.61/1.00    inference(definition_unfolding,[],[f46,f88])).
% 3.61/1.00  
% 3.61/1.00  fof(f115,plain,(
% 3.61/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.61/1.00    inference(equality_resolution,[],[f95])).
% 3.61/1.00  
% 3.61/1.00  fof(f54,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f30])).
% 3.61/1.00  
% 3.61/1.00  fof(f82,plain,(
% 3.61/1.00    sK3 = sK5 | ~r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))),
% 3.61/1.00    inference(cnf_transformation,[],[f43])).
% 3.61/1.00  
% 3.61/1.00  fof(f112,plain,(
% 3.61/1.00    sK3 = sK5 | ~r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))),
% 3.61/1.00    inference(definition_unfolding,[],[f82,f90,f91])).
% 3.61/1.00  
% 3.61/1.00  fof(f53,plain,(
% 3.61/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 3.61/1.00    inference(cnf_transformation,[],[f30])).
% 3.61/1.00  
% 3.61/1.00  fof(f9,axiom,(
% 3.61/1.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.61/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/1.00  
% 3.61/1.00  fof(f36,plain,(
% 3.61/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.61/1.00    inference(nnf_transformation,[],[f9])).
% 3.61/1.00  
% 3.61/1.00  fof(f37,plain,(
% 3.61/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.61/1.00    inference(rectify,[],[f36])).
% 3.61/1.00  
% 3.61/1.00  fof(f38,plain,(
% 3.61/1.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.61/1.00    introduced(choice_axiom,[])).
% 3.61/1.00  
% 3.61/1.00  fof(f39,plain,(
% 3.61/1.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.61/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 3.61/1.00  
% 3.61/1.00  fof(f67,plain,(
% 3.61/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.61/1.00    inference(cnf_transformation,[],[f39])).
% 3.61/1.00  
% 3.61/1.00  fof(f110,plain,(
% 3.61/1.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.61/1.00    inference(definition_unfolding,[],[f67,f91])).
% 3.61/1.00  
% 3.61/1.00  fof(f127,plain,(
% 3.61/1.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 3.61/1.00    inference(equality_resolution,[],[f110])).
% 3.61/1.00  
% 3.61/1.00  fof(f81,plain,(
% 3.61/1.00    sK3 != sK5 | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))),
% 3.61/1.00    inference(cnf_transformation,[],[f43])).
% 3.61/1.00  
% 3.61/1.00  fof(f113,plain,(
% 3.61/1.00    sK3 != sK5 | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))),
% 3.61/1.00    inference(definition_unfolding,[],[f81,f90,f91])).
% 3.61/1.00  
% 3.61/1.00  fof(f68,plain,(
% 3.61/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.61/1.00    inference(cnf_transformation,[],[f39])).
% 3.61/1.00  
% 3.61/1.00  fof(f109,plain,(
% 3.61/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 3.61/1.00    inference(definition_unfolding,[],[f68,f91])).
% 3.61/1.00  
% 3.61/1.00  fof(f125,plain,(
% 3.61/1.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 3.61/1.00    inference(equality_resolution,[],[f109])).
% 3.61/1.00  
% 3.61/1.00  fof(f126,plain,(
% 3.61/1.00    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 3.61/1.00    inference(equality_resolution,[],[f125])).
% 3.61/1.00  
% 3.61/1.00  cnf(c_5,plain,
% 3.61/1.00      ( r2_hidden(X0,X1)
% 3.61/1.00      | r2_hidden(X0,X2)
% 3.61/1.00      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.61/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_10,plain,
% 3.61/1.00      ( r2_hidden(X0,X1)
% 3.61/1.00      | r2_hidden(X0,X2)
% 3.61/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 3.61/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_28,negated_conjecture,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 3.61/1.00      | r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1164,plain,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 3.61/1.00      | r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_10,c_28]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1174,plain,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 3.61/1.00      | r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_1164,c_10]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,X1)
% 3.61/1.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.61/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1383,plain,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 3.61/1.00      inference(forward_subsumption_resolution,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_1174,c_4]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_5069,plain,
% 3.61/1.00      ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_5,c_1383]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_9,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,X1)
% 3.61/1.00      | ~ r2_hidden(X0,X2)
% 3.61/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 3.61/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1277,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 3.61/1.00      | r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_9,c_1164]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_3,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,X1)
% 3.61/1.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.61/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1482,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_1277,c_3]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1488,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(forward_subsumption_resolution,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_1482,c_10]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_7,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,X1)
% 3.61/1.00      | r2_hidden(X0,X2)
% 3.61/1.00      | r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 3.61/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1780,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_1488,c_7]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_5903,plain,
% 3.61/1.00      ( r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(global_propositional_subsumption,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_5069,c_1488,c_1780]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_26,negated_conjecture,
% 3.61/1.00      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 3.61/1.00      | ~ r2_hidden(sK3,sK4)
% 3.61/1.00      | sK3 = sK5 ),
% 3.61/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_5914,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 3.61/1.00      | sK3 = sK5 ),
% 3.61/1.00      inference(backward_subsumption_resolution,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_5903,c_26]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_8,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,X1)
% 3.61/1.00      | r2_hidden(X0,X2)
% 3.61/1.00      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 3.61/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_6343,plain,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 3.61/1.00      | ~ r2_hidden(sK3,sK4)
% 3.61/1.00      | sK3 = sK5 ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_5914,c_8]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_6358,plain,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 3.61/1.00      | sK3 = sK5 ),
% 3.61/1.00      inference(global_propositional_subsumption,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_6343,c_1488,c_1780,c_5069]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_6705,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 3.61/1.00      | sK3 = sK5 ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_6358,c_9]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_24,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 3.61/1.00      inference(cnf_transformation,[],[f127]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1054,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | sK3 = sK5 ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1331,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,X0)
% 3.61/1.00      | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | r2_hidden(sK3,k5_xboole_0(X0,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_2042,plain,
% 3.61/1.00      ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | ~ r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_1331]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_7570,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 3.61/1.00      | sK3 = sK5 ),
% 3.61/1.00      inference(global_propositional_subsumption,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_6705,c_1054,c_1488,c_1780,c_2042,c_5069]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_7588,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,sK4) | sK3 = sK5 ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_7570,c_4]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_7594,plain,
% 3.61/1.00      ( sK3 = sK5 ),
% 3.61/1.00      inference(global_propositional_subsumption,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_7588,c_1488,c_1780,c_5069]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_27,negated_conjecture,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 3.61/1.00      | sK3 != sK5 ),
% 3.61/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1275,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 3.61/1.00      | ~ r2_hidden(sK3,sK4)
% 3.61/1.00      | sK3 != sK5 ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_9,c_27]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_5915,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 3.61/1.00      | sK3 != sK5 ),
% 3.61/1.00      inference(backward_subsumption_resolution,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_5903,c_1275]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_6353,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 3.61/1.00      | sK3 != sK5 ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_5915,c_8]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_6709,plain,
% 3.61/1.00      ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 3.61/1.00      | sK3 != sK5 ),
% 3.61/1.00      inference(global_propositional_subsumption,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_6353,c_1383]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_6355,plain,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 3.61/1.00      | sK3 != sK5 ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_5915,c_7]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_6723,plain,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 3.61/1.00      | sK3 != sK5 ),
% 3.61/1.00      inference(backward_subsumption_resolution,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_6709,c_6355]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_8419,plain,
% 3.61/1.00      ( r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 3.61/1.00      inference(backward_subsumption_resolution,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_7594,c_6723]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_12826,plain,
% 3.61/1.00      ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | ~ r2_hidden(sK3,sK4) ),
% 3.61/1.00      inference(resolution,[status(thm)],[c_8419,c_9]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_270,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.61/1.00      theory(equality) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_1425,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,X1)
% 3.61/1.00      | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != X1
% 3.61/1.00      | sK3 != X0 ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_270]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4664,plain,
% 3.61/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))
% 3.61/1.00      | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
% 3.61/1.00      | sK3 != X0 ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_1425]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_4667,plain,
% 3.61/1.00      ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 3.61/1.00      | sK3 != sK5 ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_4664]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_268,plain,
% 3.61/1.00      ( X0 != X1
% 3.61/1.00      | X2 != X3
% 3.61/1.00      | X4 != X5
% 3.61/1.00      | X6 != X7
% 3.61/1.00      | X8 != X9
% 3.61/1.00      | X10 != X11
% 3.61/1.00      | X12 != X13
% 3.61/1.00      | X14 != X15
% 3.61/1.00      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 3.61/1.00      theory(equality) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_272,plain,
% 3.61/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 3.61/1.00      | sK5 != sK5 ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_268]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_23,plain,
% 3.61/1.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 3.61/1.00      inference(cnf_transformation,[],[f126]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_37,plain,
% 3.61/1.00      ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(c_34,plain,
% 3.61/1.00      ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 3.61/1.00      | sK5 = sK5 ),
% 3.61/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.61/1.00  
% 3.61/1.00  cnf(contradiction,plain,
% 3.61/1.00      ( $false ),
% 3.61/1.00      inference(minisat,
% 3.61/1.00                [status(thm)],
% 3.61/1.00                [c_12826,c_7588,c_5903,c_4667,c_272,c_37,c_34]) ).
% 3.61/1.00  
% 3.61/1.00  
% 3.61/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/1.00  
% 3.61/1.00  ------                               Statistics
% 3.61/1.00  
% 3.61/1.00  ------ Selected
% 3.61/1.00  
% 3.61/1.00  total_time:                             0.383
% 3.61/1.00  
%------------------------------------------------------------------------------
