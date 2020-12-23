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
% DateTime   : Thu Dec  3 11:35:30 EST 2020

% Result     : Theorem 7.59s
% Output     : CNFRefutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :  156 (6123 expanded)
%              Number of clauses        :   73 ( 681 expanded)
%              Number of leaves         :   25 (1762 expanded)
%              Depth                    :   30
%              Number of atoms          :  442 (15158 expanded)
%              Number of equality atoms :  183 (5741 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f2])).

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
    inference(flattening,[],[f24])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f75,f82])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f83])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f73,f84])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f72,f85])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f86])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f87])).

fof(f114,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,
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

fof(f42,plain,
    ( ( sK3 = sK5
      | ~ r2_hidden(sK3,sK4)
      | ~ r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) )
    & ( ( sK3 != sK5
        & r2_hidden(sK3,sK4) )
      | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f41])).

fof(f79,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f58,f87])).

fof(f89,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f54,f88])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f71,f86])).

fof(f111,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) ),
    inference(definition_unfolding,[],[f79,f89,f90])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f87])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f87])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f94])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,
    ( sK3 = sK5
    | ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,
    ( sK3 = sK5
    | ~ r2_hidden(sK3,sK4)
    | ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) ),
    inference(definition_unfolding,[],[f81,f89,f90])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f67,f90])).

fof(f124,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f108])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f68,f90])).

fof(f122,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f107])).

fof(f123,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f122])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f80,plain,
    ( sK3 != sK5
    | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f42])).

fof(f110,plain,
    ( sK3 != sK5
    | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) ),
    inference(definition_unfolding,[],[f80,f89,f90])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_12,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2506,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))
    | r2_hidden(X4,k5_xboole_0(k5_xboole_0(X1,X2),X3))
    | X4 != X0 ),
    inference(resolution,[status(thm)],[c_229,c_12])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_219,negated_conjecture,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))))
    | r2_hidden(sK3,sK4) ),
    inference(theory_normalisation,[status(thm)],[c_28,c_12,c_0])).

cnf(c_987,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_10,c_219])).

cnf(c_1323,plain,
    ( r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_987,c_10])).

cnf(c_1512,plain,
    ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1323,c_10])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1520,plain,
    ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1512,c_5,c_4])).

cnf(c_2946,plain,
    ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_6,c_1520])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1513,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1323,c_9])).

cnf(c_2982,plain,
    ( r2_hidden(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2946,c_1513,c_1520])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | ~ r2_hidden(sK3,sK4)
    | sK3 = sK5 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_221,negated_conjecture,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))))
    | ~ r2_hidden(sK3,sK4)
    | sK5 = sK3 ),
    inference(theory_normalisation,[status(thm)],[c_26,c_12,c_0])).

cnf(c_3553,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))))
    | sK5 = sK3 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2982,c_221])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3564,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | ~ r2_hidden(sK3,sK4)
    | sK5 = sK3 ),
    inference(resolution,[status(thm)],[c_3553,c_8])).

cnf(c_4353,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | sK5 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3564,c_1513,c_1520,c_2946])).

cnf(c_4370,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | ~ r2_hidden(sK3,sK4)
    | sK5 = sK3 ),
    inference(resolution,[status(thm)],[c_4353,c_9])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_33,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_24,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_36,plain,
    ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_227,plain,
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

cnf(c_230,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_227])).

cnf(c_225,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_936,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_1191,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_936])).

cnf(c_1193,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_224,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1192,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_224])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1062,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_13,c_12])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_910,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_0])).

cnf(c_1072,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1062,c_910])).

cnf(c_573,plain,
    ( sK5 = sK3
    | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_1454,plain,
    ( sK5 = sK3
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))) != iProver_top
    | r2_hidden(sK3,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1072,c_573])).

cnf(c_1473,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | ~ r2_hidden(sK3,sK4)
    | sK5 = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1454])).

cnf(c_830,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_1540,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(sK3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
    | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_1542,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK3 != sK5 ),
    inference(instantiation,[status(thm)],[c_1540])).

cnf(c_27,negated_conjecture,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | sK3 != sK5 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_220,negated_conjecture,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))))
    | sK5 != sK3 ),
    inference(theory_normalisation,[status(thm)],[c_27,c_12,c_0])).

cnf(c_1123,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | ~ r2_hidden(sK3,sK4)
    | sK5 != sK3 ),
    inference(resolution,[status(thm)],[c_9,c_220])).

cnf(c_3554,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
    | sK5 != sK3 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2982,c_1123])).

cnf(c_3573,plain,
    ( r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | ~ r2_hidden(sK3,sK4)
    | sK5 != sK3 ),
    inference(resolution,[status(thm)],[c_3554,c_8])).

cnf(c_572,plain,
    ( sK5 != sK3
    | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_1455,plain,
    ( sK5 != sK3
    | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1072,c_572])).

cnf(c_1474,plain,
    ( r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | sK5 != sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1455])).

cnf(c_4374,plain,
    ( r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | sK5 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3573,c_1474])).

cnf(c_4791,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK5 != sK3 ),
    inference(resolution,[status(thm)],[c_4374,c_9])).

cnf(c_4794,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4370,c_33,c_36,c_230,c_1193,c_1192,c_1473,c_1513,c_1520,c_1542,c_2946,c_4791])).

cnf(c_4805,plain,
    ( sK5 != sK3 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4794,c_4374])).

cnf(c_5448,plain,
    ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_4805,c_4353])).

cnf(c_29230,plain,
    ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_2506,c_5448])).

cnf(c_30082,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | X0 != sK3 ),
    inference(resolution,[status(thm)],[c_29230,c_9])).

cnf(c_35572,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | sK3 != sK3 ),
    inference(resolution,[status(thm)],[c_30082,c_1520])).

cnf(c_35573,plain,
    ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(equality_resolution_simp,[status(thm)],[c_35572])).

cnf(c_1377,plain,
    ( ~ r2_hidden(sK3,X0)
    | r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | r2_hidden(sK3,k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3218,plain,
    ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1377])).

cnf(c_3220,plain,
    ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3218])).

cnf(c_927,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_929,plain,
    ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | sK3 = sK5 ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_802,plain,
    ( sK5 != X0
    | sK5 = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_803,plain,
    ( sK5 != sK5
    | sK5 = sK3
    | sK3 != sK5 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35573,c_4794,c_3220,c_2982,c_1474,c_929,c_803,c_36,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 19:00:22 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running in FOF mode
% 7.59/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.59/1.48  
% 7.59/1.48  ------  iProver source info
% 7.59/1.48  
% 7.59/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.59/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.59/1.48  git: non_committed_changes: false
% 7.59/1.48  git: last_make_outside_of_git: false
% 7.59/1.48  
% 7.59/1.48  ------ 
% 7.59/1.48  ------ Parsing...
% 7.59/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.59/1.48  
% 7.59/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.59/1.48  ------ Proving...
% 7.59/1.48  ------ Problem Properties 
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  clauses                                 29
% 7.59/1.48  conjectures                             3
% 7.59/1.48  EPR                                     0
% 7.59/1.48  Horn                                    20
% 7.59/1.48  unary                                   8
% 7.59/1.48  binary                                  5
% 7.59/1.48  lits                                    70
% 7.59/1.48  lits eq                                 27
% 7.59/1.48  fd_pure                                 0
% 7.59/1.48  fd_pseudo                               0
% 7.59/1.48  fd_cond                                 0
% 7.59/1.48  fd_pseudo_cond                          9
% 7.59/1.48  AC symbols                              1
% 7.59/1.48  
% 7.59/1.48  ------ Input Options Time Limit: Unbounded
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  ------ 
% 7.59/1.48  Current options:
% 7.59/1.48  ------ 
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  ------ Proving...
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  % SZS status Theorem for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  fof(f6,axiom,(
% 7.59/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f56,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f6])).
% 7.59/1.48  
% 7.59/1.48  fof(f2,axiom,(
% 7.59/1.48    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f24,plain,(
% 7.59/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.59/1.48    inference(nnf_transformation,[],[f2])).
% 7.59/1.48  
% 7.59/1.48  fof(f25,plain,(
% 7.59/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.59/1.48    inference(flattening,[],[f24])).
% 7.59/1.48  
% 7.59/1.48  fof(f26,plain,(
% 7.59/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.59/1.48    inference(rectify,[],[f25])).
% 7.59/1.48  
% 7.59/1.48  fof(f27,plain,(
% 7.59/1.48    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f28,plain,(
% 7.59/1.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 7.59/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 7.59/1.48  
% 7.59/1.48  fof(f44,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 7.59/1.48    inference(cnf_transformation,[],[f28])).
% 7.59/1.48  
% 7.59/1.48  fof(f18,axiom,(
% 7.59/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f78,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.59/1.48    inference(cnf_transformation,[],[f18])).
% 7.59/1.48  
% 7.59/1.48  fof(f12,axiom,(
% 7.59/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f72,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f12])).
% 7.59/1.48  
% 7.59/1.48  fof(f13,axiom,(
% 7.59/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f73,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f13])).
% 7.59/1.48  
% 7.59/1.48  fof(f14,axiom,(
% 7.59/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f74,plain,(
% 7.59/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f14])).
% 7.59/1.48  
% 7.59/1.48  fof(f15,axiom,(
% 7.59/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f75,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f15])).
% 7.59/1.48  
% 7.59/1.48  fof(f16,axiom,(
% 7.59/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f76,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f16])).
% 7.59/1.48  
% 7.59/1.48  fof(f17,axiom,(
% 7.59/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f77,plain,(
% 7.59/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f17])).
% 7.59/1.48  
% 7.59/1.48  fof(f82,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.59/1.48    inference(definition_unfolding,[],[f76,f77])).
% 7.59/1.48  
% 7.59/1.48  fof(f83,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.59/1.48    inference(definition_unfolding,[],[f75,f82])).
% 7.59/1.48  
% 7.59/1.48  fof(f84,plain,(
% 7.59/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.59/1.48    inference(definition_unfolding,[],[f74,f83])).
% 7.59/1.48  
% 7.59/1.48  fof(f85,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.59/1.48    inference(definition_unfolding,[],[f73,f84])).
% 7.59/1.48  
% 7.59/1.48  fof(f86,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.59/1.48    inference(definition_unfolding,[],[f72,f85])).
% 7.59/1.48  
% 7.59/1.48  fof(f87,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.59/1.48    inference(definition_unfolding,[],[f78,f86])).
% 7.59/1.48  
% 7.59/1.48  fof(f96,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.59/1.48    inference(definition_unfolding,[],[f44,f87])).
% 7.59/1.48  
% 7.59/1.48  fof(f114,plain,(
% 7.59/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.59/1.48    inference(equality_resolution,[],[f96])).
% 7.59/1.48  
% 7.59/1.48  fof(f3,axiom,(
% 7.59/1.48    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f21,plain,(
% 7.59/1.48    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 7.59/1.48    inference(ennf_transformation,[],[f3])).
% 7.59/1.48  
% 7.59/1.48  fof(f29,plain,(
% 7.59/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 7.59/1.48    inference(nnf_transformation,[],[f21])).
% 7.59/1.48  
% 7.59/1.48  fof(f50,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 7.59/1.48    inference(cnf_transformation,[],[f29])).
% 7.59/1.48  
% 7.59/1.48  fof(f19,conjecture,(
% 7.59/1.48    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f20,negated_conjecture,(
% 7.59/1.48    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.59/1.48    inference(negated_conjecture,[],[f19])).
% 7.59/1.48  
% 7.59/1.48  fof(f23,plain,(
% 7.59/1.48    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 7.59/1.48    inference(ennf_transformation,[],[f20])).
% 7.59/1.48  
% 7.59/1.48  fof(f39,plain,(
% 7.59/1.48    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.59/1.48    inference(nnf_transformation,[],[f23])).
% 7.59/1.48  
% 7.59/1.48  fof(f40,plain,(
% 7.59/1.48    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 7.59/1.48    inference(flattening,[],[f39])).
% 7.59/1.48  
% 7.59/1.48  fof(f41,plain,(
% 7.59/1.48    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK3 = sK5 | ~r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))) & ((sK3 != sK5 & r2_hidden(sK3,sK4)) | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))))),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f42,plain,(
% 7.59/1.48    (sK3 = sK5 | ~r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))) & ((sK3 != sK5 & r2_hidden(sK3,sK4)) | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5))))),
% 7.59/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f40,f41])).
% 7.59/1.48  
% 7.59/1.48  fof(f79,plain,(
% 7.59/1.48    r2_hidden(sK3,sK4) | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))),
% 7.59/1.48    inference(cnf_transformation,[],[f42])).
% 7.59/1.48  
% 7.59/1.48  fof(f4,axiom,(
% 7.59/1.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f54,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f4])).
% 7.59/1.48  
% 7.59/1.48  fof(f8,axiom,(
% 7.59/1.48    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f58,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f8])).
% 7.59/1.48  
% 7.59/1.48  fof(f88,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 7.59/1.48    inference(definition_unfolding,[],[f58,f87])).
% 7.59/1.48  
% 7.59/1.48  fof(f89,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k4_xboole_0(X0,X1)) )),
% 7.59/1.48    inference(definition_unfolding,[],[f54,f88])).
% 7.59/1.48  
% 7.59/1.48  fof(f11,axiom,(
% 7.59/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f71,plain,(
% 7.59/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f11])).
% 7.59/1.48  
% 7.59/1.48  fof(f90,plain,(
% 7.59/1.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.59/1.48    inference(definition_unfolding,[],[f71,f86])).
% 7.59/1.48  
% 7.59/1.48  fof(f111,plain,(
% 7.59/1.48    r2_hidden(sK3,sK4) | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))),
% 7.59/1.48    inference(definition_unfolding,[],[f79,f89,f90])).
% 7.59/1.48  
% 7.59/1.48  fof(f1,axiom,(
% 7.59/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f43,plain,(
% 7.59/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f1])).
% 7.59/1.48  
% 7.59/1.48  fof(f45,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 7.59/1.48    inference(cnf_transformation,[],[f28])).
% 7.59/1.48  
% 7.59/1.48  fof(f95,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.59/1.48    inference(definition_unfolding,[],[f45,f87])).
% 7.59/1.48  
% 7.59/1.48  fof(f113,plain,(
% 7.59/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 7.59/1.48    inference(equality_resolution,[],[f95])).
% 7.59/1.48  
% 7.59/1.48  fof(f46,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 7.59/1.48    inference(cnf_transformation,[],[f28])).
% 7.59/1.48  
% 7.59/1.48  fof(f94,plain,(
% 7.59/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 7.59/1.48    inference(definition_unfolding,[],[f46,f87])).
% 7.59/1.48  
% 7.59/1.48  fof(f112,plain,(
% 7.59/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 7.59/1.48    inference(equality_resolution,[],[f94])).
% 7.59/1.48  
% 7.59/1.48  fof(f51,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 7.59/1.48    inference(cnf_transformation,[],[f29])).
% 7.59/1.48  
% 7.59/1.48  fof(f81,plain,(
% 7.59/1.48    sK3 = sK5 | ~r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))),
% 7.59/1.48    inference(cnf_transformation,[],[f42])).
% 7.59/1.48  
% 7.59/1.48  fof(f109,plain,(
% 7.59/1.48    sK3 = sK5 | ~r2_hidden(sK3,sK4) | ~r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))),
% 7.59/1.48    inference(definition_unfolding,[],[f81,f89,f90])).
% 7.59/1.48  
% 7.59/1.48  fof(f52,plain,(
% 7.59/1.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 7.59/1.48    inference(cnf_transformation,[],[f29])).
% 7.59/1.48  
% 7.59/1.48  fof(f10,axiom,(
% 7.59/1.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f35,plain,(
% 7.59/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.59/1.48    inference(nnf_transformation,[],[f10])).
% 7.59/1.48  
% 7.59/1.48  fof(f36,plain,(
% 7.59/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.59/1.48    inference(rectify,[],[f35])).
% 7.59/1.48  
% 7.59/1.48  fof(f37,plain,(
% 7.59/1.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.59/1.48    introduced(choice_axiom,[])).
% 7.59/1.48  
% 7.59/1.48  fof(f38,plain,(
% 7.59/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.59/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 7.59/1.48  
% 7.59/1.48  fof(f67,plain,(
% 7.59/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.59/1.48    inference(cnf_transformation,[],[f38])).
% 7.59/1.48  
% 7.59/1.48  fof(f108,plain,(
% 7.59/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.59/1.48    inference(definition_unfolding,[],[f67,f90])).
% 7.59/1.48  
% 7.59/1.48  fof(f124,plain,(
% 7.59/1.48    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 7.59/1.48    inference(equality_resolution,[],[f108])).
% 7.59/1.48  
% 7.59/1.48  fof(f68,plain,(
% 7.59/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.59/1.48    inference(cnf_transformation,[],[f38])).
% 7.59/1.48  
% 7.59/1.48  fof(f107,plain,(
% 7.59/1.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 7.59/1.48    inference(definition_unfolding,[],[f68,f90])).
% 7.59/1.48  
% 7.59/1.48  fof(f122,plain,(
% 7.59/1.48    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 7.59/1.48    inference(equality_resolution,[],[f107])).
% 7.59/1.48  
% 7.59/1.48  fof(f123,plain,(
% 7.59/1.48    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 7.59/1.48    inference(equality_resolution,[],[f122])).
% 7.59/1.48  
% 7.59/1.48  fof(f7,axiom,(
% 7.59/1.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f57,plain,(
% 7.59/1.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.59/1.48    inference(cnf_transformation,[],[f7])).
% 7.59/1.48  
% 7.59/1.48  fof(f5,axiom,(
% 7.59/1.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.59/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.59/1.48  
% 7.59/1.48  fof(f55,plain,(
% 7.59/1.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.59/1.48    inference(cnf_transformation,[],[f5])).
% 7.59/1.48  
% 7.59/1.48  fof(f80,plain,(
% 7.59/1.48    sK3 != sK5 | r2_hidden(sK3,k4_xboole_0(sK4,k1_tarski(sK5)))),
% 7.59/1.48    inference(cnf_transformation,[],[f42])).
% 7.59/1.48  
% 7.59/1.48  fof(f110,plain,(
% 7.59/1.48    sK3 != sK5 | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))),
% 7.59/1.48    inference(definition_unfolding,[],[f80,f89,f90])).
% 7.59/1.48  
% 7.59/1.48  cnf(c_229,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.59/1.48      theory(equality) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_12,plain,
% 7.59/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2506,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))
% 7.59/1.48      | r2_hidden(X4,k5_xboole_0(k5_xboole_0(X1,X2),X3))
% 7.59/1.48      | X4 != X0 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_229,c_12]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_6,plain,
% 7.59/1.48      ( r2_hidden(X0,X1)
% 7.59/1.48      | r2_hidden(X0,X2)
% 7.59/1.48      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 7.59/1.48      inference(cnf_transformation,[],[f114]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_10,plain,
% 7.59/1.48      ( r2_hidden(X0,X1)
% 7.59/1.48      | r2_hidden(X0,X2)
% 7.59/1.48      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_28,negated_conjecture,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 7.59/1.48      | r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_0,plain,
% 7.59/1.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.59/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_219,negated_conjecture,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))))
% 7.59/1.48      | r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(theory_normalisation,[status(thm)],[c_28,c_12,c_0]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_987,plain,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 7.59/1.48      | r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_10,c_219]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1323,plain,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 7.59/1.48      | r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_987,c_10]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1512,plain,
% 7.59/1.48      ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 7.59/1.48      | r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_1323,c_10]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,X1)
% 7.59/1.48      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 7.59/1.48      inference(cnf_transformation,[],[f113]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,X1)
% 7.59/1.48      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 7.59/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1520,plain,
% 7.59/1.48      ( r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 7.59/1.48      inference(forward_subsumption_resolution,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_1512,c_5,c_4]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2946,plain,
% 7.59/1.48      ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_6,c_1520]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_9,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,X1)
% 7.59/1.48      | ~ r2_hidden(X0,X2)
% 7.59/1.48      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1513,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 7.59/1.48      | r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_1323,c_9]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_2982,plain,
% 7.59/1.48      ( r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2946,c_1513,c_1520]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_26,negated_conjecture,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4)
% 7.59/1.48      | sK3 = sK5 ),
% 7.59/1.48      inference(cnf_transformation,[],[f109]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_221,negated_conjecture,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4)
% 7.59/1.48      | sK5 = sK3 ),
% 7.59/1.48      inference(theory_normalisation,[status(thm)],[c_26,c_12,c_0]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3553,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))))
% 7.59/1.48      | sK5 = sK3 ),
% 7.59/1.48      inference(backward_subsumption_resolution,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2982,c_221]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_8,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,X1)
% 7.59/1.48      | r2_hidden(X0,X2)
% 7.59/1.48      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3564,plain,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4)
% 7.59/1.48      | sK5 = sK3 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_3553,c_8]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4353,plain,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 7.59/1.48      | sK5 = sK3 ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_3564,c_1513,c_1520,c_2946]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4370,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4)
% 7.59/1.48      | sK5 = sK3 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_4353,c_9]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_25,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 7.59/1.48      inference(cnf_transformation,[],[f124]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_33,plain,
% 7.59/1.48      ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | sK5 = sK5 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_25]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_24,plain,
% 7.59/1.48      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 7.59/1.48      inference(cnf_transformation,[],[f123]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_36,plain,
% 7.59/1.48      ( r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_24]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_227,plain,
% 7.59/1.48      ( X0 != X1
% 7.59/1.48      | X2 != X3
% 7.59/1.48      | X4 != X5
% 7.59/1.48      | X6 != X7
% 7.59/1.48      | X8 != X9
% 7.59/1.48      | X10 != X11
% 7.59/1.48      | X12 != X13
% 7.59/1.48      | X14 != X15
% 7.59/1.48      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 7.59/1.48      theory(equality) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_230,plain,
% 7.59/1.48      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 7.59/1.48      | sK5 != sK5 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_227]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_225,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_936,plain,
% 7.59/1.48      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_225]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1191,plain,
% 7.59/1.48      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_936]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1193,plain,
% 7.59/1.48      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_1191]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_224,plain,( X0 = X0 ),theory(equality) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1192,plain,
% 7.59/1.48      ( sK3 = sK3 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_224]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_13,plain,
% 7.59/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.59/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1062,plain,
% 7.59/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_13,c_12]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_11,plain,
% 7.59/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.59/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_910,plain,
% 7.59/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.59/1.48      inference(superposition,[status(thm)],[c_11,c_0]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1072,plain,
% 7.59/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.59/1.48      inference(demodulation,[status(thm)],[c_1062,c_910]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_573,plain,
% 7.59/1.48      ( sK5 = sK3
% 7.59/1.48      | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))) != iProver_top
% 7.59/1.48      | r2_hidden(sK3,sK4) != iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1454,plain,
% 7.59/1.48      ( sK5 = sK3
% 7.59/1.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))) != iProver_top
% 7.59/1.48      | r2_hidden(sK3,sK4) != iProver_top ),
% 7.59/1.48      inference(demodulation,[status(thm)],[c_1072,c_573]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1473,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4)
% 7.59/1.48      | sK5 = sK3 ),
% 7.59/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1454]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_830,plain,
% 7.59/1.48      ( r2_hidden(X0,X1)
% 7.59/1.48      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2))
% 7.59/1.48      | X0 != X2
% 7.59/1.48      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X2) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_229]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1540,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 7.59/1.48      | r2_hidden(sK3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
% 7.59/1.48      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)
% 7.59/1.48      | sK3 != X0 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_830]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1542,plain,
% 7.59/1.48      ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 7.59/1.48      | sK3 != sK5 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_1540]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_27,negated_conjecture,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 7.59/1.48      | sK3 != sK5 ),
% 7.59/1.48      inference(cnf_transformation,[],[f110]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_220,negated_conjecture,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))))
% 7.59/1.48      | sK5 != sK3 ),
% 7.59/1.48      inference(theory_normalisation,[status(thm)],[c_27,c_12,c_0]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1123,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4)
% 7.59/1.48      | sK5 != sK3 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_9,c_220]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3554,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))
% 7.59/1.48      | sK5 != sK3 ),
% 7.59/1.48      inference(backward_subsumption_resolution,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_2982,c_1123]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3573,plain,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4)
% 7.59/1.48      | sK5 != sK3 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_3554,c_8]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_572,plain,
% 7.59/1.48      ( sK5 != sK3
% 7.59/1.48      | r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))))) = iProver_top ),
% 7.59/1.48      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1455,plain,
% 7.59/1.48      ( sK5 != sK3
% 7.59/1.48      | r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))) = iProver_top ),
% 7.59/1.48      inference(demodulation,[status(thm)],[c_1072,c_572]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1474,plain,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 7.59/1.48      | sK5 != sK3 ),
% 7.59/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1455]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4374,plain,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 7.59/1.48      | sK5 != sK3 ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_3573,c_1474]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4791,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | ~ r2_hidden(sK3,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 7.59/1.48      | sK5 != sK3 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_4374,c_9]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4794,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))) ),
% 7.59/1.48      inference(global_propositional_subsumption,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_4370,c_33,c_36,c_230,c_1193,c_1192,c_1473,c_1513,
% 7.59/1.48                 c_1520,c_1542,c_2946,c_4791]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_4805,plain,
% 7.59/1.48      ( sK5 != sK3 ),
% 7.59/1.48      inference(backward_subsumption_resolution,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_4794,c_4374]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_5448,plain,
% 7.59/1.48      ( r2_hidden(sK3,k5_xboole_0(sK4,k5_xboole_0(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))) ),
% 7.59/1.48      inference(backward_subsumption_resolution,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_4805,c_4353]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_29230,plain,
% 7.59/1.48      ( r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)),k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))))
% 7.59/1.48      | X0 != sK3 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_2506,c_5448]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_30082,plain,
% 7.59/1.48      ( ~ r2_hidden(X0,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.59/1.48      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 7.59/1.48      | X0 != sK3 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_29230,c_9]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_35572,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.59/1.48      | sK3 != sK3 ),
% 7.59/1.48      inference(resolution,[status(thm)],[c_30082,c_1520]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_35573,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 7.59/1.48      inference(equality_resolution_simp,[status(thm)],[c_35572]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_1377,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,X0)
% 7.59/1.48      | r2_hidden(sK3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 7.59/1.48      | r2_hidden(sK3,k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_8]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3218,plain,
% 7.59/1.48      ( r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.59/1.48      | r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_1377]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_3220,plain,
% 7.59/1.48      ( r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | r2_hidden(sK3,k5_xboole_0(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 7.59/1.48      | ~ r2_hidden(sK3,sK4) ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_3218]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_927,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 7.59/1.48      | sK3 = X0 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_25]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_929,plain,
% 7.59/1.48      ( ~ r2_hidden(sK3,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.59/1.48      | sK3 = sK5 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_927]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_802,plain,
% 7.59/1.48      ( sK5 != X0 | sK5 = sK3 | sK3 != X0 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_225]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(c_803,plain,
% 7.59/1.48      ( sK5 != sK5 | sK5 = sK3 | sK3 != sK5 ),
% 7.59/1.48      inference(instantiation,[status(thm)],[c_802]) ).
% 7.59/1.48  
% 7.59/1.48  cnf(contradiction,plain,
% 7.59/1.48      ( $false ),
% 7.59/1.48      inference(minisat,
% 7.59/1.48                [status(thm)],
% 7.59/1.48                [c_35573,c_4794,c_3220,c_2982,c_1474,c_929,c_803,c_36,
% 7.59/1.48                 c_33]) ).
% 7.59/1.48  
% 7.59/1.48  
% 7.59/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.59/1.48  
% 7.59/1.48  ------                               Statistics
% 7.59/1.48  
% 7.59/1.48  ------ Selected
% 7.59/1.48  
% 7.59/1.48  total_time:                             0.851
% 7.59/1.48  
%------------------------------------------------------------------------------
