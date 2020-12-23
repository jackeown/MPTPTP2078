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
% DateTime   : Thu Dec  3 11:32:20 EST 2020

% Result     : Theorem 15.60s
% Output     : CNFRefutation 15.60s
% Verified   : 
% Statistics : Number of formulae       :  168 (2319 expanded)
%              Number of clauses        :   82 ( 335 expanded)
%              Number of leaves         :   24 ( 689 expanded)
%              Depth                    :   24
%              Number of atoms          :  401 (4789 expanded)
%              Number of equality atoms :  254 (4181 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK4
        | k1_tarski(sK2) != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_xboole_0 != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_tarski(sK2) != sK3 )
      & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f48])).

fof(f85,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f81,f89])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f92,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f70,f89])).

fof(f114,plain,(
    k2_enumset1(sK2,sK2,sK2,sK2) = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f85,f90,f92])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f44])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f78,f92,f92])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f77,f92])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f67,f90])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f91])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f84,f89])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f86,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f113,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4
    | k2_enumset1(sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f86,f92,f92])).

fof(f87,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f87,f92])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f55,f91])).

fof(f88,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f111,plain,
    ( k1_xboole_0 != sK4
    | k2_enumset1(sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f88,f92])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f57,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k2_enumset1(X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f57,f91])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f115,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f63,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
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

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f42])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1277,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_30,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_16,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1267,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1826,plain,
    ( r1_tarski(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_1267])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1263,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4438,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = sK3
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1826,c_1263])).

cnf(c_20,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1266,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5364,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,X0) = iProver_top
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4438,c_1266])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_17,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_805,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_7,c_17,c_2])).

cnf(c_1274,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_7935,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_tarski(k2_enumset1(sK3,sK3,sK3,X0)))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5364,c_1274])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1262,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4806,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4438,c_1262])).

cnf(c_9117,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_tarski(k2_enumset1(sK3,sK3,sK3,X0)))) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7935,c_4806])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1270,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9170,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_tarski(k2_enumset1(sK3,sK3,sK3,X0)))) = k1_xboole_0
    | k3_tarski(k2_enumset1(sK3,sK3,sK3,X0)) = X0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9117,c_1270])).

cnf(c_19796,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0
    | k3_tarski(k2_enumset1(sK3,sK3,sK3,sK4)) = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30,c_9170])).

cnf(c_20025,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = sK4
    | k5_xboole_0(sK3,k5_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19796,c_30])).

cnf(c_29,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK3
    | k2_enumset1(sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_4810,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4438,c_29])).

cnf(c_28,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1314,plain,
    ( ~ r1_tarski(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
    | k2_enumset1(sK2,sK2,sK2,sK2) = sK3
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1833,plain,
    ( r1_tarski(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1826])).

cnf(c_4912,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4810,c_29,c_28,c_1314,c_1833])).

cnf(c_20104,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20025,c_29,c_28,c_1314,c_1833])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_806,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) != k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_6,c_17,c_2])).

cnf(c_1275,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_806])).

cnf(c_9623,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_xboole_0
    | r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_1275])).

cnf(c_20212,plain,
    ( sK3 = k1_xboole_0
    | r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_20104,c_9623])).

cnf(c_27,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4812,plain,
    ( sK3 = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4438,c_27])).

cnf(c_20109,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4438,c_20104])).

cnf(c_18,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1535,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_18,c_17])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k2_enumset1(X0,X0,X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_804,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X0)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_9,c_17,c_2])).

cnf(c_8,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1279,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_804,c_8,c_18])).

cnf(c_1450,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1279,c_2])).

cnf(c_1541,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_1535,c_1450])).

cnf(c_1667,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_2,c_1541])).

cnf(c_20347,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20109,c_1667])).

cnf(c_20366,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20212,c_4812,c_20347])).

cnf(c_4794,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4438,c_1263])).

cnf(c_6083,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(sK2,sK2,sK2,sK2)
    | k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_4794])).

cnf(c_15,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1330,plain,
    ( r1_xboole_0(sK3,sK3)
    | k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_1331,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) != k1_xboole_0
    | r1_xboole_0(sK3,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1330])).

cnf(c_809,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1360,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) != X0
    | k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1399,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) != sK3
    | k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1404,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1434,plain,
    ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) = sK3 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1458,plain,
    ( ~ r1_xboole_0(sK3,sK3)
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1459,plain,
    ( r1_xboole_0(sK3,sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_1398,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1443,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_1603,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1443])).

cnf(c_9287,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | k2_enumset1(X0,X0,X0,X1) = k2_enumset1(sK2,sK2,sK2,sK2)
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6083,c_15,c_1331,c_1399,c_1404,c_1434,c_1459,c_1603])).

cnf(c_9288,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(sK2,sK2,sK2,sK2)
    | k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_9287])).

cnf(c_20382,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(sK2,sK2,sK2,sK2)
    | k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20366,c_9288])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | k1_xboole_0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_375,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_33921,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20382,c_375])).

cnf(c_33925,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1277,c_33921])).

cnf(c_34206,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_33925,c_1270])).

cnf(c_20398,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK4)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_20366,c_30])).

cnf(c_50910,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = sK4 ),
    inference(demodulation,[status(thm)],[c_34206,c_20398])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50910,c_4912])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.60/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.60/2.48  
% 15.60/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.60/2.48  
% 15.60/2.48  ------  iProver source info
% 15.60/2.48  
% 15.60/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.60/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.60/2.48  git: non_committed_changes: false
% 15.60/2.48  git: last_make_outside_of_git: false
% 15.60/2.48  
% 15.60/2.48  ------ 
% 15.60/2.48  
% 15.60/2.48  ------ Input Options
% 15.60/2.48  
% 15.60/2.48  --out_options                           all
% 15.60/2.48  --tptp_safe_out                         true
% 15.60/2.48  --problem_path                          ""
% 15.60/2.48  --include_path                          ""
% 15.60/2.48  --clausifier                            res/vclausify_rel
% 15.60/2.48  --clausifier_options                    ""
% 15.60/2.48  --stdin                                 false
% 15.60/2.48  --stats_out                             all
% 15.60/2.48  
% 15.60/2.48  ------ General Options
% 15.60/2.48  
% 15.60/2.48  --fof                                   false
% 15.60/2.48  --time_out_real                         305.
% 15.60/2.48  --time_out_virtual                      -1.
% 15.60/2.48  --symbol_type_check                     false
% 15.60/2.48  --clausify_out                          false
% 15.60/2.48  --sig_cnt_out                           false
% 15.60/2.48  --trig_cnt_out                          false
% 15.60/2.48  --trig_cnt_out_tolerance                1.
% 15.60/2.48  --trig_cnt_out_sk_spl                   false
% 15.60/2.48  --abstr_cl_out                          false
% 15.60/2.48  
% 15.60/2.48  ------ Global Options
% 15.60/2.48  
% 15.60/2.48  --schedule                              default
% 15.60/2.48  --add_important_lit                     false
% 15.60/2.48  --prop_solver_per_cl                    1000
% 15.60/2.48  --min_unsat_core                        false
% 15.60/2.48  --soft_assumptions                      false
% 15.60/2.48  --soft_lemma_size                       3
% 15.60/2.48  --prop_impl_unit_size                   0
% 15.60/2.48  --prop_impl_unit                        []
% 15.60/2.48  --share_sel_clauses                     true
% 15.60/2.48  --reset_solvers                         false
% 15.60/2.48  --bc_imp_inh                            [conj_cone]
% 15.60/2.48  --conj_cone_tolerance                   3.
% 15.60/2.48  --extra_neg_conj                        none
% 15.60/2.48  --large_theory_mode                     true
% 15.60/2.48  --prolific_symb_bound                   200
% 15.60/2.48  --lt_threshold                          2000
% 15.60/2.48  --clause_weak_htbl                      true
% 15.60/2.48  --gc_record_bc_elim                     false
% 15.60/2.48  
% 15.60/2.48  ------ Preprocessing Options
% 15.60/2.48  
% 15.60/2.48  --preprocessing_flag                    true
% 15.60/2.48  --time_out_prep_mult                    0.1
% 15.60/2.48  --splitting_mode                        input
% 15.60/2.48  --splitting_grd                         true
% 15.60/2.48  --splitting_cvd                         false
% 15.60/2.48  --splitting_cvd_svl                     false
% 15.60/2.48  --splitting_nvd                         32
% 15.60/2.48  --sub_typing                            true
% 15.60/2.48  --prep_gs_sim                           true
% 15.60/2.48  --prep_unflatten                        true
% 15.60/2.48  --prep_res_sim                          true
% 15.60/2.48  --prep_upred                            true
% 15.60/2.48  --prep_sem_filter                       exhaustive
% 15.60/2.48  --prep_sem_filter_out                   false
% 15.60/2.48  --pred_elim                             true
% 15.60/2.48  --res_sim_input                         true
% 15.60/2.48  --eq_ax_congr_red                       true
% 15.60/2.48  --pure_diseq_elim                       true
% 15.60/2.48  --brand_transform                       false
% 15.60/2.48  --non_eq_to_eq                          false
% 15.60/2.48  --prep_def_merge                        true
% 15.60/2.48  --prep_def_merge_prop_impl              false
% 15.60/2.48  --prep_def_merge_mbd                    true
% 15.60/2.48  --prep_def_merge_tr_red                 false
% 15.60/2.48  --prep_def_merge_tr_cl                  false
% 15.60/2.48  --smt_preprocessing                     true
% 15.60/2.48  --smt_ac_axioms                         fast
% 15.60/2.48  --preprocessed_out                      false
% 15.60/2.48  --preprocessed_stats                    false
% 15.60/2.48  
% 15.60/2.48  ------ Abstraction refinement Options
% 15.60/2.48  
% 15.60/2.48  --abstr_ref                             []
% 15.60/2.48  --abstr_ref_prep                        false
% 15.60/2.48  --abstr_ref_until_sat                   false
% 15.60/2.48  --abstr_ref_sig_restrict                funpre
% 15.60/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.60/2.48  --abstr_ref_under                       []
% 15.60/2.48  
% 15.60/2.48  ------ SAT Options
% 15.60/2.48  
% 15.60/2.48  --sat_mode                              false
% 15.60/2.48  --sat_fm_restart_options                ""
% 15.60/2.48  --sat_gr_def                            false
% 15.60/2.48  --sat_epr_types                         true
% 15.60/2.48  --sat_non_cyclic_types                  false
% 15.60/2.48  --sat_finite_models                     false
% 15.60/2.48  --sat_fm_lemmas                         false
% 15.60/2.48  --sat_fm_prep                           false
% 15.60/2.48  --sat_fm_uc_incr                        true
% 15.60/2.48  --sat_out_model                         small
% 15.60/2.48  --sat_out_clauses                       false
% 15.60/2.48  
% 15.60/2.48  ------ QBF Options
% 15.60/2.48  
% 15.60/2.48  --qbf_mode                              false
% 15.60/2.48  --qbf_elim_univ                         false
% 15.60/2.48  --qbf_dom_inst                          none
% 15.60/2.48  --qbf_dom_pre_inst                      false
% 15.60/2.48  --qbf_sk_in                             false
% 15.60/2.48  --qbf_pred_elim                         true
% 15.60/2.48  --qbf_split                             512
% 15.60/2.48  
% 15.60/2.48  ------ BMC1 Options
% 15.60/2.48  
% 15.60/2.48  --bmc1_incremental                      false
% 15.60/2.48  --bmc1_axioms                           reachable_all
% 15.60/2.48  --bmc1_min_bound                        0
% 15.60/2.48  --bmc1_max_bound                        -1
% 15.60/2.48  --bmc1_max_bound_default                -1
% 15.60/2.48  --bmc1_symbol_reachability              true
% 15.60/2.48  --bmc1_property_lemmas                  false
% 15.60/2.48  --bmc1_k_induction                      false
% 15.60/2.48  --bmc1_non_equiv_states                 false
% 15.60/2.48  --bmc1_deadlock                         false
% 15.60/2.48  --bmc1_ucm                              false
% 15.60/2.48  --bmc1_add_unsat_core                   none
% 15.60/2.48  --bmc1_unsat_core_children              false
% 15.60/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.60/2.48  --bmc1_out_stat                         full
% 15.60/2.48  --bmc1_ground_init                      false
% 15.60/2.48  --bmc1_pre_inst_next_state              false
% 15.60/2.48  --bmc1_pre_inst_state                   false
% 15.60/2.48  --bmc1_pre_inst_reach_state             false
% 15.60/2.48  --bmc1_out_unsat_core                   false
% 15.60/2.48  --bmc1_aig_witness_out                  false
% 15.60/2.48  --bmc1_verbose                          false
% 15.60/2.48  --bmc1_dump_clauses_tptp                false
% 15.60/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.60/2.48  --bmc1_dump_file                        -
% 15.60/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.60/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.60/2.48  --bmc1_ucm_extend_mode                  1
% 15.60/2.48  --bmc1_ucm_init_mode                    2
% 15.60/2.48  --bmc1_ucm_cone_mode                    none
% 15.60/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.60/2.48  --bmc1_ucm_relax_model                  4
% 15.60/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.60/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.60/2.48  --bmc1_ucm_layered_model                none
% 15.60/2.48  --bmc1_ucm_max_lemma_size               10
% 15.60/2.48  
% 15.60/2.48  ------ AIG Options
% 15.60/2.48  
% 15.60/2.48  --aig_mode                              false
% 15.60/2.48  
% 15.60/2.48  ------ Instantiation Options
% 15.60/2.48  
% 15.60/2.48  --instantiation_flag                    true
% 15.60/2.48  --inst_sos_flag                         true
% 15.60/2.48  --inst_sos_phase                        true
% 15.60/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.60/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.60/2.48  --inst_lit_sel_side                     num_symb
% 15.60/2.48  --inst_solver_per_active                1400
% 15.60/2.48  --inst_solver_calls_frac                1.
% 15.60/2.48  --inst_passive_queue_type               priority_queues
% 15.60/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.60/2.48  --inst_passive_queues_freq              [25;2]
% 15.60/2.48  --inst_dismatching                      true
% 15.60/2.48  --inst_eager_unprocessed_to_passive     true
% 15.60/2.48  --inst_prop_sim_given                   true
% 15.60/2.48  --inst_prop_sim_new                     false
% 15.60/2.48  --inst_subs_new                         false
% 15.60/2.48  --inst_eq_res_simp                      false
% 15.60/2.48  --inst_subs_given                       false
% 15.60/2.48  --inst_orphan_elimination               true
% 15.60/2.48  --inst_learning_loop_flag               true
% 15.60/2.48  --inst_learning_start                   3000
% 15.60/2.48  --inst_learning_factor                  2
% 15.60/2.48  --inst_start_prop_sim_after_learn       3
% 15.60/2.48  --inst_sel_renew                        solver
% 15.60/2.48  --inst_lit_activity_flag                true
% 15.60/2.48  --inst_restr_to_given                   false
% 15.60/2.48  --inst_activity_threshold               500
% 15.60/2.48  --inst_out_proof                        true
% 15.60/2.48  
% 15.60/2.48  ------ Resolution Options
% 15.60/2.48  
% 15.60/2.48  --resolution_flag                       true
% 15.60/2.48  --res_lit_sel                           adaptive
% 15.60/2.48  --res_lit_sel_side                      none
% 15.60/2.48  --res_ordering                          kbo
% 15.60/2.48  --res_to_prop_solver                    active
% 15.60/2.48  --res_prop_simpl_new                    false
% 15.60/2.48  --res_prop_simpl_given                  true
% 15.60/2.48  --res_passive_queue_type                priority_queues
% 15.60/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.60/2.48  --res_passive_queues_freq               [15;5]
% 15.60/2.48  --res_forward_subs                      full
% 15.60/2.48  --res_backward_subs                     full
% 15.60/2.48  --res_forward_subs_resolution           true
% 15.60/2.48  --res_backward_subs_resolution          true
% 15.60/2.48  --res_orphan_elimination                true
% 15.60/2.48  --res_time_limit                        2.
% 15.60/2.48  --res_out_proof                         true
% 15.60/2.48  
% 15.60/2.48  ------ Superposition Options
% 15.60/2.48  
% 15.60/2.48  --superposition_flag                    true
% 15.60/2.48  --sup_passive_queue_type                priority_queues
% 15.60/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.60/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.60/2.48  --demod_completeness_check              fast
% 15.60/2.48  --demod_use_ground                      true
% 15.60/2.48  --sup_to_prop_solver                    passive
% 15.60/2.48  --sup_prop_simpl_new                    true
% 15.60/2.48  --sup_prop_simpl_given                  true
% 15.60/2.48  --sup_fun_splitting                     true
% 15.60/2.48  --sup_smt_interval                      50000
% 15.60/2.48  
% 15.60/2.48  ------ Superposition Simplification Setup
% 15.60/2.48  
% 15.60/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.60/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.60/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.60/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.60/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.60/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.60/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.60/2.48  --sup_immed_triv                        [TrivRules]
% 15.60/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.60/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.60/2.48  --sup_immed_bw_main                     []
% 15.60/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.60/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.60/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.60/2.48  --sup_input_bw                          []
% 15.60/2.48  
% 15.60/2.48  ------ Combination Options
% 15.60/2.48  
% 15.60/2.48  --comb_res_mult                         3
% 15.60/2.48  --comb_sup_mult                         2
% 15.60/2.48  --comb_inst_mult                        10
% 15.60/2.48  
% 15.60/2.48  ------ Debug Options
% 15.60/2.48  
% 15.60/2.48  --dbg_backtrace                         false
% 15.60/2.48  --dbg_dump_prop_clauses                 false
% 15.60/2.48  --dbg_dump_prop_clauses_file            -
% 15.60/2.48  --dbg_out_stat                          false
% 15.60/2.48  ------ Parsing...
% 15.60/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.60/2.48  
% 15.60/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.60/2.48  
% 15.60/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.60/2.48  
% 15.60/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.60/2.48  ------ Proving...
% 15.60/2.48  ------ Problem Properties 
% 15.60/2.48  
% 15.60/2.48  
% 15.60/2.48  clauses                                 31
% 15.60/2.48  conjectures                             4
% 15.60/2.48  EPR                                     4
% 15.60/2.48  Horn                                    26
% 15.60/2.48  unary                                   13
% 15.60/2.48  binary                                  14
% 15.60/2.48  lits                                    53
% 15.60/2.48  lits eq                                 21
% 15.60/2.48  fd_pure                                 0
% 15.60/2.48  fd_pseudo                               0
% 15.60/2.48  fd_cond                                 1
% 15.60/2.48  fd_pseudo_cond                          1
% 15.60/2.48  AC symbols                              1
% 15.60/2.48  
% 15.60/2.48  ------ Schedule dynamic 5 is on 
% 15.60/2.48  
% 15.60/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.60/2.48  
% 15.60/2.48  
% 15.60/2.48  ------ 
% 15.60/2.48  Current options:
% 15.60/2.48  ------ 
% 15.60/2.48  
% 15.60/2.48  ------ Input Options
% 15.60/2.48  
% 15.60/2.48  --out_options                           all
% 15.60/2.48  --tptp_safe_out                         true
% 15.60/2.48  --problem_path                          ""
% 15.60/2.48  --include_path                          ""
% 15.60/2.48  --clausifier                            res/vclausify_rel
% 15.60/2.48  --clausifier_options                    ""
% 15.60/2.48  --stdin                                 false
% 15.60/2.48  --stats_out                             all
% 15.60/2.48  
% 15.60/2.48  ------ General Options
% 15.60/2.48  
% 15.60/2.48  --fof                                   false
% 15.60/2.48  --time_out_real                         305.
% 15.60/2.48  --time_out_virtual                      -1.
% 15.60/2.48  --symbol_type_check                     false
% 15.60/2.48  --clausify_out                          false
% 15.60/2.48  --sig_cnt_out                           false
% 15.60/2.48  --trig_cnt_out                          false
% 15.60/2.48  --trig_cnt_out_tolerance                1.
% 15.60/2.48  --trig_cnt_out_sk_spl                   false
% 15.60/2.48  --abstr_cl_out                          false
% 15.60/2.48  
% 15.60/2.48  ------ Global Options
% 15.60/2.48  
% 15.60/2.48  --schedule                              default
% 15.60/2.48  --add_important_lit                     false
% 15.60/2.48  --prop_solver_per_cl                    1000
% 15.60/2.48  --min_unsat_core                        false
% 15.60/2.48  --soft_assumptions                      false
% 15.60/2.48  --soft_lemma_size                       3
% 15.60/2.48  --prop_impl_unit_size                   0
% 15.60/2.48  --prop_impl_unit                        []
% 15.60/2.48  --share_sel_clauses                     true
% 15.60/2.48  --reset_solvers                         false
% 15.60/2.48  --bc_imp_inh                            [conj_cone]
% 15.60/2.48  --conj_cone_tolerance                   3.
% 15.60/2.48  --extra_neg_conj                        none
% 15.60/2.48  --large_theory_mode                     true
% 15.60/2.48  --prolific_symb_bound                   200
% 15.60/2.48  --lt_threshold                          2000
% 15.60/2.48  --clause_weak_htbl                      true
% 15.60/2.48  --gc_record_bc_elim                     false
% 15.60/2.48  
% 15.60/2.48  ------ Preprocessing Options
% 15.60/2.48  
% 15.60/2.48  --preprocessing_flag                    true
% 15.60/2.48  --time_out_prep_mult                    0.1
% 15.60/2.48  --splitting_mode                        input
% 15.60/2.48  --splitting_grd                         true
% 15.60/2.48  --splitting_cvd                         false
% 15.60/2.48  --splitting_cvd_svl                     false
% 15.60/2.48  --splitting_nvd                         32
% 15.60/2.48  --sub_typing                            true
% 15.60/2.48  --prep_gs_sim                           true
% 15.60/2.48  --prep_unflatten                        true
% 15.60/2.48  --prep_res_sim                          true
% 15.60/2.48  --prep_upred                            true
% 15.60/2.48  --prep_sem_filter                       exhaustive
% 15.60/2.48  --prep_sem_filter_out                   false
% 15.60/2.48  --pred_elim                             true
% 15.60/2.48  --res_sim_input                         true
% 15.60/2.48  --eq_ax_congr_red                       true
% 15.60/2.48  --pure_diseq_elim                       true
% 15.60/2.48  --brand_transform                       false
% 15.60/2.48  --non_eq_to_eq                          false
% 15.60/2.48  --prep_def_merge                        true
% 15.60/2.48  --prep_def_merge_prop_impl              false
% 15.60/2.48  --prep_def_merge_mbd                    true
% 15.60/2.48  --prep_def_merge_tr_red                 false
% 15.60/2.48  --prep_def_merge_tr_cl                  false
% 15.60/2.48  --smt_preprocessing                     true
% 15.60/2.48  --smt_ac_axioms                         fast
% 15.60/2.48  --preprocessed_out                      false
% 15.60/2.48  --preprocessed_stats                    false
% 15.60/2.48  
% 15.60/2.48  ------ Abstraction refinement Options
% 15.60/2.48  
% 15.60/2.48  --abstr_ref                             []
% 15.60/2.48  --abstr_ref_prep                        false
% 15.60/2.48  --abstr_ref_until_sat                   false
% 15.60/2.48  --abstr_ref_sig_restrict                funpre
% 15.60/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.60/2.48  --abstr_ref_under                       []
% 15.60/2.48  
% 15.60/2.48  ------ SAT Options
% 15.60/2.48  
% 15.60/2.48  --sat_mode                              false
% 15.60/2.48  --sat_fm_restart_options                ""
% 15.60/2.48  --sat_gr_def                            false
% 15.60/2.48  --sat_epr_types                         true
% 15.60/2.48  --sat_non_cyclic_types                  false
% 15.60/2.48  --sat_finite_models                     false
% 15.60/2.48  --sat_fm_lemmas                         false
% 15.60/2.48  --sat_fm_prep                           false
% 15.60/2.48  --sat_fm_uc_incr                        true
% 15.60/2.48  --sat_out_model                         small
% 15.60/2.48  --sat_out_clauses                       false
% 15.60/2.48  
% 15.60/2.48  ------ QBF Options
% 15.60/2.48  
% 15.60/2.48  --qbf_mode                              false
% 15.60/2.48  --qbf_elim_univ                         false
% 15.60/2.48  --qbf_dom_inst                          none
% 15.60/2.48  --qbf_dom_pre_inst                      false
% 15.60/2.48  --qbf_sk_in                             false
% 15.60/2.48  --qbf_pred_elim                         true
% 15.60/2.48  --qbf_split                             512
% 15.60/2.48  
% 15.60/2.48  ------ BMC1 Options
% 15.60/2.48  
% 15.60/2.48  --bmc1_incremental                      false
% 15.60/2.48  --bmc1_axioms                           reachable_all
% 15.60/2.48  --bmc1_min_bound                        0
% 15.60/2.48  --bmc1_max_bound                        -1
% 15.60/2.48  --bmc1_max_bound_default                -1
% 15.60/2.48  --bmc1_symbol_reachability              true
% 15.60/2.48  --bmc1_property_lemmas                  false
% 15.60/2.48  --bmc1_k_induction                      false
% 15.60/2.48  --bmc1_non_equiv_states                 false
% 15.60/2.48  --bmc1_deadlock                         false
% 15.60/2.48  --bmc1_ucm                              false
% 15.60/2.48  --bmc1_add_unsat_core                   none
% 15.60/2.48  --bmc1_unsat_core_children              false
% 15.60/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.60/2.48  --bmc1_out_stat                         full
% 15.60/2.48  --bmc1_ground_init                      false
% 15.60/2.48  --bmc1_pre_inst_next_state              false
% 15.60/2.48  --bmc1_pre_inst_state                   false
% 15.60/2.48  --bmc1_pre_inst_reach_state             false
% 15.60/2.48  --bmc1_out_unsat_core                   false
% 15.60/2.48  --bmc1_aig_witness_out                  false
% 15.60/2.48  --bmc1_verbose                          false
% 15.60/2.48  --bmc1_dump_clauses_tptp                false
% 15.60/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.60/2.48  --bmc1_dump_file                        -
% 15.60/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.60/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.60/2.48  --bmc1_ucm_extend_mode                  1
% 15.60/2.48  --bmc1_ucm_init_mode                    2
% 15.60/2.48  --bmc1_ucm_cone_mode                    none
% 15.60/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.60/2.48  --bmc1_ucm_relax_model                  4
% 15.60/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.60/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.60/2.48  --bmc1_ucm_layered_model                none
% 15.60/2.48  --bmc1_ucm_max_lemma_size               10
% 15.60/2.48  
% 15.60/2.48  ------ AIG Options
% 15.60/2.48  
% 15.60/2.48  --aig_mode                              false
% 15.60/2.48  
% 15.60/2.48  ------ Instantiation Options
% 15.60/2.48  
% 15.60/2.48  --instantiation_flag                    true
% 15.60/2.48  --inst_sos_flag                         true
% 15.60/2.48  --inst_sos_phase                        true
% 15.60/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.60/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.60/2.48  --inst_lit_sel_side                     none
% 15.60/2.48  --inst_solver_per_active                1400
% 15.60/2.48  --inst_solver_calls_frac                1.
% 15.60/2.48  --inst_passive_queue_type               priority_queues
% 15.60/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.60/2.48  --inst_passive_queues_freq              [25;2]
% 15.60/2.48  --inst_dismatching                      true
% 15.60/2.48  --inst_eager_unprocessed_to_passive     true
% 15.60/2.48  --inst_prop_sim_given                   true
% 15.60/2.48  --inst_prop_sim_new                     false
% 15.60/2.48  --inst_subs_new                         false
% 15.60/2.48  --inst_eq_res_simp                      false
% 15.60/2.48  --inst_subs_given                       false
% 15.60/2.48  --inst_orphan_elimination               true
% 15.60/2.48  --inst_learning_loop_flag               true
% 15.60/2.48  --inst_learning_start                   3000
% 15.60/2.48  --inst_learning_factor                  2
% 15.60/2.48  --inst_start_prop_sim_after_learn       3
% 15.60/2.48  --inst_sel_renew                        solver
% 15.60/2.48  --inst_lit_activity_flag                true
% 15.60/2.48  --inst_restr_to_given                   false
% 15.60/2.48  --inst_activity_threshold               500
% 15.60/2.48  --inst_out_proof                        true
% 15.60/2.48  
% 15.60/2.48  ------ Resolution Options
% 15.60/2.48  
% 15.60/2.48  --resolution_flag                       false
% 15.60/2.48  --res_lit_sel                           adaptive
% 15.60/2.48  --res_lit_sel_side                      none
% 15.60/2.48  --res_ordering                          kbo
% 15.60/2.48  --res_to_prop_solver                    active
% 15.60/2.48  --res_prop_simpl_new                    false
% 15.60/2.48  --res_prop_simpl_given                  true
% 15.60/2.48  --res_passive_queue_type                priority_queues
% 15.60/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.60/2.48  --res_passive_queues_freq               [15;5]
% 15.60/2.48  --res_forward_subs                      full
% 15.60/2.48  --res_backward_subs                     full
% 15.60/2.48  --res_forward_subs_resolution           true
% 15.60/2.48  --res_backward_subs_resolution          true
% 15.60/2.48  --res_orphan_elimination                true
% 15.60/2.48  --res_time_limit                        2.
% 15.60/2.48  --res_out_proof                         true
% 15.60/2.48  
% 15.60/2.48  ------ Superposition Options
% 15.60/2.48  
% 15.60/2.48  --superposition_flag                    true
% 15.60/2.48  --sup_passive_queue_type                priority_queues
% 15.60/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.60/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.60/2.48  --demod_completeness_check              fast
% 15.60/2.48  --demod_use_ground                      true
% 15.60/2.48  --sup_to_prop_solver                    passive
% 15.60/2.48  --sup_prop_simpl_new                    true
% 15.60/2.48  --sup_prop_simpl_given                  true
% 15.60/2.48  --sup_fun_splitting                     true
% 15.60/2.48  --sup_smt_interval                      50000
% 15.60/2.48  
% 15.60/2.48  ------ Superposition Simplification Setup
% 15.60/2.48  
% 15.60/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.60/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.60/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.60/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.60/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.60/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.60/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.60/2.48  --sup_immed_triv                        [TrivRules]
% 15.60/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.60/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.60/2.48  --sup_immed_bw_main                     []
% 15.60/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.60/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.60/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.60/2.48  --sup_input_bw                          []
% 15.60/2.48  
% 15.60/2.48  ------ Combination Options
% 15.60/2.48  
% 15.60/2.48  --comb_res_mult                         3
% 15.60/2.48  --comb_sup_mult                         2
% 15.60/2.48  --comb_inst_mult                        10
% 15.60/2.48  
% 15.60/2.48  ------ Debug Options
% 15.60/2.48  
% 15.60/2.48  --dbg_backtrace                         false
% 15.60/2.48  --dbg_dump_prop_clauses                 false
% 15.60/2.48  --dbg_dump_prop_clauses_file            -
% 15.60/2.48  --dbg_out_stat                          false
% 15.60/2.48  
% 15.60/2.48  
% 15.60/2.48  
% 15.60/2.48  
% 15.60/2.48  ------ Proving...
% 15.60/2.48  
% 15.60/2.48  
% 15.60/2.48  % SZS status Theorem for theBenchmark.p
% 15.60/2.48  
% 15.60/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.60/2.48  
% 15.60/2.48  fof(f2,axiom,(
% 15.60/2.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f31,plain,(
% 15.60/2.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.60/2.48    inference(ennf_transformation,[],[f2])).
% 15.60/2.48  
% 15.60/2.48  fof(f37,plain,(
% 15.60/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.60/2.48    inference(nnf_transformation,[],[f31])).
% 15.60/2.48  
% 15.60/2.48  fof(f38,plain,(
% 15.60/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.60/2.48    inference(rectify,[],[f37])).
% 15.60/2.48  
% 15.60/2.48  fof(f39,plain,(
% 15.60/2.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.60/2.48    introduced(choice_axiom,[])).
% 15.60/2.48  
% 15.60/2.48  fof(f40,plain,(
% 15.60/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.60/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 15.60/2.48  
% 15.60/2.48  fof(f52,plain,(
% 15.60/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f40])).
% 15.60/2.48  
% 15.60/2.48  fof(f26,conjecture,(
% 15.60/2.48    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f27,negated_conjecture,(
% 15.60/2.48    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 15.60/2.48    inference(negated_conjecture,[],[f26])).
% 15.60/2.48  
% 15.60/2.48  fof(f36,plain,(
% 15.60/2.48    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 15.60/2.48    inference(ennf_transformation,[],[f27])).
% 15.60/2.48  
% 15.60/2.48  fof(f48,plain,(
% 15.60/2.48    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 15.60/2.48    introduced(choice_axiom,[])).
% 15.60/2.48  
% 15.60/2.48  fof(f49,plain,(
% 15.60/2.48    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 15.60/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f36,f48])).
% 15.60/2.48  
% 15.60/2.48  fof(f85,plain,(
% 15.60/2.48    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 15.60/2.48    inference(cnf_transformation,[],[f49])).
% 15.60/2.48  
% 15.60/2.48  fof(f24,axiom,(
% 15.60/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f81,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 15.60/2.48    inference(cnf_transformation,[],[f24])).
% 15.60/2.48  
% 15.60/2.48  fof(f90,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 15.60/2.48    inference(definition_unfolding,[],[f81,f89])).
% 15.60/2.48  
% 15.60/2.48  fof(f15,axiom,(
% 15.60/2.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f70,plain,(
% 15.60/2.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f15])).
% 15.60/2.48  
% 15.60/2.48  fof(f16,axiom,(
% 15.60/2.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f71,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f16])).
% 15.60/2.48  
% 15.60/2.48  fof(f17,axiom,(
% 15.60/2.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f72,plain,(
% 15.60/2.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f17])).
% 15.60/2.48  
% 15.60/2.48  fof(f89,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.60/2.48    inference(definition_unfolding,[],[f71,f72])).
% 15.60/2.48  
% 15.60/2.48  fof(f92,plain,(
% 15.60/2.48    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 15.60/2.48    inference(definition_unfolding,[],[f70,f89])).
% 15.60/2.48  
% 15.60/2.48  fof(f114,plain,(
% 15.60/2.48    k2_enumset1(sK2,sK2,sK2,sK2) = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK4))),
% 15.60/2.48    inference(definition_unfolding,[],[f85,f90,f92])).
% 15.60/2.48  
% 15.60/2.48  fof(f9,axiom,(
% 15.60/2.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f64,plain,(
% 15.60/2.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.60/2.48    inference(cnf_transformation,[],[f9])).
% 15.60/2.48  
% 15.60/2.48  fof(f102,plain,(
% 15.60/2.48    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 15.60/2.48    inference(definition_unfolding,[],[f64,f90])).
% 15.60/2.48  
% 15.60/2.48  fof(f23,axiom,(
% 15.60/2.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f44,plain,(
% 15.60/2.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 15.60/2.48    inference(nnf_transformation,[],[f23])).
% 15.60/2.48  
% 15.60/2.48  fof(f45,plain,(
% 15.60/2.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 15.60/2.48    inference(flattening,[],[f44])).
% 15.60/2.48  
% 15.60/2.48  fof(f78,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 15.60/2.48    inference(cnf_transformation,[],[f45])).
% 15.60/2.48  
% 15.60/2.48  fof(f107,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 15.60/2.48    inference(definition_unfolding,[],[f78,f92,f92])).
% 15.60/2.48  
% 15.60/2.48  fof(f22,axiom,(
% 15.60/2.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f35,plain,(
% 15.60/2.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 15.60/2.48    inference(ennf_transformation,[],[f22])).
% 15.60/2.48  
% 15.60/2.48  fof(f77,plain,(
% 15.60/2.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f35])).
% 15.60/2.48  
% 15.60/2.48  fof(f104,plain,(
% 15.60/2.48    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 15.60/2.48    inference(definition_unfolding,[],[f77,f92])).
% 15.60/2.48  
% 15.60/2.48  fof(f3,axiom,(
% 15.60/2.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f41,plain,(
% 15.60/2.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.60/2.48    inference(nnf_transformation,[],[f3])).
% 15.60/2.48  
% 15.60/2.48  fof(f54,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f41])).
% 15.60/2.48  
% 15.60/2.48  fof(f12,axiom,(
% 15.60/2.48    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f67,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f12])).
% 15.60/2.48  
% 15.60/2.48  fof(f91,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_xboole_0(X0,X1)) )),
% 15.60/2.48    inference(definition_unfolding,[],[f67,f90])).
% 15.60/2.48  
% 15.60/2.48  fof(f98,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.60/2.48    inference(definition_unfolding,[],[f54,f91])).
% 15.60/2.48  
% 15.60/2.48  fof(f10,axiom,(
% 15.60/2.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f65,plain,(
% 15.60/2.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f10])).
% 15.60/2.48  
% 15.60/2.48  fof(f1,axiom,(
% 15.60/2.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f50,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f1])).
% 15.60/2.48  
% 15.60/2.48  fof(f25,axiom,(
% 15.60/2.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f46,plain,(
% 15.60/2.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.60/2.48    inference(nnf_transformation,[],[f25])).
% 15.60/2.48  
% 15.60/2.48  fof(f47,plain,(
% 15.60/2.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.60/2.48    inference(flattening,[],[f46])).
% 15.60/2.48  
% 15.60/2.48  fof(f84,plain,(
% 15.60/2.48    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f47])).
% 15.60/2.48  
% 15.60/2.48  fof(f108,plain,(
% 15.60/2.48    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 15.60/2.48    inference(definition_unfolding,[],[f84,f89])).
% 15.60/2.48  
% 15.60/2.48  fof(f7,axiom,(
% 15.60/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f33,plain,(
% 15.60/2.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.60/2.48    inference(ennf_transformation,[],[f7])).
% 15.60/2.48  
% 15.60/2.48  fof(f61,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f33])).
% 15.60/2.48  
% 15.60/2.48  fof(f101,plain,(
% 15.60/2.48    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 15.60/2.48    inference(definition_unfolding,[],[f61,f90])).
% 15.60/2.48  
% 15.60/2.48  fof(f86,plain,(
% 15.60/2.48    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 15.60/2.48    inference(cnf_transformation,[],[f49])).
% 15.60/2.48  
% 15.60/2.48  fof(f113,plain,(
% 15.60/2.48    k2_enumset1(sK2,sK2,sK2,sK2) != sK4 | k2_enumset1(sK2,sK2,sK2,sK2) != sK3),
% 15.60/2.48    inference(definition_unfolding,[],[f86,f92,f92])).
% 15.60/2.48  
% 15.60/2.48  fof(f87,plain,(
% 15.60/2.48    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 15.60/2.48    inference(cnf_transformation,[],[f49])).
% 15.60/2.48  
% 15.60/2.48  fof(f112,plain,(
% 15.60/2.48    k2_enumset1(sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 15.60/2.48    inference(definition_unfolding,[],[f87,f92])).
% 15.60/2.48  
% 15.60/2.48  fof(f55,plain,(
% 15.60/2.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.60/2.48    inference(cnf_transformation,[],[f41])).
% 15.60/2.48  
% 15.60/2.48  fof(f97,plain,(
% 15.60/2.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) != k1_xboole_0) )),
% 15.60/2.48    inference(definition_unfolding,[],[f55,f91])).
% 15.60/2.48  
% 15.60/2.48  fof(f88,plain,(
% 15.60/2.48    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 15.60/2.48    inference(cnf_transformation,[],[f49])).
% 15.60/2.48  
% 15.60/2.48  fof(f111,plain,(
% 15.60/2.48    k1_xboole_0 != sK4 | k2_enumset1(sK2,sK2,sK2,sK2) != sK3),
% 15.60/2.48    inference(definition_unfolding,[],[f88,f92])).
% 15.60/2.48  
% 15.60/2.48  fof(f11,axiom,(
% 15.60/2.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f66,plain,(
% 15.60/2.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 15.60/2.48    inference(cnf_transformation,[],[f11])).
% 15.60/2.48  
% 15.60/2.48  fof(f5,axiom,(
% 15.60/2.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f29,plain,(
% 15.60/2.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 15.60/2.48    inference(rectify,[],[f5])).
% 15.60/2.48  
% 15.60/2.48  fof(f57,plain,(
% 15.60/2.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 15.60/2.48    inference(cnf_transformation,[],[f29])).
% 15.60/2.48  
% 15.60/2.48  fof(f100,plain,(
% 15.60/2.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k2_enumset1(X0,X0,X0,X0))) = X0) )),
% 15.60/2.48    inference(definition_unfolding,[],[f57,f91])).
% 15.60/2.48  
% 15.60/2.48  fof(f4,axiom,(
% 15.60/2.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f28,plain,(
% 15.60/2.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 15.60/2.48    inference(rectify,[],[f4])).
% 15.60/2.48  
% 15.60/2.48  fof(f56,plain,(
% 15.60/2.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 15.60/2.48    inference(cnf_transformation,[],[f28])).
% 15.60/2.48  
% 15.60/2.48  fof(f99,plain,(
% 15.60/2.48    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 15.60/2.48    inference(definition_unfolding,[],[f56,f90])).
% 15.60/2.48  
% 15.60/2.48  fof(f8,axiom,(
% 15.60/2.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f34,plain,(
% 15.60/2.48    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 15.60/2.48    inference(ennf_transformation,[],[f8])).
% 15.60/2.48  
% 15.60/2.48  fof(f62,plain,(
% 15.60/2.48    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f34])).
% 15.60/2.48  
% 15.60/2.48  fof(f115,plain,(
% 15.60/2.48    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 15.60/2.48    inference(equality_resolution,[],[f62])).
% 15.60/2.48  
% 15.60/2.48  fof(f63,plain,(
% 15.60/2.48    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 15.60/2.48    inference(cnf_transformation,[],[f34])).
% 15.60/2.48  
% 15.60/2.48  fof(f6,axiom,(
% 15.60/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.60/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.60/2.48  
% 15.60/2.48  fof(f30,plain,(
% 15.60/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.60/2.48    inference(rectify,[],[f6])).
% 15.60/2.48  
% 15.60/2.48  fof(f32,plain,(
% 15.60/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 15.60/2.48    inference(ennf_transformation,[],[f30])).
% 15.60/2.48  
% 15.60/2.48  fof(f42,plain,(
% 15.60/2.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 15.60/2.48    introduced(choice_axiom,[])).
% 15.60/2.48  
% 15.60/2.48  fof(f43,plain,(
% 15.60/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 15.60/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f42])).
% 15.60/2.48  
% 15.60/2.48  fof(f60,plain,(
% 15.60/2.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 15.60/2.48    inference(cnf_transformation,[],[f43])).
% 15.60/2.48  
% 15.60/2.48  cnf(c_4,plain,
% 15.60/2.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.60/2.48      inference(cnf_transformation,[],[f52]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1277,plain,
% 15.60/2.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.60/2.48      | r1_tarski(X0,X1) = iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_30,negated_conjecture,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) = k3_tarski(k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 15.60/2.48      inference(cnf_transformation,[],[f114]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_16,plain,
% 15.60/2.48      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 15.60/2.48      inference(cnf_transformation,[],[f102]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1267,plain,
% 15.60/2.48      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1826,plain,
% 15.60/2.48      ( r1_tarski(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_30,c_1267]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_23,plain,
% 15.60/2.48      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 15.60/2.48      | k2_enumset1(X1,X1,X1,X1) = X0
% 15.60/2.48      | k1_xboole_0 = X0 ),
% 15.60/2.48      inference(cnf_transformation,[],[f107]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1263,plain,
% 15.60/2.48      ( k2_enumset1(X0,X0,X0,X0) = X1
% 15.60/2.48      | k1_xboole_0 = X1
% 15.60/2.48      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_4438,plain,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) = sK3 | sK3 = k1_xboole_0 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_1826,c_1263]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20,plain,
% 15.60/2.48      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 15.60/2.48      inference(cnf_transformation,[],[f104]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1266,plain,
% 15.60/2.48      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
% 15.60/2.48      | r2_hidden(X0,X1) = iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_5364,plain,
% 15.60/2.48      ( sK3 = k1_xboole_0
% 15.60/2.48      | r1_xboole_0(sK3,X0) = iProver_top
% 15.60/2.48      | r2_hidden(sK2,X0) = iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_4438,c_1266]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_7,plain,
% 15.60/2.48      ( ~ r1_xboole_0(X0,X1)
% 15.60/2.48      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k1_xboole_0 ),
% 15.60/2.48      inference(cnf_transformation,[],[f98]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_17,plain,
% 15.60/2.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.60/2.48      inference(cnf_transformation,[],[f65]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_2,plain,
% 15.60/2.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 15.60/2.48      inference(cnf_transformation,[],[f50]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_805,plain,
% 15.60/2.48      ( ~ r1_xboole_0(X0,X1)
% 15.60/2.48      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0 ),
% 15.60/2.48      inference(theory_normalisation,[status(thm)],[c_7,c_17,c_2]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1274,plain,
% 15.60/2.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) = k1_xboole_0
% 15.60/2.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_7935,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_tarski(k2_enumset1(sK3,sK3,sK3,X0)))) = k1_xboole_0
% 15.60/2.48      | sK3 = k1_xboole_0
% 15.60/2.48      | r2_hidden(sK2,X0) = iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_5364,c_1274]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_24,plain,
% 15.60/2.48      ( ~ r2_hidden(X0,X1)
% 15.60/2.48      | ~ r2_hidden(X2,X1)
% 15.60/2.48      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) ),
% 15.60/2.48      inference(cnf_transformation,[],[f108]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1262,plain,
% 15.60/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.60/2.48      | r2_hidden(X2,X1) != iProver_top
% 15.60/2.48      | r1_tarski(k2_enumset1(X2,X2,X2,X0),X1) = iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_4806,plain,
% 15.60/2.48      ( sK3 = k1_xboole_0
% 15.60/2.48      | r2_hidden(sK2,X0) != iProver_top
% 15.60/2.48      | r1_tarski(sK3,X0) = iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_4438,c_1262]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_9117,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_tarski(k2_enumset1(sK3,sK3,sK3,X0)))) = k1_xboole_0
% 15.60/2.48      | sK3 = k1_xboole_0
% 15.60/2.48      | r1_tarski(sK3,X0) = iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_7935,c_4806]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_13,plain,
% 15.60/2.48      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
% 15.60/2.48      inference(cnf_transformation,[],[f101]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1270,plain,
% 15.60/2.48      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
% 15.60/2.48      | r1_tarski(X0,X1) != iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_9170,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(X0,k3_tarski(k2_enumset1(sK3,sK3,sK3,X0)))) = k1_xboole_0
% 15.60/2.48      | k3_tarski(k2_enumset1(sK3,sK3,sK3,X0)) = X0
% 15.60/2.48      | sK3 = k1_xboole_0 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_9117,c_1270]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_19796,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0
% 15.60/2.48      | k3_tarski(k2_enumset1(sK3,sK3,sK3,sK4)) = sK4
% 15.60/2.48      | sK3 = k1_xboole_0 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_30,c_9170]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20025,plain,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) = sK4
% 15.60/2.48      | k5_xboole_0(sK3,k5_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0
% 15.60/2.48      | sK3 = k1_xboole_0 ),
% 15.60/2.48      inference(demodulation,[status(thm)],[c_19796,c_30]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_29,negated_conjecture,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK3
% 15.60/2.48      | k2_enumset1(sK2,sK2,sK2,sK2) != sK4 ),
% 15.60/2.48      inference(cnf_transformation,[],[f113]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_4810,plain,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4 | sK3 = k1_xboole_0 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_4438,c_29]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_28,negated_conjecture,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3 ),
% 15.60/2.48      inference(cnf_transformation,[],[f112]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1314,plain,
% 15.60/2.48      ( ~ r1_tarski(sK3,k2_enumset1(sK2,sK2,sK2,sK2))
% 15.60/2.48      | k2_enumset1(sK2,sK2,sK2,sK2) = sK3
% 15.60/2.48      | k1_xboole_0 = sK3 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_23]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1833,plain,
% 15.60/2.48      ( r1_tarski(sK3,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 15.60/2.48      inference(predicate_to_equality_rev,[status(thm)],[c_1826]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_4912,plain,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4 ),
% 15.60/2.48      inference(global_propositional_subsumption,
% 15.60/2.48                [status(thm)],
% 15.60/2.48                [c_4810,c_29,c_28,c_1314,c_1833]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20104,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) = k1_xboole_0
% 15.60/2.48      | sK3 = k1_xboole_0 ),
% 15.60/2.48      inference(global_propositional_subsumption,
% 15.60/2.48                [status(thm)],
% 15.60/2.48                [c_20025,c_29,c_28,c_1314,c_1833]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_6,plain,
% 15.60/2.48      ( r1_xboole_0(X0,X1)
% 15.60/2.48      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_enumset1(X0,X0,X0,X1))) != k1_xboole_0 ),
% 15.60/2.48      inference(cnf_transformation,[],[f97]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_806,plain,
% 15.60/2.48      ( r1_xboole_0(X0,X1)
% 15.60/2.48      | k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) != k1_xboole_0 ),
% 15.60/2.48      inference(theory_normalisation,[status(thm)],[c_6,c_17,c_2]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1275,plain,
% 15.60/2.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) != k1_xboole_0
% 15.60/2.48      | r1_xboole_0(X0,X1) = iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_806]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_9623,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(sK4,k2_enumset1(sK2,sK2,sK2,sK2))) != k1_xboole_0
% 15.60/2.48      | r1_xboole_0(sK3,sK4) = iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_30,c_1275]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20212,plain,
% 15.60/2.48      ( sK3 = k1_xboole_0 | r1_xboole_0(sK3,sK4) = iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_20104,c_9623]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_27,negated_conjecture,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK3 | k1_xboole_0 != sK4 ),
% 15.60/2.48      inference(cnf_transformation,[],[f111]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_4812,plain,
% 15.60/2.48      ( sK3 = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_4438,c_27]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20109,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(sK4,sK3)) = k1_xboole_0
% 15.60/2.48      | sK3 = k1_xboole_0 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_4438,c_20104]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_18,plain,
% 15.60/2.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.60/2.48      inference(cnf_transformation,[],[f66]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1535,plain,
% 15.60/2.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_18,c_17]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_9,plain,
% 15.60/2.48      ( k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k2_enumset1(X0,X0,X0,X0))) = X0 ),
% 15.60/2.48      inference(cnf_transformation,[],[f100]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_804,plain,
% 15.60/2.48      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X0)))) = X0 ),
% 15.60/2.48      inference(theory_normalisation,[status(thm)],[c_9,c_17,c_2]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_8,plain,
% 15.60/2.48      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 15.60/2.48      inference(cnf_transformation,[],[f99]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1279,plain,
% 15.60/2.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.60/2.48      inference(light_normalisation,[status(thm)],[c_804,c_8,c_18]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1450,plain,
% 15.60/2.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_1279,c_2]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1541,plain,
% 15.60/2.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 15.60/2.48      inference(demodulation,[status(thm)],[c_1535,c_1450]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1667,plain,
% 15.60/2.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_2,c_1541]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20347,plain,
% 15.60/2.48      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 15.60/2.48      inference(demodulation,[status(thm)],[c_20109,c_1667]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20366,plain,
% 15.60/2.48      ( sK3 = k1_xboole_0 ),
% 15.60/2.48      inference(global_propositional_subsumption,
% 15.60/2.48                [status(thm)],
% 15.60/2.48                [c_20212,c_4812,c_20347]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_4794,plain,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) = X0
% 15.60/2.48      | sK3 = k1_xboole_0
% 15.60/2.48      | k1_xboole_0 = X0
% 15.60/2.48      | r1_tarski(X0,sK3) != iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_4438,c_1263]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_6083,plain,
% 15.60/2.48      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(sK2,sK2,sK2,sK2)
% 15.60/2.48      | k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 15.60/2.48      | sK3 = k1_xboole_0
% 15.60/2.48      | r2_hidden(X1,sK3) != iProver_top
% 15.60/2.48      | r2_hidden(X0,sK3) != iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_1262,c_4794]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_15,plain,
% 15.60/2.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 15.60/2.48      inference(cnf_transformation,[],[f115]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1330,plain,
% 15.60/2.48      ( r1_xboole_0(sK3,sK3)
% 15.60/2.48      | k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) != k1_xboole_0 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_806]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1331,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) != k1_xboole_0
% 15.60/2.48      | r1_xboole_0(sK3,sK3) = iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_1330]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_809,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1360,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) != X0
% 15.60/2.48      | k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) = k1_xboole_0
% 15.60/2.48      | k1_xboole_0 != X0 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_809]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1399,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) != sK3
% 15.60/2.48      | k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) = k1_xboole_0
% 15.60/2.48      | k1_xboole_0 != sK3 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_1360]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_14,plain,
% 15.60/2.48      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 15.60/2.48      inference(cnf_transformation,[],[f63]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1404,plain,
% 15.60/2.48      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 15.60/2.48      | k1_xboole_0 = k1_xboole_0 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_14]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1434,plain,
% 15.60/2.48      ( k5_xboole_0(sK3,k5_xboole_0(sK3,k3_tarski(k2_enumset1(sK3,sK3,sK3,sK3)))) = sK3 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_804]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_10,plain,
% 15.60/2.48      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 15.60/2.48      inference(cnf_transformation,[],[f60]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1458,plain,
% 15.60/2.48      ( ~ r1_xboole_0(sK3,sK3) | ~ r2_hidden(X0,sK3) ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_10]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1459,plain,
% 15.60/2.48      ( r1_xboole_0(sK3,sK3) != iProver_top
% 15.60/2.48      | r2_hidden(X0,sK3) != iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1398,plain,
% 15.60/2.48      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_809]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1443,plain,
% 15.60/2.48      ( X0 != k1_xboole_0
% 15.60/2.48      | k1_xboole_0 = X0
% 15.60/2.48      | k1_xboole_0 != k1_xboole_0 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_1398]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_1603,plain,
% 15.60/2.48      ( sK3 != k1_xboole_0
% 15.60/2.48      | k1_xboole_0 = sK3
% 15.60/2.48      | k1_xboole_0 != k1_xboole_0 ),
% 15.60/2.48      inference(instantiation,[status(thm)],[c_1443]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_9287,plain,
% 15.60/2.48      ( k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 15.60/2.48      | k2_enumset1(X0,X0,X0,X1) = k2_enumset1(sK2,sK2,sK2,sK2)
% 15.60/2.48      | r2_hidden(X1,sK3) != iProver_top
% 15.60/2.48      | r2_hidden(X0,sK3) != iProver_top ),
% 15.60/2.48      inference(global_propositional_subsumption,
% 15.60/2.48                [status(thm)],
% 15.60/2.48                [c_6083,c_15,c_1331,c_1399,c_1404,c_1434,c_1459,c_1603]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_9288,plain,
% 15.60/2.48      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(sK2,sK2,sK2,sK2)
% 15.60/2.48      | k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 15.60/2.48      | r2_hidden(X0,sK3) != iProver_top
% 15.60/2.48      | r2_hidden(X1,sK3) != iProver_top ),
% 15.60/2.48      inference(renaming,[status(thm)],[c_9287]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20382,plain,
% 15.60/2.48      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(sK2,sK2,sK2,sK2)
% 15.60/2.48      | k2_enumset1(X0,X0,X0,X1) = k1_xboole_0
% 15.60/2.48      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 15.60/2.48      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 15.60/2.48      inference(demodulation,[status(thm)],[c_20366,c_9288]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_373,plain,
% 15.60/2.48      ( ~ r2_hidden(X0,X1)
% 15.60/2.48      | ~ r2_hidden(X0,X2)
% 15.60/2.48      | k1_xboole_0 != X2
% 15.60/2.48      | k1_xboole_0 != X1 ),
% 15.60/2.48      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_374,plain,
% 15.60/2.48      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 15.60/2.48      inference(unflattening,[status(thm)],[c_373]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_375,plain,
% 15.60/2.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.60/2.48      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_33921,plain,
% 15.60/2.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.60/2.48      inference(global_propositional_subsumption,
% 15.60/2.48                [status(thm)],
% 15.60/2.48                [c_20382,c_375]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_33925,plain,
% 15.60/2.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_1277,c_33921]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_34206,plain,
% 15.60/2.48      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 15.60/2.48      inference(superposition,[status(thm)],[c_33925,c_1270]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_20398,plain,
% 15.60/2.48      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK4)) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 15.60/2.48      inference(demodulation,[status(thm)],[c_20366,c_30]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(c_50910,plain,
% 15.60/2.48      ( k2_enumset1(sK2,sK2,sK2,sK2) = sK4 ),
% 15.60/2.48      inference(demodulation,[status(thm)],[c_34206,c_20398]) ).
% 15.60/2.48  
% 15.60/2.48  cnf(contradiction,plain,
% 15.60/2.48      ( $false ),
% 15.60/2.48      inference(minisat,[status(thm)],[c_50910,c_4912]) ).
% 15.60/2.48  
% 15.60/2.48  
% 15.60/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.60/2.48  
% 15.60/2.48  ------                               Statistics
% 15.60/2.48  
% 15.60/2.48  ------ General
% 15.60/2.48  
% 15.60/2.48  abstr_ref_over_cycles:                  0
% 15.60/2.48  abstr_ref_under_cycles:                 0
% 15.60/2.48  gc_basic_clause_elim:                   0
% 15.60/2.48  forced_gc_time:                         0
% 15.60/2.48  parsing_time:                           0.01
% 15.60/2.48  unif_index_cands_time:                  0.
% 15.60/2.48  unif_index_add_time:                    0.
% 15.60/2.48  orderings_time:                         0.
% 15.60/2.48  out_proof_time:                         0.01
% 15.60/2.48  total_time:                             1.769
% 15.60/2.48  num_of_symbols:                         44
% 15.60/2.48  num_of_terms:                           248481
% 15.60/2.48  
% 15.60/2.48  ------ Preprocessing
% 15.60/2.48  
% 15.60/2.48  num_of_splits:                          0
% 15.60/2.48  num_of_split_atoms:                     0
% 15.60/2.48  num_of_reused_defs:                     0
% 15.60/2.48  num_eq_ax_congr_red:                    24
% 15.60/2.48  num_of_sem_filtered_clauses:            1
% 15.60/2.48  num_of_subtypes:                        0
% 15.60/2.48  monotx_restored_types:                  0
% 15.60/2.48  sat_num_of_epr_types:                   0
% 15.60/2.48  sat_num_of_non_cyclic_types:            0
% 15.60/2.48  sat_guarded_non_collapsed_types:        0
% 15.60/2.48  num_pure_diseq_elim:                    0
% 15.60/2.48  simp_replaced_by:                       0
% 15.60/2.48  res_preprocessed:                       110
% 15.60/2.48  prep_upred:                             0
% 15.60/2.48  prep_unflattend:                        63
% 15.60/2.48  smt_new_axioms:                         0
% 15.60/2.48  pred_elim_cands:                        3
% 15.60/2.48  pred_elim:                              0
% 15.60/2.48  pred_elim_cl:                           0
% 15.60/2.48  pred_elim_cycles:                       2
% 15.60/2.48  merged_defs:                            6
% 15.60/2.48  merged_defs_ncl:                        0
% 15.60/2.48  bin_hyper_res:                          6
% 15.60/2.48  prep_cycles:                            3
% 15.60/2.48  pred_elim_time:                         0.008
% 15.60/2.48  splitting_time:                         0.
% 15.60/2.48  sem_filter_time:                        0.
% 15.60/2.48  monotx_time:                            0.
% 15.60/2.48  subtype_inf_time:                       0.
% 15.60/2.48  
% 15.60/2.48  ------ Problem properties
% 15.60/2.48  
% 15.60/2.48  clauses:                                31
% 15.60/2.48  conjectures:                            4
% 15.60/2.48  epr:                                    4
% 15.60/2.48  horn:                                   26
% 15.60/2.48  ground:                                 5
% 15.60/2.48  unary:                                  13
% 15.60/2.48  binary:                                 14
% 15.60/2.48  lits:                                   53
% 15.60/2.48  lits_eq:                                21
% 15.60/2.48  fd_pure:                                0
% 15.60/2.48  fd_pseudo:                              0
% 15.60/2.48  fd_cond:                                1
% 15.60/2.48  fd_pseudo_cond:                         1
% 15.60/2.48  ac_symbols:                             1
% 15.60/2.48  
% 15.60/2.48  ------ Propositional Solver
% 15.60/2.48  
% 15.60/2.48  prop_solver_calls:                      30
% 15.60/2.48  prop_fast_solver_calls:                 911
% 15.60/2.48  smt_solver_calls:                       0
% 15.60/2.48  smt_fast_solver_calls:                  0
% 15.60/2.48  prop_num_of_clauses:                    5958
% 15.60/2.48  prop_preprocess_simplified:             10426
% 15.60/2.48  prop_fo_subsumed:                       40
% 15.60/2.48  prop_solver_time:                       0.
% 15.60/2.48  smt_solver_time:                        0.
% 15.60/2.48  smt_fast_solver_time:                   0.
% 15.60/2.48  prop_fast_solver_time:                  0.
% 15.60/2.48  prop_unsat_core_time:                   0.
% 15.60/2.48  
% 15.60/2.48  ------ QBF
% 15.60/2.48  
% 15.60/2.48  qbf_q_res:                              0
% 15.60/2.48  qbf_num_tautologies:                    0
% 15.60/2.48  qbf_prep_cycles:                        0
% 15.60/2.48  
% 15.60/2.48  ------ BMC1
% 15.60/2.48  
% 15.60/2.48  bmc1_current_bound:                     -1
% 15.60/2.48  bmc1_last_solved_bound:                 -1
% 15.60/2.48  bmc1_unsat_core_size:                   -1
% 15.60/2.48  bmc1_unsat_core_parents_size:           -1
% 15.60/2.48  bmc1_merge_next_fun:                    0
% 15.60/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.60/2.48  
% 15.60/2.48  ------ Instantiation
% 15.60/2.48  
% 15.60/2.48  inst_num_of_clauses:                    1465
% 15.60/2.48  inst_num_in_passive:                    206
% 15.60/2.48  inst_num_in_active:                     628
% 15.60/2.48  inst_num_in_unprocessed:                631
% 15.60/2.48  inst_num_of_loops:                      880
% 15.60/2.48  inst_num_of_learning_restarts:          0
% 15.60/2.48  inst_num_moves_active_passive:          247
% 15.60/2.48  inst_lit_activity:                      0
% 15.60/2.48  inst_lit_activity_moves:                0
% 15.60/2.48  inst_num_tautologies:                   0
% 15.60/2.48  inst_num_prop_implied:                  0
% 15.60/2.48  inst_num_existing_simplified:           0
% 15.60/2.48  inst_num_eq_res_simplified:             0
% 15.60/2.48  inst_num_child_elim:                    0
% 15.60/2.48  inst_num_of_dismatching_blockings:      475
% 15.60/2.48  inst_num_of_non_proper_insts:           1549
% 15.60/2.48  inst_num_of_duplicates:                 0
% 15.60/2.48  inst_inst_num_from_inst_to_res:         0
% 15.60/2.48  inst_dismatching_checking_time:         0.
% 15.60/2.48  
% 15.60/2.48  ------ Resolution
% 15.60/2.48  
% 15.60/2.48  res_num_of_clauses:                     0
% 15.60/2.48  res_num_in_passive:                     0
% 15.60/2.48  res_num_in_active:                      0
% 15.60/2.48  res_num_of_loops:                       113
% 15.60/2.48  res_forward_subset_subsumed:            112
% 15.60/2.48  res_backward_subset_subsumed:           0
% 15.60/2.48  res_forward_subsumed:                   2
% 15.60/2.48  res_backward_subsumed:                  0
% 15.60/2.48  res_forward_subsumption_resolution:     0
% 15.60/2.48  res_backward_subsumption_resolution:    0
% 15.60/2.48  res_clause_to_clause_subsumption:       70746
% 15.60/2.48  res_orphan_elimination:                 0
% 15.60/2.48  res_tautology_del:                      166
% 15.60/2.48  res_num_eq_res_simplified:              0
% 15.60/2.48  res_num_sel_changes:                    0
% 15.60/2.48  res_moves_from_active_to_pass:          0
% 15.60/2.48  
% 15.60/2.48  ------ Superposition
% 15.60/2.48  
% 15.60/2.48  sup_time_total:                         0.
% 15.60/2.48  sup_time_generating:                    0.
% 15.60/2.48  sup_time_sim_full:                      0.
% 15.60/2.48  sup_time_sim_immed:                     0.
% 15.60/2.48  
% 15.60/2.48  sup_num_of_clauses:                     1427
% 15.60/2.48  sup_num_in_active:                      101
% 15.60/2.48  sup_num_in_passive:                     1326
% 15.60/2.48  sup_num_of_loops:                       174
% 15.60/2.48  sup_fw_superposition:                   10607
% 15.60/2.48  sup_bw_superposition:                   5580
% 15.60/2.48  sup_immediate_simplified:               13327
% 15.60/2.48  sup_given_eliminated:                   0
% 15.60/2.48  comparisons_done:                       0
% 15.60/2.48  comparisons_avoided:                    33
% 15.60/2.48  
% 15.60/2.48  ------ Simplifications
% 15.60/2.48  
% 15.60/2.48  
% 15.60/2.48  sim_fw_subset_subsumed:                 7
% 15.60/2.48  sim_bw_subset_subsumed:                 70
% 15.60/2.48  sim_fw_subsumed:                        228
% 15.60/2.48  sim_bw_subsumed:                        9
% 15.60/2.48  sim_fw_subsumption_res:                 0
% 15.60/2.48  sim_bw_subsumption_res:                 0
% 15.60/2.48  sim_tautology_del:                      13
% 15.60/2.48  sim_eq_tautology_del:                   1159
% 15.60/2.48  sim_eq_res_simp:                        2
% 15.60/2.48  sim_fw_demodulated:                     21761
% 15.60/2.48  sim_bw_demodulated:                     45
% 15.60/2.48  sim_light_normalised:                   2787
% 15.60/2.48  sim_joinable_taut:                      296
% 15.60/2.48  sim_joinable_simp:                      0
% 15.60/2.48  sim_ac_normalised:                      0
% 15.60/2.48  sim_smt_subsumption:                    0
% 15.60/2.48  
%------------------------------------------------------------------------------
