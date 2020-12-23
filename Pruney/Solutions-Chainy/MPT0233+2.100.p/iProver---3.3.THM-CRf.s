%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:27 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :  132 (1457 expanded)
%              Number of clauses        :   62 ( 240 expanded)
%              Number of leaves         :   19 ( 408 expanded)
%              Depth                    :   23
%              Number of atoms          :  401 (4890 expanded)
%              Number of equality atoms :  309 (3919 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK3 != sK6
      & sK3 != sK5
      & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( sK3 != sK6
    & sK3 != sK5
    & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f32,f44])).

fof(f79,plain,(
    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f108,plain,(
    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f79,f82,f82])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f42])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f74,f82,f83,f83,f82])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f57,f69,f83])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f109,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f110,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f109])).

fof(f80,plain,(
    sK3 != sK5 ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    sK3 != sK6 ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f69])).

fof(f115,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f69])).

fof(f111,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f99])).

fof(f112,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f111])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f55])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f55,f55])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f47,f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f33])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1028,plain,
    ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1029,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1450,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1028,c_1029])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1623,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,sK5) ),
    inference(superposition,[status(thm)],[c_1450,c_1])).

cnf(c_1620,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK3,sK3,sK3,sK4))) = k2_enumset1(sK5,sK5,sK5,X0) ),
    inference(superposition,[status(thm)],[c_1450,c_1])).

cnf(c_1626,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK4,X0) = k2_enumset1(sK5,sK5,sK5,X0)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1620,c_1])).

cnf(c_1885,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k5_xboole_0(k2_enumset1(sK3,sK3,sK4,X0),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK4,X0))) = k2_enumset1(sK5,sK5,X0,sK5) ),
    inference(superposition,[status(thm)],[c_1626,c_1623])).

cnf(c_7804,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK4,X0,sK5) = k2_enumset1(sK5,sK5,X0,sK5)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1623,c_1885])).

cnf(c_7831,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK4,sK5,sK5) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7804,c_1450])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1037,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8102,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK4,sK5,sK5) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | r2_hidden(sK6,k2_enumset1(sK3,sK3,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7831,c_1037])).

cnf(c_26,negated_conjecture,
    ( sK3 != sK5 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_25,negated_conjecture,
    ( sK3 != sK6 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1069,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,X0,X1))
    | sK3 = X0
    | sK3 = X1
    | sK3 = sK6 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1098,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,X0,sK3))
    | sK3 = X0
    | sK3 = sK6
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1069])).

cnf(c_1168,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,sK3,sK3))
    | sK3 = sK6
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1098])).

cnf(c_1163,plain,
    ( r2_hidden(sK3,k2_enumset1(sK6,sK6,X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1279,plain,
    ( r2_hidden(sK3,k2_enumset1(sK6,sK6,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_1163])).

cnf(c_706,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1229,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1579,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_2322,plain,
    ( sK6 != sK3
    | sK3 = sK6
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_2323,plain,
    ( sK5 != sK3
    | sK3 = sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1579])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1036,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1043,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8540,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1028,c_1043])).

cnf(c_9057,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK4,sK6))) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1626,c_8540])).

cnf(c_1034,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8136,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1034])).

cnf(c_9073,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3 ),
    inference(superposition,[status(thm)],[c_1036,c_8136])).

cnf(c_9690,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9057,c_26,c_25,c_1168,c_1279,c_2323,c_9073])).

cnf(c_9691,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9690])).

cnf(c_9697,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = X0
    | sK6 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9691,c_1034])).

cnf(c_11632,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK5 = sK3
    | sK6 = sK3 ),
    inference(superposition,[status(thm)],[c_1036,c_9697])).

cnf(c_12378,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8102,c_26,c_25,c_1168,c_1279,c_2322,c_2323,c_11632])).

cnf(c_12379,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_12378])).

cnf(c_12390,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = X0
    | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12379,c_1029])).

cnf(c_12386,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK6 = X0
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12379,c_1034])).

cnf(c_17341,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
    | sK6 = sK3 ),
    inference(superposition,[status(thm)],[c_1036,c_12386])).

cnf(c_17679,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12390,c_25,c_1168,c_1279,c_2322,c_17341])).

cnf(c_17699,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17679,c_1037])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1522,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_9,c_2])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4145,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1522,c_3])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1047,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10799,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4145,c_1047])).

cnf(c_10810,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10799,c_9])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_57,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_59,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_10994,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10810,c_59])).

cnf(c_22006,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_17699,c_10994])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:10:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.64/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.64/1.48  
% 7.64/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.48  
% 7.64/1.48  ------  iProver source info
% 7.64/1.48  
% 7.64/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.48  git: non_committed_changes: false
% 7.64/1.48  git: last_make_outside_of_git: false
% 7.64/1.48  
% 7.64/1.48  ------ 
% 7.64/1.48  
% 7.64/1.48  ------ Input Options
% 7.64/1.48  
% 7.64/1.48  --out_options                           all
% 7.64/1.48  --tptp_safe_out                         true
% 7.64/1.48  --problem_path                          ""
% 7.64/1.48  --include_path                          ""
% 7.64/1.48  --clausifier                            res/vclausify_rel
% 7.64/1.48  --clausifier_options                    ""
% 7.64/1.48  --stdin                                 false
% 7.64/1.48  --stats_out                             all
% 7.64/1.48  
% 7.64/1.48  ------ General Options
% 7.64/1.48  
% 7.64/1.48  --fof                                   false
% 7.64/1.48  --time_out_real                         305.
% 7.64/1.48  --time_out_virtual                      -1.
% 7.64/1.48  --symbol_type_check                     false
% 7.64/1.48  --clausify_out                          false
% 7.64/1.48  --sig_cnt_out                           false
% 7.64/1.48  --trig_cnt_out                          false
% 7.64/1.48  --trig_cnt_out_tolerance                1.
% 7.64/1.48  --trig_cnt_out_sk_spl                   false
% 7.64/1.48  --abstr_cl_out                          false
% 7.64/1.48  
% 7.64/1.48  ------ Global Options
% 7.64/1.48  
% 7.64/1.48  --schedule                              default
% 7.64/1.48  --add_important_lit                     false
% 7.64/1.48  --prop_solver_per_cl                    1000
% 7.64/1.48  --min_unsat_core                        false
% 7.64/1.48  --soft_assumptions                      false
% 7.64/1.48  --soft_lemma_size                       3
% 7.64/1.48  --prop_impl_unit_size                   0
% 7.64/1.48  --prop_impl_unit                        []
% 7.64/1.48  --share_sel_clauses                     true
% 7.64/1.48  --reset_solvers                         false
% 7.64/1.48  --bc_imp_inh                            [conj_cone]
% 7.64/1.48  --conj_cone_tolerance                   3.
% 7.64/1.48  --extra_neg_conj                        none
% 7.64/1.48  --large_theory_mode                     true
% 7.64/1.48  --prolific_symb_bound                   200
% 7.64/1.48  --lt_threshold                          2000
% 7.64/1.48  --clause_weak_htbl                      true
% 7.64/1.48  --gc_record_bc_elim                     false
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing Options
% 7.64/1.48  
% 7.64/1.48  --preprocessing_flag                    true
% 7.64/1.48  --time_out_prep_mult                    0.1
% 7.64/1.48  --splitting_mode                        input
% 7.64/1.48  --splitting_grd                         true
% 7.64/1.48  --splitting_cvd                         false
% 7.64/1.48  --splitting_cvd_svl                     false
% 7.64/1.48  --splitting_nvd                         32
% 7.64/1.48  --sub_typing                            true
% 7.64/1.48  --prep_gs_sim                           true
% 7.64/1.48  --prep_unflatten                        true
% 7.64/1.48  --prep_res_sim                          true
% 7.64/1.48  --prep_upred                            true
% 7.64/1.48  --prep_sem_filter                       exhaustive
% 7.64/1.48  --prep_sem_filter_out                   false
% 7.64/1.48  --pred_elim                             true
% 7.64/1.48  --res_sim_input                         true
% 7.64/1.48  --eq_ax_congr_red                       true
% 7.64/1.48  --pure_diseq_elim                       true
% 7.64/1.48  --brand_transform                       false
% 7.64/1.48  --non_eq_to_eq                          false
% 7.64/1.48  --prep_def_merge                        true
% 7.64/1.48  --prep_def_merge_prop_impl              false
% 7.64/1.48  --prep_def_merge_mbd                    true
% 7.64/1.48  --prep_def_merge_tr_red                 false
% 7.64/1.48  --prep_def_merge_tr_cl                  false
% 7.64/1.48  --smt_preprocessing                     true
% 7.64/1.48  --smt_ac_axioms                         fast
% 7.64/1.48  --preprocessed_out                      false
% 7.64/1.48  --preprocessed_stats                    false
% 7.64/1.48  
% 7.64/1.48  ------ Abstraction refinement Options
% 7.64/1.48  
% 7.64/1.48  --abstr_ref                             []
% 7.64/1.48  --abstr_ref_prep                        false
% 7.64/1.48  --abstr_ref_until_sat                   false
% 7.64/1.48  --abstr_ref_sig_restrict                funpre
% 7.64/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.48  --abstr_ref_under                       []
% 7.64/1.48  
% 7.64/1.48  ------ SAT Options
% 7.64/1.48  
% 7.64/1.48  --sat_mode                              false
% 7.64/1.48  --sat_fm_restart_options                ""
% 7.64/1.48  --sat_gr_def                            false
% 7.64/1.48  --sat_epr_types                         true
% 7.64/1.48  --sat_non_cyclic_types                  false
% 7.64/1.48  --sat_finite_models                     false
% 7.64/1.48  --sat_fm_lemmas                         false
% 7.64/1.48  --sat_fm_prep                           false
% 7.64/1.48  --sat_fm_uc_incr                        true
% 7.64/1.48  --sat_out_model                         small
% 7.64/1.48  --sat_out_clauses                       false
% 7.64/1.48  
% 7.64/1.48  ------ QBF Options
% 7.64/1.48  
% 7.64/1.48  --qbf_mode                              false
% 7.64/1.48  --qbf_elim_univ                         false
% 7.64/1.48  --qbf_dom_inst                          none
% 7.64/1.48  --qbf_dom_pre_inst                      false
% 7.64/1.48  --qbf_sk_in                             false
% 7.64/1.48  --qbf_pred_elim                         true
% 7.64/1.48  --qbf_split                             512
% 7.64/1.48  
% 7.64/1.48  ------ BMC1 Options
% 7.64/1.48  
% 7.64/1.48  --bmc1_incremental                      false
% 7.64/1.48  --bmc1_axioms                           reachable_all
% 7.64/1.48  --bmc1_min_bound                        0
% 7.64/1.48  --bmc1_max_bound                        -1
% 7.64/1.48  --bmc1_max_bound_default                -1
% 7.64/1.48  --bmc1_symbol_reachability              true
% 7.64/1.48  --bmc1_property_lemmas                  false
% 7.64/1.48  --bmc1_k_induction                      false
% 7.64/1.48  --bmc1_non_equiv_states                 false
% 7.64/1.48  --bmc1_deadlock                         false
% 7.64/1.48  --bmc1_ucm                              false
% 7.64/1.48  --bmc1_add_unsat_core                   none
% 7.64/1.48  --bmc1_unsat_core_children              false
% 7.64/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.48  --bmc1_out_stat                         full
% 7.64/1.48  --bmc1_ground_init                      false
% 7.64/1.48  --bmc1_pre_inst_next_state              false
% 7.64/1.48  --bmc1_pre_inst_state                   false
% 7.64/1.48  --bmc1_pre_inst_reach_state             false
% 7.64/1.48  --bmc1_out_unsat_core                   false
% 7.64/1.48  --bmc1_aig_witness_out                  false
% 7.64/1.48  --bmc1_verbose                          false
% 7.64/1.48  --bmc1_dump_clauses_tptp                false
% 7.64/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.48  --bmc1_dump_file                        -
% 7.64/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.48  --bmc1_ucm_extend_mode                  1
% 7.64/1.48  --bmc1_ucm_init_mode                    2
% 7.64/1.48  --bmc1_ucm_cone_mode                    none
% 7.64/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.48  --bmc1_ucm_relax_model                  4
% 7.64/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.48  --bmc1_ucm_layered_model                none
% 7.64/1.48  --bmc1_ucm_max_lemma_size               10
% 7.64/1.48  
% 7.64/1.48  ------ AIG Options
% 7.64/1.48  
% 7.64/1.48  --aig_mode                              false
% 7.64/1.48  
% 7.64/1.48  ------ Instantiation Options
% 7.64/1.48  
% 7.64/1.48  --instantiation_flag                    true
% 7.64/1.48  --inst_sos_flag                         true
% 7.64/1.48  --inst_sos_phase                        true
% 7.64/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.48  --inst_lit_sel_side                     num_symb
% 7.64/1.48  --inst_solver_per_active                1400
% 7.64/1.48  --inst_solver_calls_frac                1.
% 7.64/1.48  --inst_passive_queue_type               priority_queues
% 7.64/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.48  --inst_passive_queues_freq              [25;2]
% 7.64/1.48  --inst_dismatching                      true
% 7.64/1.48  --inst_eager_unprocessed_to_passive     true
% 7.64/1.48  --inst_prop_sim_given                   true
% 7.64/1.48  --inst_prop_sim_new                     false
% 7.64/1.48  --inst_subs_new                         false
% 7.64/1.48  --inst_eq_res_simp                      false
% 7.64/1.48  --inst_subs_given                       false
% 7.64/1.48  --inst_orphan_elimination               true
% 7.64/1.48  --inst_learning_loop_flag               true
% 7.64/1.48  --inst_learning_start                   3000
% 7.64/1.48  --inst_learning_factor                  2
% 7.64/1.48  --inst_start_prop_sim_after_learn       3
% 7.64/1.48  --inst_sel_renew                        solver
% 7.64/1.48  --inst_lit_activity_flag                true
% 7.64/1.48  --inst_restr_to_given                   false
% 7.64/1.48  --inst_activity_threshold               500
% 7.64/1.48  --inst_out_proof                        true
% 7.64/1.48  
% 7.64/1.48  ------ Resolution Options
% 7.64/1.48  
% 7.64/1.48  --resolution_flag                       true
% 7.64/1.48  --res_lit_sel                           adaptive
% 7.64/1.48  --res_lit_sel_side                      none
% 7.64/1.48  --res_ordering                          kbo
% 7.64/1.48  --res_to_prop_solver                    active
% 7.64/1.48  --res_prop_simpl_new                    false
% 7.64/1.48  --res_prop_simpl_given                  true
% 7.64/1.48  --res_passive_queue_type                priority_queues
% 7.64/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.48  --res_passive_queues_freq               [15;5]
% 7.64/1.48  --res_forward_subs                      full
% 7.64/1.48  --res_backward_subs                     full
% 7.64/1.48  --res_forward_subs_resolution           true
% 7.64/1.48  --res_backward_subs_resolution          true
% 7.64/1.48  --res_orphan_elimination                true
% 7.64/1.48  --res_time_limit                        2.
% 7.64/1.48  --res_out_proof                         true
% 7.64/1.48  
% 7.64/1.48  ------ Superposition Options
% 7.64/1.48  
% 7.64/1.48  --superposition_flag                    true
% 7.64/1.48  --sup_passive_queue_type                priority_queues
% 7.64/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.48  --demod_completeness_check              fast
% 7.64/1.48  --demod_use_ground                      true
% 7.64/1.48  --sup_to_prop_solver                    passive
% 7.64/1.48  --sup_prop_simpl_new                    true
% 7.64/1.48  --sup_prop_simpl_given                  true
% 7.64/1.48  --sup_fun_splitting                     true
% 7.64/1.48  --sup_smt_interval                      50000
% 7.64/1.48  
% 7.64/1.48  ------ Superposition Simplification Setup
% 7.64/1.48  
% 7.64/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.64/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.64/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.64/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.64/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.64/1.48  --sup_immed_triv                        [TrivRules]
% 7.64/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.48  --sup_immed_bw_main                     []
% 7.64/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.64/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.48  --sup_input_bw                          []
% 7.64/1.48  
% 7.64/1.48  ------ Combination Options
% 7.64/1.48  
% 7.64/1.48  --comb_res_mult                         3
% 7.64/1.48  --comb_sup_mult                         2
% 7.64/1.48  --comb_inst_mult                        10
% 7.64/1.48  
% 7.64/1.48  ------ Debug Options
% 7.64/1.48  
% 7.64/1.48  --dbg_backtrace                         false
% 7.64/1.48  --dbg_dump_prop_clauses                 false
% 7.64/1.48  --dbg_dump_prop_clauses_file            -
% 7.64/1.48  --dbg_out_stat                          false
% 7.64/1.48  ------ Parsing...
% 7.64/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.48  ------ Proving...
% 7.64/1.48  ------ Problem Properties 
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  clauses                                 28
% 7.64/1.48  conjectures                             3
% 7.64/1.48  EPR                                     3
% 7.64/1.48  Horn                                    23
% 7.64/1.48  unary                                   17
% 7.64/1.48  binary                                  5
% 7.64/1.48  lits                                    50
% 7.64/1.48  lits eq                                 27
% 7.64/1.48  fd_pure                                 0
% 7.64/1.48  fd_pseudo                               0
% 7.64/1.48  fd_cond                                 1
% 7.64/1.48  fd_pseudo_cond                          5
% 7.64/1.48  AC symbols                              0
% 7.64/1.48  
% 7.64/1.48  ------ Schedule dynamic 5 is on 
% 7.64/1.48  
% 7.64/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  ------ 
% 7.64/1.48  Current options:
% 7.64/1.48  ------ 
% 7.64/1.48  
% 7.64/1.48  ------ Input Options
% 7.64/1.48  
% 7.64/1.48  --out_options                           all
% 7.64/1.48  --tptp_safe_out                         true
% 7.64/1.48  --problem_path                          ""
% 7.64/1.48  --include_path                          ""
% 7.64/1.48  --clausifier                            res/vclausify_rel
% 7.64/1.48  --clausifier_options                    ""
% 7.64/1.48  --stdin                                 false
% 7.64/1.48  --stats_out                             all
% 7.64/1.48  
% 7.64/1.48  ------ General Options
% 7.64/1.48  
% 7.64/1.48  --fof                                   false
% 7.64/1.48  --time_out_real                         305.
% 7.64/1.48  --time_out_virtual                      -1.
% 7.64/1.48  --symbol_type_check                     false
% 7.64/1.48  --clausify_out                          false
% 7.64/1.48  --sig_cnt_out                           false
% 7.64/1.48  --trig_cnt_out                          false
% 7.64/1.48  --trig_cnt_out_tolerance                1.
% 7.64/1.48  --trig_cnt_out_sk_spl                   false
% 7.64/1.48  --abstr_cl_out                          false
% 7.64/1.48  
% 7.64/1.48  ------ Global Options
% 7.64/1.48  
% 7.64/1.48  --schedule                              default
% 7.64/1.48  --add_important_lit                     false
% 7.64/1.48  --prop_solver_per_cl                    1000
% 7.64/1.48  --min_unsat_core                        false
% 7.64/1.48  --soft_assumptions                      false
% 7.64/1.48  --soft_lemma_size                       3
% 7.64/1.48  --prop_impl_unit_size                   0
% 7.64/1.48  --prop_impl_unit                        []
% 7.64/1.48  --share_sel_clauses                     true
% 7.64/1.48  --reset_solvers                         false
% 7.64/1.48  --bc_imp_inh                            [conj_cone]
% 7.64/1.48  --conj_cone_tolerance                   3.
% 7.64/1.48  --extra_neg_conj                        none
% 7.64/1.48  --large_theory_mode                     true
% 7.64/1.48  --prolific_symb_bound                   200
% 7.64/1.48  --lt_threshold                          2000
% 7.64/1.48  --clause_weak_htbl                      true
% 7.64/1.48  --gc_record_bc_elim                     false
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing Options
% 7.64/1.48  
% 7.64/1.48  --preprocessing_flag                    true
% 7.64/1.48  --time_out_prep_mult                    0.1
% 7.64/1.48  --splitting_mode                        input
% 7.64/1.48  --splitting_grd                         true
% 7.64/1.48  --splitting_cvd                         false
% 7.64/1.48  --splitting_cvd_svl                     false
% 7.64/1.48  --splitting_nvd                         32
% 7.64/1.48  --sub_typing                            true
% 7.64/1.48  --prep_gs_sim                           true
% 7.64/1.48  --prep_unflatten                        true
% 7.64/1.48  --prep_res_sim                          true
% 7.64/1.48  --prep_upred                            true
% 7.64/1.48  --prep_sem_filter                       exhaustive
% 7.64/1.48  --prep_sem_filter_out                   false
% 7.64/1.48  --pred_elim                             true
% 7.64/1.48  --res_sim_input                         true
% 7.64/1.48  --eq_ax_congr_red                       true
% 7.64/1.48  --pure_diseq_elim                       true
% 7.64/1.48  --brand_transform                       false
% 7.64/1.48  --non_eq_to_eq                          false
% 7.64/1.48  --prep_def_merge                        true
% 7.64/1.48  --prep_def_merge_prop_impl              false
% 7.64/1.48  --prep_def_merge_mbd                    true
% 7.64/1.48  --prep_def_merge_tr_red                 false
% 7.64/1.48  --prep_def_merge_tr_cl                  false
% 7.64/1.48  --smt_preprocessing                     true
% 7.64/1.48  --smt_ac_axioms                         fast
% 7.64/1.48  --preprocessed_out                      false
% 7.64/1.48  --preprocessed_stats                    false
% 7.64/1.48  
% 7.64/1.48  ------ Abstraction refinement Options
% 7.64/1.48  
% 7.64/1.48  --abstr_ref                             []
% 7.64/1.48  --abstr_ref_prep                        false
% 7.64/1.48  --abstr_ref_until_sat                   false
% 7.64/1.48  --abstr_ref_sig_restrict                funpre
% 7.64/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.64/1.48  --abstr_ref_under                       []
% 7.64/1.48  
% 7.64/1.48  ------ SAT Options
% 7.64/1.48  
% 7.64/1.48  --sat_mode                              false
% 7.64/1.48  --sat_fm_restart_options                ""
% 7.64/1.48  --sat_gr_def                            false
% 7.64/1.48  --sat_epr_types                         true
% 7.64/1.48  --sat_non_cyclic_types                  false
% 7.64/1.48  --sat_finite_models                     false
% 7.64/1.48  --sat_fm_lemmas                         false
% 7.64/1.48  --sat_fm_prep                           false
% 7.64/1.48  --sat_fm_uc_incr                        true
% 7.64/1.48  --sat_out_model                         small
% 7.64/1.48  --sat_out_clauses                       false
% 7.64/1.48  
% 7.64/1.48  ------ QBF Options
% 7.64/1.48  
% 7.64/1.48  --qbf_mode                              false
% 7.64/1.48  --qbf_elim_univ                         false
% 7.64/1.48  --qbf_dom_inst                          none
% 7.64/1.48  --qbf_dom_pre_inst                      false
% 7.64/1.48  --qbf_sk_in                             false
% 7.64/1.48  --qbf_pred_elim                         true
% 7.64/1.48  --qbf_split                             512
% 7.64/1.48  
% 7.64/1.48  ------ BMC1 Options
% 7.64/1.48  
% 7.64/1.48  --bmc1_incremental                      false
% 7.64/1.48  --bmc1_axioms                           reachable_all
% 7.64/1.48  --bmc1_min_bound                        0
% 7.64/1.48  --bmc1_max_bound                        -1
% 7.64/1.48  --bmc1_max_bound_default                -1
% 7.64/1.48  --bmc1_symbol_reachability              true
% 7.64/1.48  --bmc1_property_lemmas                  false
% 7.64/1.48  --bmc1_k_induction                      false
% 7.64/1.48  --bmc1_non_equiv_states                 false
% 7.64/1.48  --bmc1_deadlock                         false
% 7.64/1.48  --bmc1_ucm                              false
% 7.64/1.48  --bmc1_add_unsat_core                   none
% 7.64/1.48  --bmc1_unsat_core_children              false
% 7.64/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.64/1.48  --bmc1_out_stat                         full
% 7.64/1.48  --bmc1_ground_init                      false
% 7.64/1.48  --bmc1_pre_inst_next_state              false
% 7.64/1.48  --bmc1_pre_inst_state                   false
% 7.64/1.48  --bmc1_pre_inst_reach_state             false
% 7.64/1.48  --bmc1_out_unsat_core                   false
% 7.64/1.48  --bmc1_aig_witness_out                  false
% 7.64/1.48  --bmc1_verbose                          false
% 7.64/1.48  --bmc1_dump_clauses_tptp                false
% 7.64/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.64/1.48  --bmc1_dump_file                        -
% 7.64/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.64/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.64/1.48  --bmc1_ucm_extend_mode                  1
% 7.64/1.48  --bmc1_ucm_init_mode                    2
% 7.64/1.48  --bmc1_ucm_cone_mode                    none
% 7.64/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.64/1.48  --bmc1_ucm_relax_model                  4
% 7.64/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.64/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.64/1.48  --bmc1_ucm_layered_model                none
% 7.64/1.48  --bmc1_ucm_max_lemma_size               10
% 7.64/1.48  
% 7.64/1.48  ------ AIG Options
% 7.64/1.48  
% 7.64/1.48  --aig_mode                              false
% 7.64/1.48  
% 7.64/1.48  ------ Instantiation Options
% 7.64/1.48  
% 7.64/1.48  --instantiation_flag                    true
% 7.64/1.48  --inst_sos_flag                         true
% 7.64/1.48  --inst_sos_phase                        true
% 7.64/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.64/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.64/1.48  --inst_lit_sel_side                     none
% 7.64/1.48  --inst_solver_per_active                1400
% 7.64/1.48  --inst_solver_calls_frac                1.
% 7.64/1.48  --inst_passive_queue_type               priority_queues
% 7.64/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.64/1.48  --inst_passive_queues_freq              [25;2]
% 7.64/1.48  --inst_dismatching                      true
% 7.64/1.48  --inst_eager_unprocessed_to_passive     true
% 7.64/1.48  --inst_prop_sim_given                   true
% 7.64/1.48  --inst_prop_sim_new                     false
% 7.64/1.48  --inst_subs_new                         false
% 7.64/1.48  --inst_eq_res_simp                      false
% 7.64/1.48  --inst_subs_given                       false
% 7.64/1.48  --inst_orphan_elimination               true
% 7.64/1.48  --inst_learning_loop_flag               true
% 7.64/1.48  --inst_learning_start                   3000
% 7.64/1.48  --inst_learning_factor                  2
% 7.64/1.48  --inst_start_prop_sim_after_learn       3
% 7.64/1.48  --inst_sel_renew                        solver
% 7.64/1.48  --inst_lit_activity_flag                true
% 7.64/1.48  --inst_restr_to_given                   false
% 7.64/1.48  --inst_activity_threshold               500
% 7.64/1.48  --inst_out_proof                        true
% 7.64/1.48  
% 7.64/1.48  ------ Resolution Options
% 7.64/1.48  
% 7.64/1.48  --resolution_flag                       false
% 7.64/1.48  --res_lit_sel                           adaptive
% 7.64/1.48  --res_lit_sel_side                      none
% 7.64/1.48  --res_ordering                          kbo
% 7.64/1.48  --res_to_prop_solver                    active
% 7.64/1.48  --res_prop_simpl_new                    false
% 7.64/1.48  --res_prop_simpl_given                  true
% 7.64/1.48  --res_passive_queue_type                priority_queues
% 7.64/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.64/1.48  --res_passive_queues_freq               [15;5]
% 7.64/1.48  --res_forward_subs                      full
% 7.64/1.48  --res_backward_subs                     full
% 7.64/1.48  --res_forward_subs_resolution           true
% 7.64/1.48  --res_backward_subs_resolution          true
% 7.64/1.48  --res_orphan_elimination                true
% 7.64/1.48  --res_time_limit                        2.
% 7.64/1.48  --res_out_proof                         true
% 7.64/1.48  
% 7.64/1.48  ------ Superposition Options
% 7.64/1.48  
% 7.64/1.48  --superposition_flag                    true
% 7.64/1.48  --sup_passive_queue_type                priority_queues
% 7.64/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.64/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.64/1.48  --demod_completeness_check              fast
% 7.64/1.48  --demod_use_ground                      true
% 7.64/1.48  --sup_to_prop_solver                    passive
% 7.64/1.48  --sup_prop_simpl_new                    true
% 7.64/1.48  --sup_prop_simpl_given                  true
% 7.64/1.48  --sup_fun_splitting                     true
% 7.64/1.48  --sup_smt_interval                      50000
% 7.64/1.48  
% 7.64/1.48  ------ Superposition Simplification Setup
% 7.64/1.48  
% 7.64/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.64/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.64/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.64/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.64/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.64/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.64/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.64/1.48  --sup_immed_triv                        [TrivRules]
% 7.64/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.48  --sup_immed_bw_main                     []
% 7.64/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.64/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.64/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.64/1.48  --sup_input_bw                          []
% 7.64/1.48  
% 7.64/1.48  ------ Combination Options
% 7.64/1.48  
% 7.64/1.48  --comb_res_mult                         3
% 7.64/1.48  --comb_sup_mult                         2
% 7.64/1.48  --comb_inst_mult                        10
% 7.64/1.48  
% 7.64/1.48  ------ Debug Options
% 7.64/1.48  
% 7.64/1.48  --dbg_backtrace                         false
% 7.64/1.48  --dbg_dump_prop_clauses                 false
% 7.64/1.48  --dbg_dump_prop_clauses_file            -
% 7.64/1.48  --dbg_out_stat                          false
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  ------ Proving...
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  % SZS status Theorem for theBenchmark.p
% 7.64/1.48  
% 7.64/1.48   Resolution empty clause
% 7.64/1.48  
% 7.64/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.48  
% 7.64/1.48  fof(f22,conjecture,(
% 7.64/1.48    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f23,negated_conjecture,(
% 7.64/1.48    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.64/1.48    inference(negated_conjecture,[],[f22])).
% 7.64/1.48  
% 7.64/1.48  fof(f32,plain,(
% 7.64/1.48    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 7.64/1.48    inference(ennf_transformation,[],[f23])).
% 7.64/1.48  
% 7.64/1.48  fof(f44,plain,(
% 7.64/1.48    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6)))),
% 7.64/1.48    introduced(choice_axiom,[])).
% 7.64/1.48  
% 7.64/1.48  fof(f45,plain,(
% 7.64/1.48    sK3 != sK6 & sK3 != sK5 & r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.64/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f32,f44])).
% 7.64/1.48  
% 7.64/1.48  fof(f79,plain,(
% 7.64/1.48    r1_tarski(k2_tarski(sK3,sK4),k2_tarski(sK5,sK6))),
% 7.64/1.48    inference(cnf_transformation,[],[f45])).
% 7.64/1.48  
% 7.64/1.48  fof(f15,axiom,(
% 7.64/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f68,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f15])).
% 7.64/1.48  
% 7.64/1.48  fof(f16,axiom,(
% 7.64/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f69,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f16])).
% 7.64/1.48  
% 7.64/1.48  fof(f82,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f68,f69])).
% 7.64/1.48  
% 7.64/1.48  fof(f108,plain,(
% 7.64/1.48    r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))),
% 7.64/1.48    inference(definition_unfolding,[],[f79,f82,f82])).
% 7.64/1.48  
% 7.64/1.48  fof(f21,axiom,(
% 7.64/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f31,plain,(
% 7.64/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 7.64/1.48    inference(ennf_transformation,[],[f21])).
% 7.64/1.48  
% 7.64/1.48  fof(f42,plain,(
% 7.64/1.48    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.64/1.48    inference(nnf_transformation,[],[f31])).
% 7.64/1.48  
% 7.64/1.48  fof(f43,plain,(
% 7.64/1.48    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 7.64/1.48    inference(flattening,[],[f42])).
% 7.64/1.48  
% 7.64/1.48  fof(f74,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 7.64/1.48    inference(cnf_transformation,[],[f43])).
% 7.64/1.48  
% 7.64/1.48  fof(f14,axiom,(
% 7.64/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f67,plain,(
% 7.64/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f14])).
% 7.64/1.48  
% 7.64/1.48  fof(f83,plain,(
% 7.64/1.48    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f67,f82])).
% 7.64/1.48  
% 7.64/1.48  fof(f107,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 7.64/1.48    inference(definition_unfolding,[],[f74,f82,f83,f83,f82])).
% 7.64/1.48  
% 7.64/1.48  fof(f13,axiom,(
% 7.64/1.48    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f66,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f13])).
% 7.64/1.48  
% 7.64/1.48  fof(f11,axiom,(
% 7.64/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f57,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f11])).
% 7.64/1.48  
% 7.64/1.48  fof(f87,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f66,f57,f69,f83])).
% 7.64/1.48  
% 7.64/1.48  fof(f12,axiom,(
% 7.64/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f30,plain,(
% 7.64/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.64/1.48    inference(ennf_transformation,[],[f12])).
% 7.64/1.48  
% 7.64/1.48  fof(f37,plain,(
% 7.64/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.64/1.48    inference(nnf_transformation,[],[f30])).
% 7.64/1.48  
% 7.64/1.48  fof(f38,plain,(
% 7.64/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.64/1.48    inference(flattening,[],[f37])).
% 7.64/1.48  
% 7.64/1.48  fof(f39,plain,(
% 7.64/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.64/1.48    inference(rectify,[],[f38])).
% 7.64/1.48  
% 7.64/1.48  fof(f40,plain,(
% 7.64/1.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 7.64/1.48    introduced(choice_axiom,[])).
% 7.64/1.48  
% 7.64/1.48  fof(f41,plain,(
% 7.64/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.64/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 7.64/1.48  
% 7.64/1.48  fof(f61,plain,(
% 7.64/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.64/1.48    inference(cnf_transformation,[],[f41])).
% 7.64/1.48  
% 7.64/1.48  fof(f98,plain,(
% 7.64/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.64/1.48    inference(definition_unfolding,[],[f61,f69])).
% 7.64/1.48  
% 7.64/1.48  fof(f109,plain,(
% 7.64/1.48    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 7.64/1.48    inference(equality_resolution,[],[f98])).
% 7.64/1.48  
% 7.64/1.48  fof(f110,plain,(
% 7.64/1.48    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 7.64/1.48    inference(equality_resolution,[],[f109])).
% 7.64/1.48  
% 7.64/1.48  fof(f80,plain,(
% 7.64/1.48    sK3 != sK5),
% 7.64/1.48    inference(cnf_transformation,[],[f45])).
% 7.64/1.48  
% 7.64/1.48  fof(f81,plain,(
% 7.64/1.48    sK3 != sK6),
% 7.64/1.48    inference(cnf_transformation,[],[f45])).
% 7.64/1.48  
% 7.64/1.48  fof(f58,plain,(
% 7.64/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.64/1.48    inference(cnf_transformation,[],[f41])).
% 7.64/1.48  
% 7.64/1.48  fof(f101,plain,(
% 7.64/1.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.64/1.48    inference(definition_unfolding,[],[f58,f69])).
% 7.64/1.48  
% 7.64/1.48  fof(f115,plain,(
% 7.64/1.48    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 7.64/1.48    inference(equality_resolution,[],[f101])).
% 7.64/1.48  
% 7.64/1.48  fof(f60,plain,(
% 7.64/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.64/1.48    inference(cnf_transformation,[],[f41])).
% 7.64/1.48  
% 7.64/1.48  fof(f99,plain,(
% 7.64/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.64/1.48    inference(definition_unfolding,[],[f60,f69])).
% 7.64/1.48  
% 7.64/1.48  fof(f111,plain,(
% 7.64/1.48    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 7.64/1.48    inference(equality_resolution,[],[f99])).
% 7.64/1.48  
% 7.64/1.48  fof(f112,plain,(
% 7.64/1.48    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 7.64/1.48    inference(equality_resolution,[],[f111])).
% 7.64/1.48  
% 7.64/1.48  fof(f7,axiom,(
% 7.64/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f29,plain,(
% 7.64/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.64/1.48    inference(ennf_transformation,[],[f7])).
% 7.64/1.48  
% 7.64/1.48  fof(f53,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f29])).
% 7.64/1.48  
% 7.64/1.48  fof(f9,axiom,(
% 7.64/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f55,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.64/1.48    inference(cnf_transformation,[],[f9])).
% 7.64/1.48  
% 7.64/1.48  fof(f93,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f53,f55])).
% 7.64/1.48  
% 7.64/1.48  fof(f8,axiom,(
% 7.64/1.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f54,plain,(
% 7.64/1.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.64/1.48    inference(cnf_transformation,[],[f8])).
% 7.64/1.48  
% 7.64/1.48  fof(f1,axiom,(
% 7.64/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f46,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f1])).
% 7.64/1.48  
% 7.64/1.48  fof(f88,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.64/1.48    inference(definition_unfolding,[],[f46,f55,f55])).
% 7.64/1.48  
% 7.64/1.48  fof(f2,axiom,(
% 7.64/1.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f24,plain,(
% 7.64/1.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 7.64/1.48    inference(rectify,[],[f2])).
% 7.64/1.48  
% 7.64/1.48  fof(f47,plain,(
% 7.64/1.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 7.64/1.48    inference(cnf_transformation,[],[f24])).
% 7.64/1.48  
% 7.64/1.48  fof(f89,plain,(
% 7.64/1.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 7.64/1.48    inference(definition_unfolding,[],[f47,f55])).
% 7.64/1.48  
% 7.64/1.48  fof(f3,axiom,(
% 7.64/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f25,plain,(
% 7.64/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.64/1.48    inference(rectify,[],[f3])).
% 7.64/1.48  
% 7.64/1.48  fof(f26,plain,(
% 7.64/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.64/1.48    inference(ennf_transformation,[],[f25])).
% 7.64/1.48  
% 7.64/1.48  fof(f33,plain,(
% 7.64/1.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.64/1.48    introduced(choice_axiom,[])).
% 7.64/1.48  
% 7.64/1.48  fof(f34,plain,(
% 7.64/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.64/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f33])).
% 7.64/1.48  
% 7.64/1.48  fof(f49,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.64/1.48    inference(cnf_transformation,[],[f34])).
% 7.64/1.48  
% 7.64/1.48  fof(f90,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.64/1.48    inference(definition_unfolding,[],[f49,f55])).
% 7.64/1.48  
% 7.64/1.48  fof(f10,axiom,(
% 7.64/1.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.64/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f56,plain,(
% 7.64/1.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f10])).
% 7.64/1.48  
% 7.64/1.48  cnf(c_27,negated_conjecture,
% 7.64/1.48      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) ),
% 7.64/1.48      inference(cnf_transformation,[],[f108]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1028,plain,
% 7.64/1.48      ( r1_tarski(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6)) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_24,plain,
% 7.64/1.48      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 7.64/1.48      | k2_enumset1(X1,X1,X1,X2) = X0
% 7.64/1.48      | k2_enumset1(X2,X2,X2,X2) = X0
% 7.64/1.48      | k2_enumset1(X1,X1,X1,X1) = X0
% 7.64/1.48      | k1_xboole_0 = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f107]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1029,plain,
% 7.64/1.48      ( k2_enumset1(X0,X0,X0,X1) = X2
% 7.64/1.48      | k2_enumset1(X1,X1,X1,X1) = X2
% 7.64/1.48      | k2_enumset1(X0,X0,X0,X0) = X2
% 7.64/1.48      | k1_xboole_0 = X2
% 7.64/1.48      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1450,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1028,c_1029]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1,plain,
% 7.64/1.48      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
% 7.64/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1623,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,sK5) ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1450,c_1]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1620,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | k5_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK3,sK3,sK3,sK4))) = k2_enumset1(sK5,sK5,sK5,X0) ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1450,c_1]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1626,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK4,X0) = k2_enumset1(sK5,sK5,sK5,X0)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.64/1.48      inference(demodulation,[status(thm)],[c_1620,c_1]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1885,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | k5_xboole_0(k2_enumset1(sK3,sK3,sK4,X0),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK4,X0))) = k2_enumset1(sK5,sK5,X0,sK5) ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1626,c_1623]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_7804,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK4,X0,sK5) = k2_enumset1(sK5,sK5,X0,sK5)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1623,c_1885]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_7831,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK4,sK5,sK5) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_7804,c_1450]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_15,plain,
% 7.64/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 7.64/1.48      inference(cnf_transformation,[],[f110]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1037,plain,
% 7.64/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_8102,plain,
% 7.64/1.48      ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK4,sK5,sK5) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | r2_hidden(sK6,k2_enumset1(sK3,sK3,sK3,sK4)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_7831,c_1037]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_26,negated_conjecture,
% 7.64/1.48      ( sK3 != sK5 ),
% 7.64/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_25,negated_conjecture,
% 7.64/1.48      ( sK3 != sK6 ),
% 7.64/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_18,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 7.64/1.48      | X0 = X1
% 7.64/1.48      | X0 = X2
% 7.64/1.48      | X0 = X3 ),
% 7.64/1.48      inference(cnf_transformation,[],[f115]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1069,plain,
% 7.64/1.48      ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,X0,X1))
% 7.64/1.48      | sK3 = X0
% 7.64/1.48      | sK3 = X1
% 7.64/1.48      | sK3 = sK6 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_18]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1098,plain,
% 7.64/1.48      ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,X0,sK3))
% 7.64/1.48      | sK3 = X0
% 7.64/1.48      | sK3 = sK6
% 7.64/1.48      | sK3 = sK3 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1069]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1168,plain,
% 7.64/1.48      ( ~ r2_hidden(sK3,k2_enumset1(sK6,sK6,sK3,sK3)) | sK3 = sK6 | sK3 = sK3 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1098]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1163,plain,
% 7.64/1.48      ( r2_hidden(sK3,k2_enumset1(sK6,sK6,X0,sK3)) ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_15]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1279,plain,
% 7.64/1.48      ( r2_hidden(sK3,k2_enumset1(sK6,sK6,sK3,sK3)) ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1163]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_706,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1229,plain,
% 7.64/1.48      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_706]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1579,plain,
% 7.64/1.48      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1229]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2322,plain,
% 7.64/1.48      ( sK6 != sK3 | sK3 = sK6 | sK3 != sK3 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1579]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2323,plain,
% 7.64/1.48      ( sK5 != sK3 | sK3 = sK5 | sK3 != sK3 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1579]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_16,plain,
% 7.64/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 7.64/1.48      inference(cnf_transformation,[],[f112]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1036,plain,
% 7.64/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_8,plain,
% 7.64/1.48      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1043,plain,
% 7.64/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 7.64/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_8540,plain,
% 7.64/1.48      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK5,sK5,sK5,sK6))) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1028,c_1043]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_9057,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK4,sK6))) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1626,c_8540]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1034,plain,
% 7.64/1.48      ( X0 = X1
% 7.64/1.48      | X0 = X2
% 7.64/1.48      | X0 = X3
% 7.64/1.48      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_8136,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | sK5 = X0
% 7.64/1.48      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1450,c_1034]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_9073,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | sK5 = sK3 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1036,c_8136]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_9690,plain,
% 7.64/1.48      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 7.64/1.48      inference(global_propositional_subsumption,
% 7.64/1.48                [status(thm)],
% 7.64/1.48                [c_9057,c_26,c_25,c_1168,c_1279,c_2323,c_9073]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_9691,plain,
% 7.64/1.48      ( k2_enumset1(sK5,sK5,sK5,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.64/1.48      inference(renaming,[status(thm)],[c_9690]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_9697,plain,
% 7.64/1.48      ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | sK5 = X0
% 7.64/1.48      | sK6 = X0
% 7.64/1.48      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_9691,c_1034]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_11632,plain,
% 7.64/1.48      ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | sK5 = sK3
% 7.64/1.48      | sK6 = sK3 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1036,c_9697]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_12378,plain,
% 7.64/1.48      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 7.64/1.48      inference(global_propositional_subsumption,
% 7.64/1.48                [status(thm)],
% 7.64/1.48                [c_8102,c_26,c_25,c_1168,c_1279,c_2322,c_2323,c_11632]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_12379,plain,
% 7.64/1.48      ( k2_enumset1(sK6,sK6,sK6,sK6) = k2_enumset1(sK3,sK3,sK3,sK4)
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.64/1.48      inference(renaming,[status(thm)],[c_12378]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_12390,plain,
% 7.64/1.48      ( k2_enumset1(sK6,sK6,sK6,sK6) = X0
% 7.64/1.48      | k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | k1_xboole_0 = X0
% 7.64/1.48      | r1_tarski(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_12379,c_1029]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_12386,plain,
% 7.64/1.48      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0
% 7.64/1.48      | sK6 = X0
% 7.64/1.48      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_12379,c_1034]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_17341,plain,
% 7.64/1.48      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 | sK6 = sK3 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1036,c_12386]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_17679,plain,
% 7.64/1.48      ( k2_enumset1(sK3,sK3,sK3,sK4) = k1_xboole_0 ),
% 7.64/1.48      inference(global_propositional_subsumption,
% 7.64/1.48                [status(thm)],
% 7.64/1.48                [c_12390,c_25,c_1168,c_1279,c_2322,c_17341]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_17699,plain,
% 7.64/1.48      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_17679,c_1037]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_9,plain,
% 7.64/1.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2,plain,
% 7.64/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.64/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1522,plain,
% 7.64/1.48      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_9,c_2]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_3,plain,
% 7.64/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4145,plain,
% 7.64/1.48      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_1522,c_3]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.64/1.48      | ~ r1_xboole_0(X1,X2) ),
% 7.64/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1047,plain,
% 7.64/1.48      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 7.64/1.48      | r1_xboole_0(X1,X2) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_10799,plain,
% 7.64/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.64/1.48      | r1_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4145,c_1047]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_10810,plain,
% 7.64/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.64/1.48      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.64/1.48      inference(demodulation,[status(thm)],[c_10799,c_9]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_10,plain,
% 7.64/1.48      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.64/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_57,plain,
% 7.64/1.48      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_59,plain,
% 7.64/1.48      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_57]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_10994,plain,
% 7.64/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.64/1.48      inference(global_propositional_subsumption,[status(thm)],[c_10810,c_59]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_22006,plain,
% 7.64/1.48      ( $false ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_17699,c_10994]) ).
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.48  
% 7.64/1.48  ------                               Statistics
% 7.64/1.48  
% 7.64/1.48  ------ General
% 7.64/1.48  
% 7.64/1.48  abstr_ref_over_cycles:                  0
% 7.64/1.48  abstr_ref_under_cycles:                 0
% 7.64/1.48  gc_basic_clause_elim:                   0
% 7.64/1.48  forced_gc_time:                         0
% 7.64/1.48  parsing_time:                           0.01
% 7.64/1.48  unif_index_cands_time:                  0.
% 7.64/1.48  unif_index_add_time:                    0.
% 7.64/1.48  orderings_time:                         0.
% 7.64/1.48  out_proof_time:                         0.01
% 7.64/1.48  total_time:                             0.575
% 7.64/1.48  num_of_symbols:                         46
% 7.64/1.48  num_of_terms:                           26233
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing
% 7.64/1.48  
% 7.64/1.48  num_of_splits:                          0
% 7.64/1.48  num_of_split_atoms:                     0
% 7.64/1.48  num_of_reused_defs:                     0
% 7.64/1.48  num_eq_ax_congr_red:                    32
% 7.64/1.48  num_of_sem_filtered_clauses:            1
% 7.64/1.48  num_of_subtypes:                        0
% 7.64/1.48  monotx_restored_types:                  0
% 7.64/1.48  sat_num_of_epr_types:                   0
% 7.64/1.48  sat_num_of_non_cyclic_types:            0
% 7.64/1.48  sat_guarded_non_collapsed_types:        0
% 7.64/1.48  num_pure_diseq_elim:                    0
% 7.64/1.48  simp_replaced_by:                       0
% 7.64/1.48  res_preprocessed:                       101
% 7.64/1.48  prep_upred:                             0
% 7.64/1.48  prep_unflattend:                        35
% 7.64/1.48  smt_new_axioms:                         0
% 7.64/1.48  pred_elim_cands:                        3
% 7.64/1.48  pred_elim:                              0
% 7.64/1.48  pred_elim_cl:                           0
% 7.64/1.48  pred_elim_cycles:                       2
% 7.64/1.48  merged_defs:                            0
% 7.64/1.48  merged_defs_ncl:                        0
% 7.64/1.48  bin_hyper_res:                          0
% 7.64/1.48  prep_cycles:                            3
% 7.64/1.48  pred_elim_time:                         0.007
% 7.64/1.48  splitting_time:                         0.
% 7.64/1.48  sem_filter_time:                        0.
% 7.64/1.48  monotx_time:                            0.
% 7.64/1.48  subtype_inf_time:                       0.
% 7.64/1.48  
% 7.64/1.48  ------ Problem properties
% 7.64/1.48  
% 7.64/1.48  clauses:                                28
% 7.64/1.48  conjectures:                            3
% 7.64/1.48  epr:                                    3
% 7.64/1.48  horn:                                   23
% 7.64/1.48  ground:                                 3
% 7.64/1.48  unary:                                  17
% 7.64/1.48  binary:                                 5
% 7.64/1.48  lits:                                   50
% 7.64/1.48  lits_eq:                                27
% 7.64/1.48  fd_pure:                                0
% 7.64/1.48  fd_pseudo:                              0
% 7.64/1.48  fd_cond:                                1
% 7.64/1.48  fd_pseudo_cond:                         5
% 7.64/1.48  ac_symbols:                             0
% 7.64/1.48  
% 7.64/1.48  ------ Propositional Solver
% 7.64/1.48  
% 7.64/1.48  prop_solver_calls:                      29
% 7.64/1.48  prop_fast_solver_calls:                 1250
% 7.64/1.48  smt_solver_calls:                       0
% 7.64/1.48  smt_fast_solver_calls:                  0
% 7.64/1.48  prop_num_of_clauses:                    6849
% 7.64/1.48  prop_preprocess_simplified:             14702
% 7.64/1.48  prop_fo_subsumed:                       251
% 7.64/1.48  prop_solver_time:                       0.
% 7.64/1.48  smt_solver_time:                        0.
% 7.64/1.48  smt_fast_solver_time:                   0.
% 7.64/1.48  prop_fast_solver_time:                  0.
% 7.64/1.48  prop_unsat_core_time:                   0.
% 7.64/1.48  
% 7.64/1.48  ------ QBF
% 7.64/1.48  
% 7.64/1.48  qbf_q_res:                              0
% 7.64/1.48  qbf_num_tautologies:                    0
% 7.64/1.48  qbf_prep_cycles:                        0
% 7.64/1.48  
% 7.64/1.48  ------ BMC1
% 7.64/1.48  
% 7.64/1.48  bmc1_current_bound:                     -1
% 7.64/1.48  bmc1_last_solved_bound:                 -1
% 7.64/1.48  bmc1_unsat_core_size:                   -1
% 7.64/1.48  bmc1_unsat_core_parents_size:           -1
% 7.64/1.48  bmc1_merge_next_fun:                    0
% 7.64/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.64/1.48  
% 7.64/1.48  ------ Instantiation
% 7.64/1.48  
% 7.64/1.48  inst_num_of_clauses:                    1668
% 7.64/1.48  inst_num_in_passive:                    1027
% 7.64/1.48  inst_num_in_active:                     561
% 7.64/1.48  inst_num_in_unprocessed:                80
% 7.64/1.48  inst_num_of_loops:                      750
% 7.64/1.48  inst_num_of_learning_restarts:          0
% 7.64/1.48  inst_num_moves_active_passive:          186
% 7.64/1.48  inst_lit_activity:                      0
% 7.64/1.48  inst_lit_activity_moves:                0
% 7.64/1.48  inst_num_tautologies:                   0
% 7.64/1.48  inst_num_prop_implied:                  0
% 7.64/1.48  inst_num_existing_simplified:           0
% 7.64/1.48  inst_num_eq_res_simplified:             0
% 7.64/1.48  inst_num_child_elim:                    0
% 7.64/1.48  inst_num_of_dismatching_blockings:      4427
% 7.64/1.48  inst_num_of_non_proper_insts:           2305
% 7.64/1.48  inst_num_of_duplicates:                 0
% 7.64/1.48  inst_inst_num_from_inst_to_res:         0
% 7.64/1.48  inst_dismatching_checking_time:         0.
% 7.64/1.48  
% 7.64/1.48  ------ Resolution
% 7.64/1.48  
% 7.64/1.48  res_num_of_clauses:                     0
% 7.64/1.48  res_num_in_passive:                     0
% 7.64/1.48  res_num_in_active:                      0
% 7.64/1.48  res_num_of_loops:                       104
% 7.64/1.48  res_forward_subset_subsumed:            865
% 7.64/1.48  res_backward_subset_subsumed:           0
% 7.64/1.48  res_forward_subsumed:                   0
% 7.64/1.48  res_backward_subsumed:                  0
% 7.64/1.48  res_forward_subsumption_resolution:     1
% 7.64/1.48  res_backward_subsumption_resolution:    0
% 7.64/1.48  res_clause_to_clause_subsumption:       5084
% 7.64/1.48  res_orphan_elimination:                 0
% 7.64/1.48  res_tautology_del:                      57
% 7.64/1.48  res_num_eq_res_simplified:              0
% 7.64/1.48  res_num_sel_changes:                    0
% 7.64/1.48  res_moves_from_active_to_pass:          0
% 7.64/1.48  
% 7.64/1.48  ------ Superposition
% 7.64/1.48  
% 7.64/1.48  sup_time_total:                         0.
% 7.64/1.48  sup_time_generating:                    0.
% 7.64/1.48  sup_time_sim_full:                      0.
% 7.64/1.48  sup_time_sim_immed:                     0.
% 7.64/1.48  
% 7.64/1.48  sup_num_of_clauses:                     359
% 7.64/1.48  sup_num_in_active:                      87
% 7.64/1.48  sup_num_in_passive:                     272
% 7.64/1.48  sup_num_of_loops:                       149
% 7.64/1.48  sup_fw_superposition:                   1093
% 7.64/1.48  sup_bw_superposition:                   780
% 7.64/1.48  sup_immediate_simplified:               936
% 7.64/1.48  sup_given_eliminated:                   3
% 7.64/1.48  comparisons_done:                       0
% 7.64/1.48  comparisons_avoided:                    87
% 7.64/1.48  
% 7.64/1.48  ------ Simplifications
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  sim_fw_subset_subsumed:                 30
% 7.64/1.48  sim_bw_subset_subsumed:                 116
% 7.64/1.48  sim_fw_subsumed:                        152
% 7.64/1.48  sim_bw_subsumed:                        24
% 7.64/1.48  sim_fw_subsumption_res:                 0
% 7.64/1.48  sim_bw_subsumption_res:                 0
% 7.64/1.48  sim_tautology_del:                      102
% 7.64/1.48  sim_eq_tautology_del:                   245
% 7.64/1.48  sim_eq_res_simp:                        0
% 7.64/1.48  sim_fw_demodulated:                     646
% 7.64/1.48  sim_bw_demodulated:                     88
% 7.64/1.48  sim_light_normalised:                   342
% 7.64/1.48  sim_joinable_taut:                      0
% 7.64/1.48  sim_joinable_simp:                      0
% 7.64/1.48  sim_ac_normalised:                      0
% 7.64/1.48  sim_smt_subsumption:                    0
% 7.64/1.48  
%------------------------------------------------------------------------------
