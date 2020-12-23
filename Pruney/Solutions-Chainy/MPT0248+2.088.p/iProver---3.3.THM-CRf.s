%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:21 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.81s
% Verified   : 
% Statistics : Number of formulae       :  172 (2002 expanded)
%              Number of clauses        :   70 ( 178 expanded)
%              Number of leaves         :   27 ( 619 expanded)
%              Depth                    :   18
%              Number of atoms          :  490 (3989 expanded)
%              Number of equality atoms :  286 (2928 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f43])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK6
        | k1_tarski(sK4) != sK5 )
      & ( k1_tarski(sK4) != sK6
        | k1_xboole_0 != sK5 )
      & ( k1_tarski(sK4) != sK6
        | k1_tarski(sK4) != sK5 )
      & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( k1_xboole_0 != sK6
      | k1_tarski(sK4) != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_xboole_0 != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_tarski(sK4) != sK5 )
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f33,f53])).

fof(f94,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f24,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f103,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f91,f102])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f87,f88])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f86,f98])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f85,f99])).

fof(f101,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f84,f100])).

fof(f102,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f83,f101])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f82,f102])).

fof(f129,plain,(
    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f94,f103,f106])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f103])).

fof(f130,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f111])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f77,f106])).

fof(f137,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f121])).

fof(f97,plain,
    ( k1_xboole_0 != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f126,plain,
    ( k1_xboole_0 != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f97,f106])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f92,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f76,f103])).

fof(f105,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f69,f104])).

fof(f125,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f92,f105,f106,f106,f106])).

fof(f138,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f125])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f93,f105,f106,f106,f106])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f90,f106])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f117,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f73,f103])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f78,f106])).

fof(f135,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f120])).

fof(f136,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f135])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f103])).

fof(f132,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f113])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f79,f106])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f103])).

fof(f131,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f95,plain,
    ( k1_tarski(sK4) != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f128,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f95,f106,f106])).

fof(f96,plain,
    ( k1_tarski(sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f54])).

fof(f127,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(definition_unfolding,[],[f96,f106])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_987,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_32,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_990,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_45304,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_990])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_979,plain,
    ( X0 = X1
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_51711,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_45304,c_979])).

cnf(c_51835,plain,
    ( sK2(sK6) = sK4
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_987,c_51711])).

cnf(c_29,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_28,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_33,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_27,plain,
    ( X0 = X1
    | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_34,plain,
    ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_496,plain,
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

cnf(c_501,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1177,plain,
    ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
    | ~ r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1178,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
    | r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1177])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1474,plain,
    ( ~ r2_hidden(sK4,sK5)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1475,plain,
    ( r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_494,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1899,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_494])).

cnf(c_5386,plain,
    ( ~ r2_hidden(sK4,sK6)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_5387,plain,
    ( r2_hidden(sK4,sK6) != iProver_top
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5386])).

cnf(c_495,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1382,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_19824,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_19826,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_19824])).

cnf(c_18,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_983,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20164,plain,
    ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_983])).

cnf(c_1187,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_22450,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1187])).

cnf(c_23,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_980,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_988,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_34319,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_988])).

cnf(c_39248,plain,
    ( r2_hidden(sK4,sK5) = iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_34319])).

cnf(c_2086,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_44283,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6)
    | ~ r1_tarski(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | sK6 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_44284,plain,
    ( sK6 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6) != iProver_top
    | r1_tarski(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44283])).

cnf(c_44286,plain,
    ( sK6 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top
    | r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44284])).

cnf(c_22,plain,
    ( r2_hidden(sK3(X0,X1),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_981,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | sK3(X0,X1) = X0
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_989,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_41215,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_32,c_989])).

cnf(c_44394,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_41215,c_979])).

cnf(c_44413,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK5
    | sK3(X0,sK5) = X0
    | sK3(X0,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_981,c_44394])).

cnf(c_31,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_44858,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | sK3(sK4,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_44413,c_31])).

cnf(c_30,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1191,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_1898,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1191])).

cnf(c_44412,plain,
    ( sK2(sK5) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_987,c_44394])).

cnf(c_44605,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_44412,c_987])).

cnf(c_51400,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_44858,c_31,c_30,c_1178,c_1475,c_1898,c_1899,c_20164,c_44605])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_995,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_996,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_51710,plain,
    ( r2_hidden(sK0(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
    | r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_45304,c_996])).

cnf(c_51864,plain,
    ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_51710])).

cnf(c_52207,plain,
    ( sK2(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_51835,c_31,c_30,c_29,c_33,c_34,c_501,c_1178,c_1475,c_1898,c_1899,c_5387,c_19826,c_20164,c_22450,c_39248,c_44286,c_44605,c_51864])).

cnf(c_52210,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_52207,c_987])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52210,c_51864,c_51400,c_44286,c_39248,c_22450,c_20164,c_19826,c_5387,c_1899,c_1475,c_1178,c_501,c_34,c_33,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:41:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.81/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.81/1.99  
% 11.81/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.81/1.99  
% 11.81/1.99  ------  iProver source info
% 11.81/1.99  
% 11.81/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.81/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.81/1.99  git: non_committed_changes: false
% 11.81/1.99  git: last_make_outside_of_git: false
% 11.81/1.99  
% 11.81/1.99  ------ 
% 11.81/1.99  
% 11.81/1.99  ------ Input Options
% 11.81/1.99  
% 11.81/1.99  --out_options                           all
% 11.81/1.99  --tptp_safe_out                         true
% 11.81/1.99  --problem_path                          ""
% 11.81/1.99  --include_path                          ""
% 11.81/1.99  --clausifier                            res/vclausify_rel
% 11.81/1.99  --clausifier_options                    --mode clausify
% 11.81/1.99  --stdin                                 false
% 11.81/1.99  --stats_out                             all
% 11.81/1.99  
% 11.81/1.99  ------ General Options
% 11.81/1.99  
% 11.81/1.99  --fof                                   false
% 11.81/1.99  --time_out_real                         305.
% 11.81/1.99  --time_out_virtual                      -1.
% 11.81/1.99  --symbol_type_check                     false
% 11.81/1.99  --clausify_out                          false
% 11.81/1.99  --sig_cnt_out                           false
% 11.81/1.99  --trig_cnt_out                          false
% 11.81/1.99  --trig_cnt_out_tolerance                1.
% 11.81/1.99  --trig_cnt_out_sk_spl                   false
% 11.81/1.99  --abstr_cl_out                          false
% 11.81/1.99  
% 11.81/1.99  ------ Global Options
% 11.81/1.99  
% 11.81/1.99  --schedule                              default
% 11.81/1.99  --add_important_lit                     false
% 11.81/1.99  --prop_solver_per_cl                    1000
% 11.81/1.99  --min_unsat_core                        false
% 11.81/1.99  --soft_assumptions                      false
% 11.81/1.99  --soft_lemma_size                       3
% 11.81/1.99  --prop_impl_unit_size                   0
% 11.81/1.99  --prop_impl_unit                        []
% 11.81/1.99  --share_sel_clauses                     true
% 11.81/1.99  --reset_solvers                         false
% 11.81/1.99  --bc_imp_inh                            [conj_cone]
% 11.81/1.99  --conj_cone_tolerance                   3.
% 11.81/1.99  --extra_neg_conj                        none
% 11.81/1.99  --large_theory_mode                     true
% 11.81/1.99  --prolific_symb_bound                   200
% 11.81/1.99  --lt_threshold                          2000
% 11.81/1.99  --clause_weak_htbl                      true
% 11.81/1.99  --gc_record_bc_elim                     false
% 11.81/1.99  
% 11.81/1.99  ------ Preprocessing Options
% 11.81/1.99  
% 11.81/1.99  --preprocessing_flag                    true
% 11.81/1.99  --time_out_prep_mult                    0.1
% 11.81/1.99  --splitting_mode                        input
% 11.81/1.99  --splitting_grd                         true
% 11.81/1.99  --splitting_cvd                         false
% 11.81/1.99  --splitting_cvd_svl                     false
% 11.81/1.99  --splitting_nvd                         32
% 11.81/1.99  --sub_typing                            true
% 11.81/1.99  --prep_gs_sim                           true
% 11.81/1.99  --prep_unflatten                        true
% 11.81/1.99  --prep_res_sim                          true
% 11.81/1.99  --prep_upred                            true
% 11.81/1.99  --prep_sem_filter                       exhaustive
% 11.81/1.99  --prep_sem_filter_out                   false
% 11.81/1.99  --pred_elim                             true
% 11.81/1.99  --res_sim_input                         true
% 11.81/1.99  --eq_ax_congr_red                       true
% 11.81/1.99  --pure_diseq_elim                       true
% 11.81/1.99  --brand_transform                       false
% 11.81/1.99  --non_eq_to_eq                          false
% 11.81/1.99  --prep_def_merge                        true
% 11.81/1.99  --prep_def_merge_prop_impl              false
% 11.81/1.99  --prep_def_merge_mbd                    true
% 11.81/1.99  --prep_def_merge_tr_red                 false
% 11.81/1.99  --prep_def_merge_tr_cl                  false
% 11.81/1.99  --smt_preprocessing                     true
% 11.81/1.99  --smt_ac_axioms                         fast
% 11.81/1.99  --preprocessed_out                      false
% 11.81/1.99  --preprocessed_stats                    false
% 11.81/1.99  
% 11.81/1.99  ------ Abstraction refinement Options
% 11.81/1.99  
% 11.81/1.99  --abstr_ref                             []
% 11.81/1.99  --abstr_ref_prep                        false
% 11.81/1.99  --abstr_ref_until_sat                   false
% 11.81/1.99  --abstr_ref_sig_restrict                funpre
% 11.81/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/1.99  --abstr_ref_under                       []
% 11.81/1.99  
% 11.81/1.99  ------ SAT Options
% 11.81/1.99  
% 11.81/1.99  --sat_mode                              false
% 11.81/1.99  --sat_fm_restart_options                ""
% 11.81/1.99  --sat_gr_def                            false
% 11.81/1.99  --sat_epr_types                         true
% 11.81/1.99  --sat_non_cyclic_types                  false
% 11.81/1.99  --sat_finite_models                     false
% 11.81/1.99  --sat_fm_lemmas                         false
% 11.81/1.99  --sat_fm_prep                           false
% 11.81/1.99  --sat_fm_uc_incr                        true
% 11.81/1.99  --sat_out_model                         small
% 11.81/1.99  --sat_out_clauses                       false
% 11.81/1.99  
% 11.81/1.99  ------ QBF Options
% 11.81/1.99  
% 11.81/1.99  --qbf_mode                              false
% 11.81/1.99  --qbf_elim_univ                         false
% 11.81/1.99  --qbf_dom_inst                          none
% 11.81/1.99  --qbf_dom_pre_inst                      false
% 11.81/1.99  --qbf_sk_in                             false
% 11.81/1.99  --qbf_pred_elim                         true
% 11.81/1.99  --qbf_split                             512
% 11.81/1.99  
% 11.81/1.99  ------ BMC1 Options
% 11.81/1.99  
% 11.81/1.99  --bmc1_incremental                      false
% 11.81/1.99  --bmc1_axioms                           reachable_all
% 11.81/1.99  --bmc1_min_bound                        0
% 11.81/1.99  --bmc1_max_bound                        -1
% 11.81/1.99  --bmc1_max_bound_default                -1
% 11.81/1.99  --bmc1_symbol_reachability              true
% 11.81/1.99  --bmc1_property_lemmas                  false
% 11.81/1.99  --bmc1_k_induction                      false
% 11.81/1.99  --bmc1_non_equiv_states                 false
% 11.81/1.99  --bmc1_deadlock                         false
% 11.81/1.99  --bmc1_ucm                              false
% 11.81/1.99  --bmc1_add_unsat_core                   none
% 11.81/1.99  --bmc1_unsat_core_children              false
% 11.81/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/1.99  --bmc1_out_stat                         full
% 11.81/1.99  --bmc1_ground_init                      false
% 11.81/1.99  --bmc1_pre_inst_next_state              false
% 11.81/1.99  --bmc1_pre_inst_state                   false
% 11.81/1.99  --bmc1_pre_inst_reach_state             false
% 11.81/1.99  --bmc1_out_unsat_core                   false
% 11.81/1.99  --bmc1_aig_witness_out                  false
% 11.81/1.99  --bmc1_verbose                          false
% 11.81/1.99  --bmc1_dump_clauses_tptp                false
% 11.81/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.81/1.99  --bmc1_dump_file                        -
% 11.81/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.81/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.81/1.99  --bmc1_ucm_extend_mode                  1
% 11.81/1.99  --bmc1_ucm_init_mode                    2
% 11.81/1.99  --bmc1_ucm_cone_mode                    none
% 11.81/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.81/1.99  --bmc1_ucm_relax_model                  4
% 11.81/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.81/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/1.99  --bmc1_ucm_layered_model                none
% 11.81/1.99  --bmc1_ucm_max_lemma_size               10
% 11.81/1.99  
% 11.81/1.99  ------ AIG Options
% 11.81/1.99  
% 11.81/1.99  --aig_mode                              false
% 11.81/1.99  
% 11.81/1.99  ------ Instantiation Options
% 11.81/1.99  
% 11.81/1.99  --instantiation_flag                    true
% 11.81/1.99  --inst_sos_flag                         false
% 11.81/1.99  --inst_sos_phase                        true
% 11.81/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/1.99  --inst_lit_sel_side                     num_symb
% 11.81/1.99  --inst_solver_per_active                1400
% 11.81/1.99  --inst_solver_calls_frac                1.
% 11.81/1.99  --inst_passive_queue_type               priority_queues
% 11.81/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/1.99  --inst_passive_queues_freq              [25;2]
% 11.81/1.99  --inst_dismatching                      true
% 11.81/1.99  --inst_eager_unprocessed_to_passive     true
% 11.81/1.99  --inst_prop_sim_given                   true
% 11.81/1.99  --inst_prop_sim_new                     false
% 11.81/1.99  --inst_subs_new                         false
% 11.81/1.99  --inst_eq_res_simp                      false
% 11.81/1.99  --inst_subs_given                       false
% 11.81/1.99  --inst_orphan_elimination               true
% 11.81/1.99  --inst_learning_loop_flag               true
% 11.81/1.99  --inst_learning_start                   3000
% 11.81/1.99  --inst_learning_factor                  2
% 11.81/1.99  --inst_start_prop_sim_after_learn       3
% 11.81/1.99  --inst_sel_renew                        solver
% 11.81/1.99  --inst_lit_activity_flag                true
% 11.81/1.99  --inst_restr_to_given                   false
% 11.81/1.99  --inst_activity_threshold               500
% 11.81/1.99  --inst_out_proof                        true
% 11.81/1.99  
% 11.81/1.99  ------ Resolution Options
% 11.81/1.99  
% 11.81/1.99  --resolution_flag                       true
% 11.81/1.99  --res_lit_sel                           adaptive
% 11.81/1.99  --res_lit_sel_side                      none
% 11.81/1.99  --res_ordering                          kbo
% 11.81/1.99  --res_to_prop_solver                    active
% 11.81/1.99  --res_prop_simpl_new                    false
% 11.81/1.99  --res_prop_simpl_given                  true
% 11.81/1.99  --res_passive_queue_type                priority_queues
% 11.81/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/1.99  --res_passive_queues_freq               [15;5]
% 11.81/1.99  --res_forward_subs                      full
% 11.81/1.99  --res_backward_subs                     full
% 11.81/1.99  --res_forward_subs_resolution           true
% 11.81/1.99  --res_backward_subs_resolution          true
% 11.81/1.99  --res_orphan_elimination                true
% 11.81/1.99  --res_time_limit                        2.
% 11.81/1.99  --res_out_proof                         true
% 11.81/1.99  
% 11.81/1.99  ------ Superposition Options
% 11.81/1.99  
% 11.81/1.99  --superposition_flag                    true
% 11.81/1.99  --sup_passive_queue_type                priority_queues
% 11.81/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.81/1.99  --demod_completeness_check              fast
% 11.81/1.99  --demod_use_ground                      true
% 11.81/1.99  --sup_to_prop_solver                    passive
% 11.81/1.99  --sup_prop_simpl_new                    true
% 11.81/1.99  --sup_prop_simpl_given                  true
% 11.81/1.99  --sup_fun_splitting                     false
% 11.81/1.99  --sup_smt_interval                      50000
% 11.81/1.99  
% 11.81/1.99  ------ Superposition Simplification Setup
% 11.81/1.99  
% 11.81/1.99  --sup_indices_passive                   []
% 11.81/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/1.99  --sup_full_bw                           [BwDemod]
% 11.81/1.99  --sup_immed_triv                        [TrivRules]
% 11.81/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/1.99  --sup_immed_bw_main                     []
% 11.81/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.81/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.81/1.99  
% 11.81/1.99  ------ Combination Options
% 11.81/1.99  
% 11.81/1.99  --comb_res_mult                         3
% 11.81/1.99  --comb_sup_mult                         2
% 11.81/1.99  --comb_inst_mult                        10
% 11.81/1.99  
% 11.81/1.99  ------ Debug Options
% 11.81/1.99  
% 11.81/1.99  --dbg_backtrace                         false
% 11.81/1.99  --dbg_dump_prop_clauses                 false
% 11.81/1.99  --dbg_dump_prop_clauses_file            -
% 11.81/1.99  --dbg_out_stat                          false
% 11.81/1.99  ------ Parsing...
% 11.81/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.81/1.99  
% 11.81/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.81/1.99  
% 11.81/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.81/1.99  
% 11.81/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.81/1.99  ------ Proving...
% 11.81/1.99  ------ Problem Properties 
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  clauses                                 32
% 11.81/1.99  conjectures                             4
% 11.81/1.99  EPR                                     3
% 11.81/1.99  Horn                                    26
% 11.81/1.99  unary                                   10
% 11.81/1.99  binary                                  14
% 11.81/1.99  lits                                    63
% 11.81/1.99  lits eq                                 28
% 11.81/1.99  fd_pure                                 0
% 11.81/1.99  fd_pseudo                               0
% 11.81/1.99  fd_cond                                 2
% 11.81/1.99  fd_pseudo_cond                          7
% 11.81/1.99  AC symbols                              0
% 11.81/1.99  
% 11.81/1.99  ------ Schedule dynamic 5 is on 
% 11.81/1.99  
% 11.81/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  ------ 
% 11.81/1.99  Current options:
% 11.81/1.99  ------ 
% 11.81/1.99  
% 11.81/1.99  ------ Input Options
% 11.81/1.99  
% 11.81/1.99  --out_options                           all
% 11.81/1.99  --tptp_safe_out                         true
% 11.81/1.99  --problem_path                          ""
% 11.81/1.99  --include_path                          ""
% 11.81/1.99  --clausifier                            res/vclausify_rel
% 11.81/1.99  --clausifier_options                    --mode clausify
% 11.81/1.99  --stdin                                 false
% 11.81/1.99  --stats_out                             all
% 11.81/1.99  
% 11.81/1.99  ------ General Options
% 11.81/1.99  
% 11.81/1.99  --fof                                   false
% 11.81/1.99  --time_out_real                         305.
% 11.81/1.99  --time_out_virtual                      -1.
% 11.81/1.99  --symbol_type_check                     false
% 11.81/1.99  --clausify_out                          false
% 11.81/1.99  --sig_cnt_out                           false
% 11.81/1.99  --trig_cnt_out                          false
% 11.81/1.99  --trig_cnt_out_tolerance                1.
% 11.81/1.99  --trig_cnt_out_sk_spl                   false
% 11.81/1.99  --abstr_cl_out                          false
% 11.81/1.99  
% 11.81/1.99  ------ Global Options
% 11.81/1.99  
% 11.81/1.99  --schedule                              default
% 11.81/1.99  --add_important_lit                     false
% 11.81/1.99  --prop_solver_per_cl                    1000
% 11.81/1.99  --min_unsat_core                        false
% 11.81/1.99  --soft_assumptions                      false
% 11.81/1.99  --soft_lemma_size                       3
% 11.81/1.99  --prop_impl_unit_size                   0
% 11.81/1.99  --prop_impl_unit                        []
% 11.81/1.99  --share_sel_clauses                     true
% 11.81/1.99  --reset_solvers                         false
% 11.81/1.99  --bc_imp_inh                            [conj_cone]
% 11.81/1.99  --conj_cone_tolerance                   3.
% 11.81/1.99  --extra_neg_conj                        none
% 11.81/1.99  --large_theory_mode                     true
% 11.81/1.99  --prolific_symb_bound                   200
% 11.81/1.99  --lt_threshold                          2000
% 11.81/1.99  --clause_weak_htbl                      true
% 11.81/1.99  --gc_record_bc_elim                     false
% 11.81/1.99  
% 11.81/1.99  ------ Preprocessing Options
% 11.81/1.99  
% 11.81/1.99  --preprocessing_flag                    true
% 11.81/1.99  --time_out_prep_mult                    0.1
% 11.81/1.99  --splitting_mode                        input
% 11.81/1.99  --splitting_grd                         true
% 11.81/1.99  --splitting_cvd                         false
% 11.81/1.99  --splitting_cvd_svl                     false
% 11.81/1.99  --splitting_nvd                         32
% 11.81/1.99  --sub_typing                            true
% 11.81/1.99  --prep_gs_sim                           true
% 11.81/1.99  --prep_unflatten                        true
% 11.81/1.99  --prep_res_sim                          true
% 11.81/1.99  --prep_upred                            true
% 11.81/1.99  --prep_sem_filter                       exhaustive
% 11.81/1.99  --prep_sem_filter_out                   false
% 11.81/1.99  --pred_elim                             true
% 11.81/1.99  --res_sim_input                         true
% 11.81/1.99  --eq_ax_congr_red                       true
% 11.81/1.99  --pure_diseq_elim                       true
% 11.81/1.99  --brand_transform                       false
% 11.81/1.99  --non_eq_to_eq                          false
% 11.81/1.99  --prep_def_merge                        true
% 11.81/1.99  --prep_def_merge_prop_impl              false
% 11.81/1.99  --prep_def_merge_mbd                    true
% 11.81/1.99  --prep_def_merge_tr_red                 false
% 11.81/1.99  --prep_def_merge_tr_cl                  false
% 11.81/1.99  --smt_preprocessing                     true
% 11.81/1.99  --smt_ac_axioms                         fast
% 11.81/1.99  --preprocessed_out                      false
% 11.81/1.99  --preprocessed_stats                    false
% 11.81/1.99  
% 11.81/1.99  ------ Abstraction refinement Options
% 11.81/1.99  
% 11.81/1.99  --abstr_ref                             []
% 11.81/1.99  --abstr_ref_prep                        false
% 11.81/1.99  --abstr_ref_until_sat                   false
% 11.81/1.99  --abstr_ref_sig_restrict                funpre
% 11.81/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/1.99  --abstr_ref_under                       []
% 11.81/1.99  
% 11.81/1.99  ------ SAT Options
% 11.81/1.99  
% 11.81/1.99  --sat_mode                              false
% 11.81/1.99  --sat_fm_restart_options                ""
% 11.81/1.99  --sat_gr_def                            false
% 11.81/1.99  --sat_epr_types                         true
% 11.81/1.99  --sat_non_cyclic_types                  false
% 11.81/1.99  --sat_finite_models                     false
% 11.81/1.99  --sat_fm_lemmas                         false
% 11.81/1.99  --sat_fm_prep                           false
% 11.81/1.99  --sat_fm_uc_incr                        true
% 11.81/1.99  --sat_out_model                         small
% 11.81/1.99  --sat_out_clauses                       false
% 11.81/1.99  
% 11.81/1.99  ------ QBF Options
% 11.81/1.99  
% 11.81/1.99  --qbf_mode                              false
% 11.81/1.99  --qbf_elim_univ                         false
% 11.81/1.99  --qbf_dom_inst                          none
% 11.81/1.99  --qbf_dom_pre_inst                      false
% 11.81/1.99  --qbf_sk_in                             false
% 11.81/1.99  --qbf_pred_elim                         true
% 11.81/1.99  --qbf_split                             512
% 11.81/1.99  
% 11.81/1.99  ------ BMC1 Options
% 11.81/1.99  
% 11.81/1.99  --bmc1_incremental                      false
% 11.81/1.99  --bmc1_axioms                           reachable_all
% 11.81/1.99  --bmc1_min_bound                        0
% 11.81/1.99  --bmc1_max_bound                        -1
% 11.81/1.99  --bmc1_max_bound_default                -1
% 11.81/1.99  --bmc1_symbol_reachability              true
% 11.81/1.99  --bmc1_property_lemmas                  false
% 11.81/1.99  --bmc1_k_induction                      false
% 11.81/1.99  --bmc1_non_equiv_states                 false
% 11.81/1.99  --bmc1_deadlock                         false
% 11.81/1.99  --bmc1_ucm                              false
% 11.81/1.99  --bmc1_add_unsat_core                   none
% 11.81/1.99  --bmc1_unsat_core_children              false
% 11.81/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/1.99  --bmc1_out_stat                         full
% 11.81/1.99  --bmc1_ground_init                      false
% 11.81/1.99  --bmc1_pre_inst_next_state              false
% 11.81/1.99  --bmc1_pre_inst_state                   false
% 11.81/1.99  --bmc1_pre_inst_reach_state             false
% 11.81/1.99  --bmc1_out_unsat_core                   false
% 11.81/1.99  --bmc1_aig_witness_out                  false
% 11.81/1.99  --bmc1_verbose                          false
% 11.81/1.99  --bmc1_dump_clauses_tptp                false
% 11.81/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.81/1.99  --bmc1_dump_file                        -
% 11.81/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.81/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.81/1.99  --bmc1_ucm_extend_mode                  1
% 11.81/1.99  --bmc1_ucm_init_mode                    2
% 11.81/1.99  --bmc1_ucm_cone_mode                    none
% 11.81/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.81/1.99  --bmc1_ucm_relax_model                  4
% 11.81/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.81/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/1.99  --bmc1_ucm_layered_model                none
% 11.81/1.99  --bmc1_ucm_max_lemma_size               10
% 11.81/1.99  
% 11.81/1.99  ------ AIG Options
% 11.81/1.99  
% 11.81/1.99  --aig_mode                              false
% 11.81/1.99  
% 11.81/1.99  ------ Instantiation Options
% 11.81/1.99  
% 11.81/1.99  --instantiation_flag                    true
% 11.81/1.99  --inst_sos_flag                         false
% 11.81/1.99  --inst_sos_phase                        true
% 11.81/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/1.99  --inst_lit_sel_side                     none
% 11.81/1.99  --inst_solver_per_active                1400
% 11.81/1.99  --inst_solver_calls_frac                1.
% 11.81/1.99  --inst_passive_queue_type               priority_queues
% 11.81/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/1.99  --inst_passive_queues_freq              [25;2]
% 11.81/1.99  --inst_dismatching                      true
% 11.81/1.99  --inst_eager_unprocessed_to_passive     true
% 11.81/1.99  --inst_prop_sim_given                   true
% 11.81/1.99  --inst_prop_sim_new                     false
% 11.81/1.99  --inst_subs_new                         false
% 11.81/1.99  --inst_eq_res_simp                      false
% 11.81/1.99  --inst_subs_given                       false
% 11.81/1.99  --inst_orphan_elimination               true
% 11.81/1.99  --inst_learning_loop_flag               true
% 11.81/1.99  --inst_learning_start                   3000
% 11.81/1.99  --inst_learning_factor                  2
% 11.81/1.99  --inst_start_prop_sim_after_learn       3
% 11.81/1.99  --inst_sel_renew                        solver
% 11.81/1.99  --inst_lit_activity_flag                true
% 11.81/1.99  --inst_restr_to_given                   false
% 11.81/1.99  --inst_activity_threshold               500
% 11.81/1.99  --inst_out_proof                        true
% 11.81/1.99  
% 11.81/1.99  ------ Resolution Options
% 11.81/1.99  
% 11.81/1.99  --resolution_flag                       false
% 11.81/1.99  --res_lit_sel                           adaptive
% 11.81/1.99  --res_lit_sel_side                      none
% 11.81/1.99  --res_ordering                          kbo
% 11.81/1.99  --res_to_prop_solver                    active
% 11.81/1.99  --res_prop_simpl_new                    false
% 11.81/1.99  --res_prop_simpl_given                  true
% 11.81/1.99  --res_passive_queue_type                priority_queues
% 11.81/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/1.99  --res_passive_queues_freq               [15;5]
% 11.81/1.99  --res_forward_subs                      full
% 11.81/1.99  --res_backward_subs                     full
% 11.81/1.99  --res_forward_subs_resolution           true
% 11.81/1.99  --res_backward_subs_resolution          true
% 11.81/1.99  --res_orphan_elimination                true
% 11.81/1.99  --res_time_limit                        2.
% 11.81/1.99  --res_out_proof                         true
% 11.81/1.99  
% 11.81/1.99  ------ Superposition Options
% 11.81/1.99  
% 11.81/1.99  --superposition_flag                    true
% 11.81/1.99  --sup_passive_queue_type                priority_queues
% 11.81/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.81/1.99  --demod_completeness_check              fast
% 11.81/1.99  --demod_use_ground                      true
% 11.81/1.99  --sup_to_prop_solver                    passive
% 11.81/1.99  --sup_prop_simpl_new                    true
% 11.81/1.99  --sup_prop_simpl_given                  true
% 11.81/1.99  --sup_fun_splitting                     false
% 11.81/1.99  --sup_smt_interval                      50000
% 11.81/1.99  
% 11.81/1.99  ------ Superposition Simplification Setup
% 11.81/1.99  
% 11.81/1.99  --sup_indices_passive                   []
% 11.81/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.81/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/1.99  --sup_full_bw                           [BwDemod]
% 11.81/1.99  --sup_immed_triv                        [TrivRules]
% 11.81/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/1.99  --sup_immed_bw_main                     []
% 11.81/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.81/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.81/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.81/1.99  
% 11.81/1.99  ------ Combination Options
% 11.81/1.99  
% 11.81/1.99  --comb_res_mult                         3
% 11.81/1.99  --comb_sup_mult                         2
% 11.81/1.99  --comb_inst_mult                        10
% 11.81/1.99  
% 11.81/1.99  ------ Debug Options
% 11.81/1.99  
% 11.81/1.99  --dbg_backtrace                         false
% 11.81/1.99  --dbg_dump_prop_clauses                 false
% 11.81/1.99  --dbg_dump_prop_clauses_file            -
% 11.81/1.99  --dbg_out_stat                          false
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  ------ Proving...
% 11.81/1.99  
% 11.81/1.99  
% 11.81/1.99  % SZS status Theorem for theBenchmark.p
% 11.81/1.99  
% 11.81/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.81/1.99  
% 11.81/1.99  fof(f4,axiom,(
% 11.81/1.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f30,plain,(
% 11.81/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 11.81/1.99    inference(ennf_transformation,[],[f4])).
% 11.81/1.99  
% 11.81/1.99  fof(f43,plain,(
% 11.81/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f44,plain,(
% 11.81/1.99    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f43])).
% 11.81/1.99  
% 11.81/1.99  fof(f65,plain,(
% 11.81/1.99    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 11.81/1.99    inference(cnf_transformation,[],[f44])).
% 11.81/1.99  
% 11.81/1.99  fof(f26,conjecture,(
% 11.81/1.99    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f27,negated_conjecture,(
% 11.81/1.99    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.81/1.99    inference(negated_conjecture,[],[f26])).
% 11.81/1.99  
% 11.81/1.99  fof(f33,plain,(
% 11.81/1.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.81/1.99    inference(ennf_transformation,[],[f27])).
% 11.81/1.99  
% 11.81/1.99  fof(f53,plain,(
% 11.81/1.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f54,plain,(
% 11.81/1.99    (k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f33,f53])).
% 11.81/1.99  
% 11.81/1.99  fof(f94,plain,(
% 11.81/1.99    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 11.81/1.99    inference(cnf_transformation,[],[f54])).
% 11.81/1.99  
% 11.81/1.99  fof(f24,axiom,(
% 11.81/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f91,plain,(
% 11.81/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.81/1.99    inference(cnf_transformation,[],[f24])).
% 11.81/1.99  
% 11.81/1.99  fof(f103,plain,(
% 11.81/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 11.81/1.99    inference(definition_unfolding,[],[f91,f102])).
% 11.81/1.99  
% 11.81/1.99  fof(f16,axiom,(
% 11.81/1.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f82,plain,(
% 11.81/1.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f16])).
% 11.81/1.99  
% 11.81/1.99  fof(f17,axiom,(
% 11.81/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f83,plain,(
% 11.81/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f17])).
% 11.81/1.99  
% 11.81/1.99  fof(f18,axiom,(
% 11.81/1.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f84,plain,(
% 11.81/1.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f18])).
% 11.81/1.99  
% 11.81/1.99  fof(f19,axiom,(
% 11.81/1.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f85,plain,(
% 11.81/1.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f19])).
% 11.81/1.99  
% 11.81/1.99  fof(f20,axiom,(
% 11.81/1.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f86,plain,(
% 11.81/1.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f20])).
% 11.81/1.99  
% 11.81/1.99  fof(f21,axiom,(
% 11.81/1.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f87,plain,(
% 11.81/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f21])).
% 11.81/1.99  
% 11.81/1.99  fof(f22,axiom,(
% 11.81/1.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f88,plain,(
% 11.81/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 11.81/1.99    inference(cnf_transformation,[],[f22])).
% 11.81/1.99  
% 11.81/1.99  fof(f98,plain,(
% 11.81/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 11.81/1.99    inference(definition_unfolding,[],[f87,f88])).
% 11.81/1.99  
% 11.81/1.99  fof(f99,plain,(
% 11.81/1.99    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 11.81/1.99    inference(definition_unfolding,[],[f86,f98])).
% 11.81/1.99  
% 11.81/1.99  fof(f100,plain,(
% 11.81/1.99    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 11.81/1.99    inference(definition_unfolding,[],[f85,f99])).
% 11.81/1.99  
% 11.81/1.99  fof(f101,plain,(
% 11.81/1.99    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 11.81/1.99    inference(definition_unfolding,[],[f84,f100])).
% 11.81/1.99  
% 11.81/1.99  fof(f102,plain,(
% 11.81/1.99    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.81/1.99    inference(definition_unfolding,[],[f83,f101])).
% 11.81/1.99  
% 11.81/1.99  fof(f106,plain,(
% 11.81/1.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.81/1.99    inference(definition_unfolding,[],[f82,f102])).
% 11.81/1.99  
% 11.81/1.99  fof(f129,plain,(
% 11.81/1.99    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 11.81/1.99    inference(definition_unfolding,[],[f94,f103,f106])).
% 11.81/1.99  
% 11.81/1.99  fof(f2,axiom,(
% 11.81/1.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f38,plain,(
% 11.81/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.81/1.99    inference(nnf_transformation,[],[f2])).
% 11.81/1.99  
% 11.81/1.99  fof(f39,plain,(
% 11.81/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.81/1.99    inference(flattening,[],[f38])).
% 11.81/1.99  
% 11.81/1.99  fof(f40,plain,(
% 11.81/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.81/1.99    inference(rectify,[],[f39])).
% 11.81/1.99  
% 11.81/1.99  fof(f41,plain,(
% 11.81/1.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 11.81/1.99    introduced(choice_axiom,[])).
% 11.81/1.99  
% 11.81/1.99  fof(f42,plain,(
% 11.81/1.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.81/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 11.81/1.99  
% 11.81/1.99  fof(f60,plain,(
% 11.81/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 11.81/1.99    inference(cnf_transformation,[],[f42])).
% 11.81/1.99  
% 11.81/1.99  fof(f111,plain,(
% 11.81/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.81/1.99    inference(definition_unfolding,[],[f60,f103])).
% 11.81/1.99  
% 11.81/1.99  fof(f130,plain,(
% 11.81/1.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 11.81/1.99    inference(equality_resolution,[],[f111])).
% 11.81/1.99  
% 11.81/1.99  fof(f14,axiom,(
% 11.81/1.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.81/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/1.99  
% 11.81/1.99  fof(f47,plain,(
% 11.81/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.81/1.99    inference(nnf_transformation,[],[f14])).
% 11.81/1.99  
% 11.81/1.99  fof(f48,plain,(
% 11.81/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.81/2.00    inference(rectify,[],[f47])).
% 11.81/2.00  
% 11.81/2.00  fof(f49,plain,(
% 11.81/2.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f50,plain,(
% 11.81/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 11.81/2.00  
% 11.81/2.00  fof(f77,plain,(
% 11.81/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f50])).
% 11.81/2.00  
% 11.81/2.00  fof(f121,plain,(
% 11.81/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 11.81/2.00    inference(definition_unfolding,[],[f77,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f137,plain,(
% 11.81/2.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 11.81/2.00    inference(equality_resolution,[],[f121])).
% 11.81/2.00  
% 11.81/2.00  fof(f97,plain,(
% 11.81/2.00    k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5),
% 11.81/2.00    inference(cnf_transformation,[],[f54])).
% 11.81/2.00  
% 11.81/2.00  fof(f126,plain,(
% 11.81/2.00    k1_xboole_0 != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 11.81/2.00    inference(definition_unfolding,[],[f97,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f25,axiom,(
% 11.81/2.00    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 11.81/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f52,plain,(
% 11.81/2.00    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 11.81/2.00    inference(nnf_transformation,[],[f25])).
% 11.81/2.00  
% 11.81/2.00  fof(f92,plain,(
% 11.81/2.00    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f52])).
% 11.81/2.00  
% 11.81/2.00  fof(f6,axiom,(
% 11.81/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.81/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f69,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f6])).
% 11.81/2.00  
% 11.81/2.00  fof(f13,axiom,(
% 11.81/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.81/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f76,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f13])).
% 11.81/2.00  
% 11.81/2.00  fof(f104,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.81/2.00    inference(definition_unfolding,[],[f76,f103])).
% 11.81/2.00  
% 11.81/2.00  fof(f105,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 11.81/2.00    inference(definition_unfolding,[],[f69,f104])).
% 11.81/2.00  
% 11.81/2.00  fof(f125,plain,(
% 11.81/2.00    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.81/2.00    inference(definition_unfolding,[],[f92,f105,f106,f106,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f138,plain,(
% 11.81/2.00    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 11.81/2.00    inference(equality_resolution,[],[f125])).
% 11.81/2.00  
% 11.81/2.00  fof(f93,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f52])).
% 11.81/2.00  
% 11.81/2.00  fof(f124,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 = X1) )),
% 11.81/2.00    inference(definition_unfolding,[],[f93,f105,f106,f106,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f5,axiom,(
% 11.81/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f45,plain,(
% 11.81/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.81/2.00    inference(nnf_transformation,[],[f5])).
% 11.81/2.00  
% 11.81/2.00  fof(f46,plain,(
% 11.81/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.81/2.00    inference(flattening,[],[f45])).
% 11.81/2.00  
% 11.81/2.00  fof(f68,plain,(
% 11.81/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f46])).
% 11.81/2.00  
% 11.81/2.00  fof(f23,axiom,(
% 11.81/2.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 11.81/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f51,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 11.81/2.00    inference(nnf_transformation,[],[f23])).
% 11.81/2.00  
% 11.81/2.00  fof(f90,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f51])).
% 11.81/2.00  
% 11.81/2.00  fof(f122,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 11.81/2.00    inference(definition_unfolding,[],[f90,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f10,axiom,(
% 11.81/2.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.81/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f73,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f10])).
% 11.81/2.00  
% 11.81/2.00  fof(f117,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.81/2.00    inference(definition_unfolding,[],[f73,f103])).
% 11.81/2.00  
% 11.81/2.00  fof(f78,plain,(
% 11.81/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f50])).
% 11.81/2.00  
% 11.81/2.00  fof(f120,plain,(
% 11.81/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 11.81/2.00    inference(definition_unfolding,[],[f78,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f135,plain,(
% 11.81/2.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 11.81/2.00    inference(equality_resolution,[],[f120])).
% 11.81/2.00  
% 11.81/2.00  fof(f136,plain,(
% 11.81/2.00    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 11.81/2.00    inference(equality_resolution,[],[f135])).
% 11.81/2.00  
% 11.81/2.00  fof(f58,plain,(
% 11.81/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 11.81/2.00    inference(cnf_transformation,[],[f42])).
% 11.81/2.00  
% 11.81/2.00  fof(f113,plain,(
% 11.81/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.81/2.00    inference(definition_unfolding,[],[f58,f103])).
% 11.81/2.00  
% 11.81/2.00  fof(f132,plain,(
% 11.81/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 11.81/2.00    inference(equality_resolution,[],[f113])).
% 11.81/2.00  
% 11.81/2.00  fof(f79,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f50])).
% 11.81/2.00  
% 11.81/2.00  fof(f119,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1 | sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)) )),
% 11.81/2.00    inference(definition_unfolding,[],[f79,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f59,plain,(
% 11.81/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 11.81/2.00    inference(cnf_transformation,[],[f42])).
% 11.81/2.00  
% 11.81/2.00  fof(f112,plain,(
% 11.81/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 11.81/2.00    inference(definition_unfolding,[],[f59,f103])).
% 11.81/2.00  
% 11.81/2.00  fof(f131,plain,(
% 11.81/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 11.81/2.00    inference(equality_resolution,[],[f112])).
% 11.81/2.00  
% 11.81/2.00  fof(f95,plain,(
% 11.81/2.00    k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5),
% 11.81/2.00    inference(cnf_transformation,[],[f54])).
% 11.81/2.00  
% 11.81/2.00  fof(f128,plain,(
% 11.81/2.00    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 11.81/2.00    inference(definition_unfolding,[],[f95,f106,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f96,plain,(
% 11.81/2.00    k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5),
% 11.81/2.00    inference(cnf_transformation,[],[f54])).
% 11.81/2.00  
% 11.81/2.00  fof(f127,plain,(
% 11.81/2.00    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5),
% 11.81/2.00    inference(definition_unfolding,[],[f96,f106])).
% 11.81/2.00  
% 11.81/2.00  fof(f1,axiom,(
% 11.81/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f29,plain,(
% 11.81/2.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.81/2.00    inference(ennf_transformation,[],[f1])).
% 11.81/2.00  
% 11.81/2.00  fof(f34,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/2.00    inference(nnf_transformation,[],[f29])).
% 11.81/2.00  
% 11.81/2.00  fof(f35,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/2.00    inference(rectify,[],[f34])).
% 11.81/2.00  
% 11.81/2.00  fof(f36,plain,(
% 11.81/2.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f37,plain,(
% 11.81/2.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 11.81/2.00  
% 11.81/2.00  fof(f56,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f37])).
% 11.81/2.00  
% 11.81/2.00  fof(f57,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f37])).
% 11.81/2.00  
% 11.81/2.00  cnf(c_11,plain,
% 11.81/2.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 11.81/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_987,plain,
% 11.81/2.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_32,negated_conjecture,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 11.81/2.00      inference(cnf_transformation,[],[f129]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_7,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1)
% 11.81/2.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 11.81/2.00      inference(cnf_transformation,[],[f130]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_990,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.81/2.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_45304,plain,
% 11.81/2.00      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 11.81/2.00      | r2_hidden(X0,sK6) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_32,c_990]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_24,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 11.81/2.00      inference(cnf_transformation,[],[f137]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_979,plain,
% 11.81/2.00      ( X0 = X1
% 11.81/2.00      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_51711,plain,
% 11.81/2.00      ( sK4 = X0 | r2_hidden(X0,sK6) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_45304,c_979]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_51835,plain,
% 11.81/2.00      ( sK2(sK6) = sK4 | sK6 = k1_xboole_0 ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_987,c_51711]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_29,negated_conjecture,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 11.81/2.00      | k1_xboole_0 != sK6 ),
% 11.81/2.00      inference(cnf_transformation,[],[f126]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_28,plain,
% 11.81/2.00      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f138]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_33,plain,
% 11.81/2.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_28]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_27,plain,
% 11.81/2.00      ( X0 = X1
% 11.81/2.00      | k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f124]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_34,plain,
% 11.81/2.00      ( k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k5_xboole_0(k5_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k3_tarski(k6_enumset1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 11.81/2.00      | sK4 = sK4 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_27]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_496,plain,
% 11.81/2.00      ( X0 != X1
% 11.81/2.00      | X2 != X3
% 11.81/2.00      | X4 != X5
% 11.81/2.00      | X6 != X7
% 11.81/2.00      | X8 != X9
% 11.81/2.00      | X10 != X11
% 11.81/2.00      | X12 != X13
% 11.81/2.00      | X14 != X15
% 11.81/2.00      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 11.81/2.00      theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_501,plain,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 11.81/2.00      | sK4 != sK4 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_496]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 11.81/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1177,plain,
% 11.81/2.00      ( ~ r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5)
% 11.81/2.00      | ~ r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 11.81/2.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1178,plain,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 11.81/2.00      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
% 11.81/2.00      | r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1177]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_25,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1)
% 11.81/2.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f122]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1474,plain,
% 11.81/2.00      ( ~ r2_hidden(sK4,sK5)
% 11.81/2.00      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_25]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1475,plain,
% 11.81/2.00      ( r2_hidden(sK4,sK5) != iProver_top
% 11.81/2.00      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1474]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_494,plain,( X0 = X0 ),theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1899,plain,
% 11.81/2.00      ( k1_xboole_0 = k1_xboole_0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_494]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5386,plain,
% 11.81/2.00      ( ~ r2_hidden(sK4,sK6)
% 11.81/2.00      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_25]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5387,plain,
% 11.81/2.00      ( r2_hidden(sK4,sK6) != iProver_top
% 11.81/2.00      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_5386]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_495,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1382,plain,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 11.81/2.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 11.81/2.00      | sK6 != X0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_495]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_19824,plain,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 11.81/2.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 11.81/2.00      | sK6 != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1382]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_19826,plain,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 11.81/2.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 11.81/2.00      | sK6 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_19824]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_18,plain,
% 11.81/2.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 11.81/2.00      inference(cnf_transformation,[],[f117]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_983,plain,
% 11.81/2.00      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_20164,plain,
% 11.81/2.00      ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_32,c_983]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1187,plain,
% 11.81/2.00      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_495]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_22450,plain,
% 11.81/2.00      ( sK6 != k1_xboole_0
% 11.81/2.00      | k1_xboole_0 = sK6
% 11.81/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1187]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_23,plain,
% 11.81/2.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 11.81/2.00      inference(cnf_transformation,[],[f136]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_980,plain,
% 11.81/2.00      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_9,plain,
% 11.81/2.00      ( r2_hidden(X0,X1)
% 11.81/2.00      | r2_hidden(X0,X2)
% 11.81/2.00      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 11.81/2.00      inference(cnf_transformation,[],[f132]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_988,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.81/2.00      | r2_hidden(X0,X2) = iProver_top
% 11.81/2.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_34319,plain,
% 11.81/2.00      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 11.81/2.00      | r2_hidden(X0,sK5) = iProver_top
% 11.81/2.00      | r2_hidden(X0,sK6) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_32,c_988]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_39248,plain,
% 11.81/2.00      ( r2_hidden(sK4,sK5) = iProver_top
% 11.81/2.00      | r2_hidden(sK4,sK6) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_980,c_34319]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2086,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_12]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_44283,plain,
% 11.81/2.00      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6)
% 11.81/2.00      | ~ r1_tarski(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 11.81/2.00      | sK6 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_2086]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_44284,plain,
% 11.81/2.00      ( sK6 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 11.81/2.00      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6) != iProver_top
% 11.81/2.00      | r1_tarski(sK6,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_44283]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_44286,plain,
% 11.81/2.00      ( sK6 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 11.81/2.00      | r1_tarski(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top
% 11.81/2.00      | r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_44284]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_22,plain,
% 11.81/2.00      ( r2_hidden(sK3(X0,X1),X1)
% 11.81/2.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 11.81/2.00      | sK3(X0,X1) = X0 ),
% 11.81/2.00      inference(cnf_transformation,[],[f119]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_981,plain,
% 11.81/2.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 11.81/2.00      | sK3(X0,X1) = X0
% 11.81/2.00      | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_8,plain,
% 11.81/2.00      ( ~ r2_hidden(X0,X1)
% 11.81/2.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 11.81/2.00      inference(cnf_transformation,[],[f131]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_989,plain,
% 11.81/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.81/2.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_41215,plain,
% 11.81/2.00      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 11.81/2.00      | r2_hidden(X0,sK5) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_32,c_989]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_44394,plain,
% 11.81/2.00      ( sK4 = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_41215,c_979]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_44413,plain,
% 11.81/2.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = sK5
% 11.81/2.00      | sK3(X0,sK5) = X0
% 11.81/2.00      | sK3(X0,sK5) = sK4 ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_981,c_44394]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_31,negated_conjecture,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 11.81/2.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 11.81/2.00      inference(cnf_transformation,[],[f128]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_44858,plain,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
% 11.81/2.00      | sK3(sK4,sK5) = sK4 ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_44413,c_31]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_30,negated_conjecture,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
% 11.81/2.00      | k1_xboole_0 != sK5 ),
% 11.81/2.00      inference(cnf_transformation,[],[f127]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1191,plain,
% 11.81/2.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_495]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1898,plain,
% 11.81/2.00      ( sK5 != k1_xboole_0
% 11.81/2.00      | k1_xboole_0 = sK5
% 11.81/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1191]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_44412,plain,
% 11.81/2.00      ( sK2(sK5) = sK4 | sK5 = k1_xboole_0 ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_987,c_44394]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_44605,plain,
% 11.81/2.00      ( sK5 = k1_xboole_0 | r2_hidden(sK4,sK5) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_44412,c_987]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_51400,plain,
% 11.81/2.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_44858,c_31,c_30,c_1178,c_1475,c_1898,c_1899,c_20164,
% 11.81/2.00                 c_44605]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2,plain,
% 11.81/2.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_995,plain,
% 11.81/2.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 11.81/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1,plain,
% 11.81/2.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_996,plain,
% 11.81/2.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 11.81/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_51710,plain,
% 11.81/2.00      ( r2_hidden(sK0(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK6) != iProver_top
% 11.81/2.00      | r1_tarski(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_45304,c_996]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_51864,plain,
% 11.81/2.00      ( r1_tarski(sK6,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_995,c_51710]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_52207,plain,
% 11.81/2.00      ( sK2(sK6) = sK4 ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_51835,c_31,c_30,c_29,c_33,c_34,c_501,c_1178,c_1475,
% 11.81/2.00                 c_1898,c_1899,c_5387,c_19826,c_20164,c_22450,c_39248,
% 11.81/2.00                 c_44286,c_44605,c_51864]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_52210,plain,
% 11.81/2.00      ( sK6 = k1_xboole_0 | r2_hidden(sK4,sK6) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_52207,c_987]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(contradiction,plain,
% 11.81/2.00      ( $false ),
% 11.81/2.00      inference(minisat,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_52210,c_51864,c_51400,c_44286,c_39248,c_22450,c_20164,
% 11.81/2.00                 c_19826,c_5387,c_1899,c_1475,c_1178,c_501,c_34,c_33,
% 11.81/2.00                 c_29]) ).
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  ------                               Statistics
% 11.81/2.00  
% 11.81/2.00  ------ General
% 11.81/2.00  
% 11.81/2.00  abstr_ref_over_cycles:                  0
% 11.81/2.00  abstr_ref_under_cycles:                 0
% 11.81/2.00  gc_basic_clause_elim:                   0
% 11.81/2.00  forced_gc_time:                         0
% 11.81/2.00  parsing_time:                           0.041
% 11.81/2.00  unif_index_cands_time:                  0.
% 11.81/2.00  unif_index_add_time:                    0.
% 11.81/2.00  orderings_time:                         0.
% 11.81/2.00  out_proof_time:                         0.012
% 11.81/2.00  total_time:                             1.338
% 11.81/2.00  num_of_symbols:                         44
% 11.81/2.00  num_of_terms:                           58780
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing
% 11.81/2.00  
% 11.81/2.00  num_of_splits:                          0
% 11.81/2.00  num_of_split_atoms:                     0
% 11.81/2.00  num_of_reused_defs:                     0
% 11.81/2.00  num_eq_ax_congr_red:                    24
% 11.81/2.00  num_of_sem_filtered_clauses:            1
% 11.81/2.00  num_of_subtypes:                        0
% 11.81/2.00  monotx_restored_types:                  0
% 11.81/2.00  sat_num_of_epr_types:                   0
% 11.81/2.00  sat_num_of_non_cyclic_types:            0
% 11.81/2.00  sat_guarded_non_collapsed_types:        0
% 11.81/2.00  num_pure_diseq_elim:                    0
% 11.81/2.00  simp_replaced_by:                       0
% 11.81/2.00  res_preprocessed:                       143
% 11.81/2.00  prep_upred:                             0
% 11.81/2.00  prep_unflattend:                        0
% 11.81/2.00  smt_new_axioms:                         0
% 11.81/2.00  pred_elim_cands:                        2
% 11.81/2.00  pred_elim:                              0
% 11.81/2.00  pred_elim_cl:                           0
% 11.81/2.00  pred_elim_cycles:                       2
% 11.81/2.00  merged_defs:                            8
% 11.81/2.00  merged_defs_ncl:                        0
% 11.81/2.00  bin_hyper_res:                          8
% 11.81/2.00  prep_cycles:                            4
% 11.81/2.00  pred_elim_time:                         0.
% 11.81/2.00  splitting_time:                         0.
% 11.81/2.00  sem_filter_time:                        0.
% 11.81/2.00  monotx_time:                            0.
% 11.81/2.00  subtype_inf_time:                       0.
% 11.81/2.00  
% 11.81/2.00  ------ Problem properties
% 11.81/2.00  
% 11.81/2.00  clauses:                                32
% 11.81/2.00  conjectures:                            4
% 11.81/2.00  epr:                                    3
% 11.81/2.00  horn:                                   26
% 11.81/2.00  ground:                                 4
% 11.81/2.00  unary:                                  10
% 11.81/2.00  binary:                                 14
% 11.81/2.00  lits:                                   63
% 11.81/2.00  lits_eq:                                28
% 11.81/2.00  fd_pure:                                0
% 11.81/2.00  fd_pseudo:                              0
% 11.81/2.00  fd_cond:                                2
% 11.81/2.00  fd_pseudo_cond:                         7
% 11.81/2.00  ac_symbols:                             1
% 11.81/2.00  
% 11.81/2.00  ------ Propositional Solver
% 11.81/2.00  
% 11.81/2.00  prop_solver_calls:                      27
% 11.81/2.00  prop_fast_solver_calls:                 812
% 11.81/2.00  smt_solver_calls:                       0
% 11.81/2.00  smt_fast_solver_calls:                  0
% 11.81/2.00  prop_num_of_clauses:                    8479
% 11.81/2.00  prop_preprocess_simplified:             12299
% 11.81/2.00  prop_fo_subsumed:                       2
% 11.81/2.00  prop_solver_time:                       0.
% 11.81/2.00  smt_solver_time:                        0.
% 11.81/2.00  smt_fast_solver_time:                   0.
% 11.81/2.00  prop_fast_solver_time:                  0.
% 11.81/2.00  prop_unsat_core_time:                   0.
% 11.81/2.00  
% 11.81/2.00  ------ QBF
% 11.81/2.00  
% 11.81/2.00  qbf_q_res:                              0
% 11.81/2.00  qbf_num_tautologies:                    0
% 11.81/2.00  qbf_prep_cycles:                        0
% 11.81/2.00  
% 11.81/2.00  ------ BMC1
% 11.81/2.00  
% 11.81/2.00  bmc1_current_bound:                     -1
% 11.81/2.00  bmc1_last_solved_bound:                 -1
% 11.81/2.00  bmc1_unsat_core_size:                   -1
% 11.81/2.00  bmc1_unsat_core_parents_size:           -1
% 11.81/2.00  bmc1_merge_next_fun:                    0
% 11.81/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.81/2.00  
% 11.81/2.00  ------ Instantiation
% 11.81/2.00  
% 11.81/2.00  inst_num_of_clauses:                    1227
% 11.81/2.00  inst_num_in_passive:                    269
% 11.81/2.00  inst_num_in_active:                     421
% 11.81/2.00  inst_num_in_unprocessed:                537
% 11.81/2.00  inst_num_of_loops:                      680
% 11.81/2.00  inst_num_of_learning_restarts:          0
% 11.81/2.00  inst_num_moves_active_passive:          255
% 11.81/2.00  inst_lit_activity:                      0
% 11.81/2.00  inst_lit_activity_moves:                0
% 11.81/2.00  inst_num_tautologies:                   0
% 11.81/2.00  inst_num_prop_implied:                  0
% 11.81/2.00  inst_num_existing_simplified:           0
% 11.81/2.00  inst_num_eq_res_simplified:             0
% 11.81/2.00  inst_num_child_elim:                    0
% 11.81/2.00  inst_num_of_dismatching_blockings:      650
% 11.81/2.00  inst_num_of_non_proper_insts:           1475
% 11.81/2.00  inst_num_of_duplicates:                 0
% 11.81/2.00  inst_inst_num_from_inst_to_res:         0
% 11.81/2.00  inst_dismatching_checking_time:         0.
% 11.81/2.00  
% 11.81/2.00  ------ Resolution
% 11.81/2.00  
% 11.81/2.00  res_num_of_clauses:                     0
% 11.81/2.00  res_num_in_passive:                     0
% 11.81/2.00  res_num_in_active:                      0
% 11.81/2.00  res_num_of_loops:                       147
% 11.81/2.00  res_forward_subset_subsumed:            203
% 11.81/2.00  res_backward_subset_subsumed:           6
% 11.81/2.00  res_forward_subsumed:                   0
% 11.81/2.00  res_backward_subsumed:                  0
% 11.81/2.00  res_forward_subsumption_resolution:     0
% 11.81/2.00  res_backward_subsumption_resolution:    0
% 11.81/2.00  res_clause_to_clause_subsumption:       265638
% 11.81/2.00  res_orphan_elimination:                 0
% 11.81/2.00  res_tautology_del:                      120
% 11.81/2.00  res_num_eq_res_simplified:              0
% 11.81/2.00  res_num_sel_changes:                    0
% 11.81/2.00  res_moves_from_active_to_pass:          0
% 11.81/2.00  
% 11.81/2.00  ------ Superposition
% 11.81/2.00  
% 11.81/2.00  sup_time_total:                         0.
% 11.81/2.00  sup_time_generating:                    0.
% 11.81/2.00  sup_time_sim_full:                      0.
% 11.81/2.00  sup_time_sim_immed:                     0.
% 11.81/2.00  
% 11.81/2.00  sup_num_of_clauses:                     3751
% 11.81/2.00  sup_num_in_active:                      123
% 11.81/2.00  sup_num_in_passive:                     3628
% 11.81/2.00  sup_num_of_loops:                       134
% 11.81/2.00  sup_fw_superposition:                   12114
% 11.81/2.00  sup_bw_superposition:                   8452
% 11.81/2.00  sup_immediate_simplified:               6958
% 11.81/2.00  sup_given_eliminated:                   6
% 11.81/2.00  comparisons_done:                       0
% 11.81/2.00  comparisons_avoided:                    13
% 11.81/2.00  
% 11.81/2.00  ------ Simplifications
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  sim_fw_subset_subsumed:                 0
% 11.81/2.00  sim_bw_subset_subsumed:                 2
% 11.81/2.00  sim_fw_subsumed:                        482
% 11.81/2.00  sim_bw_subsumed:                        3
% 11.81/2.00  sim_fw_subsumption_res:                 0
% 11.81/2.00  sim_bw_subsumption_res:                 0
% 11.81/2.00  sim_tautology_del:                      11
% 11.81/2.00  sim_eq_tautology_del:                   481
% 11.81/2.00  sim_eq_res_simp:                        0
% 11.81/2.00  sim_fw_demodulated:                     3714
% 11.81/2.00  sim_bw_demodulated:                     647
% 11.81/2.00  sim_light_normalised:                   2515
% 11.81/2.00  sim_joinable_taut:                      586
% 11.81/2.00  sim_joinable_simp:                      0
% 11.81/2.00  sim_ac_normalised:                      0
% 11.81/2.00  sim_smt_subsumption:                    0
% 11.81/2.00  
%------------------------------------------------------------------------------
