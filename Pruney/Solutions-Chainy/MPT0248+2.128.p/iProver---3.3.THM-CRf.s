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
% DateTime   : Thu Dec  3 11:32:29 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  186 (2086 expanded)
%              Number of clauses        :   97 ( 183 expanded)
%              Number of leaves         :   26 ( 650 expanded)
%              Depth                    :   24
%              Number of atoms          :  448 (3391 expanded)
%              Number of equality atoms :  280 (2973 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f46,plain,
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

fof(f47,plain,
    ( ( k1_xboole_0 != sK6
      | k1_tarski(sK4) != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_xboole_0 != sK5 )
    & ( k1_tarski(sK4) != sK6
      | k1_tarski(sK4) != sK5 )
    & k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f46])).

fof(f83,plain,(
    k2_xboole_0(sK5,sK6) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f75,f91])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f87])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f88])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f89])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f93,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f60,f91])).

fof(f110,plain,(
    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(definition_unfolding,[],[f83,f92,f93])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f56,f92])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f59,f92])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f44])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f80,f93,f93])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f58,f92])).

fof(f84,plain,
    ( k1_tarski(sK4) != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f84,f93,f93])).

fof(f85,plain,
    ( k1_tarski(sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(definition_unfolding,[],[f85,f93])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f93])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f42])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f78,f91])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f82,f93,f93])).

fof(f115,plain,(
    ! [X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f104])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f73,f93])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f86,plain,
    ( k1_xboole_0 != sK6
    | k1_tarski(sK4) != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,
    ( k1_xboole_0 != sK6
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5 ),
    inference(definition_unfolding,[],[f86,f93])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f79,f91])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f92])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_30,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1330,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7127,plain,
    ( r1_xboole_0(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r1_xboole_0(X0,sK5) != iProver_top
    | r1_xboole_0(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_1330])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1337,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7207,plain,
    ( r1_xboole_0(X0,sK5) != iProver_top
    | r1_xboole_0(X0,sK6) != iProver_top
    | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7127,c_1337])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1329,plain,
    ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1817,plain,
    ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_1329])).

cnf(c_26,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1315,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1923,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1817,c_1315])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1332,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5232,plain,
    ( r1_xboole_0(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r1_xboole_0(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_1332])).

cnf(c_5261,plain,
    ( sK5 = k1_xboole_0
    | r1_xboole_0(X0,sK5) != iProver_top
    | r1_xboole_0(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_5232])).

cnf(c_7690,plain,
    ( sK5 = k1_xboole_0
    | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = iProver_top
    | r1_xboole_0(sK5,sK5) != iProver_top
    | r1_xboole_0(sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7207,c_5261])).

cnf(c_725,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1769,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_29,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1930,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1923,c_29])).

cnf(c_28,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1626,plain,
    ( ~ r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1818,plain,
    ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1817])).

cnf(c_2056,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1930,c_29,c_28,c_1626,c_1818])).

cnf(c_726,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1756,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_2425,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(X0)
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 != k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1756])).

cnf(c_3981,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
    | sK6 != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_2425])).

cnf(c_1655,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_1768,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1655])).

cnf(c_2139,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6)) != sK6
    | sK6 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1768])).

cnf(c_6923,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != sK6
    | sK6 = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_19,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1321,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1334,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7208,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
    | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
    | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7127,c_1334])).

cnf(c_22,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_24,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_599,plain,
    ( r2_hidden(X0,X1)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X0) ),
    inference(resolution_lifted,[status(thm)],[c_22,c_24])).

cnf(c_600,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_601,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
    | r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_603,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_730,plain,
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

cnf(c_735,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_738,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1322,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7209,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK5) != iProver_top
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6) != iProver_top
    | r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7127,c_1322])).

cnf(c_7244,plain,
    ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
    | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top
    | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7209])).

cnf(c_7902,plain,
    ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
    | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7208,c_603,c_735,c_738,c_7244])).

cnf(c_7908,plain,
    ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_7902])).

cnf(c_8056,plain,
    ( r2_hidden(sK4,sK5) = iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_7908])).

cnf(c_7,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1525,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_27,negated_conjecture,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1932,plain,
    ( sK5 = k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1923,c_27])).

cnf(c_1973,plain,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1975,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1973])).

cnf(c_1977,plain,
    ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1975])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1974,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1979,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_1981,plain,
    ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1979])).

cnf(c_1536,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_2368,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_728,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2304,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k1_xboole_0)
    | X2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_3131,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X1,k1_xboole_0)
    | X1 != X0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_3132,plain,
    ( X0 != X1
    | k1_xboole_0 != sK5
    | r2_hidden(X1,sK5) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3131])).

cnf(c_3134,plain,
    ( sK4 != sK4
    | k1_xboole_0 != sK5
    | r2_hidden(sK4,sK5) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3132])).

cnf(c_2512,plain,
    ( sK5 = k1_xboole_0
    | r1_xboole_0(sK5,X0) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_1321])).

cnf(c_2542,plain,
    ( sK5 = k1_xboole_0
    | r1_xboole_0(X0,sK5) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2512,c_1337])).

cnf(c_5518,plain,
    ( sK5 = k1_xboole_0
    | r1_xboole_0(X0,sK6) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_5261])).

cnf(c_6930,plain,
    ( sK5 = k1_xboole_0
    | sK6 = k1_xboole_0
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5518,c_1334])).

cnf(c_8657,plain,
    ( r2_hidden(sK4,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8056,c_7,c_738,c_1525,c_1932,c_1977,c_1981,c_2368,c_3134,c_6930])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1320,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4860,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK4,X0) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1923,c_1320])).

cnf(c_11484,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK5,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_8657,c_4860])).

cnf(c_11514,plain,
    ( r1_tarski(sK5,sK6)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11484])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2140,plain,
    ( ~ r1_tarski(X0,sK6)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13389,plain,
    ( ~ r1_tarski(sK5,sK6)
    | k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = sK6 ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_13455,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7690,c_30,c_29,c_28,c_1626,c_1769,c_1818,c_3981,c_6923,c_11514,c_13389])).

cnf(c_13483,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_13455,c_30])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1339,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1335,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4909,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_1322])).

cnf(c_7468,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_4909])).

cnf(c_1336,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8645,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_7468,c_1336])).

cnf(c_13490,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6 ),
    inference(demodulation,[status(thm)],[c_13483,c_8645])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13490,c_2056])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.53/0.99  
% 3.53/0.99  ------  iProver source info
% 3.53/0.99  
% 3.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.53/0.99  git: non_committed_changes: false
% 3.53/0.99  git: last_make_outside_of_git: false
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    --mode clausify
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             all
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         305.
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              default
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           true
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             true
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         false
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     num_symb
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       true
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     false
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   []
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_full_bw                           [BwDemod]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  ------ Parsing...
% 3.53/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.53/0.99  ------ Proving...
% 3.53/0.99  ------ Problem Properties 
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  clauses                                 31
% 3.53/0.99  conjectures                             4
% 3.53/0.99  EPR                                     5
% 3.53/0.99  Horn                                    26
% 3.53/0.99  unary                                   7
% 3.53/0.99  binary                                  16
% 3.53/0.99  lits                                    64
% 3.53/0.99  lits eq                                 15
% 3.53/0.99  fd_pure                                 0
% 3.53/0.99  fd_pseudo                               0
% 3.53/0.99  fd_cond                                 1
% 3.53/0.99  fd_pseudo_cond                          4
% 3.53/0.99  AC symbols                              0
% 3.53/0.99  
% 3.53/0.99  ------ Schedule dynamic 5 is on 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ 
% 3.53/0.99  Current options:
% 3.53/0.99  ------ 
% 3.53/0.99  
% 3.53/0.99  ------ Input Options
% 3.53/0.99  
% 3.53/0.99  --out_options                           all
% 3.53/0.99  --tptp_safe_out                         true
% 3.53/0.99  --problem_path                          ""
% 3.53/0.99  --include_path                          ""
% 3.53/0.99  --clausifier                            res/vclausify_rel
% 3.53/0.99  --clausifier_options                    --mode clausify
% 3.53/0.99  --stdin                                 false
% 3.53/0.99  --stats_out                             all
% 3.53/0.99  
% 3.53/0.99  ------ General Options
% 3.53/0.99  
% 3.53/0.99  --fof                                   false
% 3.53/0.99  --time_out_real                         305.
% 3.53/0.99  --time_out_virtual                      -1.
% 3.53/0.99  --symbol_type_check                     false
% 3.53/0.99  --clausify_out                          false
% 3.53/0.99  --sig_cnt_out                           false
% 3.53/0.99  --trig_cnt_out                          false
% 3.53/0.99  --trig_cnt_out_tolerance                1.
% 3.53/0.99  --trig_cnt_out_sk_spl                   false
% 3.53/0.99  --abstr_cl_out                          false
% 3.53/0.99  
% 3.53/0.99  ------ Global Options
% 3.53/0.99  
% 3.53/0.99  --schedule                              default
% 3.53/0.99  --add_important_lit                     false
% 3.53/0.99  --prop_solver_per_cl                    1000
% 3.53/0.99  --min_unsat_core                        false
% 3.53/0.99  --soft_assumptions                      false
% 3.53/0.99  --soft_lemma_size                       3
% 3.53/0.99  --prop_impl_unit_size                   0
% 3.53/0.99  --prop_impl_unit                        []
% 3.53/0.99  --share_sel_clauses                     true
% 3.53/0.99  --reset_solvers                         false
% 3.53/0.99  --bc_imp_inh                            [conj_cone]
% 3.53/0.99  --conj_cone_tolerance                   3.
% 3.53/0.99  --extra_neg_conj                        none
% 3.53/0.99  --large_theory_mode                     true
% 3.53/0.99  --prolific_symb_bound                   200
% 3.53/0.99  --lt_threshold                          2000
% 3.53/0.99  --clause_weak_htbl                      true
% 3.53/0.99  --gc_record_bc_elim                     false
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing Options
% 3.53/0.99  
% 3.53/0.99  --preprocessing_flag                    true
% 3.53/0.99  --time_out_prep_mult                    0.1
% 3.53/0.99  --splitting_mode                        input
% 3.53/0.99  --splitting_grd                         true
% 3.53/0.99  --splitting_cvd                         false
% 3.53/0.99  --splitting_cvd_svl                     false
% 3.53/0.99  --splitting_nvd                         32
% 3.53/0.99  --sub_typing                            true
% 3.53/0.99  --prep_gs_sim                           true
% 3.53/0.99  --prep_unflatten                        true
% 3.53/0.99  --prep_res_sim                          true
% 3.53/0.99  --prep_upred                            true
% 3.53/0.99  --prep_sem_filter                       exhaustive
% 3.53/0.99  --prep_sem_filter_out                   false
% 3.53/0.99  --pred_elim                             true
% 3.53/0.99  --res_sim_input                         true
% 3.53/0.99  --eq_ax_congr_red                       true
% 3.53/0.99  --pure_diseq_elim                       true
% 3.53/0.99  --brand_transform                       false
% 3.53/0.99  --non_eq_to_eq                          false
% 3.53/0.99  --prep_def_merge                        true
% 3.53/0.99  --prep_def_merge_prop_impl              false
% 3.53/0.99  --prep_def_merge_mbd                    true
% 3.53/0.99  --prep_def_merge_tr_red                 false
% 3.53/0.99  --prep_def_merge_tr_cl                  false
% 3.53/0.99  --smt_preprocessing                     true
% 3.53/0.99  --smt_ac_axioms                         fast
% 3.53/0.99  --preprocessed_out                      false
% 3.53/0.99  --preprocessed_stats                    false
% 3.53/0.99  
% 3.53/0.99  ------ Abstraction refinement Options
% 3.53/0.99  
% 3.53/0.99  --abstr_ref                             []
% 3.53/0.99  --abstr_ref_prep                        false
% 3.53/0.99  --abstr_ref_until_sat                   false
% 3.53/0.99  --abstr_ref_sig_restrict                funpre
% 3.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.53/0.99  --abstr_ref_under                       []
% 3.53/0.99  
% 3.53/0.99  ------ SAT Options
% 3.53/0.99  
% 3.53/0.99  --sat_mode                              false
% 3.53/0.99  --sat_fm_restart_options                ""
% 3.53/0.99  --sat_gr_def                            false
% 3.53/0.99  --sat_epr_types                         true
% 3.53/0.99  --sat_non_cyclic_types                  false
% 3.53/0.99  --sat_finite_models                     false
% 3.53/0.99  --sat_fm_lemmas                         false
% 3.53/0.99  --sat_fm_prep                           false
% 3.53/0.99  --sat_fm_uc_incr                        true
% 3.53/0.99  --sat_out_model                         small
% 3.53/0.99  --sat_out_clauses                       false
% 3.53/0.99  
% 3.53/0.99  ------ QBF Options
% 3.53/0.99  
% 3.53/0.99  --qbf_mode                              false
% 3.53/0.99  --qbf_elim_univ                         false
% 3.53/0.99  --qbf_dom_inst                          none
% 3.53/0.99  --qbf_dom_pre_inst                      false
% 3.53/0.99  --qbf_sk_in                             false
% 3.53/0.99  --qbf_pred_elim                         true
% 3.53/0.99  --qbf_split                             512
% 3.53/0.99  
% 3.53/0.99  ------ BMC1 Options
% 3.53/0.99  
% 3.53/0.99  --bmc1_incremental                      false
% 3.53/0.99  --bmc1_axioms                           reachable_all
% 3.53/0.99  --bmc1_min_bound                        0
% 3.53/0.99  --bmc1_max_bound                        -1
% 3.53/0.99  --bmc1_max_bound_default                -1
% 3.53/0.99  --bmc1_symbol_reachability              true
% 3.53/0.99  --bmc1_property_lemmas                  false
% 3.53/0.99  --bmc1_k_induction                      false
% 3.53/0.99  --bmc1_non_equiv_states                 false
% 3.53/0.99  --bmc1_deadlock                         false
% 3.53/0.99  --bmc1_ucm                              false
% 3.53/0.99  --bmc1_add_unsat_core                   none
% 3.53/0.99  --bmc1_unsat_core_children              false
% 3.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.53/0.99  --bmc1_out_stat                         full
% 3.53/0.99  --bmc1_ground_init                      false
% 3.53/0.99  --bmc1_pre_inst_next_state              false
% 3.53/0.99  --bmc1_pre_inst_state                   false
% 3.53/0.99  --bmc1_pre_inst_reach_state             false
% 3.53/0.99  --bmc1_out_unsat_core                   false
% 3.53/0.99  --bmc1_aig_witness_out                  false
% 3.53/0.99  --bmc1_verbose                          false
% 3.53/0.99  --bmc1_dump_clauses_tptp                false
% 3.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.53/0.99  --bmc1_dump_file                        -
% 3.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.53/0.99  --bmc1_ucm_extend_mode                  1
% 3.53/0.99  --bmc1_ucm_init_mode                    2
% 3.53/0.99  --bmc1_ucm_cone_mode                    none
% 3.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.53/0.99  --bmc1_ucm_relax_model                  4
% 3.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.53/0.99  --bmc1_ucm_layered_model                none
% 3.53/0.99  --bmc1_ucm_max_lemma_size               10
% 3.53/0.99  
% 3.53/0.99  ------ AIG Options
% 3.53/0.99  
% 3.53/0.99  --aig_mode                              false
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation Options
% 3.53/0.99  
% 3.53/0.99  --instantiation_flag                    true
% 3.53/0.99  --inst_sos_flag                         false
% 3.53/0.99  --inst_sos_phase                        true
% 3.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.53/0.99  --inst_lit_sel_side                     none
% 3.53/0.99  --inst_solver_per_active                1400
% 3.53/0.99  --inst_solver_calls_frac                1.
% 3.53/0.99  --inst_passive_queue_type               priority_queues
% 3.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.53/0.99  --inst_passive_queues_freq              [25;2]
% 3.53/0.99  --inst_dismatching                      true
% 3.53/0.99  --inst_eager_unprocessed_to_passive     true
% 3.53/0.99  --inst_prop_sim_given                   true
% 3.53/0.99  --inst_prop_sim_new                     false
% 3.53/0.99  --inst_subs_new                         false
% 3.53/0.99  --inst_eq_res_simp                      false
% 3.53/0.99  --inst_subs_given                       false
% 3.53/0.99  --inst_orphan_elimination               true
% 3.53/0.99  --inst_learning_loop_flag               true
% 3.53/0.99  --inst_learning_start                   3000
% 3.53/0.99  --inst_learning_factor                  2
% 3.53/0.99  --inst_start_prop_sim_after_learn       3
% 3.53/0.99  --inst_sel_renew                        solver
% 3.53/0.99  --inst_lit_activity_flag                true
% 3.53/0.99  --inst_restr_to_given                   false
% 3.53/0.99  --inst_activity_threshold               500
% 3.53/0.99  --inst_out_proof                        true
% 3.53/0.99  
% 3.53/0.99  ------ Resolution Options
% 3.53/0.99  
% 3.53/0.99  --resolution_flag                       false
% 3.53/0.99  --res_lit_sel                           adaptive
% 3.53/0.99  --res_lit_sel_side                      none
% 3.53/0.99  --res_ordering                          kbo
% 3.53/0.99  --res_to_prop_solver                    active
% 3.53/0.99  --res_prop_simpl_new                    false
% 3.53/0.99  --res_prop_simpl_given                  true
% 3.53/0.99  --res_passive_queue_type                priority_queues
% 3.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.53/0.99  --res_passive_queues_freq               [15;5]
% 3.53/0.99  --res_forward_subs                      full
% 3.53/0.99  --res_backward_subs                     full
% 3.53/0.99  --res_forward_subs_resolution           true
% 3.53/0.99  --res_backward_subs_resolution          true
% 3.53/0.99  --res_orphan_elimination                true
% 3.53/0.99  --res_time_limit                        2.
% 3.53/0.99  --res_out_proof                         true
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Options
% 3.53/0.99  
% 3.53/0.99  --superposition_flag                    true
% 3.53/0.99  --sup_passive_queue_type                priority_queues
% 3.53/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.53/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.53/0.99  --demod_completeness_check              fast
% 3.53/0.99  --demod_use_ground                      true
% 3.53/0.99  --sup_to_prop_solver                    passive
% 3.53/0.99  --sup_prop_simpl_new                    true
% 3.53/0.99  --sup_prop_simpl_given                  true
% 3.53/0.99  --sup_fun_splitting                     false
% 3.53/0.99  --sup_smt_interval                      50000
% 3.53/0.99  
% 3.53/0.99  ------ Superposition Simplification Setup
% 3.53/0.99  
% 3.53/0.99  --sup_indices_passive                   []
% 3.53/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.53/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.53/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_full_bw                           [BwDemod]
% 3.53/0.99  --sup_immed_triv                        [TrivRules]
% 3.53/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.53/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_immed_bw_main                     []
% 3.53/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.53/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.53/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.53/0.99  
% 3.53/0.99  ------ Combination Options
% 3.53/0.99  
% 3.53/0.99  --comb_res_mult                         3
% 3.53/0.99  --comb_sup_mult                         2
% 3.53/0.99  --comb_inst_mult                        10
% 3.53/0.99  
% 3.53/0.99  ------ Debug Options
% 3.53/0.99  
% 3.53/0.99  --dbg_backtrace                         false
% 3.53/0.99  --dbg_dump_prop_clauses                 false
% 3.53/0.99  --dbg_dump_prop_clauses_file            -
% 3.53/0.99  --dbg_out_stat                          false
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  ------ Proving...
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS status Theorem for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  fof(f22,conjecture,(
% 3.53/0.99    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f23,negated_conjecture,(
% 3.53/0.99    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.53/0.99    inference(negated_conjecture,[],[f22])).
% 3.53/0.99  
% 3.53/0.99  fof(f31,plain,(
% 3.53/0.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 3.53/0.99    inference(ennf_transformation,[],[f23])).
% 3.53/0.99  
% 3.53/0.99  fof(f46,plain,(
% 3.53/0.99    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f47,plain,(
% 3.53/0.99    (k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5) & (k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5) & (k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5) & k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f46])).
% 3.53/0.99  
% 3.53/0.99  fof(f83,plain,(
% 3.53/0.99    k2_xboole_0(sK5,sK6) = k1_tarski(sK4)),
% 3.53/0.99    inference(cnf_transformation,[],[f47])).
% 3.53/0.99  
% 3.53/0.99  fof(f18,axiom,(
% 3.53/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f75,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f18])).
% 3.53/0.99  
% 3.53/0.99  fof(f92,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.53/0.99    inference(definition_unfolding,[],[f75,f91])).
% 3.53/0.99  
% 3.53/0.99  fof(f8,axiom,(
% 3.53/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f60,plain,(
% 3.53/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f8])).
% 3.53/0.99  
% 3.53/0.99  fof(f9,axiom,(
% 3.53/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f61,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f9])).
% 3.53/0.99  
% 3.53/0.99  fof(f10,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f62,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f10])).
% 3.53/0.99  
% 3.53/0.99  fof(f11,axiom,(
% 3.53/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f63,plain,(
% 3.53/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f11])).
% 3.53/0.99  
% 3.53/0.99  fof(f12,axiom,(
% 3.53/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f64,plain,(
% 3.53/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f12])).
% 3.53/0.99  
% 3.53/0.99  fof(f13,axiom,(
% 3.53/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f65,plain,(
% 3.53/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f13])).
% 3.53/0.99  
% 3.53/0.99  fof(f14,axiom,(
% 3.53/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f66,plain,(
% 3.53/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f14])).
% 3.53/0.99  
% 3.53/0.99  fof(f87,plain,(
% 3.53/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f65,f66])).
% 3.53/0.99  
% 3.53/0.99  fof(f88,plain,(
% 3.53/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f64,f87])).
% 3.53/0.99  
% 3.53/0.99  fof(f89,plain,(
% 3.53/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f63,f88])).
% 3.53/0.99  
% 3.53/0.99  fof(f90,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f62,f89])).
% 3.53/0.99  
% 3.53/0.99  fof(f91,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f61,f90])).
% 3.53/0.99  
% 3.53/0.99  fof(f93,plain,(
% 3.53/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f60,f91])).
% 3.53/0.99  
% 3.53/0.99  fof(f110,plain,(
% 3.53/0.99    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))),
% 3.53/0.99    inference(definition_unfolding,[],[f83,f92,f93])).
% 3.53/0.99  
% 3.53/0.99  fof(f6,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f28,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.53/0.99    inference(ennf_transformation,[],[f6])).
% 3.53/0.99  
% 3.53/0.99  fof(f56,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f28])).
% 3.53/0.99  
% 3.53/0.99  fof(f97,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 3.53/0.99    inference(definition_unfolding,[],[f56,f92])).
% 3.53/0.99  
% 3.53/0.99  fof(f2,axiom,(
% 3.53/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f25,plain,(
% 3.53/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.53/0.99    inference(ennf_transformation,[],[f2])).
% 3.53/0.99  
% 3.53/0.99  fof(f51,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f25])).
% 3.53/0.99  
% 3.53/0.99  fof(f7,axiom,(
% 3.53/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f59,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f7])).
% 3.53/0.99  
% 3.53/0.99  fof(f98,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.53/0.99    inference(definition_unfolding,[],[f59,f92])).
% 3.53/0.99  
% 3.53/0.99  fof(f21,axiom,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f44,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.53/0.99    inference(nnf_transformation,[],[f21])).
% 3.53/0.99  
% 3.53/0.99  fof(f45,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.53/0.99    inference(flattening,[],[f44])).
% 3.53/0.99  
% 3.53/0.99  fof(f80,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.53/0.99    inference(cnf_transformation,[],[f45])).
% 3.53/0.99  
% 3.53/0.99  fof(f106,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.53/0.99    inference(definition_unfolding,[],[f80,f93,f93])).
% 3.53/0.99  
% 3.53/0.99  fof(f58,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f28])).
% 3.53/0.99  
% 3.53/0.99  fof(f95,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | r1_xboole_0(X0,X2)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f58,f92])).
% 3.53/0.99  
% 3.53/0.99  fof(f84,plain,(
% 3.53/0.99    k1_tarski(sK4) != sK6 | k1_tarski(sK4) != sK5),
% 3.53/0.99    inference(cnf_transformation,[],[f47])).
% 3.53/0.99  
% 3.53/0.99  fof(f109,plain,(
% 3.53/0.99    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 3.53/0.99    inference(definition_unfolding,[],[f84,f93,f93])).
% 3.53/0.99  
% 3.53/0.99  fof(f85,plain,(
% 3.53/0.99    k1_tarski(sK4) != sK6 | k1_xboole_0 != sK5),
% 3.53/0.99    inference(cnf_transformation,[],[f47])).
% 3.53/0.99  
% 3.53/0.99  fof(f108,plain,(
% 3.53/0.99    k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 | k1_xboole_0 != sK5),
% 3.53/0.99    inference(definition_unfolding,[],[f85,f93])).
% 3.53/0.99  
% 3.53/0.99  fof(f17,axiom,(
% 3.53/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f30,plain,(
% 3.53/0.99    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 3.53/0.99    inference(ennf_transformation,[],[f17])).
% 3.53/0.99  
% 3.53/0.99  fof(f74,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f30])).
% 3.53/0.99  
% 3.53/0.99  fof(f100,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f74,f93])).
% 3.53/0.99  
% 3.53/0.99  fof(f5,axiom,(
% 3.53/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f27,plain,(
% 3.53/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 3.53/0.99    inference(ennf_transformation,[],[f5])).
% 3.53/0.99  
% 3.53/0.99  fof(f55,plain,(
% 3.53/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 3.53/0.99    inference(cnf_transformation,[],[f27])).
% 3.53/0.99  
% 3.53/0.99  fof(f20,axiom,(
% 3.53/0.99    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f42,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.53/0.99    inference(nnf_transformation,[],[f20])).
% 3.53/0.99  
% 3.53/0.99  fof(f43,plain,(
% 3.53/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.53/0.99    inference(flattening,[],[f42])).
% 3.53/0.99  
% 3.53/0.99  fof(f78,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f43])).
% 3.53/0.99  
% 3.53/0.99  fof(f102,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f78,f91])).
% 3.53/0.99  
% 3.53/0.99  fof(f82,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 3.53/0.99    inference(cnf_transformation,[],[f45])).
% 3.53/0.99  
% 3.53/0.99  fof(f104,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 3.53/0.99    inference(definition_unfolding,[],[f82,f93,f93])).
% 3.53/0.99  
% 3.53/0.99  fof(f115,plain,(
% 3.53/0.99    ( ! [X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.53/0.99    inference(equality_resolution,[],[f104])).
% 3.53/0.99  
% 3.53/0.99  fof(f16,axiom,(
% 3.53/0.99    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f29,plain,(
% 3.53/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 3.53/0.99    inference(ennf_transformation,[],[f16])).
% 3.53/0.99  
% 3.53/0.99  fof(f73,plain,(
% 3.53/0.99    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f29])).
% 3.53/0.99  
% 3.53/0.99  fof(f99,plain,(
% 3.53/0.99    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f73,f93])).
% 3.53/0.99  
% 3.53/0.99  fof(f54,plain,(
% 3.53/0.99    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f27])).
% 3.53/0.99  
% 3.53/0.99  fof(f111,plain,(
% 3.53/0.99    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.53/0.99    inference(equality_resolution,[],[f54])).
% 3.53/0.99  
% 3.53/0.99  fof(f86,plain,(
% 3.53/0.99    k1_xboole_0 != sK6 | k1_tarski(sK4) != sK5),
% 3.53/0.99    inference(cnf_transformation,[],[f47])).
% 3.53/0.99  
% 3.53/0.99  fof(f107,plain,(
% 3.53/0.99    k1_xboole_0 != sK6 | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5),
% 3.53/0.99    inference(definition_unfolding,[],[f86,f93])).
% 3.53/0.99  
% 3.53/0.99  fof(f4,axiom,(
% 3.53/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f53,plain,(
% 3.53/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f4])).
% 3.53/0.99  
% 3.53/0.99  fof(f79,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f43])).
% 3.53/0.99  
% 3.53/0.99  fof(f101,plain,(
% 3.53/0.99    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f79,f91])).
% 3.53/0.99  
% 3.53/0.99  fof(f3,axiom,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f26,plain,(
% 3.53/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.53/0.99    inference(ennf_transformation,[],[f3])).
% 3.53/0.99  
% 3.53/0.99  fof(f52,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f26])).
% 3.53/0.99  
% 3.53/0.99  fof(f94,plain,(
% 3.53/0.99    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.53/0.99    inference(definition_unfolding,[],[f52,f92])).
% 3.53/0.99  
% 3.53/0.99  fof(f1,axiom,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.53/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.53/0.99  
% 3.53/0.99  fof(f24,plain,(
% 3.53/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.53/0.99    inference(ennf_transformation,[],[f1])).
% 3.53/0.99  
% 3.53/0.99  fof(f32,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/0.99    inference(nnf_transformation,[],[f24])).
% 3.53/0.99  
% 3.53/0.99  fof(f33,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/0.99    inference(rectify,[],[f32])).
% 3.53/0.99  
% 3.53/0.99  fof(f34,plain,(
% 3.53/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.53/0.99    introduced(choice_axiom,[])).
% 3.53/0.99  
% 3.53/0.99  fof(f35,plain,(
% 3.53/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.53/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 3.53/0.99  
% 3.53/0.99  fof(f49,plain,(
% 3.53/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.53/0.99    inference(cnf_transformation,[],[f35])).
% 3.53/0.99  
% 3.53/0.99  cnf(c_30,negated_conjecture,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_10,plain,
% 3.53/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.53/0.99      | ~ r1_xboole_0(X0,X2)
% 3.53/0.99      | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.53/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1330,plain,
% 3.53/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.53/0.99      | r1_xboole_0(X0,X2) != iProver_top
% 3.53/0.99      | r1_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7127,plain,
% 3.53/0.99      ( r1_xboole_0(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 3.53/0.99      | r1_xboole_0(X0,sK5) != iProver_top
% 3.53/0.99      | r1_xboole_0(X0,sK6) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_30,c_1330]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3,plain,
% 3.53/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1337,plain,
% 3.53/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.53/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7207,plain,
% 3.53/0.99      ( r1_xboole_0(X0,sK5) != iProver_top
% 3.53/0.99      | r1_xboole_0(X0,sK6) != iProver_top
% 3.53/0.99      | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_7127,c_1337]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_11,plain,
% 3.53/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
% 3.53/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1329,plain,
% 3.53/0.99      ( r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1817,plain,
% 3.53/0.99      ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_30,c_1329]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_26,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.53/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.53/0.99      | k1_xboole_0 = X0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1315,plain,
% 3.53/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.53/0.99      | k1_xboole_0 = X1
% 3.53/0.99      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1923,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 3.53/0.99      | sK5 = k1_xboole_0 ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1817,c_1315]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_8,plain,
% 3.53/0.99      ( r1_xboole_0(X0,X1)
% 3.53/0.99      | ~ r1_xboole_0(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.53/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1332,plain,
% 3.53/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.53/0.99      | r1_xboole_0(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5232,plain,
% 3.53/0.99      ( r1_xboole_0(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 3.53/0.99      | r1_xboole_0(X0,sK6) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_30,c_1332]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5261,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0
% 3.53/0.99      | r1_xboole_0(X0,sK5) != iProver_top
% 3.53/0.99      | r1_xboole_0(X0,sK6) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1923,c_5232]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7690,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0
% 3.53/0.99      | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) = iProver_top
% 3.53/0.99      | r1_xboole_0(sK5,sK5) != iProver_top
% 3.53/0.99      | r1_xboole_0(sK5,sK6) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_7207,c_5261]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_725,plain,( X0 = X0 ),theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1769,plain,
% 3.53/0.99      ( sK6 = sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_725]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_29,negated_conjecture,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 3.53/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 3.53/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1930,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
% 3.53/0.99      | sK5 = k1_xboole_0 ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1923,c_29]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_28,negated_conjecture,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6
% 3.53/0.99      | k1_xboole_0 != sK5 ),
% 3.53/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1626,plain,
% 3.53/0.99      ( ~ r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 3.53/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK5
% 3.53/0.99      | k1_xboole_0 = sK5 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1818,plain,
% 3.53/0.99      ( r1_tarski(sK5,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 3.53/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1817]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2056,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK6 ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_1930,c_29,c_28,c_1626,c_1818]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_726,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1756,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 3.53/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 3.53/0.99      | sK6 != X0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2425,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(X0)
% 3.53/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 3.53/0.99      | sK6 != k3_tarski(X0) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1756]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3981,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
% 3.53/0.99      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6
% 3.53/0.99      | sK6 != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2425]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1655,plain,
% 3.53/0.99      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1768,plain,
% 3.53/0.99      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1655]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2139,plain,
% 3.53/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6)) != sK6
% 3.53/0.99      | sK6 = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6))
% 3.53/0.99      | sK6 != sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1768]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6923,plain,
% 3.53/0.99      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) != sK6
% 3.53/0.99      | sK6 = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6))
% 3.53/0.99      | sK6 != sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2139]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_19,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 3.53/0.99      | r2_hidden(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1321,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 3.53/0.99      | r2_hidden(X0,X1) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6,plain,
% 3.53/0.99      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 3.53/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1334,plain,
% 3.53/0.99      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7208,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k1_xboole_0
% 3.53/0.99      | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
% 3.53/0.99      | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_7127,c_1334]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_22,plain,
% 3.53/0.99      ( r2_hidden(X0,X1)
% 3.53/0.99      | ~ r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_24,plain,
% 3.53/0.99      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 3.53/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_599,plain,
% 3.53/0.99      ( r2_hidden(X0,X1)
% 3.53/0.99      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1
% 3.53/0.99      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X0) ),
% 3.53/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_24]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_600,plain,
% 3.53/0.99      ( r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.53/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0) ),
% 3.53/0.99      inference(unflattening,[status(thm)],[c_599]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_601,plain,
% 3.53/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
% 3.53/0.99      | r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_603,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 3.53/0.99      | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_601]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_730,plain,
% 3.53/0.99      ( X0 != X1
% 3.53/0.99      | X2 != X3
% 3.53/0.99      | X4 != X5
% 3.53/0.99      | X6 != X7
% 3.53/0.99      | X8 != X9
% 3.53/0.99      | X10 != X11
% 3.53/0.99      | X12 != X13
% 3.53/0.99      | X14 != X15
% 3.53/0.99      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 3.53/0.99      theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_735,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 3.53/0.99      | sK4 != sK4 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_730]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_738,plain,
% 3.53/0.99      ( sK4 = sK4 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_725]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_18,plain,
% 3.53/0.99      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 3.53/0.99      | ~ r2_hidden(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1322,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != iProver_top
% 3.53/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7209,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK5) != iProver_top
% 3.53/0.99      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),sK6) != iProver_top
% 3.53/0.99      | r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_7127,c_1322]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7244,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
% 3.53/0.99      | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top
% 3.53/0.99      | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_7209]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7902,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK5) != iProver_top
% 3.53/0.99      | r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_7208,c_603,c_735,c_738,c_7244]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7908,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) != iProver_top
% 3.53/0.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1321,c_7902]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_8056,plain,
% 3.53/0.99      ( r2_hidden(sK4,sK5) = iProver_top
% 3.53/0.99      | r2_hidden(sK4,sK6) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1321,c_7908]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7,plain,
% 3.53/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1525,plain,
% 3.53/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.53/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_27,negated_conjecture,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != sK5
% 3.53/0.99      | k1_xboole_0 != sK6 ),
% 3.53/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1932,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0 | sK6 != k1_xboole_0 ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1923,c_27]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1973,plain,
% 3.53/0.99      ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)
% 3.53/0.99      | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1975,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) != iProver_top
% 3.53/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1973]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1977,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0) != iProver_top
% 3.53/0.99      | r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1975]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5,plain,
% 3.53/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.53/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1974,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1979,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1981,plain,
% 3.53/0.99      ( r1_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_xboole_0) = iProver_top ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1979]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1536,plain,
% 3.53/0.99      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_726]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2368,plain,
% 3.53/0.99      ( sK5 != k1_xboole_0
% 3.53/0.99      | k1_xboole_0 = sK5
% 3.53/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_1536]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_728,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.53/0.99      theory(equality) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2304,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1)
% 3.53/0.99      | r2_hidden(X2,k1_xboole_0)
% 3.53/0.99      | X2 != X0
% 3.53/0.99      | k1_xboole_0 != X1 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_728]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3131,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,sK5)
% 3.53/0.99      | r2_hidden(X1,k1_xboole_0)
% 3.53/0.99      | X1 != X0
% 3.53/0.99      | k1_xboole_0 != sK5 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2304]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3132,plain,
% 3.53/0.99      ( X0 != X1
% 3.53/0.99      | k1_xboole_0 != sK5
% 3.53/0.99      | r2_hidden(X1,sK5) != iProver_top
% 3.53/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_3131]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_3134,plain,
% 3.53/0.99      ( sK4 != sK4
% 3.53/0.99      | k1_xboole_0 != sK5
% 3.53/0.99      | r2_hidden(sK4,sK5) != iProver_top
% 3.53/0.99      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_3132]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2512,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0
% 3.53/0.99      | r1_xboole_0(sK5,X0) = iProver_top
% 3.53/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1923,c_1321]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2542,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0
% 3.53/0.99      | r1_xboole_0(X0,sK5) = iProver_top
% 3.53/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_2512,c_1337]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_5518,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0
% 3.53/0.99      | r1_xboole_0(X0,sK6) = iProver_top
% 3.53/0.99      | r2_hidden(sK4,X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_2542,c_5261]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_6930,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0
% 3.53/0.99      | sK6 = k1_xboole_0
% 3.53/0.99      | r2_hidden(sK4,sK6) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_5518,c_1334]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_8657,plain,
% 3.53/0.99      ( r2_hidden(sK4,sK6) = iProver_top ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_8056,c_7,c_738,c_1525,c_1932,c_1977,c_1981,c_2368,
% 3.53/0.99                 c_3134,c_6930]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_21,plain,
% 3.53/0.99      ( ~ r2_hidden(X0,X1)
% 3.53/0.99      | ~ r2_hidden(X2,X1)
% 3.53/0.99      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1320,plain,
% 3.53/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.53/0.99      | r2_hidden(X2,X1) != iProver_top
% 3.53/0.99      | r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4860,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0
% 3.53/0.99      | r2_hidden(sK4,X0) != iProver_top
% 3.53/0.99      | r1_tarski(sK5,X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1923,c_1320]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_11484,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0 | r1_tarski(sK5,sK6) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_8657,c_4860]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_11514,plain,
% 3.53/0.99      ( r1_tarski(sK5,sK6) | sK5 = k1_xboole_0 ),
% 3.53/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_11484]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,X1)
% 3.53/0.99      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 3.53/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_2140,plain,
% 3.53/0.99      ( ~ r1_tarski(X0,sK6)
% 3.53/0.99      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK6)) = sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_13389,plain,
% 3.53/0.99      ( ~ r1_tarski(sK5,sK6)
% 3.53/0.99      | k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK6)) = sK6 ),
% 3.53/0.99      inference(instantiation,[status(thm)],[c_2140]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_13455,plain,
% 3.53/0.99      ( sK5 = k1_xboole_0 ),
% 3.53/0.99      inference(global_propositional_subsumption,
% 3.53/0.99                [status(thm)],
% 3.53/0.99                [c_7690,c_30,c_29,c_28,c_1626,c_1769,c_1818,c_3981,
% 3.53/0.99                 c_6923,c_11514,c_13389]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_13483,plain,
% 3.53/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK6)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 3.53/0.99      inference(demodulation,[status(thm)],[c_13455,c_30]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1,plain,
% 3.53/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.53/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1339,plain,
% 3.53/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.53/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1335,plain,
% 3.53/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_4909,plain,
% 3.53/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1335,c_1322]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_7468,plain,
% 3.53/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_1339,c_4909]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_1336,plain,
% 3.53/0.99      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 3.53/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.53/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_8645,plain,
% 3.53/0.99      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 3.53/0.99      inference(superposition,[status(thm)],[c_7468,c_1336]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(c_13490,plain,
% 3.53/0.99      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = sK6 ),
% 3.53/0.99      inference(demodulation,[status(thm)],[c_13483,c_8645]) ).
% 3.53/0.99  
% 3.53/0.99  cnf(contradiction,plain,
% 3.53/0.99      ( $false ),
% 3.53/0.99      inference(minisat,[status(thm)],[c_13490,c_2056]) ).
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.53/0.99  
% 3.53/0.99  ------                               Statistics
% 3.53/0.99  
% 3.53/0.99  ------ General
% 3.53/0.99  
% 3.53/0.99  abstr_ref_over_cycles:                  0
% 3.53/0.99  abstr_ref_under_cycles:                 0
% 3.53/0.99  gc_basic_clause_elim:                   0
% 3.53/0.99  forced_gc_time:                         0
% 3.53/0.99  parsing_time:                           0.011
% 3.53/0.99  unif_index_cands_time:                  0.
% 3.53/0.99  unif_index_add_time:                    0.
% 3.53/0.99  orderings_time:                         0.
% 3.53/0.99  out_proof_time:                         0.013
% 3.53/0.99  total_time:                             0.383
% 3.53/0.99  num_of_symbols:                         44
% 3.53/0.99  num_of_terms:                           13957
% 3.53/0.99  
% 3.53/0.99  ------ Preprocessing
% 3.53/0.99  
% 3.53/0.99  num_of_splits:                          0
% 3.53/0.99  num_of_split_atoms:                     0
% 3.53/0.99  num_of_reused_defs:                     0
% 3.53/0.99  num_eq_ax_congr_red:                    16
% 3.53/0.99  num_of_sem_filtered_clauses:            1
% 3.53/0.99  num_of_subtypes:                        0
% 3.53/0.99  monotx_restored_types:                  0
% 3.53/0.99  sat_num_of_epr_types:                   0
% 3.53/0.99  sat_num_of_non_cyclic_types:            0
% 3.53/0.99  sat_guarded_non_collapsed_types:        0
% 3.53/0.99  num_pure_diseq_elim:                    0
% 3.53/0.99  simp_replaced_by:                       0
% 3.53/0.99  res_preprocessed:                       108
% 3.53/0.99  prep_upred:                             0
% 3.53/0.99  prep_unflattend:                        46
% 3.53/0.99  smt_new_axioms:                         0
% 3.53/0.99  pred_elim_cands:                        3
% 3.53/0.99  pred_elim:                              0
% 3.53/0.99  pred_elim_cl:                           0
% 3.53/0.99  pred_elim_cycles:                       1
% 3.53/0.99  merged_defs:                            6
% 3.53/0.99  merged_defs_ncl:                        0
% 3.53/0.99  bin_hyper_res:                          6
% 3.53/0.99  prep_cycles:                            3
% 3.53/0.99  pred_elim_time:                         0.006
% 3.53/0.99  splitting_time:                         0.
% 3.53/0.99  sem_filter_time:                        0.
% 3.53/0.99  monotx_time:                            0.
% 3.53/0.99  subtype_inf_time:                       0.
% 3.53/0.99  
% 3.53/0.99  ------ Problem properties
% 3.53/0.99  
% 3.53/0.99  clauses:                                31
% 3.53/0.99  conjectures:                            4
% 3.53/0.99  epr:                                    5
% 3.53/0.99  horn:                                   26
% 3.53/0.99  ground:                                 6
% 3.53/0.99  unary:                                  7
% 3.53/0.99  binary:                                 16
% 3.53/0.99  lits:                                   64
% 3.53/0.99  lits_eq:                                15
% 3.53/0.99  fd_pure:                                0
% 3.53/0.99  fd_pseudo:                              0
% 3.53/0.99  fd_cond:                                1
% 3.53/0.99  fd_pseudo_cond:                         4
% 3.53/0.99  ac_symbols:                             0
% 3.53/0.99  
% 3.53/0.99  ------ Propositional Solver
% 3.53/0.99  
% 3.53/0.99  prop_solver_calls:                      25
% 3.53/0.99  prop_fast_solver_calls:                 816
% 3.53/0.99  smt_solver_calls:                       0
% 3.53/0.99  smt_fast_solver_calls:                  0
% 3.53/0.99  prop_num_of_clauses:                    5134
% 3.53/0.99  prop_preprocess_simplified:             12841
% 3.53/0.99  prop_fo_subsumed:                       16
% 3.53/0.99  prop_solver_time:                       0.
% 3.53/0.99  smt_solver_time:                        0.
% 3.53/0.99  smt_fast_solver_time:                   0.
% 3.53/0.99  prop_fast_solver_time:                  0.
% 3.53/0.99  prop_unsat_core_time:                   0.
% 3.53/0.99  
% 3.53/0.99  ------ QBF
% 3.53/0.99  
% 3.53/0.99  qbf_q_res:                              0
% 3.53/0.99  qbf_num_tautologies:                    0
% 3.53/0.99  qbf_prep_cycles:                        0
% 3.53/0.99  
% 3.53/0.99  ------ BMC1
% 3.53/0.99  
% 3.53/0.99  bmc1_current_bound:                     -1
% 3.53/0.99  bmc1_last_solved_bound:                 -1
% 3.53/0.99  bmc1_unsat_core_size:                   -1
% 3.53/0.99  bmc1_unsat_core_parents_size:           -1
% 3.53/0.99  bmc1_merge_next_fun:                    0
% 3.53/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.53/0.99  
% 3.53/0.99  ------ Instantiation
% 3.53/0.99  
% 3.53/0.99  inst_num_of_clauses:                    1363
% 3.53/0.99  inst_num_in_passive:                    937
% 3.53/0.99  inst_num_in_active:                     404
% 3.53/0.99  inst_num_in_unprocessed:                24
% 3.53/0.99  inst_num_of_loops:                      530
% 3.53/0.99  inst_num_of_learning_restarts:          0
% 3.53/0.99  inst_num_moves_active_passive:          123
% 3.53/0.99  inst_lit_activity:                      0
% 3.53/0.99  inst_lit_activity_moves:                0
% 3.53/0.99  inst_num_tautologies:                   0
% 3.53/0.99  inst_num_prop_implied:                  0
% 3.53/0.99  inst_num_existing_simplified:           0
% 3.53/0.99  inst_num_eq_res_simplified:             0
% 3.53/0.99  inst_num_child_elim:                    0
% 3.53/0.99  inst_num_of_dismatching_blockings:      1126
% 3.53/0.99  inst_num_of_non_proper_insts:           1228
% 3.53/0.99  inst_num_of_duplicates:                 0
% 3.53/0.99  inst_inst_num_from_inst_to_res:         0
% 3.53/0.99  inst_dismatching_checking_time:         0.
% 3.53/0.99  
% 3.53/0.99  ------ Resolution
% 3.53/0.99  
% 3.53/0.99  res_num_of_clauses:                     0
% 3.53/0.99  res_num_in_passive:                     0
% 3.53/0.99  res_num_in_active:                      0
% 3.53/0.99  res_num_of_loops:                       111
% 3.53/0.99  res_forward_subset_subsumed:            101
% 3.53/0.99  res_backward_subset_subsumed:           8
% 3.53/0.99  res_forward_subsumed:                   0
% 3.53/0.99  res_backward_subsumed:                  0
% 3.53/0.99  res_forward_subsumption_resolution:     0
% 3.53/0.99  res_backward_subsumption_resolution:    0
% 3.53/0.99  res_clause_to_clause_subsumption:       845
% 3.53/0.99  res_orphan_elimination:                 0
% 3.53/0.99  res_tautology_del:                      93
% 3.53/0.99  res_num_eq_res_simplified:              0
% 3.53/0.99  res_num_sel_changes:                    0
% 3.53/0.99  res_moves_from_active_to_pass:          0
% 3.53/0.99  
% 3.53/0.99  ------ Superposition
% 3.53/0.99  
% 3.53/0.99  sup_time_total:                         0.
% 3.53/0.99  sup_time_generating:                    0.
% 3.53/0.99  sup_time_sim_full:                      0.
% 3.53/0.99  sup_time_sim_immed:                     0.
% 3.53/0.99  
% 3.53/0.99  sup_num_of_clauses:                     145
% 3.53/0.99  sup_num_in_active:                      51
% 3.53/0.99  sup_num_in_passive:                     94
% 3.53/0.99  sup_num_of_loops:                       104
% 3.53/0.99  sup_fw_superposition:                   215
% 3.53/0.99  sup_bw_superposition:                   186
% 3.53/0.99  sup_immediate_simplified:               99
% 3.53/0.99  sup_given_eliminated:                   0
% 3.53/0.99  comparisons_done:                       0
% 3.53/0.99  comparisons_avoided:                    9
% 3.53/0.99  
% 3.53/0.99  ------ Simplifications
% 3.53/0.99  
% 3.53/0.99  
% 3.53/0.99  sim_fw_subset_subsumed:                 41
% 3.53/0.99  sim_bw_subset_subsumed:                 56
% 3.53/0.99  sim_fw_subsumed:                        37
% 3.53/0.99  sim_bw_subsumed:                        4
% 3.53/0.99  sim_fw_subsumption_res:                 1
% 3.53/0.99  sim_bw_subsumption_res:                 0
% 3.53/0.99  sim_tautology_del:                      41
% 3.53/0.99  sim_eq_tautology_del:                   11
% 3.53/0.99  sim_eq_res_simp:                        0
% 3.53/0.99  sim_fw_demodulated:                     8
% 3.53/0.99  sim_bw_demodulated:                     33
% 3.53/0.99  sim_light_normalised:                   22
% 3.53/0.99  sim_joinable_taut:                      0
% 3.53/0.99  sim_joinable_simp:                      0
% 3.53/0.99  sim_ac_normalised:                      0
% 3.53/0.99  sim_smt_subsumption:                    0
% 3.53/0.99  
%------------------------------------------------------------------------------
