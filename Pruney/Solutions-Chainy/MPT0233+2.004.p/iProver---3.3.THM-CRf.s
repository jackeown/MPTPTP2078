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
% DateTime   : Thu Dec  3 11:31:16 EST 2020

% Result     : Theorem 23.68s
% Output     : CNFRefutation 23.68s
% Verified   : 
% Statistics : Number of formulae       :  262 (26533 expanded)
%              Number of clauses        :  163 (5879 expanded)
%              Number of leaves         :   27 (7286 expanded)
%              Depth                    :   31
%              Number of atoms          :  598 (60683 expanded)
%              Number of equality atoms :  486 (48731 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f85,f75])).

fof(f127,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f111])).

fof(f25,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f46,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK2 != sK5
      & sK2 != sK4
      & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( sK2 != sK5
    & sK2 != sK4
    & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f46])).

fof(f88,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f58,f51])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f73,f91])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f79,f94])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f78,f92,f95])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f98,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f91,f91])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f77,f92])).

fof(f97,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f76,f93])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) ),
    inference(definition_unfolding,[],[f74,f91,f93,f75,f92])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f83,f75,f75])).

fof(f89,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    sK2 != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f124,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f121,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f120])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f96,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f56,f51,f51])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f122,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f68])).

fof(f123,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f122])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

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
    inference(nnf_transformation,[],[f31])).

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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f61,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f61,f93])).

fof(f115,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(equality_resolution,[],[f104])).

fof(f116,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0))))) ),
    inference(equality_resolution,[],[f115])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f128,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f84])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3 ) ),
    inference(definition_unfolding,[],[f60,f93])).

fof(f117,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) != X3 ) ),
    inference(equality_resolution,[],[f105])).

fof(f118,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5))))) ),
    inference(equality_resolution,[],[f117])).

cnf(c_29,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1411,plain,
    ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1408,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1429,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7248,plain,
    ( k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) = k2_tarski(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1408,c_1429])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1430,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8700,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1430])).

cnf(c_8721,plain,
    ( r1_tarski(X0,k2_tarski(sK4,sK5)) = iProver_top
    | r1_tarski(X0,k2_tarski(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7248,c_8700])).

cnf(c_8867,plain,
    ( r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_8721])).

cnf(c_9333,plain,
    ( k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) = k2_tarski(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_8867,c_1429])).

cnf(c_25,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2238,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_3,c_25])).

cnf(c_22788,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK2))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_9333,c_2238])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2092,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_9763,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_2092,c_1])).

cnf(c_24,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_15703,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) ),
    inference(superposition,[status(thm)],[c_9763,c_24])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3079,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)))))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) ),
    inference(superposition,[status(thm)],[c_4,c_24])).

cnf(c_2099,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))) = k2_tarski(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_3085,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3079,c_1,c_2099])).

cnf(c_14784,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X1,X0) ),
    inference(superposition,[status(thm)],[c_3085,c_2])).

cnf(c_15713,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_15703,c_1,c_14784])).

cnf(c_15931,plain,
    ( k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK5,sK4)) = k2_tarski(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_15713,c_7248])).

cnf(c_5,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1431,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8865,plain,
    ( r1_tarski(k3_xboole_0(k2_tarski(sK2,sK3),X0),k2_tarski(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1431,c_8721])).

cnf(c_9342,plain,
    ( k3_xboole_0(k3_xboole_0(k2_tarski(sK2,sK3),X0),k2_tarski(sK4,sK5)) = k3_xboole_0(k2_tarski(sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_8865,c_1429])).

cnf(c_24952,plain,
    ( k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK2,sK3),X0)) = k3_xboole_0(k2_tarski(sK2,sK3),X0) ),
    inference(superposition,[status(thm)],[c_9342,c_3])).

cnf(c_32172,plain,
    ( k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK5,sK4)) = k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_15931,c_24952])).

cnf(c_32198,plain,
    ( k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) = k2_tarski(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_32172,c_15931])).

cnf(c_32751,plain,
    ( k3_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) = k2_tarski(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_15713,c_32198])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,k2_tarski(X1,X2))
    | k2_tarski(X1,X2) = X0
    | k2_tarski(X2,X2) = X0
    | k2_tarski(X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1409,plain,
    ( k2_tarski(X0,X1) = X2
    | k2_tarski(X1,X1) = X2
    | k2_tarski(X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1984,plain,
    ( k2_tarski(sK4,sK4) = k2_tarski(sK2,sK3)
    | k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1408,c_1409])).

cnf(c_2252,plain,
    ( k2_tarski(sK4,sK4) = X0
    | k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k2_tarski(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1984,c_1409])).

cnf(c_2939,plain,
    ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK2,sK2) = k2_tarski(sK4,sK4)
    | k2_tarski(sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1411,c_2252])).

cnf(c_5935,plain,
    ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK2,sK2) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2939,c_1984])).

cnf(c_33,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_32,negated_conjecture,
    ( sK2 != sK5 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1458,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK5,X0))
    | sK2 = X0
    | sK2 = sK5 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1485,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK5,sK2))
    | sK2 = sK5
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_21,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1566,plain,
    ( r2_hidden(sK2,k2_tarski(sK5,sK2)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1053,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1645,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1872,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1645])).

cnf(c_2914,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_2012,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK2,X1))
    | X0 = X1
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2573,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK2,sK2))
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_3025,plain,
    ( ~ r2_hidden(sK4,k2_tarski(sK2,sK2))
    | sK4 = sK2 ),
    inference(instantiation,[status(thm)],[c_2573])).

cnf(c_3029,plain,
    ( sK4 = sK2
    | r2_hidden(sK4,k2_tarski(sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3025])).

cnf(c_1416,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5925,plain,
    ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK2,sK2) = k1_xboole_0
    | r2_hidden(sK4,k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2939,c_1416])).

cnf(c_5975,plain,
    ( k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5935,c_33,c_32,c_1485,c_1566,c_2914,c_3029,c_5925])).

cnf(c_5976,plain,
    ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK2,sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5975])).

cnf(c_7381,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK2,sK3))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_7248,c_25])).

cnf(c_7388,plain,
    ( k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK2,sK2) = k1_xboole_0
    | k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK2,sK3))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_5976,c_7381])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1988,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,X0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_1990,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1988,c_4])).

cnf(c_5047,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_1990,c_0])).

cnf(c_5049,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_5047,c_4])).

cnf(c_5050,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_5049,c_1990])).

cnf(c_7389,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK2,sK3) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7388,c_5050])).

cnf(c_2913,plain,
    ( sK5 != sK2
    | sK2 = sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1415,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1414,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6423,plain,
    ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | sK4 = X0
    | r2_hidden(X0,k2_tarski(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1984,c_1414])).

cnf(c_7602,plain,
    ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | sK3 = sK4 ),
    inference(superposition,[status(thm)],[c_1416,c_6423])).

cnf(c_7603,plain,
    ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | sK4 = sK2 ),
    inference(superposition,[status(thm)],[c_1415,c_6423])).

cnf(c_11632,plain,
    ( k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7602,c_33,c_32,c_1485,c_1566,c_2914,c_7603])).

cnf(c_11633,plain,
    ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_11632])).

cnf(c_11642,plain,
    ( k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | sK4 = X0
    | sK5 = X0
    | r2_hidden(X0,k2_tarski(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11633,c_1414])).

cnf(c_50609,plain,
    ( k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0
    | sK4 = sK2
    | sK5 = sK2 ),
    inference(superposition,[status(thm)],[c_1415,c_11642])).

cnf(c_53795,plain,
    ( k2_tarski(sK2,sK3) = k1_xboole_0
    | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7389,c_33,c_32,c_1485,c_1566,c_2913,c_2914,c_50609])).

cnf(c_53796,plain,
    ( k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
    | k2_tarski(sK2,sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_53795])).

cnf(c_53866,plain,
    ( k2_tarski(sK2,sK3) = k1_xboole_0
    | k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK5,X0),k3_xboole_0(k2_tarski(sK5,X0),k2_tarski(sK2,sK3)))) = k2_tarski(sK5,X0) ),
    inference(superposition,[status(thm)],[c_53796,c_1])).

cnf(c_89623,plain,
    ( k2_tarski(sK2,sK3) = k1_xboole_0
    | k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k2_tarski(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_32751,c_53866])).

cnf(c_17550,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_15931,c_2238])).

cnf(c_89656,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) = k2_tarski(sK5,sK4)
    | k2_tarski(sK2,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89623,c_17550])).

cnf(c_2816,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK5,sK5))
    | sK2 = sK5 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2817,plain,
    ( sK2 = sK5
    | r2_hidden(sK2,k2_tarski(sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2816])).

cnf(c_15,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1422,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13544,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1422])).

cnf(c_89647,plain,
    ( k2_tarski(sK2,sK3) = k1_xboole_0
    | r2_hidden(sK2,k2_tarski(sK5,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_53866,c_13544])).

cnf(c_89825,plain,
    ( k2_tarski(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_89656,c_32,c_2817,c_89647])).

cnf(c_2242,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k6_enumset1(X2,X2,X2,X2,X2,X3,X0,X1) ),
    inference(superposition,[status(thm)],[c_25,c_2])).

cnf(c_18263,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_15931,c_2242])).

cnf(c_89898,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) = k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_89825,c_18263])).

cnf(c_89899,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_89825,c_17550])).

cnf(c_9,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_89909,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) = k5_xboole_0(k1_xboole_0,k2_tarski(sK5,sK4)) ),
    inference(demodulation,[status(thm)],[c_89899,c_9])).

cnf(c_89910,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k2_tarski(sK5,sK4)) ),
    inference(demodulation,[status(thm)],[c_89898,c_89909])).

cnf(c_89911,plain,
    ( k5_xboole_0(k1_xboole_0,k2_tarski(sK5,sK4)) = k2_tarski(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_89910,c_9])).

cnf(c_90028,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_89825,c_1])).

cnf(c_90221,plain,
    ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_tarski(sK2,sK2)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_90028,c_89825])).

cnf(c_30,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1410,plain,
    ( r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7247,plain,
    ( k3_xboole_0(k1_xboole_0,k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1410,c_1429])).

cnf(c_90222,plain,
    ( k2_tarski(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_90221,c_9,c_7247])).

cnf(c_1986,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_7379,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)))) = k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_7248,c_1986])).

cnf(c_7598,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)))) = k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_7379,c_0])).

cnf(c_8105,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))) = k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_3,c_7598])).

cnf(c_8113,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) = k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
    inference(light_normalisation,[status(thm)],[c_8105,c_7248])).

cnf(c_8210,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))) = k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_3,c_8113])).

cnf(c_8229,plain,
    ( k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) = k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_8210,c_7248])).

cnf(c_9081,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))))) = k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_8229,c_1986])).

cnf(c_9086,plain,
    ( k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) = k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_9081,c_5049,c_5050])).

cnf(c_36307,plain,
    ( k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK5,sK4)) = k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_15713,c_9086])).

cnf(c_15928,plain,
    ( k3_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_15713,c_8229])).

cnf(c_16579,plain,
    ( k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))))) = k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_15928,c_1986])).

cnf(c_16584,plain,
    ( k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK5,sK4)) = k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_16579,c_5049,c_5050])).

cnf(c_36346,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) = k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_36307,c_16584])).

cnf(c_36352,plain,
    ( k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) = k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_36346,c_9086])).

cnf(c_100681,plain,
    ( k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0),k2_tarski(sK4,sK5)) = k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_36352,c_36352,c_89825])).

cnf(c_100682,plain,
    ( k3_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK4,sK5)) = k2_tarski(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_100681,c_9])).

cnf(c_100716,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK5,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_100682,c_25])).

cnf(c_9771,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)))) = k6_enumset1(X2,X2,X2,X2,X2,X3,X0,X1) ),
    inference(superposition,[status(thm)],[c_2092,c_25])).

cnf(c_100717,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK5,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_100682,c_9771])).

cnf(c_100718,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK5,sK4))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK4,sK4,sK5) ),
    inference(superposition,[status(thm)],[c_100682,c_2238])).

cnf(c_16013,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
    inference(superposition,[status(thm)],[c_15713,c_25])).

cnf(c_20164,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
    inference(superposition,[status(thm)],[c_16013,c_25])).

cnf(c_2240,plain,
    ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_25])).

cnf(c_17863,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X0,X1) = k2_tarski(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2240,c_5050])).

cnf(c_20258,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X1,X0) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_20164,c_17863])).

cnf(c_100736,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK5,sK4))) = k2_tarski(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_100718,c_20258])).

cnf(c_100737,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK5,sK4) = k2_tarski(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_100717,c_100736])).

cnf(c_100738,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK5,sK4))) = k2_tarski(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_100716,c_100737])).

cnf(c_8213,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))))) = k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_8113,c_0])).

cnf(c_8109,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))))) = k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_7598,c_0])).

cnf(c_8429,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) = k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_8213,c_8109,c_8229])).

cnf(c_15921,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k3_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_15713,c_8429])).

cnf(c_36519,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k2_tarski(sK2,sK3) ),
    inference(light_normalisation,[status(thm)],[c_15921,c_15921,c_32751])).

cnf(c_89880,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89825,c_36519])).

cnf(c_89928,plain,
    ( k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK5,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89880,c_9])).

cnf(c_2091,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_32756,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_32198,c_2091])).

cnf(c_32796,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_32756,c_32198])).

cnf(c_7599,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
    inference(superposition,[status(thm)],[c_7379,c_2])).

cnf(c_32797,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_32796,c_7599,c_9086])).

cnf(c_40317,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3)) ),
    inference(light_normalisation,[status(thm)],[c_32797,c_32797,c_36346])).

cnf(c_89873,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0),k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_89825,c_40317])).

cnf(c_89936,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK5,sK4))) = k2_tarski(sK5,sK4) ),
    inference(demodulation,[status(thm)],[c_89873,c_9])).

cnf(c_100739,plain,
    ( k5_xboole_0(k2_tarski(sK4,sK5),k1_xboole_0) = k2_tarski(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_100738,c_89928,c_89936])).

cnf(c_100806,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4,sK5) = k2_tarski(sK5,sK4) ),
    inference(light_normalisation,[status(thm)],[c_22788,c_22788,c_89911,c_90222,c_100739])).

cnf(c_16,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1421,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13316,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1421])).

cnf(c_100812,plain,
    ( r2_hidden(sK2,k2_tarski(sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_100806,c_13316])).

cnf(c_2819,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK5,sK4))
    | sK2 = sK4
    | sK2 = sK5 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2820,plain,
    ( sK2 = sK4
    | sK2 = sK5
    | r2_hidden(sK2,k2_tarski(sK5,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2819])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_100812,c_2820,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.68/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.68/3.49  
% 23.68/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.68/3.49  
% 23.68/3.49  ------  iProver source info
% 23.68/3.49  
% 23.68/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.68/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.68/3.49  git: non_committed_changes: false
% 23.68/3.49  git: last_make_outside_of_git: false
% 23.68/3.49  
% 23.68/3.49  ------ 
% 23.68/3.49  
% 23.68/3.49  ------ Input Options
% 23.68/3.49  
% 23.68/3.49  --out_options                           all
% 23.68/3.49  --tptp_safe_out                         true
% 23.68/3.49  --problem_path                          ""
% 23.68/3.49  --include_path                          ""
% 23.68/3.49  --clausifier                            res/vclausify_rel
% 23.68/3.49  --clausifier_options                    ""
% 23.68/3.49  --stdin                                 false
% 23.68/3.49  --stats_out                             all
% 23.68/3.49  
% 23.68/3.49  ------ General Options
% 23.68/3.49  
% 23.68/3.49  --fof                                   false
% 23.68/3.49  --time_out_real                         305.
% 23.68/3.49  --time_out_virtual                      -1.
% 23.68/3.49  --symbol_type_check                     false
% 23.68/3.49  --clausify_out                          false
% 23.68/3.49  --sig_cnt_out                           false
% 23.68/3.49  --trig_cnt_out                          false
% 23.68/3.49  --trig_cnt_out_tolerance                1.
% 23.68/3.49  --trig_cnt_out_sk_spl                   false
% 23.68/3.49  --abstr_cl_out                          false
% 23.68/3.49  
% 23.68/3.49  ------ Global Options
% 23.68/3.49  
% 23.68/3.49  --schedule                              default
% 23.68/3.49  --add_important_lit                     false
% 23.68/3.49  --prop_solver_per_cl                    1000
% 23.68/3.49  --min_unsat_core                        false
% 23.68/3.49  --soft_assumptions                      false
% 23.68/3.49  --soft_lemma_size                       3
% 23.68/3.49  --prop_impl_unit_size                   0
% 23.68/3.49  --prop_impl_unit                        []
% 23.68/3.49  --share_sel_clauses                     true
% 23.68/3.49  --reset_solvers                         false
% 23.68/3.49  --bc_imp_inh                            [conj_cone]
% 23.68/3.49  --conj_cone_tolerance                   3.
% 23.68/3.49  --extra_neg_conj                        none
% 23.68/3.49  --large_theory_mode                     true
% 23.68/3.49  --prolific_symb_bound                   200
% 23.68/3.49  --lt_threshold                          2000
% 23.68/3.49  --clause_weak_htbl                      true
% 23.68/3.49  --gc_record_bc_elim                     false
% 23.68/3.49  
% 23.68/3.49  ------ Preprocessing Options
% 23.68/3.49  
% 23.68/3.49  --preprocessing_flag                    true
% 23.68/3.49  --time_out_prep_mult                    0.1
% 23.68/3.49  --splitting_mode                        input
% 23.68/3.49  --splitting_grd                         true
% 23.68/3.49  --splitting_cvd                         false
% 23.68/3.49  --splitting_cvd_svl                     false
% 23.68/3.49  --splitting_nvd                         32
% 23.68/3.49  --sub_typing                            true
% 23.68/3.49  --prep_gs_sim                           true
% 23.68/3.49  --prep_unflatten                        true
% 23.68/3.49  --prep_res_sim                          true
% 23.68/3.49  --prep_upred                            true
% 23.68/3.49  --prep_sem_filter                       exhaustive
% 23.68/3.49  --prep_sem_filter_out                   false
% 23.68/3.49  --pred_elim                             true
% 23.68/3.49  --res_sim_input                         true
% 23.68/3.49  --eq_ax_congr_red                       true
% 23.68/3.49  --pure_diseq_elim                       true
% 23.68/3.49  --brand_transform                       false
% 23.68/3.49  --non_eq_to_eq                          false
% 23.68/3.49  --prep_def_merge                        true
% 23.68/3.49  --prep_def_merge_prop_impl              false
% 23.68/3.49  --prep_def_merge_mbd                    true
% 23.68/3.49  --prep_def_merge_tr_red                 false
% 23.68/3.49  --prep_def_merge_tr_cl                  false
% 23.68/3.49  --smt_preprocessing                     true
% 23.68/3.49  --smt_ac_axioms                         fast
% 23.68/3.49  --preprocessed_out                      false
% 23.68/3.49  --preprocessed_stats                    false
% 23.68/3.49  
% 23.68/3.49  ------ Abstraction refinement Options
% 23.68/3.49  
% 23.68/3.49  --abstr_ref                             []
% 23.68/3.49  --abstr_ref_prep                        false
% 23.68/3.49  --abstr_ref_until_sat                   false
% 23.68/3.49  --abstr_ref_sig_restrict                funpre
% 23.68/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.68/3.49  --abstr_ref_under                       []
% 23.68/3.49  
% 23.68/3.49  ------ SAT Options
% 23.68/3.49  
% 23.68/3.49  --sat_mode                              false
% 23.68/3.49  --sat_fm_restart_options                ""
% 23.68/3.49  --sat_gr_def                            false
% 23.68/3.49  --sat_epr_types                         true
% 23.68/3.49  --sat_non_cyclic_types                  false
% 23.68/3.49  --sat_finite_models                     false
% 23.68/3.49  --sat_fm_lemmas                         false
% 23.68/3.49  --sat_fm_prep                           false
% 23.68/3.49  --sat_fm_uc_incr                        true
% 23.68/3.49  --sat_out_model                         small
% 23.68/3.49  --sat_out_clauses                       false
% 23.68/3.49  
% 23.68/3.49  ------ QBF Options
% 23.68/3.49  
% 23.68/3.49  --qbf_mode                              false
% 23.68/3.49  --qbf_elim_univ                         false
% 23.68/3.49  --qbf_dom_inst                          none
% 23.68/3.49  --qbf_dom_pre_inst                      false
% 23.68/3.49  --qbf_sk_in                             false
% 23.68/3.49  --qbf_pred_elim                         true
% 23.68/3.49  --qbf_split                             512
% 23.68/3.49  
% 23.68/3.49  ------ BMC1 Options
% 23.68/3.49  
% 23.68/3.49  --bmc1_incremental                      false
% 23.68/3.49  --bmc1_axioms                           reachable_all
% 23.68/3.49  --bmc1_min_bound                        0
% 23.68/3.49  --bmc1_max_bound                        -1
% 23.68/3.49  --bmc1_max_bound_default                -1
% 23.68/3.49  --bmc1_symbol_reachability              true
% 23.68/3.49  --bmc1_property_lemmas                  false
% 23.68/3.49  --bmc1_k_induction                      false
% 23.68/3.49  --bmc1_non_equiv_states                 false
% 23.68/3.49  --bmc1_deadlock                         false
% 23.68/3.49  --bmc1_ucm                              false
% 23.68/3.49  --bmc1_add_unsat_core                   none
% 23.68/3.49  --bmc1_unsat_core_children              false
% 23.68/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.68/3.49  --bmc1_out_stat                         full
% 23.68/3.49  --bmc1_ground_init                      false
% 23.68/3.49  --bmc1_pre_inst_next_state              false
% 23.68/3.49  --bmc1_pre_inst_state                   false
% 23.68/3.49  --bmc1_pre_inst_reach_state             false
% 23.68/3.49  --bmc1_out_unsat_core                   false
% 23.68/3.49  --bmc1_aig_witness_out                  false
% 23.68/3.49  --bmc1_verbose                          false
% 23.68/3.49  --bmc1_dump_clauses_tptp                false
% 23.68/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.68/3.49  --bmc1_dump_file                        -
% 23.68/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.68/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.68/3.49  --bmc1_ucm_extend_mode                  1
% 23.68/3.49  --bmc1_ucm_init_mode                    2
% 23.68/3.49  --bmc1_ucm_cone_mode                    none
% 23.68/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.68/3.49  --bmc1_ucm_relax_model                  4
% 23.68/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.68/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.68/3.49  --bmc1_ucm_layered_model                none
% 23.68/3.49  --bmc1_ucm_max_lemma_size               10
% 23.68/3.49  
% 23.68/3.49  ------ AIG Options
% 23.68/3.49  
% 23.68/3.49  --aig_mode                              false
% 23.68/3.49  
% 23.68/3.49  ------ Instantiation Options
% 23.68/3.49  
% 23.68/3.49  --instantiation_flag                    true
% 23.68/3.49  --inst_sos_flag                         true
% 23.68/3.49  --inst_sos_phase                        true
% 23.68/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.68/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.68/3.49  --inst_lit_sel_side                     num_symb
% 23.68/3.49  --inst_solver_per_active                1400
% 23.68/3.49  --inst_solver_calls_frac                1.
% 23.68/3.49  --inst_passive_queue_type               priority_queues
% 23.68/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.68/3.49  --inst_passive_queues_freq              [25;2]
% 23.68/3.49  --inst_dismatching                      true
% 23.68/3.49  --inst_eager_unprocessed_to_passive     true
% 23.68/3.49  --inst_prop_sim_given                   true
% 23.68/3.49  --inst_prop_sim_new                     false
% 23.68/3.49  --inst_subs_new                         false
% 23.68/3.49  --inst_eq_res_simp                      false
% 23.68/3.49  --inst_subs_given                       false
% 23.68/3.49  --inst_orphan_elimination               true
% 23.68/3.49  --inst_learning_loop_flag               true
% 23.68/3.49  --inst_learning_start                   3000
% 23.68/3.49  --inst_learning_factor                  2
% 23.68/3.49  --inst_start_prop_sim_after_learn       3
% 23.68/3.49  --inst_sel_renew                        solver
% 23.68/3.49  --inst_lit_activity_flag                true
% 23.68/3.49  --inst_restr_to_given                   false
% 23.68/3.49  --inst_activity_threshold               500
% 23.68/3.49  --inst_out_proof                        true
% 23.68/3.49  
% 23.68/3.49  ------ Resolution Options
% 23.68/3.49  
% 23.68/3.49  --resolution_flag                       true
% 23.68/3.49  --res_lit_sel                           adaptive
% 23.68/3.49  --res_lit_sel_side                      none
% 23.68/3.49  --res_ordering                          kbo
% 23.68/3.49  --res_to_prop_solver                    active
% 23.68/3.49  --res_prop_simpl_new                    false
% 23.68/3.49  --res_prop_simpl_given                  true
% 23.68/3.49  --res_passive_queue_type                priority_queues
% 23.68/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.68/3.49  --res_passive_queues_freq               [15;5]
% 23.68/3.49  --res_forward_subs                      full
% 23.68/3.49  --res_backward_subs                     full
% 23.68/3.49  --res_forward_subs_resolution           true
% 23.68/3.49  --res_backward_subs_resolution          true
% 23.68/3.49  --res_orphan_elimination                true
% 23.68/3.49  --res_time_limit                        2.
% 23.68/3.49  --res_out_proof                         true
% 23.68/3.49  
% 23.68/3.49  ------ Superposition Options
% 23.68/3.49  
% 23.68/3.49  --superposition_flag                    true
% 23.68/3.49  --sup_passive_queue_type                priority_queues
% 23.68/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.68/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.68/3.49  --demod_completeness_check              fast
% 23.68/3.49  --demod_use_ground                      true
% 23.68/3.49  --sup_to_prop_solver                    passive
% 23.68/3.49  --sup_prop_simpl_new                    true
% 23.68/3.49  --sup_prop_simpl_given                  true
% 23.68/3.49  --sup_fun_splitting                     true
% 23.68/3.49  --sup_smt_interval                      50000
% 23.68/3.49  
% 23.68/3.49  ------ Superposition Simplification Setup
% 23.68/3.49  
% 23.68/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.68/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.68/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.68/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.68/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.68/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.68/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.68/3.49  --sup_immed_triv                        [TrivRules]
% 23.68/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.68/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.68/3.49  --sup_immed_bw_main                     []
% 23.68/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.68/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.68/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.68/3.49  --sup_input_bw                          []
% 23.68/3.49  
% 23.68/3.49  ------ Combination Options
% 23.68/3.49  
% 23.68/3.49  --comb_res_mult                         3
% 23.68/3.49  --comb_sup_mult                         2
% 23.68/3.49  --comb_inst_mult                        10
% 23.68/3.49  
% 23.68/3.49  ------ Debug Options
% 23.68/3.49  
% 23.68/3.49  --dbg_backtrace                         false
% 23.68/3.49  --dbg_dump_prop_clauses                 false
% 23.68/3.49  --dbg_dump_prop_clauses_file            -
% 23.68/3.49  --dbg_out_stat                          false
% 23.68/3.49  ------ Parsing...
% 23.68/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.68/3.49  
% 23.68/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.68/3.49  
% 23.68/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.68/3.49  
% 23.68/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.68/3.49  ------ Proving...
% 23.68/3.49  ------ Problem Properties 
% 23.68/3.49  
% 23.68/3.49  
% 23.68/3.49  clauses                                 35
% 23.68/3.49  conjectures                             3
% 23.68/3.49  EPR                                     3
% 23.68/3.49  Horn                                    30
% 23.68/3.49  unary                                   22
% 23.68/3.49  binary                                  3
% 23.68/3.49  lits                                    64
% 23.68/3.49  lits eq                                 39
% 23.68/3.49  fd_pure                                 0
% 23.68/3.49  fd_pseudo                               0
% 23.68/3.49  fd_cond                                 1
% 23.68/3.49  fd_pseudo_cond                          8
% 23.68/3.49  AC symbols                              0
% 23.68/3.49  
% 23.68/3.49  ------ Schedule dynamic 5 is on 
% 23.68/3.49  
% 23.68/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.68/3.49  
% 23.68/3.49  
% 23.68/3.49  ------ 
% 23.68/3.49  Current options:
% 23.68/3.49  ------ 
% 23.68/3.49  
% 23.68/3.49  ------ Input Options
% 23.68/3.49  
% 23.68/3.49  --out_options                           all
% 23.68/3.49  --tptp_safe_out                         true
% 23.68/3.49  --problem_path                          ""
% 23.68/3.49  --include_path                          ""
% 23.68/3.49  --clausifier                            res/vclausify_rel
% 23.68/3.49  --clausifier_options                    ""
% 23.68/3.49  --stdin                                 false
% 23.68/3.49  --stats_out                             all
% 23.68/3.49  
% 23.68/3.49  ------ General Options
% 23.68/3.49  
% 23.68/3.49  --fof                                   false
% 23.68/3.49  --time_out_real                         305.
% 23.68/3.49  --time_out_virtual                      -1.
% 23.68/3.49  --symbol_type_check                     false
% 23.68/3.49  --clausify_out                          false
% 23.68/3.49  --sig_cnt_out                           false
% 23.68/3.49  --trig_cnt_out                          false
% 23.68/3.49  --trig_cnt_out_tolerance                1.
% 23.68/3.49  --trig_cnt_out_sk_spl                   false
% 23.68/3.49  --abstr_cl_out                          false
% 23.68/3.49  
% 23.68/3.49  ------ Global Options
% 23.68/3.49  
% 23.68/3.49  --schedule                              default
% 23.68/3.49  --add_important_lit                     false
% 23.68/3.49  --prop_solver_per_cl                    1000
% 23.68/3.49  --min_unsat_core                        false
% 23.68/3.49  --soft_assumptions                      false
% 23.68/3.49  --soft_lemma_size                       3
% 23.68/3.49  --prop_impl_unit_size                   0
% 23.68/3.49  --prop_impl_unit                        []
% 23.68/3.49  --share_sel_clauses                     true
% 23.68/3.49  --reset_solvers                         false
% 23.68/3.49  --bc_imp_inh                            [conj_cone]
% 23.68/3.49  --conj_cone_tolerance                   3.
% 23.68/3.49  --extra_neg_conj                        none
% 23.68/3.49  --large_theory_mode                     true
% 23.68/3.49  --prolific_symb_bound                   200
% 23.68/3.49  --lt_threshold                          2000
% 23.68/3.49  --clause_weak_htbl                      true
% 23.68/3.49  --gc_record_bc_elim                     false
% 23.68/3.49  
% 23.68/3.49  ------ Preprocessing Options
% 23.68/3.49  
% 23.68/3.49  --preprocessing_flag                    true
% 23.68/3.49  --time_out_prep_mult                    0.1
% 23.68/3.49  --splitting_mode                        input
% 23.68/3.49  --splitting_grd                         true
% 23.68/3.49  --splitting_cvd                         false
% 23.68/3.49  --splitting_cvd_svl                     false
% 23.68/3.49  --splitting_nvd                         32
% 23.68/3.49  --sub_typing                            true
% 23.68/3.49  --prep_gs_sim                           true
% 23.68/3.49  --prep_unflatten                        true
% 23.68/3.49  --prep_res_sim                          true
% 23.68/3.49  --prep_upred                            true
% 23.68/3.49  --prep_sem_filter                       exhaustive
% 23.68/3.49  --prep_sem_filter_out                   false
% 23.68/3.49  --pred_elim                             true
% 23.68/3.49  --res_sim_input                         true
% 23.68/3.49  --eq_ax_congr_red                       true
% 23.68/3.49  --pure_diseq_elim                       true
% 23.68/3.49  --brand_transform                       false
% 23.68/3.49  --non_eq_to_eq                          false
% 23.68/3.49  --prep_def_merge                        true
% 23.68/3.49  --prep_def_merge_prop_impl              false
% 23.68/3.49  --prep_def_merge_mbd                    true
% 23.68/3.49  --prep_def_merge_tr_red                 false
% 23.68/3.49  --prep_def_merge_tr_cl                  false
% 23.68/3.49  --smt_preprocessing                     true
% 23.68/3.49  --smt_ac_axioms                         fast
% 23.68/3.49  --preprocessed_out                      false
% 23.68/3.49  --preprocessed_stats                    false
% 23.68/3.49  
% 23.68/3.49  ------ Abstraction refinement Options
% 23.68/3.49  
% 23.68/3.49  --abstr_ref                             []
% 23.68/3.49  --abstr_ref_prep                        false
% 23.68/3.49  --abstr_ref_until_sat                   false
% 23.68/3.49  --abstr_ref_sig_restrict                funpre
% 23.68/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.68/3.49  --abstr_ref_under                       []
% 23.68/3.49  
% 23.68/3.49  ------ SAT Options
% 23.68/3.49  
% 23.68/3.49  --sat_mode                              false
% 23.68/3.49  --sat_fm_restart_options                ""
% 23.68/3.49  --sat_gr_def                            false
% 23.68/3.49  --sat_epr_types                         true
% 23.68/3.49  --sat_non_cyclic_types                  false
% 23.68/3.49  --sat_finite_models                     false
% 23.68/3.49  --sat_fm_lemmas                         false
% 23.68/3.49  --sat_fm_prep                           false
% 23.68/3.49  --sat_fm_uc_incr                        true
% 23.68/3.49  --sat_out_model                         small
% 23.68/3.49  --sat_out_clauses                       false
% 23.68/3.49  
% 23.68/3.49  ------ QBF Options
% 23.68/3.49  
% 23.68/3.49  --qbf_mode                              false
% 23.68/3.49  --qbf_elim_univ                         false
% 23.68/3.49  --qbf_dom_inst                          none
% 23.68/3.49  --qbf_dom_pre_inst                      false
% 23.68/3.49  --qbf_sk_in                             false
% 23.68/3.49  --qbf_pred_elim                         true
% 23.68/3.49  --qbf_split                             512
% 23.68/3.49  
% 23.68/3.49  ------ BMC1 Options
% 23.68/3.49  
% 23.68/3.49  --bmc1_incremental                      false
% 23.68/3.49  --bmc1_axioms                           reachable_all
% 23.68/3.49  --bmc1_min_bound                        0
% 23.68/3.49  --bmc1_max_bound                        -1
% 23.68/3.49  --bmc1_max_bound_default                -1
% 23.68/3.49  --bmc1_symbol_reachability              true
% 23.68/3.49  --bmc1_property_lemmas                  false
% 23.68/3.49  --bmc1_k_induction                      false
% 23.68/3.49  --bmc1_non_equiv_states                 false
% 23.68/3.49  --bmc1_deadlock                         false
% 23.68/3.49  --bmc1_ucm                              false
% 23.68/3.49  --bmc1_add_unsat_core                   none
% 23.68/3.49  --bmc1_unsat_core_children              false
% 23.68/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.68/3.49  --bmc1_out_stat                         full
% 23.68/3.49  --bmc1_ground_init                      false
% 23.68/3.49  --bmc1_pre_inst_next_state              false
% 23.68/3.49  --bmc1_pre_inst_state                   false
% 23.68/3.49  --bmc1_pre_inst_reach_state             false
% 23.68/3.49  --bmc1_out_unsat_core                   false
% 23.68/3.49  --bmc1_aig_witness_out                  false
% 23.68/3.49  --bmc1_verbose                          false
% 23.68/3.49  --bmc1_dump_clauses_tptp                false
% 23.68/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.68/3.49  --bmc1_dump_file                        -
% 23.68/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.68/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.68/3.49  --bmc1_ucm_extend_mode                  1
% 23.68/3.49  --bmc1_ucm_init_mode                    2
% 23.68/3.49  --bmc1_ucm_cone_mode                    none
% 23.68/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.68/3.49  --bmc1_ucm_relax_model                  4
% 23.68/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.68/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.68/3.49  --bmc1_ucm_layered_model                none
% 23.68/3.49  --bmc1_ucm_max_lemma_size               10
% 23.68/3.49  
% 23.68/3.49  ------ AIG Options
% 23.68/3.49  
% 23.68/3.49  --aig_mode                              false
% 23.68/3.49  
% 23.68/3.49  ------ Instantiation Options
% 23.68/3.49  
% 23.68/3.49  --instantiation_flag                    true
% 23.68/3.49  --inst_sos_flag                         true
% 23.68/3.49  --inst_sos_phase                        true
% 23.68/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.68/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.68/3.49  --inst_lit_sel_side                     none
% 23.68/3.49  --inst_solver_per_active                1400
% 23.68/3.49  --inst_solver_calls_frac                1.
% 23.68/3.49  --inst_passive_queue_type               priority_queues
% 23.68/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.68/3.49  --inst_passive_queues_freq              [25;2]
% 23.68/3.49  --inst_dismatching                      true
% 23.68/3.49  --inst_eager_unprocessed_to_passive     true
% 23.68/3.49  --inst_prop_sim_given                   true
% 23.68/3.49  --inst_prop_sim_new                     false
% 23.68/3.49  --inst_subs_new                         false
% 23.68/3.49  --inst_eq_res_simp                      false
% 23.68/3.49  --inst_subs_given                       false
% 23.68/3.49  --inst_orphan_elimination               true
% 23.68/3.49  --inst_learning_loop_flag               true
% 23.68/3.49  --inst_learning_start                   3000
% 23.68/3.49  --inst_learning_factor                  2
% 23.68/3.49  --inst_start_prop_sim_after_learn       3
% 23.68/3.49  --inst_sel_renew                        solver
% 23.68/3.49  --inst_lit_activity_flag                true
% 23.68/3.49  --inst_restr_to_given                   false
% 23.68/3.49  --inst_activity_threshold               500
% 23.68/3.49  --inst_out_proof                        true
% 23.68/3.49  
% 23.68/3.49  ------ Resolution Options
% 23.68/3.49  
% 23.68/3.49  --resolution_flag                       false
% 23.68/3.49  --res_lit_sel                           adaptive
% 23.68/3.49  --res_lit_sel_side                      none
% 23.68/3.49  --res_ordering                          kbo
% 23.68/3.49  --res_to_prop_solver                    active
% 23.68/3.49  --res_prop_simpl_new                    false
% 23.68/3.49  --res_prop_simpl_given                  true
% 23.68/3.49  --res_passive_queue_type                priority_queues
% 23.68/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.68/3.49  --res_passive_queues_freq               [15;5]
% 23.68/3.49  --res_forward_subs                      full
% 23.68/3.49  --res_backward_subs                     full
% 23.68/3.49  --res_forward_subs_resolution           true
% 23.68/3.49  --res_backward_subs_resolution          true
% 23.68/3.49  --res_orphan_elimination                true
% 23.68/3.49  --res_time_limit                        2.
% 23.68/3.49  --res_out_proof                         true
% 23.68/3.49  
% 23.68/3.49  ------ Superposition Options
% 23.68/3.49  
% 23.68/3.49  --superposition_flag                    true
% 23.68/3.49  --sup_passive_queue_type                priority_queues
% 23.68/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.68/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.68/3.49  --demod_completeness_check              fast
% 23.68/3.49  --demod_use_ground                      true
% 23.68/3.49  --sup_to_prop_solver                    passive
% 23.68/3.49  --sup_prop_simpl_new                    true
% 23.68/3.49  --sup_prop_simpl_given                  true
% 23.68/3.49  --sup_fun_splitting                     true
% 23.68/3.49  --sup_smt_interval                      50000
% 23.68/3.49  
% 23.68/3.49  ------ Superposition Simplification Setup
% 23.68/3.49  
% 23.68/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.68/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.68/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.68/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.68/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.68/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.68/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.68/3.49  --sup_immed_triv                        [TrivRules]
% 23.68/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.68/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.68/3.49  --sup_immed_bw_main                     []
% 23.68/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.68/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.68/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.68/3.49  --sup_input_bw                          []
% 23.68/3.49  
% 23.68/3.49  ------ Combination Options
% 23.68/3.49  
% 23.68/3.49  --comb_res_mult                         3
% 23.68/3.49  --comb_sup_mult                         2
% 23.68/3.49  --comb_inst_mult                        10
% 23.68/3.49  
% 23.68/3.49  ------ Debug Options
% 23.68/3.49  
% 23.68/3.49  --dbg_backtrace                         false
% 23.68/3.49  --dbg_dump_prop_clauses                 false
% 23.68/3.49  --dbg_dump_prop_clauses_file            -
% 23.68/3.49  --dbg_out_stat                          false
% 23.68/3.49  
% 23.68/3.49  
% 23.68/3.49  
% 23.68/3.49  
% 23.68/3.49  ------ Proving...
% 23.68/3.49  
% 23.68/3.49  
% 23.68/3.49  % SZS status Theorem for theBenchmark.p
% 23.68/3.49  
% 23.68/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.68/3.49  
% 23.68/3.49  fof(f24,axiom,(
% 23.68/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f32,plain,(
% 23.68/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 23.68/3.49    inference(ennf_transformation,[],[f24])).
% 23.68/3.49  
% 23.68/3.49  fof(f44,plain,(
% 23.68/3.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 23.68/3.49    inference(nnf_transformation,[],[f32])).
% 23.68/3.49  
% 23.68/3.49  fof(f45,plain,(
% 23.68/3.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 23.68/3.49    inference(flattening,[],[f44])).
% 23.68/3.49  
% 23.68/3.49  fof(f85,plain,(
% 23.68/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 23.68/3.49    inference(cnf_transformation,[],[f45])).
% 23.68/3.49  
% 23.68/3.49  fof(f16,axiom,(
% 23.68/3.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f75,plain,(
% 23.68/3.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f16])).
% 23.68/3.49  
% 23.68/3.49  fof(f111,plain,(
% 23.68/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) != X0) )),
% 23.68/3.49    inference(definition_unfolding,[],[f85,f75])).
% 23.68/3.49  
% 23.68/3.49  fof(f127,plain,(
% 23.68/3.49    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))) )),
% 23.68/3.49    inference(equality_resolution,[],[f111])).
% 23.68/3.49  
% 23.68/3.49  fof(f25,conjecture,(
% 23.68/3.49    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f26,negated_conjecture,(
% 23.68/3.49    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 23.68/3.49    inference(negated_conjecture,[],[f25])).
% 23.68/3.49  
% 23.68/3.49  fof(f33,plain,(
% 23.68/3.49    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 23.68/3.49    inference(ennf_transformation,[],[f26])).
% 23.68/3.49  
% 23.68/3.49  fof(f46,plain,(
% 23.68/3.49    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))),
% 23.68/3.49    introduced(choice_axiom,[])).
% 23.68/3.49  
% 23.68/3.49  fof(f47,plain,(
% 23.68/3.49    sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 23.68/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f33,f46])).
% 23.68/3.49  
% 23.68/3.49  fof(f88,plain,(
% 23.68/3.49    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 23.68/3.49    inference(cnf_transformation,[],[f47])).
% 23.68/3.49  
% 23.68/3.49  fof(f7,axiom,(
% 23.68/3.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f29,plain,(
% 23.68/3.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.68/3.49    inference(ennf_transformation,[],[f7])).
% 23.68/3.49  
% 23.68/3.49  fof(f54,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f29])).
% 23.68/3.49  
% 23.68/3.49  fof(f2,axiom,(
% 23.68/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f49,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f2])).
% 23.68/3.49  
% 23.68/3.49  fof(f6,axiom,(
% 23.68/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f28,plain,(
% 23.68/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 23.68/3.49    inference(ennf_transformation,[],[f6])).
% 23.68/3.49  
% 23.68/3.49  fof(f53,plain,(
% 23.68/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 23.68/3.49    inference(cnf_transformation,[],[f28])).
% 23.68/3.49  
% 23.68/3.49  fof(f19,axiom,(
% 23.68/3.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f78,plain,(
% 23.68/3.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f19])).
% 23.68/3.49  
% 23.68/3.49  fof(f14,axiom,(
% 23.68/3.49    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f73,plain,(
% 23.68/3.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f14])).
% 23.68/3.49  
% 23.68/3.49  fof(f11,axiom,(
% 23.68/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f58,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 23.68/3.49    inference(cnf_transformation,[],[f11])).
% 23.68/3.49  
% 23.68/3.49  fof(f4,axiom,(
% 23.68/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f51,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.68/3.49    inference(cnf_transformation,[],[f4])).
% 23.68/3.49  
% 23.68/3.49  fof(f91,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 23.68/3.49    inference(definition_unfolding,[],[f58,f51])).
% 23.68/3.49  
% 23.68/3.49  fof(f92,plain,(
% 23.68/3.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 23.68/3.49    inference(definition_unfolding,[],[f73,f91])).
% 23.68/3.49  
% 23.68/3.49  fof(f20,axiom,(
% 23.68/3.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f79,plain,(
% 23.68/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f20])).
% 23.68/3.49  
% 23.68/3.49  fof(f21,axiom,(
% 23.68/3.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f80,plain,(
% 23.68/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f21])).
% 23.68/3.49  
% 23.68/3.49  fof(f22,axiom,(
% 23.68/3.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f81,plain,(
% 23.68/3.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f22])).
% 23.68/3.49  
% 23.68/3.49  fof(f94,plain,(
% 23.68/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 23.68/3.49    inference(definition_unfolding,[],[f80,f81])).
% 23.68/3.49  
% 23.68/3.49  fof(f95,plain,(
% 23.68/3.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 23.68/3.49    inference(definition_unfolding,[],[f79,f94])).
% 23.68/3.49  
% 23.68/3.49  fof(f108,plain,(
% 23.68/3.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 23.68/3.49    inference(definition_unfolding,[],[f78,f92,f95])).
% 23.68/3.49  
% 23.68/3.49  fof(f1,axiom,(
% 23.68/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f48,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f1])).
% 23.68/3.49  
% 23.68/3.49  fof(f98,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 23.68/3.49    inference(definition_unfolding,[],[f48,f91,f91])).
% 23.68/3.49  
% 23.68/3.49  fof(f17,axiom,(
% 23.68/3.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f76,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f17])).
% 23.68/3.49  
% 23.68/3.49  fof(f18,axiom,(
% 23.68/3.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f77,plain,(
% 23.68/3.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f18])).
% 23.68/3.49  
% 23.68/3.49  fof(f93,plain,(
% 23.68/3.49    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 23.68/3.49    inference(definition_unfolding,[],[f77,f92])).
% 23.68/3.49  
% 23.68/3.49  fof(f97,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1)) )),
% 23.68/3.49    inference(definition_unfolding,[],[f76,f93])).
% 23.68/3.49  
% 23.68/3.49  fof(f15,axiom,(
% 23.68/3.49    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f74,plain,(
% 23.68/3.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f15])).
% 23.68/3.49  
% 23.68/3.49  fof(f107,plain,(
% 23.68/3.49    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))))))) )),
% 23.68/3.49    inference(definition_unfolding,[],[f74,f91,f93,f75,f92])).
% 23.68/3.49  
% 23.68/3.49  fof(f3,axiom,(
% 23.68/3.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f27,plain,(
% 23.68/3.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 23.68/3.49    inference(rectify,[],[f3])).
% 23.68/3.49  
% 23.68/3.49  fof(f50,plain,(
% 23.68/3.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 23.68/3.49    inference(cnf_transformation,[],[f27])).
% 23.68/3.49  
% 23.68/3.49  fof(f5,axiom,(
% 23.68/3.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f52,plain,(
% 23.68/3.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.68/3.49    inference(cnf_transformation,[],[f5])).
% 23.68/3.49  
% 23.68/3.49  fof(f83,plain,(
% 23.68/3.49    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 23.68/3.49    inference(cnf_transformation,[],[f45])).
% 23.68/3.49  
% 23.68/3.49  fof(f112,plain,(
% 23.68/3.49    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 23.68/3.49    inference(definition_unfolding,[],[f83,f75,f75])).
% 23.68/3.49  
% 23.68/3.49  fof(f89,plain,(
% 23.68/3.49    sK2 != sK4),
% 23.68/3.49    inference(cnf_transformation,[],[f47])).
% 23.68/3.49  
% 23.68/3.49  fof(f90,plain,(
% 23.68/3.49    sK2 != sK5),
% 23.68/3.49    inference(cnf_transformation,[],[f47])).
% 23.68/3.49  
% 23.68/3.49  fof(f13,axiom,(
% 23.68/3.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f39,plain,(
% 23.68/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.68/3.49    inference(nnf_transformation,[],[f13])).
% 23.68/3.49  
% 23.68/3.49  fof(f40,plain,(
% 23.68/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 23.68/3.49    inference(flattening,[],[f39])).
% 23.68/3.49  
% 23.68/3.49  fof(f41,plain,(
% 23.68/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.68/3.49    inference(rectify,[],[f40])).
% 23.68/3.49  
% 23.68/3.49  fof(f42,plain,(
% 23.68/3.49    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 23.68/3.49    introduced(choice_axiom,[])).
% 23.68/3.49  
% 23.68/3.49  fof(f43,plain,(
% 23.68/3.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 23.68/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 23.68/3.49  
% 23.68/3.49  fof(f67,plain,(
% 23.68/3.49    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 23.68/3.49    inference(cnf_transformation,[],[f43])).
% 23.68/3.49  
% 23.68/3.49  fof(f124,plain,(
% 23.68/3.49    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_tarski(X0,X1))) )),
% 23.68/3.49    inference(equality_resolution,[],[f67])).
% 23.68/3.49  
% 23.68/3.49  fof(f69,plain,(
% 23.68/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 23.68/3.49    inference(cnf_transformation,[],[f43])).
% 23.68/3.49  
% 23.68/3.49  fof(f120,plain,(
% 23.68/3.49    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 23.68/3.49    inference(equality_resolution,[],[f69])).
% 23.68/3.49  
% 23.68/3.49  fof(f121,plain,(
% 23.68/3.49    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 23.68/3.49    inference(equality_resolution,[],[f120])).
% 23.68/3.49  
% 23.68/3.49  fof(f9,axiom,(
% 23.68/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f56,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.68/3.49    inference(cnf_transformation,[],[f9])).
% 23.68/3.49  
% 23.68/3.49  fof(f96,plain,(
% 23.68/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 23.68/3.49    inference(definition_unfolding,[],[f56,f51,f51])).
% 23.68/3.49  
% 23.68/3.49  fof(f68,plain,(
% 23.68/3.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 23.68/3.49    inference(cnf_transformation,[],[f43])).
% 23.68/3.49  
% 23.68/3.49  fof(f122,plain,(
% 23.68/3.49    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 23.68/3.49    inference(equality_resolution,[],[f68])).
% 23.68/3.49  
% 23.68/3.49  fof(f123,plain,(
% 23.68/3.49    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 23.68/3.49    inference(equality_resolution,[],[f122])).
% 23.68/3.49  
% 23.68/3.49  fof(f12,axiom,(
% 23.68/3.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f31,plain,(
% 23.68/3.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 23.68/3.49    inference(ennf_transformation,[],[f12])).
% 23.68/3.49  
% 23.68/3.49  fof(f34,plain,(
% 23.68/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.68/3.49    inference(nnf_transformation,[],[f31])).
% 23.68/3.49  
% 23.68/3.49  fof(f35,plain,(
% 23.68/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.68/3.49    inference(flattening,[],[f34])).
% 23.68/3.49  
% 23.68/3.49  fof(f36,plain,(
% 23.68/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.68/3.49    inference(rectify,[],[f35])).
% 23.68/3.49  
% 23.68/3.49  fof(f37,plain,(
% 23.68/3.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 23.68/3.49    introduced(choice_axiom,[])).
% 23.68/3.49  
% 23.68/3.49  fof(f38,plain,(
% 23.68/3.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.68/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 23.68/3.49  
% 23.68/3.49  fof(f61,plain,(
% 23.68/3.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 23.68/3.49    inference(cnf_transformation,[],[f38])).
% 23.68/3.49  
% 23.68/3.49  fof(f104,plain,(
% 23.68/3.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 23.68/3.49    inference(definition_unfolding,[],[f61,f93])).
% 23.68/3.49  
% 23.68/3.49  fof(f115,plain,(
% 23.68/3.49    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) != X3) )),
% 23.68/3.49    inference(equality_resolution,[],[f104])).
% 23.68/3.49  
% 23.68/3.49  fof(f116,plain,(
% 23.68/3.49    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X5,X2),k3_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))))) )),
% 23.68/3.49    inference(equality_resolution,[],[f115])).
% 23.68/3.49  
% 23.68/3.49  fof(f10,axiom,(
% 23.68/3.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 23.68/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.68/3.49  
% 23.68/3.49  fof(f57,plain,(
% 23.68/3.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.68/3.49    inference(cnf_transformation,[],[f10])).
% 23.68/3.49  
% 23.68/3.49  fof(f84,plain,(
% 23.68/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 23.68/3.49    inference(cnf_transformation,[],[f45])).
% 23.68/3.49  
% 23.68/3.49  fof(f128,plain,(
% 23.68/3.49    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 23.68/3.49    inference(equality_resolution,[],[f84])).
% 23.68/3.49  
% 23.68/3.49  fof(f60,plain,(
% 23.68/3.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 23.68/3.49    inference(cnf_transformation,[],[f38])).
% 23.68/3.49  
% 23.68/3.49  fof(f105,plain,(
% 23.68/3.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) != X3) )),
% 23.68/3.49    inference(definition_unfolding,[],[f60,f93])).
% 23.68/3.49  
% 23.68/3.49  fof(f117,plain,(
% 23.68/3.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) != X3) )),
% 23.68/3.49    inference(equality_resolution,[],[f105])).
% 23.68/3.49  
% 23.68/3.49  fof(f118,plain,(
% 23.68/3.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))))) )),
% 23.68/3.49    inference(equality_resolution,[],[f117])).
% 23.68/3.49  
% 23.68/3.49  cnf(c_29,plain,
% 23.68/3.49      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
% 23.68/3.49      inference(cnf_transformation,[],[f127]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1411,plain,
% 23.68/3.49      ( r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) = iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_34,negated_conjecture,
% 23.68/3.49      ( r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
% 23.68/3.49      inference(cnf_transformation,[],[f88]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1408,plain,
% 23.68/3.49      ( r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) = iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7,plain,
% 23.68/3.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 23.68/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1429,plain,
% 23.68/3.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7248,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) = k2_tarski(sK2,sK3) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1408,c_1429]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_3,plain,
% 23.68/3.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.68/3.49      inference(cnf_transformation,[],[f49]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_6,plain,
% 23.68/3.49      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 23.68/3.49      inference(cnf_transformation,[],[f53]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1430,plain,
% 23.68/3.49      ( r1_tarski(X0,X1) = iProver_top
% 23.68/3.49      | r1_tarski(X0,k3_xboole_0(X1,X2)) != iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8700,plain,
% 23.68/3.49      ( r1_tarski(X0,X1) = iProver_top
% 23.68/3.49      | r1_tarski(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_3,c_1430]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8721,plain,
% 23.68/3.49      ( r1_tarski(X0,k2_tarski(sK4,sK5)) = iProver_top
% 23.68/3.49      | r1_tarski(X0,k2_tarski(sK2,sK3)) != iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_7248,c_8700]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8867,plain,
% 23.68/3.49      ( r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) = iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1411,c_8721]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_9333,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK4,sK5)) = k2_tarski(sK2,sK2) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_8867,c_1429]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_25,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
% 23.68/3.49      inference(cnf_transformation,[],[f108]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2238,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_3,c_25]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_22788,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK2))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4,sK5) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_9333,c_2238]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 23.68/3.49      inference(cnf_transformation,[],[f98]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2092,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 23.68/3.49      inference(cnf_transformation,[],[f97]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_9763,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_2092,c_1]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_24,plain,
% 23.68/3.49      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))),k5_xboole_0(k2_tarski(X3,X3),k3_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))))) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) ),
% 23.68/3.49      inference(cnf_transformation,[],[f107]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_15703,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_9763,c_24]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_4,plain,
% 23.68/3.49      ( k3_xboole_0(X0,X0) = X0 ),
% 23.68/3.49      inference(cnf_transformation,[],[f50]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_3079,plain,
% 23.68/3.49      ( k5_xboole_0(k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)))))) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X1),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0)))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_4,c_24]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2099,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))) = k2_tarski(X0,X0) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_3085,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X0,X1) ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_3079,c_1,c_2099]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_14784,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) = k2_tarski(X1,X0) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_3085,c_2]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_15713,plain,
% 23.68/3.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_15703,c_1,c_14784]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_15931,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK5,sK4)) = k2_tarski(sK2,sK3) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_15713,c_7248]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_5,plain,
% 23.68/3.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 23.68/3.49      inference(cnf_transformation,[],[f52]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1431,plain,
% 23.68/3.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8865,plain,
% 23.68/3.49      ( r1_tarski(k3_xboole_0(k2_tarski(sK2,sK3),X0),k2_tarski(sK4,sK5)) = iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1431,c_8721]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_9342,plain,
% 23.68/3.49      ( k3_xboole_0(k3_xboole_0(k2_tarski(sK2,sK3),X0),k2_tarski(sK4,sK5)) = k3_xboole_0(k2_tarski(sK2,sK3),X0) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_8865,c_1429]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_24952,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK2,sK3),X0)) = k3_xboole_0(k2_tarski(sK2,sK3),X0) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_9342,c_3]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_32172,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK5,sK4)) = k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_15931,c_24952]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_32198,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) = k2_tarski(sK2,sK3) ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_32172,c_15931]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_32751,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) = k2_tarski(sK2,sK3) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_15713,c_32198]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_31,plain,
% 23.68/3.49      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
% 23.68/3.49      | k2_tarski(X1,X2) = X0
% 23.68/3.49      | k2_tarski(X2,X2) = X0
% 23.68/3.49      | k2_tarski(X1,X1) = X0
% 23.68/3.49      | k1_xboole_0 = X0 ),
% 23.68/3.49      inference(cnf_transformation,[],[f112]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1409,plain,
% 23.68/3.49      ( k2_tarski(X0,X1) = X2
% 23.68/3.49      | k2_tarski(X1,X1) = X2
% 23.68/3.49      | k2_tarski(X0,X0) = X2
% 23.68/3.49      | k1_xboole_0 = X2
% 23.68/3.49      | r1_tarski(X2,k2_tarski(X0,X1)) != iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1984,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK4) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0 ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1408,c_1409]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2252,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK4) = X0
% 23.68/3.49      | k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k1_xboole_0 = X0
% 23.68/3.49      | r1_tarski(X0,k2_tarski(sK2,sK3)) != iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1984,c_1409]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2939,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK2,sK2) = k2_tarski(sK4,sK4)
% 23.68/3.49      | k2_tarski(sK2,sK2) = k1_xboole_0 ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1411,c_2252]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_5935,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK2,sK2) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK2) = k1_xboole_0 ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_2939,c_1984]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_33,negated_conjecture,
% 23.68/3.49      ( sK2 != sK4 ),
% 23.68/3.49      inference(cnf_transformation,[],[f89]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_32,negated_conjecture,
% 23.68/3.49      ( sK2 != sK5 ),
% 23.68/3.49      inference(cnf_transformation,[],[f90]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_23,plain,
% 23.68/3.49      ( ~ r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X1 | X0 = X2 ),
% 23.68/3.49      inference(cnf_transformation,[],[f124]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1458,plain,
% 23.68/3.49      ( ~ r2_hidden(sK2,k2_tarski(sK5,X0)) | sK2 = X0 | sK2 = sK5 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_23]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1485,plain,
% 23.68/3.49      ( ~ r2_hidden(sK2,k2_tarski(sK5,sK2)) | sK2 = sK5 | sK2 = sK2 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_1458]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_21,plain,
% 23.68/3.49      ( r2_hidden(X0,k2_tarski(X1,X0)) ),
% 23.68/3.49      inference(cnf_transformation,[],[f121]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1566,plain,
% 23.68/3.49      ( r2_hidden(sK2,k2_tarski(sK5,sK2)) ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_21]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1053,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1645,plain,
% 23.68/3.49      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_1053]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1872,plain,
% 23.68/3.49      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_1645]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2914,plain,
% 23.68/3.49      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_1872]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2012,plain,
% 23.68/3.49      ( ~ r2_hidden(X0,k2_tarski(sK2,X1)) | X0 = X1 | X0 = sK2 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_23]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2573,plain,
% 23.68/3.49      ( ~ r2_hidden(X0,k2_tarski(sK2,sK2)) | X0 = sK2 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_2012]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_3025,plain,
% 23.68/3.49      ( ~ r2_hidden(sK4,k2_tarski(sK2,sK2)) | sK4 = sK2 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_2573]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_3029,plain,
% 23.68/3.49      ( sK4 = sK2 | r2_hidden(sK4,k2_tarski(sK2,sK2)) != iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_3025]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1416,plain,
% 23.68/3.49      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_5925,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK2,sK2) = k1_xboole_0
% 23.68/3.49      | r2_hidden(sK4,k2_tarski(sK2,sK2)) = iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_2939,c_1416]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_5975,plain,
% 23.68/3.49      ( k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK2) = k1_xboole_0 ),
% 23.68/3.49      inference(global_propositional_subsumption,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_5935,c_33,c_32,c_1485,c_1566,c_2914,c_3029,c_5925]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_5976,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK2,sK2) = k1_xboole_0 ),
% 23.68/3.49      inference(renaming,[status(thm)],[c_5975]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7381,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK2,sK3))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK2,sK3) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_7248,c_25]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7388,plain,
% 23.68/3.49      ( k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK2,sK2) = k1_xboole_0
% 23.68/3.49      | k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK2,sK3))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK2,sK3) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_5976,c_7381]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_0,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 23.68/3.49      inference(cnf_transformation,[],[f96]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1988,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,X0))) = k3_xboole_0(X0,X0) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1990,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,X0))) = X0 ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_1988,c_4]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_5047,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X0)) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1990,c_0]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_5049,plain,
% 23.68/3.49      ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_5047,c_4]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_5050,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_5049,c_1990]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7389,plain,
% 23.68/3.49      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK2,sK3) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK2,sK2) = k1_xboole_0 ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_7388,c_5050]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2913,plain,
% 23.68/3.49      ( sK5 != sK2 | sK2 = sK5 | sK2 != sK2 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_1872]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_22,plain,
% 23.68/3.49      ( r2_hidden(X0,k2_tarski(X0,X1)) ),
% 23.68/3.49      inference(cnf_transformation,[],[f123]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1415,plain,
% 23.68/3.49      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1414,plain,
% 23.68/3.49      ( X0 = X1
% 23.68/3.49      | X0 = X2
% 23.68/3.49      | r2_hidden(X0,k2_tarski(X1,X2)) != iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_6423,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | sK4 = X0
% 23.68/3.49      | r2_hidden(X0,k2_tarski(sK2,sK3)) != iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1984,c_1414]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7602,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | sK3 = sK4 ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1416,c_6423]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7603,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | sK4 = sK2 ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1415,c_6423]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_11632,plain,
% 23.68/3.49      ( k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3) ),
% 23.68/3.49      inference(global_propositional_subsumption,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_7602,c_33,c_32,c_1485,c_1566,c_2914,c_7603]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_11633,plain,
% 23.68/3.49      ( k2_tarski(sK4,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0 ),
% 23.68/3.49      inference(renaming,[status(thm)],[c_11632]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_11642,plain,
% 23.68/3.49      ( k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | sK4 = X0
% 23.68/3.49      | sK5 = X0
% 23.68/3.49      | r2_hidden(X0,k2_tarski(sK2,sK3)) != iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_11633,c_1414]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_50609,plain,
% 23.68/3.49      ( k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | sK4 = sK2
% 23.68/3.49      | sK5 = sK2 ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1415,c_11642]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_53795,plain,
% 23.68/3.49      ( k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3) ),
% 23.68/3.49      inference(global_propositional_subsumption,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_7389,c_33,c_32,c_1485,c_1566,c_2913,c_2914,c_50609]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_53796,plain,
% 23.68/3.49      ( k2_tarski(sK5,sK5) = k2_tarski(sK2,sK3)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0 ),
% 23.68/3.49      inference(renaming,[status(thm)],[c_53795]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_53866,plain,
% 23.68/3.49      ( k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK5,X0),k3_xboole_0(k2_tarski(sK5,X0),k2_tarski(sK2,sK3)))) = k2_tarski(sK5,X0) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_53796,c_1]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89623,plain,
% 23.68/3.49      ( k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_32751,c_53866]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_17550,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK2,sK3),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_15931,c_2238]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89656,plain,
% 23.68/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) = k2_tarski(sK5,sK4)
% 23.68/3.49      | k2_tarski(sK2,sK3) = k1_xboole_0 ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89623,c_17550]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2816,plain,
% 23.68/3.49      ( ~ r2_hidden(sK2,k2_tarski(sK5,sK5)) | sK2 = sK5 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_1458]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2817,plain,
% 23.68/3.49      ( sK2 = sK5 | r2_hidden(sK2,k2_tarski(sK5,sK5)) != iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_2816]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_15,plain,
% 23.68/3.49      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) ),
% 23.68/3.49      inference(cnf_transformation,[],[f116]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1422,plain,
% 23.68/3.49      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k5_xboole_0(k2_tarski(X0,X2),k3_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1))))) = iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_13544,plain,
% 23.68/3.49      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))) = iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_2,c_1422]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89647,plain,
% 23.68/3.49      ( k2_tarski(sK2,sK3) = k1_xboole_0
% 23.68/3.49      | r2_hidden(sK2,k2_tarski(sK5,sK5)) = iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_53866,c_13544]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89825,plain,
% 23.68/3.49      ( k2_tarski(sK2,sK3) = k1_xboole_0 ),
% 23.68/3.49      inference(global_propositional_subsumption,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_89656,c_32,c_2817,c_89647]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2242,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k6_enumset1(X2,X2,X2,X2,X2,X3,X0,X1) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_25,c_2]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_18263,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK2,sK3))) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_15931,c_2242]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89898,plain,
% 23.68/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) = k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89825,c_18263]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89899,plain,
% 23.68/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89825,c_17550]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_9,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.68/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89909,plain,
% 23.68/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK3,sK5,sK4) = k5_xboole_0(k1_xboole_0,k2_tarski(sK5,sK4)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89899,c_9]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89910,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k2_tarski(sK5,sK4)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89898,c_89909]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89911,plain,
% 23.68/3.49      ( k5_xboole_0(k1_xboole_0,k2_tarski(sK5,sK4)) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89910,c_9]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_90028,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_tarski(sK2,sK2)))) = k2_tarski(sK2,sK3) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_89825,c_1]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_90221,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK2,sK2),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_tarski(sK2,sK2)))) = k1_xboole_0 ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_90028,c_89825]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_30,plain,
% 23.68/3.49      ( r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) ),
% 23.68/3.49      inference(cnf_transformation,[],[f128]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1410,plain,
% 23.68/3.49      ( r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) = iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7247,plain,
% 23.68/3.49      ( k3_xboole_0(k1_xboole_0,k2_tarski(X0,X1)) = k1_xboole_0 ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_1410,c_1429]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_90222,plain,
% 23.68/3.49      ( k2_tarski(sK2,sK2) = k1_xboole_0 ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_90221,c_9,c_7247]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1986,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7379,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)))) = k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_7248,c_1986]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7598,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)))) = k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_7379,c_0]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8105,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))) = k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_3,c_7598]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8113,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) = k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_8105,c_7248]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8210,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))) = k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_3,c_8113]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8229,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) = k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_8210,c_7248]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_9081,plain,
% 23.68/3.49      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))))) = k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_8229,c_1986]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_9086,plain,
% 23.68/3.49      ( k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) = k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_9081,c_5049,c_5050]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_36307,plain,
% 23.68/3.49      ( k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK5,sK4)) = k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_15713,c_9086]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_15928,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_15713,c_8229]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_16579,plain,
% 23.68/3.49      ( k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))))) = k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK5,sK4)) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_15928,c_1986]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_16584,plain,
% 23.68/3.49      ( k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK5,sK4)) = k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_16579,c_5049,c_5050]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_36346,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) = k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_36307,c_16584]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_36352,plain,
% 23.68/3.49      ( k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) = k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_36346,c_9086]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100681,plain,
% 23.68/3.49      ( k3_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0),k2_tarski(sK4,sK5)) = k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0) ),
% 23.68/3.49      inference(light_normalisation,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_36352,c_36352,c_89825]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100682,plain,
% 23.68/3.49      ( k3_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK4,sK5)) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_100681,c_9]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100716,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK5,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK5,sK4) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_100682,c_25]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_9771,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)))) = k6_enumset1(X2,X2,X2,X2,X2,X3,X0,X1) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_2092,c_25]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100717,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK5,sK4))) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK5,sK4) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_100682,c_9771]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100718,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK5,sK4))) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK4,sK4,sK5) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_100682,c_2238]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_16013,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X3),k3_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_15713,c_25]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_20164,plain,
% 23.68/3.49      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_16013,c_25]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2240,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X1))) = k6_enumset1(X0,X0,X0,X0,X0,X1,X0,X1) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_4,c_25]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_17863,plain,
% 23.68/3.49      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X0,X1) = k2_tarski(X0,X1) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_2240,c_5050]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_20258,plain,
% 23.68/3.49      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X1,X0) = k2_tarski(X0,X1) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_20164,c_17863]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100736,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK5,sK4))) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_100718,c_20258]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100737,plain,
% 23.68/3.49      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK5,sK5,sK4) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_100717,c_100736]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100738,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK5,sK4))) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_100716,c_100737]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8213,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))))) = k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_8113,c_0]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8109,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))))) = k3_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_7598,c_0]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_8429,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) = k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(light_normalisation,[status(thm)],[c_8213,c_8109,c_8229]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_15921,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k3_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_15713,c_8429]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_36519,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3))) = k2_tarski(sK2,sK3) ),
% 23.68/3.49      inference(light_normalisation,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_15921,c_15921,c_32751]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89880,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0)) = k1_xboole_0 ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89825,c_36519]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89928,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK5,sK4)) = k1_xboole_0 ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89880,c_9]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2091,plain,
% 23.68/3.49      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_32756,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_32198,c_2091]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_32796,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_32756,c_32198]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_7599,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k3_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3))) ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_7379,c_2]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_32797,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK4,sK5),k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(light_normalisation,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_32796,c_7599,c_9086]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_40317,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK2,sK3)),k2_tarski(sK2,sK3)) ),
% 23.68/3.49      inference(light_normalisation,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_32797,c_32797,c_36346]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89873,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0),k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK5,sK4),k1_xboole_0),k1_xboole_0) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89825,c_40317]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_89936,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k5_xboole_0(k2_tarski(sK5,sK4),k2_tarski(sK5,sK4))) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(demodulation,[status(thm)],[c_89873,c_9]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100739,plain,
% 23.68/3.49      ( k5_xboole_0(k2_tarski(sK4,sK5),k1_xboole_0) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(light_normalisation,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_100738,c_89928,c_89936]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100806,plain,
% 23.68/3.49      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK4,sK5) = k2_tarski(sK5,sK4) ),
% 23.68/3.49      inference(light_normalisation,
% 23.68/3.49                [status(thm)],
% 23.68/3.49                [c_22788,c_22788,c_89911,c_90222,c_100739]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_16,plain,
% 23.68/3.49      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) ),
% 23.68/3.49      inference(cnf_transformation,[],[f118]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_1421,plain,
% 23.68/3.49      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) = iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_13316,plain,
% 23.68/3.49      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_25,c_1421]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_100812,plain,
% 23.68/3.49      ( r2_hidden(sK2,k2_tarski(sK5,sK4)) = iProver_top ),
% 23.68/3.49      inference(superposition,[status(thm)],[c_100806,c_13316]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2819,plain,
% 23.68/3.49      ( ~ r2_hidden(sK2,k2_tarski(sK5,sK4)) | sK2 = sK4 | sK2 = sK5 ),
% 23.68/3.49      inference(instantiation,[status(thm)],[c_1458]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(c_2820,plain,
% 23.68/3.49      ( sK2 = sK4
% 23.68/3.49      | sK2 = sK5
% 23.68/3.49      | r2_hidden(sK2,k2_tarski(sK5,sK4)) != iProver_top ),
% 23.68/3.49      inference(predicate_to_equality,[status(thm)],[c_2819]) ).
% 23.68/3.49  
% 23.68/3.49  cnf(contradiction,plain,
% 23.68/3.49      ( $false ),
% 23.68/3.49      inference(minisat,[status(thm)],[c_100812,c_2820,c_32,c_33]) ).
% 23.68/3.49  
% 23.68/3.49  
% 23.68/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.68/3.49  
% 23.68/3.49  ------                               Statistics
% 23.68/3.49  
% 23.68/3.49  ------ General
% 23.68/3.49  
% 23.68/3.49  abstr_ref_over_cycles:                  0
% 23.68/3.49  abstr_ref_under_cycles:                 0
% 23.68/3.49  gc_basic_clause_elim:                   0
% 23.68/3.49  forced_gc_time:                         0
% 23.68/3.49  parsing_time:                           0.009
% 23.68/3.49  unif_index_cands_time:                  0.
% 23.68/3.49  unif_index_add_time:                    0.
% 23.68/3.49  orderings_time:                         0.
% 23.68/3.49  out_proof_time:                         0.021
% 23.68/3.49  total_time:                             2.972
% 23.68/3.49  num_of_symbols:                         44
% 23.68/3.49  num_of_terms:                           136342
% 23.68/3.49  
% 23.68/3.49  ------ Preprocessing
% 23.68/3.49  
% 23.68/3.49  num_of_splits:                          0
% 23.68/3.49  num_of_split_atoms:                     0
% 23.68/3.49  num_of_reused_defs:                     0
% 23.68/3.49  num_eq_ax_congr_red:                    30
% 23.68/3.49  num_of_sem_filtered_clauses:            1
% 23.68/3.49  num_of_subtypes:                        0
% 23.68/3.49  monotx_restored_types:                  0
% 23.68/3.49  sat_num_of_epr_types:                   0
% 23.68/3.49  sat_num_of_non_cyclic_types:            0
% 23.68/3.49  sat_guarded_non_collapsed_types:        0
% 23.68/3.49  num_pure_diseq_elim:                    0
% 23.68/3.49  simp_replaced_by:                       0
% 23.68/3.49  res_preprocessed:                       120
% 23.68/3.49  prep_upred:                             0
% 23.68/3.49  prep_unflattend:                        48
% 23.68/3.49  smt_new_axioms:                         0
% 23.68/3.49  pred_elim_cands:                        2
% 23.68/3.49  pred_elim:                              0
% 23.68/3.49  pred_elim_cl:                           0
% 23.68/3.49  pred_elim_cycles:                       1
% 23.68/3.49  merged_defs:                            0
% 23.68/3.49  merged_defs_ncl:                        0
% 23.68/3.49  bin_hyper_res:                          0
% 23.68/3.49  prep_cycles:                            3
% 23.68/3.49  pred_elim_time:                         0.014
% 23.68/3.49  splitting_time:                         0.
% 23.68/3.49  sem_filter_time:                        0.
% 23.68/3.49  monotx_time:                            0.001
% 23.68/3.49  subtype_inf_time:                       0.
% 23.68/3.49  
% 23.68/3.49  ------ Problem properties
% 23.68/3.49  
% 23.68/3.49  clauses:                                35
% 23.68/3.49  conjectures:                            3
% 23.68/3.49  epr:                                    3
% 23.68/3.49  horn:                                   30
% 23.68/3.49  ground:                                 3
% 23.68/3.49  unary:                                  22
% 23.68/3.49  binary:                                 3
% 23.68/3.49  lits:                                   64
% 23.68/3.49  lits_eq:                                39
% 23.68/3.49  fd_pure:                                0
% 23.68/3.49  fd_pseudo:                              0
% 23.68/3.49  fd_cond:                                1
% 23.68/3.49  fd_pseudo_cond:                         8
% 23.68/3.49  ac_symbols:                             0
% 23.68/3.49  
% 23.68/3.49  ------ Propositional Solver
% 23.68/3.49  
% 23.68/3.49  prop_solver_calls:                      33
% 23.68/3.49  prop_fast_solver_calls:                 1625
% 23.68/3.49  smt_solver_calls:                       0
% 23.68/3.49  smt_fast_solver_calls:                  0
% 23.68/3.49  prop_num_of_clauses:                    32006
% 23.68/3.49  prop_preprocess_simplified:             60537
% 23.68/3.49  prop_fo_subsumed:                       73
% 23.68/3.49  prop_solver_time:                       0.
% 23.68/3.49  smt_solver_time:                        0.
% 23.68/3.49  smt_fast_solver_time:                   0.
% 23.68/3.49  prop_fast_solver_time:                  0.
% 23.68/3.49  prop_unsat_core_time:                   0.003
% 23.68/3.49  
% 23.68/3.49  ------ QBF
% 23.68/3.49  
% 23.68/3.49  qbf_q_res:                              0
% 23.68/3.49  qbf_num_tautologies:                    0
% 23.68/3.49  qbf_prep_cycles:                        0
% 23.68/3.49  
% 23.68/3.49  ------ BMC1
% 23.68/3.49  
% 23.68/3.49  bmc1_current_bound:                     -1
% 23.68/3.49  bmc1_last_solved_bound:                 -1
% 23.68/3.49  bmc1_unsat_core_size:                   -1
% 23.68/3.49  bmc1_unsat_core_parents_size:           -1
% 23.68/3.49  bmc1_merge_next_fun:                    0
% 23.68/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.68/3.49  
% 23.68/3.49  ------ Instantiation
% 23.68/3.49  
% 23.68/3.49  inst_num_of_clauses:                    7281
% 23.68/3.49  inst_num_in_passive:                    5846
% 23.68/3.49  inst_num_in_active:                     1435
% 23.68/3.49  inst_num_in_unprocessed:                0
% 23.68/3.49  inst_num_of_loops:                      1910
% 23.68/3.49  inst_num_of_learning_restarts:          0
% 23.68/3.49  inst_num_moves_active_passive:          474
% 23.68/3.49  inst_lit_activity:                      0
% 23.68/3.49  inst_lit_activity_moves:                0
% 23.68/3.49  inst_num_tautologies:                   0
% 23.68/3.49  inst_num_prop_implied:                  0
% 23.68/3.49  inst_num_existing_simplified:           0
% 23.68/3.49  inst_num_eq_res_simplified:             0
% 23.68/3.49  inst_num_child_elim:                    0
% 23.68/3.49  inst_num_of_dismatching_blockings:      24134
% 23.68/3.49  inst_num_of_non_proper_insts:           7581
% 23.68/3.49  inst_num_of_duplicates:                 0
% 23.68/3.49  inst_inst_num_from_inst_to_res:         0
% 23.68/3.49  inst_dismatching_checking_time:         0.
% 23.68/3.49  
% 23.68/3.49  ------ Resolution
% 23.68/3.49  
% 23.68/3.49  res_num_of_clauses:                     0
% 23.68/3.49  res_num_in_passive:                     0
% 23.68/3.49  res_num_in_active:                      0
% 23.68/3.49  res_num_of_loops:                       123
% 23.68/3.49  res_forward_subset_subsumed:            2269
% 23.68/3.49  res_backward_subset_subsumed:           0
% 23.68/3.49  res_forward_subsumed:                   0
% 23.68/3.49  res_backward_subsumed:                  0
% 23.68/3.49  res_forward_subsumption_resolution:     0
% 23.68/3.49  res_backward_subsumption_resolution:    0
% 23.68/3.49  res_clause_to_clause_subsumption:       70188
% 23.68/3.49  res_orphan_elimination:                 0
% 23.68/3.49  res_tautology_del:                      129
% 23.68/3.49  res_num_eq_res_simplified:              0
% 23.68/3.49  res_num_sel_changes:                    0
% 23.68/3.49  res_moves_from_active_to_pass:          0
% 23.68/3.49  
% 23.68/3.49  ------ Superposition
% 23.68/3.49  
% 23.68/3.49  sup_time_total:                         0.
% 23.68/3.49  sup_time_generating:                    0.
% 23.68/3.49  sup_time_sim_full:                      0.
% 23.68/3.49  sup_time_sim_immed:                     0.
% 23.68/3.49  
% 23.68/3.49  sup_num_of_clauses:                     3412
% 23.68/3.49  sup_num_in_active:                      185
% 23.68/3.49  sup_num_in_passive:                     3227
% 23.68/3.49  sup_num_of_loops:                       381
% 23.68/3.49  sup_fw_superposition:                   6812
% 23.68/3.49  sup_bw_superposition:                   12846
% 23.68/3.49  sup_immediate_simplified:               3368
% 23.68/3.49  sup_given_eliminated:                   9
% 23.68/3.49  comparisons_done:                       0
% 23.68/3.49  comparisons_avoided:                    462
% 23.68/3.49  
% 23.68/3.49  ------ Simplifications
% 23.68/3.49  
% 23.68/3.49  
% 23.68/3.49  sim_fw_subset_subsumed:                 128
% 23.68/3.49  sim_bw_subset_subsumed:                 500
% 23.68/3.49  sim_fw_subsumed:                        543
% 23.68/3.49  sim_bw_subsumed:                        64
% 23.68/3.49  sim_fw_subsumption_res:                 0
% 23.68/3.49  sim_bw_subsumption_res:                 0
% 23.68/3.49  sim_tautology_del:                      42
% 23.68/3.50  sim_eq_tautology_del:                   484
% 23.68/3.50  sim_eq_res_simp:                        4
% 23.68/3.50  sim_fw_demodulated:                     2089
% 23.68/3.50  sim_bw_demodulated:                     261
% 23.68/3.50  sim_light_normalised:                   955
% 23.68/3.50  sim_joinable_taut:                      0
% 23.68/3.50  sim_joinable_simp:                      0
% 23.68/3.50  sim_ac_normalised:                      0
% 23.68/3.50  sim_smt_subsumption:                    0
% 23.68/3.50  
%------------------------------------------------------------------------------
