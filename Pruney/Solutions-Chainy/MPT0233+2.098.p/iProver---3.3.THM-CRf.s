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
% DateTime   : Thu Dec  3 11:31:27 EST 2020

% Result     : Theorem 27.61s
% Output     : CNFRefutation 27.61s
% Verified   : 
% Statistics : Number of formulae       :  134 (1840 expanded)
%              Number of clauses        :   61 ( 451 expanded)
%              Number of leaves         :   21 ( 542 expanded)
%              Depth                    :   25
%              Number of atoms          :  360 (2446 expanded)
%              Number of equality atoms :  272 (2097 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f21,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f65,f77])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f78,f77])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f72,f67,f67])).

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

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK2 != sK5
      & sK2 != sK4
      & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( sK2 != sK5
    & sK2 != sK4
    & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f39])).

fof(f74,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,(
    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(definition_unfolding,[],[f74,f77,f77])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f47,f47])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f49,f67,f78])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(rectify,[],[f30])).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f106,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f92])).

fof(f107,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f106])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f117,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f101])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f59,f77])).

fof(f115,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f100])).

fof(f116,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f115])).

fof(f76,plain,(
    sK2 != sK5 ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1154,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1153,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1940,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK5,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23,c_1153])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1169,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2876,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK5,sK4))) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1940,c_1169])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2880,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_2876,c_0])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1868,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1873,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1868,c_7])).

cnf(c_1870,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_1871,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1870,c_6])).

cnf(c_1874,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1873,c_1871])).

cnf(c_2884,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK5,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2880,c_1874])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1170,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3852,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1170])).

cnf(c_4019,plain,
    ( r1_tarski(X0,k2_enumset1(sK4,sK4,sK5,sK4)) = iProver_top
    | r1_tarski(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2884,c_3852])).

cnf(c_4020,plain,
    ( r1_tarski(X0,k2_enumset1(sK4,sK4,sK5,sK4)) = iProver_top
    | r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4019,c_1873])).

cnf(c_4189,plain,
    ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK5,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_4020])).

cnf(c_4302,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK5,sK4))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_4189,c_1169])).

cnf(c_4305,plain,
    ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_4302,c_0])).

cnf(c_4323,plain,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK5,sK4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4305,c_1874])).

cnf(c_1,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_5443,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK5,sK4),k1_xboole_0) = k2_enumset1(sK4,sK5,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_4323,c_1])).

cnf(c_5986,plain,
    ( k2_enumset1(sK4,sK5,sK4,sK2) = k2_enumset1(sK4,sK4,sK5,sK4) ),
    inference(superposition,[status(thm)],[c_7,c_5443])).

cnf(c_2548,plain,
    ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X2,X1,X3) ),
    inference(superposition,[status(thm)],[c_23,c_1])).

cnf(c_6358,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK5,sK4,sK2),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK4,sK5,sK4,sK2))) = k2_enumset1(sK4,sK4,sK5,X0) ),
    inference(superposition,[status(thm)],[c_5986,c_2548])).

cnf(c_6172,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK5,sK4,sK2),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK4,sK5,sK4,sK2))) = k2_enumset1(sK4,sK5,sK4,X0) ),
    inference(superposition,[status(thm)],[c_5986,c_1])).

cnf(c_6360,plain,
    ( k2_enumset1(sK4,sK5,sK4,X0) = k2_enumset1(sK4,sK4,sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_6358,c_6172])).

cnf(c_6359,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(superposition,[status(thm)],[c_2548,c_1])).

cnf(c_7770,plain,
    ( k5_xboole_0(k2_enumset1(X0,X1,X0,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X1,X0,X2))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(superposition,[status(thm)],[c_6359,c_1])).

cnf(c_7970,plain,
    ( k2_enumset1(sK4,sK5,sK2,X0) = k2_enumset1(sK4,sK5,sK4,X0) ),
    inference(demodulation,[status(thm)],[c_7770,c_6172])).

cnf(c_79514,plain,
    ( k2_enumset1(sK4,sK5,sK2,X0) = k2_enumset1(sK4,sK4,sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_6360,c_6360,c_7970])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1164,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_79547,plain,
    ( r2_hidden(X0,k2_enumset1(sK4,sK5,sK2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_79514,c_1164])).

cnf(c_79701,plain,
    ( r2_hidden(sK2,k2_enumset1(sK4,sK5,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_79547])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1155,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2467,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X1,k2_enumset1(X2,X2,X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1155])).

cnf(c_6179,plain,
    ( sK4 = X0
    | sK5 = X0
    | r2_hidden(X0,k2_enumset1(sK4,sK5,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5986,c_2467])).

cnf(c_72465,plain,
    ( sK4 = X0
    | sK5 = X0
    | r2_hidden(X0,k2_enumset1(sK4,sK5,sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6179,c_7970])).

cnf(c_72467,plain,
    ( sK4 = sK2
    | sK5 = sK2
    | r2_hidden(sK2,k2_enumset1(sK4,sK5,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_72465])).

cnf(c_878,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1204,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_1205,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_1196,plain,
    ( sK5 != X0
    | sK2 != X0
    | sK2 = sK5 ),
    inference(instantiation,[status(thm)],[c_878])).

cnf(c_1197,plain,
    ( sK5 != sK2
    | sK2 = sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_20,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_38,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_35,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_25,negated_conjecture,
    ( sK2 != sK5 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_26,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79701,c_72467,c_1205,c_1197,c_38,c_35,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.61/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.61/3.99  
% 27.61/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.61/3.99  
% 27.61/3.99  ------  iProver source info
% 27.61/3.99  
% 27.61/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.61/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.61/3.99  git: non_committed_changes: false
% 27.61/3.99  git: last_make_outside_of_git: false
% 27.61/3.99  
% 27.61/3.99  ------ 
% 27.61/3.99  
% 27.61/3.99  ------ Input Options
% 27.61/3.99  
% 27.61/3.99  --out_options                           all
% 27.61/3.99  --tptp_safe_out                         true
% 27.61/3.99  --problem_path                          ""
% 27.61/3.99  --include_path                          ""
% 27.61/3.99  --clausifier                            res/vclausify_rel
% 27.61/3.99  --clausifier_options                    ""
% 27.61/3.99  --stdin                                 false
% 27.61/3.99  --stats_out                             all
% 27.61/3.99  
% 27.61/3.99  ------ General Options
% 27.61/3.99  
% 27.61/3.99  --fof                                   false
% 27.61/3.99  --time_out_real                         305.
% 27.61/3.99  --time_out_virtual                      -1.
% 27.61/3.99  --symbol_type_check                     false
% 27.61/3.99  --clausify_out                          false
% 27.61/3.99  --sig_cnt_out                           false
% 27.61/3.99  --trig_cnt_out                          false
% 27.61/3.99  --trig_cnt_out_tolerance                1.
% 27.61/3.99  --trig_cnt_out_sk_spl                   false
% 27.61/3.99  --abstr_cl_out                          false
% 27.61/3.99  
% 27.61/3.99  ------ Global Options
% 27.61/3.99  
% 27.61/3.99  --schedule                              default
% 27.61/3.99  --add_important_lit                     false
% 27.61/3.99  --prop_solver_per_cl                    1000
% 27.61/3.99  --min_unsat_core                        false
% 27.61/3.99  --soft_assumptions                      false
% 27.61/3.99  --soft_lemma_size                       3
% 27.61/3.99  --prop_impl_unit_size                   0
% 27.61/3.99  --prop_impl_unit                        []
% 27.61/3.99  --share_sel_clauses                     true
% 27.61/3.99  --reset_solvers                         false
% 27.61/3.99  --bc_imp_inh                            [conj_cone]
% 27.61/3.99  --conj_cone_tolerance                   3.
% 27.61/3.99  --extra_neg_conj                        none
% 27.61/3.99  --large_theory_mode                     true
% 27.61/3.99  --prolific_symb_bound                   200
% 27.61/3.99  --lt_threshold                          2000
% 27.61/3.99  --clause_weak_htbl                      true
% 27.61/3.99  --gc_record_bc_elim                     false
% 27.61/3.99  
% 27.61/3.99  ------ Preprocessing Options
% 27.61/3.99  
% 27.61/3.99  --preprocessing_flag                    true
% 27.61/3.99  --time_out_prep_mult                    0.1
% 27.61/3.99  --splitting_mode                        input
% 27.61/3.99  --splitting_grd                         true
% 27.61/3.99  --splitting_cvd                         false
% 27.61/3.99  --splitting_cvd_svl                     false
% 27.61/3.99  --splitting_nvd                         32
% 27.61/3.99  --sub_typing                            true
% 27.61/3.99  --prep_gs_sim                           true
% 27.61/3.99  --prep_unflatten                        true
% 27.61/3.99  --prep_res_sim                          true
% 27.61/3.99  --prep_upred                            true
% 27.61/3.99  --prep_sem_filter                       exhaustive
% 27.61/3.99  --prep_sem_filter_out                   false
% 27.61/3.99  --pred_elim                             true
% 27.61/3.99  --res_sim_input                         true
% 27.61/3.99  --eq_ax_congr_red                       true
% 27.61/3.99  --pure_diseq_elim                       true
% 27.61/3.99  --brand_transform                       false
% 27.61/3.99  --non_eq_to_eq                          false
% 27.61/3.99  --prep_def_merge                        true
% 27.61/3.99  --prep_def_merge_prop_impl              false
% 27.61/3.99  --prep_def_merge_mbd                    true
% 27.61/3.99  --prep_def_merge_tr_red                 false
% 27.61/3.99  --prep_def_merge_tr_cl                  false
% 27.61/3.99  --smt_preprocessing                     true
% 27.61/3.99  --smt_ac_axioms                         fast
% 27.61/3.99  --preprocessed_out                      false
% 27.61/3.99  --preprocessed_stats                    false
% 27.61/3.99  
% 27.61/3.99  ------ Abstraction refinement Options
% 27.61/3.99  
% 27.61/3.99  --abstr_ref                             []
% 27.61/3.99  --abstr_ref_prep                        false
% 27.61/3.99  --abstr_ref_until_sat                   false
% 27.61/3.99  --abstr_ref_sig_restrict                funpre
% 27.61/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.61/3.99  --abstr_ref_under                       []
% 27.61/3.99  
% 27.61/3.99  ------ SAT Options
% 27.61/3.99  
% 27.61/3.99  --sat_mode                              false
% 27.61/3.99  --sat_fm_restart_options                ""
% 27.61/3.99  --sat_gr_def                            false
% 27.61/3.99  --sat_epr_types                         true
% 27.61/3.99  --sat_non_cyclic_types                  false
% 27.61/3.99  --sat_finite_models                     false
% 27.61/3.99  --sat_fm_lemmas                         false
% 27.61/3.99  --sat_fm_prep                           false
% 27.61/3.99  --sat_fm_uc_incr                        true
% 27.61/3.99  --sat_out_model                         small
% 27.61/3.99  --sat_out_clauses                       false
% 27.61/3.99  
% 27.61/3.99  ------ QBF Options
% 27.61/3.99  
% 27.61/3.99  --qbf_mode                              false
% 27.61/3.99  --qbf_elim_univ                         false
% 27.61/3.99  --qbf_dom_inst                          none
% 27.61/3.99  --qbf_dom_pre_inst                      false
% 27.61/3.99  --qbf_sk_in                             false
% 27.61/3.99  --qbf_pred_elim                         true
% 27.61/3.99  --qbf_split                             512
% 27.61/3.99  
% 27.61/3.99  ------ BMC1 Options
% 27.61/3.99  
% 27.61/3.99  --bmc1_incremental                      false
% 27.61/3.99  --bmc1_axioms                           reachable_all
% 27.61/3.99  --bmc1_min_bound                        0
% 27.61/3.99  --bmc1_max_bound                        -1
% 27.61/3.99  --bmc1_max_bound_default                -1
% 27.61/3.99  --bmc1_symbol_reachability              true
% 27.61/3.99  --bmc1_property_lemmas                  false
% 27.61/3.99  --bmc1_k_induction                      false
% 27.61/3.99  --bmc1_non_equiv_states                 false
% 27.61/3.99  --bmc1_deadlock                         false
% 27.61/3.99  --bmc1_ucm                              false
% 27.61/3.99  --bmc1_add_unsat_core                   none
% 27.61/3.99  --bmc1_unsat_core_children              false
% 27.61/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.61/3.99  --bmc1_out_stat                         full
% 27.61/3.99  --bmc1_ground_init                      false
% 27.61/3.99  --bmc1_pre_inst_next_state              false
% 27.61/3.99  --bmc1_pre_inst_state                   false
% 27.61/3.99  --bmc1_pre_inst_reach_state             false
% 27.61/3.99  --bmc1_out_unsat_core                   false
% 27.61/3.99  --bmc1_aig_witness_out                  false
% 27.61/3.99  --bmc1_verbose                          false
% 27.61/3.99  --bmc1_dump_clauses_tptp                false
% 27.61/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.61/3.99  --bmc1_dump_file                        -
% 27.61/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.61/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.61/3.99  --bmc1_ucm_extend_mode                  1
% 27.61/3.99  --bmc1_ucm_init_mode                    2
% 27.61/3.99  --bmc1_ucm_cone_mode                    none
% 27.61/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.61/3.99  --bmc1_ucm_relax_model                  4
% 27.61/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.61/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.61/3.99  --bmc1_ucm_layered_model                none
% 27.61/3.99  --bmc1_ucm_max_lemma_size               10
% 27.61/3.99  
% 27.61/3.99  ------ AIG Options
% 27.61/3.99  
% 27.61/3.99  --aig_mode                              false
% 27.61/3.99  
% 27.61/3.99  ------ Instantiation Options
% 27.61/3.99  
% 27.61/3.99  --instantiation_flag                    true
% 27.61/3.99  --inst_sos_flag                         true
% 27.61/3.99  --inst_sos_phase                        true
% 27.61/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.61/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.61/3.99  --inst_lit_sel_side                     num_symb
% 27.61/3.99  --inst_solver_per_active                1400
% 27.61/3.99  --inst_solver_calls_frac                1.
% 27.61/3.99  --inst_passive_queue_type               priority_queues
% 27.61/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.61/3.99  --inst_passive_queues_freq              [25;2]
% 27.61/3.99  --inst_dismatching                      true
% 27.61/3.99  --inst_eager_unprocessed_to_passive     true
% 27.61/3.99  --inst_prop_sim_given                   true
% 27.61/3.99  --inst_prop_sim_new                     false
% 27.61/3.99  --inst_subs_new                         false
% 27.61/3.99  --inst_eq_res_simp                      false
% 27.61/3.99  --inst_subs_given                       false
% 27.61/3.99  --inst_orphan_elimination               true
% 27.61/3.99  --inst_learning_loop_flag               true
% 27.61/3.99  --inst_learning_start                   3000
% 27.61/3.99  --inst_learning_factor                  2
% 27.61/3.99  --inst_start_prop_sim_after_learn       3
% 27.61/3.99  --inst_sel_renew                        solver
% 27.61/3.99  --inst_lit_activity_flag                true
% 27.61/3.99  --inst_restr_to_given                   false
% 27.61/3.99  --inst_activity_threshold               500
% 27.61/3.99  --inst_out_proof                        true
% 27.61/3.99  
% 27.61/3.99  ------ Resolution Options
% 27.61/3.99  
% 27.61/3.99  --resolution_flag                       true
% 27.61/3.99  --res_lit_sel                           adaptive
% 27.61/3.99  --res_lit_sel_side                      none
% 27.61/3.99  --res_ordering                          kbo
% 27.61/3.99  --res_to_prop_solver                    active
% 27.61/3.99  --res_prop_simpl_new                    false
% 27.61/3.99  --res_prop_simpl_given                  true
% 27.61/3.99  --res_passive_queue_type                priority_queues
% 27.61/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.61/3.99  --res_passive_queues_freq               [15;5]
% 27.61/3.99  --res_forward_subs                      full
% 27.61/3.99  --res_backward_subs                     full
% 27.61/3.99  --res_forward_subs_resolution           true
% 27.61/3.99  --res_backward_subs_resolution          true
% 27.61/3.99  --res_orphan_elimination                true
% 27.61/3.99  --res_time_limit                        2.
% 27.61/3.99  --res_out_proof                         true
% 27.61/3.99  
% 27.61/3.99  ------ Superposition Options
% 27.61/3.99  
% 27.61/3.99  --superposition_flag                    true
% 27.61/3.99  --sup_passive_queue_type                priority_queues
% 27.61/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.61/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.61/3.99  --demod_completeness_check              fast
% 27.61/3.99  --demod_use_ground                      true
% 27.61/3.99  --sup_to_prop_solver                    passive
% 27.61/3.99  --sup_prop_simpl_new                    true
% 27.61/3.99  --sup_prop_simpl_given                  true
% 27.61/3.99  --sup_fun_splitting                     true
% 27.61/3.99  --sup_smt_interval                      50000
% 27.61/4.00  
% 27.61/4.00  ------ Superposition Simplification Setup
% 27.61/4.00  
% 27.61/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.61/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.61/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.61/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.61/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.61/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.61/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.61/4.00  --sup_immed_triv                        [TrivRules]
% 27.61/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.61/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.61/4.00  --sup_immed_bw_main                     []
% 27.61/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.61/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.61/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.61/4.00  --sup_input_bw                          []
% 27.61/4.00  
% 27.61/4.00  ------ Combination Options
% 27.61/4.00  
% 27.61/4.00  --comb_res_mult                         3
% 27.61/4.00  --comb_sup_mult                         2
% 27.61/4.00  --comb_inst_mult                        10
% 27.61/4.00  
% 27.61/4.00  ------ Debug Options
% 27.61/4.00  
% 27.61/4.00  --dbg_backtrace                         false
% 27.61/4.00  --dbg_dump_prop_clauses                 false
% 27.61/4.00  --dbg_dump_prop_clauses_file            -
% 27.61/4.00  --dbg_out_stat                          false
% 27.61/4.00  ------ Parsing...
% 27.61/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.61/4.00  
% 27.61/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.61/4.00  
% 27.61/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.61/4.00  
% 27.61/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.61/4.00  ------ Proving...
% 27.61/4.00  ------ Problem Properties 
% 27.61/4.00  
% 27.61/4.00  
% 27.61/4.00  clauses                                 28
% 27.61/4.00  conjectures                             3
% 27.61/4.00  EPR                                     2
% 27.61/4.00  Horn                                    24
% 27.61/4.00  unary                                   17
% 27.61/4.00  binary                                  2
% 27.61/4.00  lits                                    52
% 27.61/4.00  lits eq                                 33
% 27.61/4.00  fd_pure                                 0
% 27.61/4.00  fd_pseudo                               0
% 27.61/4.00  fd_cond                                 0
% 27.61/4.00  fd_pseudo_cond                          7
% 27.61/4.00  AC symbols                              0
% 27.61/4.00  
% 27.61/4.00  ------ Schedule dynamic 5 is on 
% 27.61/4.00  
% 27.61/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.61/4.00  
% 27.61/4.00  
% 27.61/4.00  ------ 
% 27.61/4.00  Current options:
% 27.61/4.00  ------ 
% 27.61/4.00  
% 27.61/4.00  ------ Input Options
% 27.61/4.00  
% 27.61/4.00  --out_options                           all
% 27.61/4.00  --tptp_safe_out                         true
% 27.61/4.00  --problem_path                          ""
% 27.61/4.00  --include_path                          ""
% 27.61/4.00  --clausifier                            res/vclausify_rel
% 27.61/4.00  --clausifier_options                    ""
% 27.61/4.00  --stdin                                 false
% 27.61/4.00  --stats_out                             all
% 27.61/4.00  
% 27.61/4.00  ------ General Options
% 27.61/4.00  
% 27.61/4.00  --fof                                   false
% 27.61/4.00  --time_out_real                         305.
% 27.61/4.00  --time_out_virtual                      -1.
% 27.61/4.00  --symbol_type_check                     false
% 27.61/4.00  --clausify_out                          false
% 27.61/4.00  --sig_cnt_out                           false
% 27.61/4.00  --trig_cnt_out                          false
% 27.61/4.00  --trig_cnt_out_tolerance                1.
% 27.61/4.00  --trig_cnt_out_sk_spl                   false
% 27.61/4.00  --abstr_cl_out                          false
% 27.61/4.00  
% 27.61/4.00  ------ Global Options
% 27.61/4.00  
% 27.61/4.00  --schedule                              default
% 27.61/4.00  --add_important_lit                     false
% 27.61/4.00  --prop_solver_per_cl                    1000
% 27.61/4.00  --min_unsat_core                        false
% 27.61/4.00  --soft_assumptions                      false
% 27.61/4.00  --soft_lemma_size                       3
% 27.61/4.00  --prop_impl_unit_size                   0
% 27.61/4.00  --prop_impl_unit                        []
% 27.61/4.00  --share_sel_clauses                     true
% 27.61/4.00  --reset_solvers                         false
% 27.61/4.00  --bc_imp_inh                            [conj_cone]
% 27.61/4.00  --conj_cone_tolerance                   3.
% 27.61/4.00  --extra_neg_conj                        none
% 27.61/4.00  --large_theory_mode                     true
% 27.61/4.00  --prolific_symb_bound                   200
% 27.61/4.00  --lt_threshold                          2000
% 27.61/4.00  --clause_weak_htbl                      true
% 27.61/4.00  --gc_record_bc_elim                     false
% 27.61/4.00  
% 27.61/4.00  ------ Preprocessing Options
% 27.61/4.00  
% 27.61/4.00  --preprocessing_flag                    true
% 27.61/4.00  --time_out_prep_mult                    0.1
% 27.61/4.00  --splitting_mode                        input
% 27.61/4.00  --splitting_grd                         true
% 27.61/4.00  --splitting_cvd                         false
% 27.61/4.00  --splitting_cvd_svl                     false
% 27.61/4.00  --splitting_nvd                         32
% 27.61/4.00  --sub_typing                            true
% 27.61/4.00  --prep_gs_sim                           true
% 27.61/4.00  --prep_unflatten                        true
% 27.61/4.00  --prep_res_sim                          true
% 27.61/4.00  --prep_upred                            true
% 27.61/4.00  --prep_sem_filter                       exhaustive
% 27.61/4.00  --prep_sem_filter_out                   false
% 27.61/4.00  --pred_elim                             true
% 27.61/4.00  --res_sim_input                         true
% 27.61/4.00  --eq_ax_congr_red                       true
% 27.61/4.00  --pure_diseq_elim                       true
% 27.61/4.00  --brand_transform                       false
% 27.61/4.00  --non_eq_to_eq                          false
% 27.61/4.00  --prep_def_merge                        true
% 27.61/4.00  --prep_def_merge_prop_impl              false
% 27.61/4.00  --prep_def_merge_mbd                    true
% 27.61/4.00  --prep_def_merge_tr_red                 false
% 27.61/4.00  --prep_def_merge_tr_cl                  false
% 27.61/4.00  --smt_preprocessing                     true
% 27.61/4.00  --smt_ac_axioms                         fast
% 27.61/4.00  --preprocessed_out                      false
% 27.61/4.00  --preprocessed_stats                    false
% 27.61/4.00  
% 27.61/4.00  ------ Abstraction refinement Options
% 27.61/4.00  
% 27.61/4.00  --abstr_ref                             []
% 27.61/4.00  --abstr_ref_prep                        false
% 27.61/4.00  --abstr_ref_until_sat                   false
% 27.61/4.00  --abstr_ref_sig_restrict                funpre
% 27.61/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.61/4.00  --abstr_ref_under                       []
% 27.61/4.00  
% 27.61/4.00  ------ SAT Options
% 27.61/4.00  
% 27.61/4.00  --sat_mode                              false
% 27.61/4.00  --sat_fm_restart_options                ""
% 27.61/4.00  --sat_gr_def                            false
% 27.61/4.00  --sat_epr_types                         true
% 27.61/4.00  --sat_non_cyclic_types                  false
% 27.61/4.00  --sat_finite_models                     false
% 27.61/4.00  --sat_fm_lemmas                         false
% 27.61/4.00  --sat_fm_prep                           false
% 27.61/4.00  --sat_fm_uc_incr                        true
% 27.61/4.00  --sat_out_model                         small
% 27.61/4.00  --sat_out_clauses                       false
% 27.61/4.00  
% 27.61/4.00  ------ QBF Options
% 27.61/4.00  
% 27.61/4.00  --qbf_mode                              false
% 27.61/4.00  --qbf_elim_univ                         false
% 27.61/4.00  --qbf_dom_inst                          none
% 27.61/4.00  --qbf_dom_pre_inst                      false
% 27.61/4.00  --qbf_sk_in                             false
% 27.61/4.00  --qbf_pred_elim                         true
% 27.61/4.00  --qbf_split                             512
% 27.61/4.00  
% 27.61/4.00  ------ BMC1 Options
% 27.61/4.00  
% 27.61/4.00  --bmc1_incremental                      false
% 27.61/4.00  --bmc1_axioms                           reachable_all
% 27.61/4.00  --bmc1_min_bound                        0
% 27.61/4.00  --bmc1_max_bound                        -1
% 27.61/4.00  --bmc1_max_bound_default                -1
% 27.61/4.00  --bmc1_symbol_reachability              true
% 27.61/4.00  --bmc1_property_lemmas                  false
% 27.61/4.00  --bmc1_k_induction                      false
% 27.61/4.00  --bmc1_non_equiv_states                 false
% 27.61/4.00  --bmc1_deadlock                         false
% 27.61/4.00  --bmc1_ucm                              false
% 27.61/4.00  --bmc1_add_unsat_core                   none
% 27.61/4.00  --bmc1_unsat_core_children              false
% 27.61/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.61/4.00  --bmc1_out_stat                         full
% 27.61/4.00  --bmc1_ground_init                      false
% 27.61/4.00  --bmc1_pre_inst_next_state              false
% 27.61/4.00  --bmc1_pre_inst_state                   false
% 27.61/4.00  --bmc1_pre_inst_reach_state             false
% 27.61/4.00  --bmc1_out_unsat_core                   false
% 27.61/4.00  --bmc1_aig_witness_out                  false
% 27.61/4.00  --bmc1_verbose                          false
% 27.61/4.00  --bmc1_dump_clauses_tptp                false
% 27.61/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.61/4.00  --bmc1_dump_file                        -
% 27.61/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.61/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.61/4.00  --bmc1_ucm_extend_mode                  1
% 27.61/4.00  --bmc1_ucm_init_mode                    2
% 27.61/4.00  --bmc1_ucm_cone_mode                    none
% 27.61/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.61/4.00  --bmc1_ucm_relax_model                  4
% 27.61/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.61/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.61/4.00  --bmc1_ucm_layered_model                none
% 27.61/4.00  --bmc1_ucm_max_lemma_size               10
% 27.61/4.00  
% 27.61/4.00  ------ AIG Options
% 27.61/4.00  
% 27.61/4.00  --aig_mode                              false
% 27.61/4.00  
% 27.61/4.00  ------ Instantiation Options
% 27.61/4.00  
% 27.61/4.00  --instantiation_flag                    true
% 27.61/4.00  --inst_sos_flag                         true
% 27.61/4.00  --inst_sos_phase                        true
% 27.61/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.61/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.61/4.00  --inst_lit_sel_side                     none
% 27.61/4.00  --inst_solver_per_active                1400
% 27.61/4.00  --inst_solver_calls_frac                1.
% 27.61/4.00  --inst_passive_queue_type               priority_queues
% 27.61/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.61/4.00  --inst_passive_queues_freq              [25;2]
% 27.61/4.00  --inst_dismatching                      true
% 27.61/4.00  --inst_eager_unprocessed_to_passive     true
% 27.61/4.00  --inst_prop_sim_given                   true
% 27.61/4.00  --inst_prop_sim_new                     false
% 27.61/4.00  --inst_subs_new                         false
% 27.61/4.00  --inst_eq_res_simp                      false
% 27.61/4.00  --inst_subs_given                       false
% 27.61/4.00  --inst_orphan_elimination               true
% 27.61/4.00  --inst_learning_loop_flag               true
% 27.61/4.00  --inst_learning_start                   3000
% 27.61/4.00  --inst_learning_factor                  2
% 27.61/4.00  --inst_start_prop_sim_after_learn       3
% 27.61/4.00  --inst_sel_renew                        solver
% 27.61/4.00  --inst_lit_activity_flag                true
% 27.61/4.00  --inst_restr_to_given                   false
% 27.61/4.00  --inst_activity_threshold               500
% 27.61/4.00  --inst_out_proof                        true
% 27.61/4.00  
% 27.61/4.00  ------ Resolution Options
% 27.61/4.00  
% 27.61/4.00  --resolution_flag                       false
% 27.61/4.00  --res_lit_sel                           adaptive
% 27.61/4.00  --res_lit_sel_side                      none
% 27.61/4.00  --res_ordering                          kbo
% 27.61/4.00  --res_to_prop_solver                    active
% 27.61/4.00  --res_prop_simpl_new                    false
% 27.61/4.00  --res_prop_simpl_given                  true
% 27.61/4.00  --res_passive_queue_type                priority_queues
% 27.61/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.61/4.00  --res_passive_queues_freq               [15;5]
% 27.61/4.00  --res_forward_subs                      full
% 27.61/4.00  --res_backward_subs                     full
% 27.61/4.00  --res_forward_subs_resolution           true
% 27.61/4.00  --res_backward_subs_resolution          true
% 27.61/4.00  --res_orphan_elimination                true
% 27.61/4.00  --res_time_limit                        2.
% 27.61/4.00  --res_out_proof                         true
% 27.61/4.00  
% 27.61/4.00  ------ Superposition Options
% 27.61/4.00  
% 27.61/4.00  --superposition_flag                    true
% 27.61/4.00  --sup_passive_queue_type                priority_queues
% 27.61/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.61/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.61/4.00  --demod_completeness_check              fast
% 27.61/4.00  --demod_use_ground                      true
% 27.61/4.00  --sup_to_prop_solver                    passive
% 27.61/4.00  --sup_prop_simpl_new                    true
% 27.61/4.00  --sup_prop_simpl_given                  true
% 27.61/4.00  --sup_fun_splitting                     true
% 27.61/4.00  --sup_smt_interval                      50000
% 27.61/4.00  
% 27.61/4.00  ------ Superposition Simplification Setup
% 27.61/4.00  
% 27.61/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.61/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.61/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.61/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.61/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.61/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.61/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.61/4.00  --sup_immed_triv                        [TrivRules]
% 27.61/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.61/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.61/4.00  --sup_immed_bw_main                     []
% 27.61/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.61/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.61/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.61/4.00  --sup_input_bw                          []
% 27.61/4.00  
% 27.61/4.00  ------ Combination Options
% 27.61/4.00  
% 27.61/4.00  --comb_res_mult                         3
% 27.61/4.00  --comb_sup_mult                         2
% 27.61/4.00  --comb_inst_mult                        10
% 27.61/4.00  
% 27.61/4.00  ------ Debug Options
% 27.61/4.00  
% 27.61/4.00  --dbg_backtrace                         false
% 27.61/4.00  --dbg_dump_prop_clauses                 false
% 27.61/4.00  --dbg_dump_prop_clauses_file            -
% 27.61/4.00  --dbg_out_stat                          false
% 27.61/4.00  
% 27.61/4.00  
% 27.61/4.00  
% 27.61/4.00  
% 27.61/4.00  ------ Proving...
% 27.61/4.00  
% 27.61/4.00  
% 27.61/4.00  % SZS status Theorem for theBenchmark.p
% 27.61/4.00  
% 27.61/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.61/4.00  
% 27.61/4.00  fof(f8,axiom,(
% 27.61/4.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f48,plain,(
% 27.61/4.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 27.61/4.00    inference(cnf_transformation,[],[f8])).
% 27.61/4.00  
% 27.61/4.00  fof(f21,axiom,(
% 27.61/4.00    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f73,plain,(
% 27.61/4.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 27.61/4.00    inference(cnf_transformation,[],[f21])).
% 27.61/4.00  
% 27.61/4.00  fof(f13,axiom,(
% 27.61/4.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f65,plain,(
% 27.61/4.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 27.61/4.00    inference(cnf_transformation,[],[f13])).
% 27.61/4.00  
% 27.61/4.00  fof(f78,plain,(
% 27.61/4.00    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 27.61/4.00    inference(definition_unfolding,[],[f65,f77])).
% 27.61/4.00  
% 27.61/4.00  fof(f14,axiom,(
% 27.61/4.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f66,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.61/4.00    inference(cnf_transformation,[],[f14])).
% 27.61/4.00  
% 27.61/4.00  fof(f15,axiom,(
% 27.61/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f67,plain,(
% 27.61/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.61/4.00    inference(cnf_transformation,[],[f15])).
% 27.61/4.00  
% 27.61/4.00  fof(f77,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 27.61/4.00    inference(definition_unfolding,[],[f66,f67])).
% 27.61/4.00  
% 27.61/4.00  fof(f104,plain,(
% 27.61/4.00    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 27.61/4.00    inference(definition_unfolding,[],[f73,f78,f77])).
% 27.61/4.00  
% 27.61/4.00  fof(f20,axiom,(
% 27.61/4.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f72,plain,(
% 27.61/4.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 27.61/4.00    inference(cnf_transformation,[],[f20])).
% 27.61/4.00  
% 27.61/4.00  fof(f103,plain,(
% 27.61/4.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 27.61/4.00    inference(definition_unfolding,[],[f72,f67,f67])).
% 27.61/4.00  
% 27.61/4.00  fof(f22,conjecture,(
% 27.61/4.00    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f23,negated_conjecture,(
% 27.61/4.00    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 27.61/4.00    inference(negated_conjecture,[],[f22])).
% 27.61/4.00  
% 27.61/4.00  fof(f28,plain,(
% 27.61/4.00    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 27.61/4.00    inference(ennf_transformation,[],[f23])).
% 27.61/4.00  
% 27.61/4.00  fof(f39,plain,(
% 27.61/4.00    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)))),
% 27.61/4.00    introduced(choice_axiom,[])).
% 27.61/4.00  
% 27.61/4.00  fof(f40,plain,(
% 27.61/4.00    sK2 != sK5 & sK2 != sK4 & r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 27.61/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f28,f39])).
% 27.61/4.00  
% 27.61/4.00  fof(f74,plain,(
% 27.61/4.00    r1_tarski(k2_tarski(sK2,sK3),k2_tarski(sK4,sK5))),
% 27.61/4.00    inference(cnf_transformation,[],[f40])).
% 27.61/4.00  
% 27.61/4.00  fof(f105,plain,(
% 27.61/4.00    r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5))),
% 27.61/4.00    inference(definition_unfolding,[],[f74,f77,f77])).
% 27.61/4.00  
% 27.61/4.00  fof(f5,axiom,(
% 27.61/4.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f26,plain,(
% 27.61/4.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 27.61/4.00    inference(ennf_transformation,[],[f5])).
% 27.61/4.00  
% 27.61/4.00  fof(f45,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 27.61/4.00    inference(cnf_transformation,[],[f26])).
% 27.61/4.00  
% 27.61/4.00  fof(f7,axiom,(
% 27.61/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f47,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.61/4.00    inference(cnf_transformation,[],[f7])).
% 27.61/4.00  
% 27.61/4.00  fof(f86,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 27.61/4.00    inference(definition_unfolding,[],[f45,f47])).
% 27.61/4.00  
% 27.61/4.00  fof(f3,axiom,(
% 27.61/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f43,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.61/4.00    inference(cnf_transformation,[],[f3])).
% 27.61/4.00  
% 27.61/4.00  fof(f81,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 27.61/4.00    inference(definition_unfolding,[],[f43,f47])).
% 27.61/4.00  
% 27.61/4.00  fof(f6,axiom,(
% 27.61/4.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f46,plain,(
% 27.61/4.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.61/4.00    inference(cnf_transformation,[],[f6])).
% 27.61/4.00  
% 27.61/4.00  fof(f87,plain,(
% 27.61/4.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 27.61/4.00    inference(definition_unfolding,[],[f46,f47])).
% 27.61/4.00  
% 27.61/4.00  fof(f1,axiom,(
% 27.61/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f41,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.61/4.00    inference(cnf_transformation,[],[f1])).
% 27.61/4.00  
% 27.61/4.00  fof(f83,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.61/4.00    inference(definition_unfolding,[],[f41,f47,f47])).
% 27.61/4.00  
% 27.61/4.00  fof(f4,axiom,(
% 27.61/4.00    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f25,plain,(
% 27.61/4.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 27.61/4.00    inference(ennf_transformation,[],[f4])).
% 27.61/4.00  
% 27.61/4.00  fof(f44,plain,(
% 27.61/4.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 27.61/4.00    inference(cnf_transformation,[],[f25])).
% 27.61/4.00  
% 27.61/4.00  fof(f85,plain,(
% 27.61/4.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 27.61/4.00    inference(definition_unfolding,[],[f44,f47])).
% 27.61/4.00  
% 27.61/4.00  fof(f12,axiom,(
% 27.61/4.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f64,plain,(
% 27.61/4.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.61/4.00    inference(cnf_transformation,[],[f12])).
% 27.61/4.00  
% 27.61/4.00  fof(f9,axiom,(
% 27.61/4.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f49,plain,(
% 27.61/4.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 27.61/4.00    inference(cnf_transformation,[],[f9])).
% 27.61/4.00  
% 27.61/4.00  fof(f82,plain,(
% 27.61/4.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.61/4.00    inference(definition_unfolding,[],[f64,f49,f67,f78])).
% 27.61/4.00  
% 27.61/4.00  fof(f10,axiom,(
% 27.61/4.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f27,plain,(
% 27.61/4.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 27.61/4.00    inference(ennf_transformation,[],[f10])).
% 27.61/4.00  
% 27.61/4.00  fof(f29,plain,(
% 27.61/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.61/4.00    inference(nnf_transformation,[],[f27])).
% 27.61/4.00  
% 27.61/4.00  fof(f30,plain,(
% 27.61/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.61/4.00    inference(flattening,[],[f29])).
% 27.61/4.00  
% 27.61/4.00  fof(f31,plain,(
% 27.61/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.61/4.00    inference(rectify,[],[f30])).
% 27.61/4.00  
% 27.61/4.00  fof(f32,plain,(
% 27.61/4.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 27.61/4.00    introduced(choice_axiom,[])).
% 27.61/4.00  
% 27.61/4.00  fof(f33,plain,(
% 27.61/4.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 27.61/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 27.61/4.00  
% 27.61/4.00  fof(f53,plain,(
% 27.61/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 27.61/4.00    inference(cnf_transformation,[],[f33])).
% 27.61/4.00  
% 27.61/4.00  fof(f92,plain,(
% 27.61/4.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 27.61/4.00    inference(definition_unfolding,[],[f53,f67])).
% 27.61/4.00  
% 27.61/4.00  fof(f106,plain,(
% 27.61/4.00    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 27.61/4.00    inference(equality_resolution,[],[f92])).
% 27.61/4.00  
% 27.61/4.00  fof(f107,plain,(
% 27.61/4.00    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 27.61/4.00    inference(equality_resolution,[],[f106])).
% 27.61/4.00  
% 27.61/4.00  fof(f11,axiom,(
% 27.61/4.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 27.61/4.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.61/4.00  
% 27.61/4.00  fof(f34,plain,(
% 27.61/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.61/4.00    inference(nnf_transformation,[],[f11])).
% 27.61/4.00  
% 27.61/4.00  fof(f35,plain,(
% 27.61/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 27.61/4.00    inference(flattening,[],[f34])).
% 27.61/4.00  
% 27.61/4.00  fof(f36,plain,(
% 27.61/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.61/4.00    inference(rectify,[],[f35])).
% 27.61/4.00  
% 27.61/4.00  fof(f37,plain,(
% 27.61/4.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 27.61/4.00    introduced(choice_axiom,[])).
% 27.61/4.00  
% 27.61/4.00  fof(f38,plain,(
% 27.61/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 27.61/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f36,f37])).
% 27.61/4.00  
% 27.61/4.00  fof(f58,plain,(
% 27.61/4.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 27.61/4.00    inference(cnf_transformation,[],[f38])).
% 27.61/4.00  
% 27.61/4.00  fof(f101,plain,(
% 27.61/4.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 27.61/4.00    inference(definition_unfolding,[],[f58,f77])).
% 27.61/4.00  
% 27.61/4.00  fof(f117,plain,(
% 27.61/4.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 27.61/4.00    inference(equality_resolution,[],[f101])).
% 27.61/4.00  
% 27.61/4.00  fof(f59,plain,(
% 27.61/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 27.61/4.00    inference(cnf_transformation,[],[f38])).
% 27.61/4.00  
% 27.61/4.00  fof(f100,plain,(
% 27.61/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 27.61/4.00    inference(definition_unfolding,[],[f59,f77])).
% 27.61/4.00  
% 27.61/4.00  fof(f115,plain,(
% 27.61/4.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 27.61/4.00    inference(equality_resolution,[],[f100])).
% 27.61/4.00  
% 27.61/4.00  fof(f116,plain,(
% 27.61/4.00    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 27.61/4.00    inference(equality_resolution,[],[f115])).
% 27.61/4.00  
% 27.61/4.00  fof(f76,plain,(
% 27.61/4.00    sK2 != sK5),
% 27.61/4.00    inference(cnf_transformation,[],[f40])).
% 27.61/4.00  
% 27.61/4.00  fof(f75,plain,(
% 27.61/4.00    sK2 != sK4),
% 27.61/4.00    inference(cnf_transformation,[],[f40])).
% 27.61/4.00  
% 27.61/4.00  cnf(c_7,plain,
% 27.61/4.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.61/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_24,plain,
% 27.61/4.00      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
% 27.61/4.00      inference(cnf_transformation,[],[f104]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1154,plain,
% 27.61/4.00      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 27.61/4.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_23,plain,
% 27.61/4.00      ( k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
% 27.61/4.00      inference(cnf_transformation,[],[f103]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_27,negated_conjecture,
% 27.61/4.00      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5)) ),
% 27.61/4.00      inference(cnf_transformation,[],[f105]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1153,plain,
% 27.61/4.00      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top ),
% 27.61/4.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1940,plain,
% 27.61/4.00      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK5,sK4)) = iProver_top ),
% 27.61/4.00      inference(demodulation,[status(thm)],[c_23,c_1153]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_5,plain,
% 27.61/4.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 27.61/4.00      inference(cnf_transformation,[],[f86]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1169,plain,
% 27.61/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 27.61/4.00      | r1_tarski(X0,X1) != iProver_top ),
% 27.61/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_2876,plain,
% 27.61/4.00      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK5,sK4))) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_1940,c_1169]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_0,plain,
% 27.61/4.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.61/4.00      inference(cnf_transformation,[],[f81]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_2880,plain,
% 27.61/4.00      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK2,sK2,sK2,sK3)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK5,sK4)) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_2876,c_0]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_6,plain,
% 27.61/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.61/4.00      inference(cnf_transformation,[],[f87]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1868,plain,
% 27.61/4.00      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1873,plain,
% 27.61/4.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.61/4.00      inference(light_normalisation,[status(thm)],[c_1868,c_7]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1870,plain,
% 27.61/4.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1871,plain,
% 27.61/4.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.61/4.00      inference(light_normalisation,[status(thm)],[c_1870,c_6]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1874,plain,
% 27.61/4.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 27.61/4.00      inference(demodulation,[status(thm)],[c_1873,c_1871]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_2884,plain,
% 27.61/4.00      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k2_enumset1(sK4,sK4,sK5,sK4)) = k1_xboole_0 ),
% 27.61/4.00      inference(demodulation,[status(thm)],[c_2880,c_1874]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_2,plain,
% 27.61/4.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.61/4.00      inference(cnf_transformation,[],[f83]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_4,plain,
% 27.61/4.00      ( r1_tarski(X0,X1)
% 27.61/4.00      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 27.61/4.00      inference(cnf_transformation,[],[f85]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1170,plain,
% 27.61/4.00      ( r1_tarski(X0,X1) = iProver_top
% 27.61/4.00      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top ),
% 27.61/4.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_3852,plain,
% 27.61/4.00      ( r1_tarski(X0,X1) = iProver_top
% 27.61/4.00      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_2,c_1170]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_4019,plain,
% 27.61/4.00      ( r1_tarski(X0,k2_enumset1(sK4,sK4,sK5,sK4)) = iProver_top
% 27.61/4.00      | r1_tarski(X0,k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k1_xboole_0)) != iProver_top ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_2884,c_3852]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_4020,plain,
% 27.61/4.00      ( r1_tarski(X0,k2_enumset1(sK4,sK4,sK5,sK4)) = iProver_top
% 27.61/4.00      | r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top ),
% 27.61/4.00      inference(demodulation,[status(thm)],[c_4019,c_1873]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_4189,plain,
% 27.61/4.00      ( r1_tarski(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK5,sK4)) = iProver_top ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_1154,c_4020]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_4302,plain,
% 27.61/4.00      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK5,sK4))) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_4189,c_1169]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_4305,plain,
% 27.61/4.00      ( k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK5,sK4)) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_4302,c_0]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_4323,plain,
% 27.61/4.00      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK4,sK4,sK5,sK4)) = k1_xboole_0 ),
% 27.61/4.00      inference(demodulation,[status(thm)],[c_4305,c_1874]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1,plain,
% 27.61/4.00      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X1,X2,X3) ),
% 27.61/4.00      inference(cnf_transformation,[],[f82]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_5443,plain,
% 27.61/4.00      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK5,sK4),k1_xboole_0) = k2_enumset1(sK4,sK5,sK4,sK2) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_4323,c_1]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_5986,plain,
% 27.61/4.00      ( k2_enumset1(sK4,sK5,sK4,sK2) = k2_enumset1(sK4,sK4,sK5,sK4) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_7,c_5443]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_2548,plain,
% 27.61/4.00      ( k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X0,X1,X2))) = k2_enumset1(X0,X2,X1,X3) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_23,c_1]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_6358,plain,
% 27.61/4.00      ( k5_xboole_0(k2_enumset1(sK4,sK5,sK4,sK2),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK4,sK5,sK4,sK2))) = k2_enumset1(sK4,sK4,sK5,X0) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_5986,c_2548]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_6172,plain,
% 27.61/4.00      ( k5_xboole_0(k2_enumset1(sK4,sK5,sK4,sK2),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK4,sK5,sK4,sK2))) = k2_enumset1(sK4,sK5,sK4,X0) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_5986,c_1]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_6360,plain,
% 27.61/4.00      ( k2_enumset1(sK4,sK5,sK4,X0) = k2_enumset1(sK4,sK4,sK5,X0) ),
% 27.61/4.00      inference(light_normalisation,[status(thm)],[c_6358,c_6172]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_6359,plain,
% 27.61/4.00      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_2548,c_1]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_7770,plain,
% 27.61/4.00      ( k5_xboole_0(k2_enumset1(X0,X1,X0,X2),k4_xboole_0(k2_enumset1(X3,X3,X3,X3),k2_enumset1(X0,X1,X0,X2))) = k2_enumset1(X0,X1,X2,X3) ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_6359,c_1]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_7970,plain,
% 27.61/4.00      ( k2_enumset1(sK4,sK5,sK2,X0) = k2_enumset1(sK4,sK5,sK4,X0) ),
% 27.61/4.00      inference(demodulation,[status(thm)],[c_7770,c_6172]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_79514,plain,
% 27.61/4.00      ( k2_enumset1(sK4,sK5,sK2,X0) = k2_enumset1(sK4,sK4,sK5,X0) ),
% 27.61/4.00      inference(light_normalisation,[status(thm)],[c_6360,c_6360,c_7970]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_12,plain,
% 27.61/4.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 27.61/4.00      inference(cnf_transformation,[],[f107]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1164,plain,
% 27.61/4.00      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 27.61/4.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_79547,plain,
% 27.61/4.00      ( r2_hidden(X0,k2_enumset1(sK4,sK5,sK2,X0)) = iProver_top ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_79514,c_1164]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_79701,plain,
% 27.61/4.00      ( r2_hidden(sK2,k2_enumset1(sK4,sK5,sK2,sK2)) = iProver_top ),
% 27.61/4.00      inference(instantiation,[status(thm)],[c_79547]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_21,plain,
% 27.61/4.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 27.61/4.00      inference(cnf_transformation,[],[f117]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1155,plain,
% 27.61/4.00      ( X0 = X1
% 27.61/4.00      | X0 = X2
% 27.61/4.00      | r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) != iProver_top ),
% 27.61/4.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_2467,plain,
% 27.61/4.00      ( X0 = X1
% 27.61/4.00      | X2 = X1
% 27.61/4.00      | r2_hidden(X1,k2_enumset1(X2,X2,X0,X2)) != iProver_top ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_23,c_1155]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_6179,plain,
% 27.61/4.00      ( sK4 = X0
% 27.61/4.00      | sK5 = X0
% 27.61/4.00      | r2_hidden(X0,k2_enumset1(sK4,sK5,sK4,sK2)) != iProver_top ),
% 27.61/4.00      inference(superposition,[status(thm)],[c_5986,c_2467]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_72465,plain,
% 27.61/4.00      ( sK4 = X0
% 27.61/4.00      | sK5 = X0
% 27.61/4.00      | r2_hidden(X0,k2_enumset1(sK4,sK5,sK2,sK2)) != iProver_top ),
% 27.61/4.00      inference(demodulation,[status(thm)],[c_6179,c_7970]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_72467,plain,
% 27.61/4.00      ( sK4 = sK2
% 27.61/4.00      | sK5 = sK2
% 27.61/4.00      | r2_hidden(sK2,k2_enumset1(sK4,sK5,sK2,sK2)) != iProver_top ),
% 27.61/4.00      inference(instantiation,[status(thm)],[c_72465]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_878,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1204,plain,
% 27.61/4.00      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 27.61/4.00      inference(instantiation,[status(thm)],[c_878]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1205,plain,
% 27.61/4.00      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 27.61/4.00      inference(instantiation,[status(thm)],[c_1204]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1196,plain,
% 27.61/4.00      ( sK5 != X0 | sK2 != X0 | sK2 = sK5 ),
% 27.61/4.00      inference(instantiation,[status(thm)],[c_878]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_1197,plain,
% 27.61/4.00      ( sK5 != sK2 | sK2 = sK5 | sK2 != sK2 ),
% 27.61/4.00      inference(instantiation,[status(thm)],[c_1196]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_20,plain,
% 27.61/4.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 27.61/4.00      inference(cnf_transformation,[],[f116]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_38,plain,
% 27.61/4.00      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 27.61/4.00      inference(instantiation,[status(thm)],[c_20]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_35,plain,
% 27.61/4.00      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) | sK2 = sK2 ),
% 27.61/4.00      inference(instantiation,[status(thm)],[c_21]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_25,negated_conjecture,
% 27.61/4.00      ( sK2 != sK5 ),
% 27.61/4.00      inference(cnf_transformation,[],[f76]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(c_26,negated_conjecture,
% 27.61/4.00      ( sK2 != sK4 ),
% 27.61/4.00      inference(cnf_transformation,[],[f75]) ).
% 27.61/4.00  
% 27.61/4.00  cnf(contradiction,plain,
% 27.61/4.00      ( $false ),
% 27.61/4.00      inference(minisat,
% 27.61/4.00                [status(thm)],
% 27.61/4.00                [c_79701,c_72467,c_1205,c_1197,c_38,c_35,c_25,c_26]) ).
% 27.61/4.00  
% 27.61/4.00  
% 27.61/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.61/4.00  
% 27.61/4.00  ------                               Statistics
% 27.61/4.00  
% 27.61/4.00  ------ General
% 27.61/4.00  
% 27.61/4.00  abstr_ref_over_cycles:                  0
% 27.61/4.00  abstr_ref_under_cycles:                 0
% 27.61/4.00  gc_basic_clause_elim:                   0
% 27.61/4.00  forced_gc_time:                         0
% 27.61/4.00  parsing_time:                           0.012
% 27.61/4.00  unif_index_cands_time:                  0.
% 27.61/4.00  unif_index_add_time:                    0.
% 27.61/4.00  orderings_time:                         0.
% 27.61/4.00  out_proof_time:                         0.011
% 27.61/4.00  total_time:                             3.367
% 27.61/4.00  num_of_symbols:                         44
% 27.61/4.00  num_of_terms:                           87226
% 27.61/4.00  
% 27.61/4.00  ------ Preprocessing
% 27.61/4.00  
% 27.61/4.00  num_of_splits:                          0
% 27.61/4.00  num_of_split_atoms:                     0
% 27.61/4.00  num_of_reused_defs:                     0
% 27.61/4.00  num_eq_ax_congr_red:                    30
% 27.61/4.00  num_of_sem_filtered_clauses:            1
% 27.61/4.00  num_of_subtypes:                        0
% 27.61/4.00  monotx_restored_types:                  0
% 27.61/4.00  sat_num_of_epr_types:                   0
% 27.61/4.00  sat_num_of_non_cyclic_types:            0
% 27.61/4.00  sat_guarded_non_collapsed_types:        0
% 27.61/4.00  num_pure_diseq_elim:                    0
% 27.61/4.00  simp_replaced_by:                       0
% 27.61/4.00  res_preprocessed:                       99
% 27.61/4.00  prep_upred:                             0
% 27.61/4.00  prep_unflattend:                        48
% 27.61/4.00  smt_new_axioms:                         0
% 27.61/4.00  pred_elim_cands:                        2
% 27.61/4.00  pred_elim:                              0
% 27.61/4.00  pred_elim_cl:                           0
% 27.61/4.00  pred_elim_cycles:                       1
% 27.61/4.00  merged_defs:                            0
% 27.61/4.00  merged_defs_ncl:                        0
% 27.61/4.00  bin_hyper_res:                          0
% 27.61/4.00  prep_cycles:                            3
% 27.61/4.00  pred_elim_time:                         0.016
% 27.61/4.00  splitting_time:                         0.
% 27.61/4.00  sem_filter_time:                        0.
% 27.61/4.00  monotx_time:                            0.
% 27.61/4.00  subtype_inf_time:                       0.
% 27.61/4.00  
% 27.61/4.00  ------ Problem properties
% 27.61/4.00  
% 27.61/4.00  clauses:                                28
% 27.61/4.00  conjectures:                            3
% 27.61/4.00  epr:                                    2
% 27.61/4.00  horn:                                   24
% 27.61/4.00  ground:                                 3
% 27.61/4.00  unary:                                  17
% 27.61/4.00  binary:                                 2
% 27.61/4.00  lits:                                   52
% 27.61/4.00  lits_eq:                                33
% 27.61/4.00  fd_pure:                                0
% 27.61/4.00  fd_pseudo:                              0
% 27.61/4.00  fd_cond:                                0
% 27.61/4.00  fd_pseudo_cond:                         7
% 27.61/4.00  ac_symbols:                             0
% 27.61/4.00  
% 27.61/4.00  ------ Propositional Solver
% 27.61/4.00  
% 27.61/4.00  prop_solver_calls:                      30
% 27.61/4.00  prop_fast_solver_calls:                 1476
% 27.61/4.00  smt_solver_calls:                       0
% 27.61/4.00  smt_fast_solver_calls:                  0
% 27.61/4.00  prop_num_of_clauses:                    24620
% 27.61/4.00  prop_preprocess_simplified:             39059
% 27.61/4.00  prop_fo_subsumed:                       0
% 27.61/4.00  prop_solver_time:                       0.
% 27.61/4.00  smt_solver_time:                        0.
% 27.61/4.00  smt_fast_solver_time:                   0.
% 27.61/4.00  prop_fast_solver_time:                  0.
% 27.61/4.00  prop_unsat_core_time:                   0.002
% 27.61/4.00  
% 27.61/4.00  ------ QBF
% 27.61/4.00  
% 27.61/4.00  qbf_q_res:                              0
% 27.61/4.00  qbf_num_tautologies:                    0
% 27.61/4.00  qbf_prep_cycles:                        0
% 27.61/4.00  
% 27.61/4.00  ------ BMC1
% 27.61/4.00  
% 27.61/4.00  bmc1_current_bound:                     -1
% 27.61/4.00  bmc1_last_solved_bound:                 -1
% 27.61/4.00  bmc1_unsat_core_size:                   -1
% 27.61/4.00  bmc1_unsat_core_parents_size:           -1
% 27.61/4.00  bmc1_merge_next_fun:                    0
% 27.61/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.61/4.00  
% 27.61/4.00  ------ Instantiation
% 27.61/4.00  
% 27.61/4.00  inst_num_of_clauses:                    5499
% 27.61/4.00  inst_num_in_passive:                    1955
% 27.61/4.00  inst_num_in_active:                     1171
% 27.61/4.00  inst_num_in_unprocessed:                2377
% 27.61/4.00  inst_num_of_loops:                      1400
% 27.61/4.00  inst_num_of_learning_restarts:          0
% 27.61/4.00  inst_num_moves_active_passive:          227
% 27.61/4.00  inst_lit_activity:                      0
% 27.61/4.00  inst_lit_activity_moves:                0
% 27.61/4.00  inst_num_tautologies:                   0
% 27.61/4.00  inst_num_prop_implied:                  0
% 27.61/4.00  inst_num_existing_simplified:           0
% 27.61/4.00  inst_num_eq_res_simplified:             0
% 27.61/4.00  inst_num_child_elim:                    0
% 27.61/4.00  inst_num_of_dismatching_blockings:      8915
% 27.61/4.00  inst_num_of_non_proper_insts:           6136
% 27.61/4.00  inst_num_of_duplicates:                 0
% 27.61/4.00  inst_inst_num_from_inst_to_res:         0
% 27.61/4.00  inst_dismatching_checking_time:         0.
% 27.61/4.00  
% 27.61/4.00  ------ Resolution
% 27.61/4.00  
% 27.61/4.00  res_num_of_clauses:                     0
% 27.61/4.00  res_num_in_passive:                     0
% 27.61/4.00  res_num_in_active:                      0
% 27.61/4.00  res_num_of_loops:                       102
% 27.61/4.00  res_forward_subset_subsumed:            2075
% 27.61/4.00  res_backward_subset_subsumed:           10
% 27.61/4.00  res_forward_subsumed:                   8
% 27.61/4.00  res_backward_subsumed:                  0
% 27.61/4.00  res_forward_subsumption_resolution:     0
% 27.61/4.00  res_backward_subsumption_resolution:    0
% 27.61/4.00  res_clause_to_clause_subsumption:       83688
% 27.61/4.00  res_orphan_elimination:                 0
% 27.61/4.00  res_tautology_del:                      234
% 27.61/4.00  res_num_eq_res_simplified:              0
% 27.61/4.00  res_num_sel_changes:                    0
% 27.61/4.00  res_moves_from_active_to_pass:          0
% 27.61/4.00  
% 27.61/4.00  ------ Superposition
% 27.61/4.00  
% 27.61/4.00  sup_time_total:                         0.
% 27.61/4.00  sup_time_generating:                    0.
% 27.61/4.00  sup_time_sim_full:                      0.
% 27.61/4.00  sup_time_sim_immed:                     0.
% 27.61/4.00  
% 27.61/4.00  sup_num_of_clauses:                     6201
% 27.61/4.00  sup_num_in_active:                      241
% 27.61/4.00  sup_num_in_passive:                     5960
% 27.61/4.00  sup_num_of_loops:                       278
% 27.61/4.00  sup_fw_superposition:                   10632
% 27.61/4.00  sup_bw_superposition:                   9055
% 27.61/4.00  sup_immediate_simplified:               5993
% 27.61/4.00  sup_given_eliminated:                   5
% 27.61/4.00  comparisons_done:                       0
% 27.61/4.00  comparisons_avoided:                    1308
% 27.61/4.00  
% 27.61/4.00  ------ Simplifications
% 27.61/4.00  
% 27.61/4.00  
% 27.61/4.00  sim_fw_subset_subsumed:                 64
% 27.61/4.00  sim_bw_subset_subsumed:                 2
% 27.61/4.00  sim_fw_subsumed:                        893
% 27.61/4.00  sim_bw_subsumed:                        35
% 27.61/4.00  sim_fw_subsumption_res:                 0
% 27.61/4.00  sim_bw_subsumption_res:                 0
% 27.61/4.00  sim_tautology_del:                      750
% 27.61/4.00  sim_eq_tautology_del:                   1164
% 27.61/4.00  sim_eq_res_simp:                        4
% 27.61/4.00  sim_fw_demodulated:                     5831
% 27.61/4.00  sim_bw_demodulated:                     66
% 27.61/4.00  sim_light_normalised:                   1869
% 27.61/4.00  sim_joinable_taut:                      0
% 27.61/4.00  sim_joinable_simp:                      0
% 27.61/4.00  sim_ac_normalised:                      0
% 27.61/4.00  sim_smt_subsumption:                    0
% 27.61/4.00  
%------------------------------------------------------------------------------
