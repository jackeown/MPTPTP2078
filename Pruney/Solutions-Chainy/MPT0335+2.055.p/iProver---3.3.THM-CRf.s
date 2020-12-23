%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:34 EST 2020

% Result     : Theorem 35.22s
% Output     : CNFRefutation 35.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 834 expanded)
%              Number of clauses        :   73 ( 136 expanded)
%              Number of leaves         :   18 ( 254 expanded)
%              Depth                    :   19
%              Number of atoms          :  389 (2311 expanded)
%              Number of equality atoms :  174 (1062 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
      & r2_hidden(sK4,sK1)
      & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k3_xboole_0(sK1,sK3) != k1_tarski(sK4)
    & r2_hidden(sK4,sK1)
    & k3_xboole_0(sK2,sK3) = k1_tarski(sK4)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f24])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    k3_xboole_0(sK2,sK3) = k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f63,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f44,f33,f52])).

fof(f46,plain,(
    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f46,f33,f52])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | X0 != X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f33,f51,f52])).

fof(f67,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
      | ~ r2_hidden(X2,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f45,plain,(
    r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f33])).

cnf(c_196,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_195,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_884,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != k4_xboole_0(X1,X3)
    | k4_xboole_0(X0,X2) = X4 ),
    inference(resolution,[status(thm)],[c_196,c_195])).

cnf(c_4132,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X1
    | X5 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X4,X5) ),
    inference(resolution,[status(thm)],[c_884,c_196])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_124,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_125,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(unflattening,[status(thm)],[c_124])).

cnf(c_36065,plain,
    ( X0 != X1
    | X2 != X1
    | X3 != sK1
    | k4_xboole_0(X0,X3) = k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_4132,c_125])).

cnf(c_11,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_39031,plain,
    ( X0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | X1 != sK1
    | k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_36065,c_11])).

cnf(c_39620,plain,
    ( X0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | X2 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | X3 != sK1
    | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X3) ),
    inference(resolution,[status(thm)],[c_39031,c_884])).

cnf(c_79873,plain,
    ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | X1 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | X2 != sK1
    | k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X2) ),
    inference(resolution,[status(thm)],[c_39620,c_11])).

cnf(c_9,negated_conjecture,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_534,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_194,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_743,plain,
    ( sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_481,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_195,c_194])).

cnf(c_1558,plain,
    ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_481,c_11])).

cnf(c_1569,plain,
    ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0 ),
    inference(resolution,[status(thm)],[c_1558,c_195])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_962,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r2_hidden(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2169,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_962])).

cnf(c_197,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_445,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_1233,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | X0 != sK1
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_2271,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1976,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r2_hidden(X3,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))
    | X3 != X2 ),
    inference(resolution,[status(thm)],[c_7,c_197])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1911,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) ),
    inference(resolution,[status(thm)],[c_2,c_9])).

cnf(c_11795,plain,
    ( r2_hidden(X0,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X1)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | ~ r2_hidden(sK4,X1)
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_1976,c_1911])).

cnf(c_528,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_10,negated_conjecture,
    ( r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_359,plain,
    ( r2_hidden(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_361,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_825,plain,
    ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK1)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_359,c_361])).

cnf(c_363,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2038,plain,
    ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_825,c_363])).

cnf(c_2326,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_2038])).

cnf(c_2353,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(X0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2326])).

cnf(c_864,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_197,c_11])).

cnf(c_2361,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_1911,c_864])).

cnf(c_2249,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_6845,plain,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2249])).

cnf(c_2206,plain,
    ( X0 != X1
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != X1
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_9255,plain,
    ( X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = X0
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_2206])).

cnf(c_12643,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11795,c_528,c_743,c_2353,c_2361,c_6845,c_9255])).

cnf(c_12667,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) ),
    inference(resolution,[status(thm)],[c_12643,c_194])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2216,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X1)
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7190,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2) ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_20552,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_7190])).

cnf(c_2239,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2,X3,X4),X4)
    | X4 != X1
    | sK0(X2,X3,X4) != X0 ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_5607,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X3)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | X2 != X3
    | sK0(X0,X1,X2) != sK0(X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_21323,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_5607])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1795,plain,
    ( r2_hidden(sK0(X0,X1,X1),X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 ),
    inference(factoring,[status(thm)],[c_1])).

cnf(c_868,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_197,c_194])).

cnf(c_4062,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X2,X0,X0),X0)
    | r2_hidden(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) ),
    inference(resolution,[status(thm)],[c_1795,c_868])).

cnf(c_15332,plain,
    ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(X2,X0,X0),X0)
    | X1 != k4_xboole_0(X2,k4_xboole_0(X2,X0)) ),
    inference(resolution,[status(thm)],[c_4062,c_864])).

cnf(c_1757,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(resolution,[status(thm)],[c_1,c_9])).

cnf(c_15442,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(X1,sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
    | X0 != k4_xboole_0(X1,k4_xboole_0(X1,sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(resolution,[status(thm)],[c_15332,c_1757])).

cnf(c_2155,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_1757,c_864])).

cnf(c_2595,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(resolution,[status(thm)],[c_2155,c_194])).

cnf(c_1602,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_24421,plain,
    ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_1602])).

cnf(c_27677,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15442,c_2595,c_24421])).

cnf(c_28611,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_66892,plain,
    ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
    | X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
    | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_28611])).

cnf(c_79927,plain,
    ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_79873,c_9,c_125,c_534,c_743,c_1569,c_2169,c_2271,c_2595,c_12667,c_20552,c_21323,c_24421,c_66892])).

cnf(c_81049,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_79927,c_1558])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:31 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 35.22/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.22/5.00  
% 35.22/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.22/5.00  
% 35.22/5.00  ------  iProver source info
% 35.22/5.00  
% 35.22/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.22/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.22/5.00  git: non_committed_changes: false
% 35.22/5.00  git: last_make_outside_of_git: false
% 35.22/5.00  
% 35.22/5.00  ------ 
% 35.22/5.00  ------ Parsing...
% 35.22/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.22/5.00  
% 35.22/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.22/5.00  
% 35.22/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.22/5.00  
% 35.22/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.22/5.00  ------ Proving...
% 35.22/5.00  ------ Problem Properties 
% 35.22/5.00  
% 35.22/5.00  
% 35.22/5.00  clauses                                 12
% 35.22/5.00  conjectures                             3
% 35.22/5.00  EPR                                     1
% 35.22/5.00  Horn                                    9
% 35.22/5.00  unary                                   4
% 35.22/5.00  binary                                  3
% 35.22/5.00  lits                                    26
% 35.22/5.00  lits eq                                 8
% 35.22/5.00  fd_pure                                 0
% 35.22/5.00  fd_pseudo                               0
% 35.22/5.00  fd_cond                                 0
% 35.22/5.00  fd_pseudo_cond                          3
% 35.22/5.00  AC symbols                              0
% 35.22/5.00  
% 35.22/5.00  ------ Input Options Time Limit: Unbounded
% 35.22/5.00  
% 35.22/5.00  
% 35.22/5.00  ------ 
% 35.22/5.00  Current options:
% 35.22/5.00  ------ 
% 35.22/5.00  
% 35.22/5.00  
% 35.22/5.00  
% 35.22/5.00  
% 35.22/5.00  ------ Proving...
% 35.22/5.00  
% 35.22/5.00  
% 35.22/5.00  % SZS status Theorem for theBenchmark.p
% 35.22/5.00  
% 35.22/5.00   Resolution empty clause
% 35.22/5.00  
% 35.22/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.22/5.00  
% 35.22/5.00  fof(f2,axiom,(
% 35.22/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f14,plain,(
% 35.22/5.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.22/5.00    inference(ennf_transformation,[],[f2])).
% 35.22/5.00  
% 35.22/5.00  fof(f32,plain,(
% 35.22/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f14])).
% 35.22/5.00  
% 35.22/5.00  fof(f3,axiom,(
% 35.22/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f33,plain,(
% 35.22/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.22/5.00    inference(cnf_transformation,[],[f3])).
% 35.22/5.00  
% 35.22/5.00  fof(f59,plain,(
% 35.22/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f32,f33])).
% 35.22/5.00  
% 35.22/5.00  fof(f12,conjecture,(
% 35.22/5.00    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f13,negated_conjecture,(
% 35.22/5.00    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 35.22/5.00    inference(negated_conjecture,[],[f12])).
% 35.22/5.00  
% 35.22/5.00  fof(f17,plain,(
% 35.22/5.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 35.22/5.00    inference(ennf_transformation,[],[f13])).
% 35.22/5.00  
% 35.22/5.00  fof(f18,plain,(
% 35.22/5.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 35.22/5.00    inference(flattening,[],[f17])).
% 35.22/5.00  
% 35.22/5.00  fof(f24,plain,(
% 35.22/5.00    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2))),
% 35.22/5.00    introduced(choice_axiom,[])).
% 35.22/5.00  
% 35.22/5.00  fof(f25,plain,(
% 35.22/5.00    k3_xboole_0(sK1,sK3) != k1_tarski(sK4) & r2_hidden(sK4,sK1) & k3_xboole_0(sK2,sK3) = k1_tarski(sK4) & r1_tarski(sK1,sK2)),
% 35.22/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f24])).
% 35.22/5.00  
% 35.22/5.00  fof(f43,plain,(
% 35.22/5.00    r1_tarski(sK1,sK2)),
% 35.22/5.00    inference(cnf_transformation,[],[f25])).
% 35.22/5.00  
% 35.22/5.00  fof(f44,plain,(
% 35.22/5.00    k3_xboole_0(sK2,sK3) = k1_tarski(sK4)),
% 35.22/5.00    inference(cnf_transformation,[],[f25])).
% 35.22/5.00  
% 35.22/5.00  fof(f4,axiom,(
% 35.22/5.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f34,plain,(
% 35.22/5.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f4])).
% 35.22/5.00  
% 35.22/5.00  fof(f5,axiom,(
% 35.22/5.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f35,plain,(
% 35.22/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f5])).
% 35.22/5.00  
% 35.22/5.00  fof(f6,axiom,(
% 35.22/5.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f36,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f6])).
% 35.22/5.00  
% 35.22/5.00  fof(f7,axiom,(
% 35.22/5.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f37,plain,(
% 35.22/5.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f7])).
% 35.22/5.00  
% 35.22/5.00  fof(f8,axiom,(
% 35.22/5.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f38,plain,(
% 35.22/5.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f8])).
% 35.22/5.00  
% 35.22/5.00  fof(f9,axiom,(
% 35.22/5.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f39,plain,(
% 35.22/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f9])).
% 35.22/5.00  
% 35.22/5.00  fof(f10,axiom,(
% 35.22/5.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f40,plain,(
% 35.22/5.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f10])).
% 35.22/5.00  
% 35.22/5.00  fof(f47,plain,(
% 35.22/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f39,f40])).
% 35.22/5.00  
% 35.22/5.00  fof(f48,plain,(
% 35.22/5.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f38,f47])).
% 35.22/5.00  
% 35.22/5.00  fof(f49,plain,(
% 35.22/5.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f37,f48])).
% 35.22/5.00  
% 35.22/5.00  fof(f50,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f36,f49])).
% 35.22/5.00  
% 35.22/5.00  fof(f51,plain,(
% 35.22/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f35,f50])).
% 35.22/5.00  
% 35.22/5.00  fof(f52,plain,(
% 35.22/5.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f34,f51])).
% 35.22/5.00  
% 35.22/5.00  fof(f63,plain,(
% 35.22/5.00    k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 35.22/5.00    inference(definition_unfolding,[],[f44,f33,f52])).
% 35.22/5.00  
% 35.22/5.00  fof(f46,plain,(
% 35.22/5.00    k3_xboole_0(sK1,sK3) != k1_tarski(sK4)),
% 35.22/5.00    inference(cnf_transformation,[],[f25])).
% 35.22/5.00  
% 35.22/5.00  fof(f62,plain,(
% 35.22/5.00    k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 35.22/5.00    inference(definition_unfolding,[],[f46,f33,f52])).
% 35.22/5.00  
% 35.22/5.00  fof(f1,axiom,(
% 35.22/5.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f19,plain,(
% 35.22/5.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.22/5.00    inference(nnf_transformation,[],[f1])).
% 35.22/5.00  
% 35.22/5.00  fof(f20,plain,(
% 35.22/5.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.22/5.00    inference(flattening,[],[f19])).
% 35.22/5.00  
% 35.22/5.00  fof(f21,plain,(
% 35.22/5.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.22/5.00    inference(rectify,[],[f20])).
% 35.22/5.00  
% 35.22/5.00  fof(f22,plain,(
% 35.22/5.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 35.22/5.00    introduced(choice_axiom,[])).
% 35.22/5.00  
% 35.22/5.00  fof(f23,plain,(
% 35.22/5.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 35.22/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 35.22/5.00  
% 35.22/5.00  fof(f31,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f23])).
% 35.22/5.00  
% 35.22/5.00  fof(f53,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f31,f33])).
% 35.22/5.00  
% 35.22/5.00  fof(f27,plain,(
% 35.22/5.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 35.22/5.00    inference(cnf_transformation,[],[f23])).
% 35.22/5.00  
% 35.22/5.00  fof(f57,plain,(
% 35.22/5.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 35.22/5.00    inference(definition_unfolding,[],[f27,f33])).
% 35.22/5.00  
% 35.22/5.00  fof(f65,plain,(
% 35.22/5.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 35.22/5.00    inference(equality_resolution,[],[f57])).
% 35.22/5.00  
% 35.22/5.00  fof(f11,axiom,(
% 35.22/5.00    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 35.22/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.22/5.00  
% 35.22/5.00  fof(f15,plain,(
% 35.22/5.00    ! [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 35.22/5.00    inference(ennf_transformation,[],[f11])).
% 35.22/5.00  
% 35.22/5.00  fof(f16,plain,(
% 35.22/5.00    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 35.22/5.00    inference(flattening,[],[f15])).
% 35.22/5.00  
% 35.22/5.00  fof(f42,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f16])).
% 35.22/5.00  
% 35.22/5.00  fof(f60,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | X0 != X2 | ~r2_hidden(X0,X1)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f42,f33,f51,f52])).
% 35.22/5.00  
% 35.22/5.00  fof(f67,plain,(
% 35.22/5.00    ( ! [X2,X1] : (k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) | ~r2_hidden(X2,X1)) )),
% 35.22/5.00    inference(equality_resolution,[],[f60])).
% 35.22/5.00  
% 35.22/5.00  fof(f29,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f23])).
% 35.22/5.00  
% 35.22/5.00  fof(f55,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f29,f33])).
% 35.22/5.00  
% 35.22/5.00  fof(f45,plain,(
% 35.22/5.00    r2_hidden(sK4,sK1)),
% 35.22/5.00    inference(cnf_transformation,[],[f25])).
% 35.22/5.00  
% 35.22/5.00  fof(f28,plain,(
% 35.22/5.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 35.22/5.00    inference(cnf_transformation,[],[f23])).
% 35.22/5.00  
% 35.22/5.00  fof(f56,plain,(
% 35.22/5.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 35.22/5.00    inference(definition_unfolding,[],[f28,f33])).
% 35.22/5.00  
% 35.22/5.00  fof(f64,plain,(
% 35.22/5.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 35.22/5.00    inference(equality_resolution,[],[f56])).
% 35.22/5.00  
% 35.22/5.00  fof(f30,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.22/5.00    inference(cnf_transformation,[],[f23])).
% 35.22/5.00  
% 35.22/5.00  fof(f54,plain,(
% 35.22/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 35.22/5.00    inference(definition_unfolding,[],[f30,f33])).
% 35.22/5.00  
% 35.22/5.00  cnf(c_196,plain,
% 35.22/5.00      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 35.22/5.00      theory(equality) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_195,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_884,plain,
% 35.22/5.00      ( X0 != X1
% 35.22/5.00      | X2 != X3
% 35.22/5.00      | X4 != k4_xboole_0(X1,X3)
% 35.22/5.00      | k4_xboole_0(X0,X2) = X4 ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_196,c_195]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_4132,plain,
% 35.22/5.00      ( X0 != X1
% 35.22/5.00      | X2 != X3
% 35.22/5.00      | X4 != X1
% 35.22/5.00      | X5 != X3
% 35.22/5.00      | k4_xboole_0(X0,X2) = k4_xboole_0(X4,X5) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_884,c_196]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_6,plain,
% 35.22/5.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 35.22/5.00      inference(cnf_transformation,[],[f59]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_12,negated_conjecture,
% 35.22/5.00      ( r1_tarski(sK1,sK2) ),
% 35.22/5.00      inference(cnf_transformation,[],[f43]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_124,plain,
% 35.22/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | sK2 != X1 | sK1 != X0 ),
% 35.22/5.00      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_125,plain,
% 35.22/5.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK1 ),
% 35.22/5.00      inference(unflattening,[status(thm)],[c_124]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_36065,plain,
% 35.22/5.00      ( X0 != X1
% 35.22/5.00      | X2 != X1
% 35.22/5.00      | X3 != sK1
% 35.22/5.00      | k4_xboole_0(X0,X3) = k4_xboole_0(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_4132,c_125]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_11,negated_conjecture,
% 35.22/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 35.22/5.00      inference(cnf_transformation,[],[f63]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_39031,plain,
% 35.22/5.00      ( X0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 35.22/5.00      | X1 != sK1
% 35.22/5.00      | k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_36065,c_11]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_39620,plain,
% 35.22/5.00      ( X0 != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 35.22/5.00      | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 35.22/5.00      | X2 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 35.22/5.00      | X3 != sK1
% 35.22/5.00      | k4_xboole_0(X1,X2) = k4_xboole_0(X0,X3) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_39031,c_884]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_79873,plain,
% 35.22/5.00      ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 35.22/5.00      | X1 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 35.22/5.00      | X2 != sK1
% 35.22/5.00      | k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),X2) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_39620,c_11]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_9,negated_conjecture,
% 35.22/5.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 35.22/5.00      inference(cnf_transformation,[],[f62]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_0,plain,
% 35.22/5.00      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 35.22/5.00      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 35.22/5.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 35.22/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 35.22/5.00      inference(cnf_transformation,[],[f53]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_534,plain,
% 35.22/5.00      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_0]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_194,plain,( X0 = X0 ),theory(equality) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_743,plain,
% 35.22/5.00      ( sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_194]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_481,plain,
% 35.22/5.00      ( X0 != X1 | X1 = X0 ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_195,c_194]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1558,plain,
% 35.22/5.00      ( k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_481,c_11]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1569,plain,
% 35.22/5.00      ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 35.22/5.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) = X0 ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_1558,c_195]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_4,plain,
% 35.22/5.00      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 35.22/5.00      inference(cnf_transformation,[],[f65]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_962,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 35.22/5.00      | r2_hidden(X0,sK2) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_4]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2169,plain,
% 35.22/5.00      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_962]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_197,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.22/5.00      theory(equality) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_445,plain,
% 35.22/5.00      ( r2_hidden(X0,X1)
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | X1 != sK1 ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_197]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1233,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | X0 != sK1
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_445]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2271,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK1 ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_1233]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_7,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,X1)
% 35.22/5.00      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 35.22/5.00      inference(cnf_transformation,[],[f67]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1976,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,X1)
% 35.22/5.00      | ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
% 35.22/5.00      | r2_hidden(X3,k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)))
% 35.22/5.00      | X3 != X2 ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_7,c_197]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2,plain,
% 35.22/5.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 35.22/5.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 35.22/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 35.22/5.00      inference(cnf_transformation,[],[f55]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1911,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_2,c_9]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_11795,plain,
% 35.22/5.00      ( r2_hidden(X0,k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),X1)))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | ~ r2_hidden(sK4,X1)
% 35.22/5.00      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_1976,c_1911]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_528,plain,
% 35.22/5.00      ( sK1 = sK1 ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_194]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_10,negated_conjecture,
% 35.22/5.00      ( r2_hidden(sK4,sK1) ),
% 35.22/5.00      inference(cnf_transformation,[],[f45]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_359,plain,
% 35.22/5.00      ( r2_hidden(sK4,sK1) = iProver_top ),
% 35.22/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_361,plain,
% 35.22/5.00      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 35.22/5.00      | r2_hidden(X0,X1) != iProver_top ),
% 35.22/5.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_825,plain,
% 35.22/5.00      ( k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k4_xboole_0(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK1)) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
% 35.22/5.00      inference(superposition,[status(thm)],[c_359,c_361]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_363,plain,
% 35.22/5.00      ( r2_hidden(X0,X1) = iProver_top
% 35.22/5.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 35.22/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2038,plain,
% 35.22/5.00      ( r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top
% 35.22/5.00      | r2_hidden(X0,sK1) = iProver_top ),
% 35.22/5.00      inference(superposition,[status(thm)],[c_825,c_363]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2326,plain,
% 35.22/5.00      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 35.22/5.00      | r2_hidden(X0,sK1) = iProver_top ),
% 35.22/5.00      inference(superposition,[status(thm)],[c_11,c_2038]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2353,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | r2_hidden(X0,sK1) ),
% 35.22/5.00      inference(predicate_to_equality_rev,[status(thm)],[c_2326]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_864,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | X1 != X0 ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_197,c_11]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2361,plain,
% 35.22/5.00      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_1911,c_864]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2249,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,X1)
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != X0
% 35.22/5.00      | sK1 != X1 ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_197]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_6845,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,sK1)
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != X0
% 35.22/5.00      | sK1 != sK1 ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_2249]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2206,plain,
% 35.22/5.00      ( X0 != X1
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != X1
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = X0 ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_195]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_9255,plain,
% 35.22/5.00      ( X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = X0
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_2206]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_12643,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1)
% 35.22/5.00      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(global_propositional_subsumption,
% 35.22/5.00                [status(thm)],
% 35.22/5.00                [c_11795,c_528,c_743,c_2353,c_2361,c_6845,c_9255]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_12667,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK1) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_12643,c_194]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_3,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,X1)
% 35.22/5.00      | ~ r2_hidden(X0,X2)
% 35.22/5.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 35.22/5.00      inference(cnf_transformation,[],[f64]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2216,plain,
% 35.22/5.00      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X1)
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_3]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_7190,plain,
% 35.22/5.00      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_2216]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_20552,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK2)
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_7190]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2239,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,X1)
% 35.22/5.00      | r2_hidden(sK0(X2,X3,X4),X4)
% 35.22/5.00      | X4 != X1
% 35.22/5.00      | sK0(X2,X3,X4) != X0 ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_197]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_5607,plain,
% 35.22/5.00      ( ~ r2_hidden(sK0(X0,X1,X2),X3)
% 35.22/5.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 35.22/5.00      | X2 != X3
% 35.22/5.00      | sK0(X0,X1,X2) != sK0(X0,X1,X2) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_2239]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_21323,plain,
% 35.22/5.00      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X0
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_5607]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1,plain,
% 35.22/5.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 35.22/5.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 35.22/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 35.22/5.00      inference(cnf_transformation,[],[f54]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1795,plain,
% 35.22/5.00      ( r2_hidden(sK0(X0,X1,X1),X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 ),
% 35.22/5.00      inference(factoring,[status(thm)],[c_1]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_868,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_197,c_194]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_4062,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,X1)
% 35.22/5.00      | r2_hidden(sK0(X2,X0,X0),X0)
% 35.22/5.00      | r2_hidden(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X1) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_1795,c_868]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_15332,plain,
% 35.22/5.00      ( ~ r2_hidden(X0,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | r2_hidden(X1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | r2_hidden(sK0(X2,X0,X0),X0)
% 35.22/5.00      | X1 != k4_xboole_0(X2,k4_xboole_0(X2,X0)) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_4062,c_864]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1757,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_1,c_9]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_15442,plain,
% 35.22/5.00      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | r2_hidden(sK0(X1,sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
% 35.22/5.00      | X0 != k4_xboole_0(X1,k4_xboole_0(X1,sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_15332,c_1757]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2155,plain,
% 35.22/5.00      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3)
% 35.22/5.00      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_1757,c_864]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_2595,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 35.22/5.00      inference(resolution,[status(thm)],[c_2155,c_194]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_1602,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_4]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_24421,plain,
% 35.22/5.00      ( ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_1602]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_27677,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),sK3) ),
% 35.22/5.00      inference(global_propositional_subsumption,
% 35.22/5.00                [status(thm)],
% 35.22/5.00                [c_15442,c_2595,c_24421]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_28611,plain,
% 35.22/5.00      ( r2_hidden(X0,X1)
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | X0 != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 35.22/5.00      | X1 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_197]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_66892,plain,
% 35.22/5.00      ( r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
% 35.22/5.00      | ~ r2_hidden(sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))
% 35.22/5.00      | X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))
% 35.22/5.00      | sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != sK0(sK1,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 35.22/5.00      inference(instantiation,[status(thm)],[c_28611]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_79927,plain,
% 35.22/5.00      ( X0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 35.22/5.00      inference(global_propositional_subsumption,
% 35.22/5.00                [status(thm)],
% 35.22/5.00                [c_79873,c_9,c_125,c_534,c_743,c_1569,c_2169,c_2271,c_2595,
% 35.22/5.00                 c_12667,c_20552,c_21323,c_24421,c_66892]) ).
% 35.22/5.00  
% 35.22/5.00  cnf(c_81049,plain,
% 35.22/5.00      ( $false ),
% 35.22/5.00      inference(backward_subsumption_resolution,[status(thm)],[c_79927,c_1558]) ).
% 35.22/5.00  
% 35.22/5.00  
% 35.22/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.22/5.00  
% 35.22/5.00  ------                               Statistics
% 35.22/5.00  
% 35.22/5.00  ------ Selected
% 35.22/5.00  
% 35.22/5.00  total_time:                             4.375
% 35.22/5.00  
%------------------------------------------------------------------------------
