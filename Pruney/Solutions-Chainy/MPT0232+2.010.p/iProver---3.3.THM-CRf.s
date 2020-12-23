%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:31:12 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 166 expanded)
%              Number of clauses        :   33 (  35 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  302 ( 481 expanded)
%              Number of equality atoms :  173 ( 320 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK2,sK3) != k1_tarski(sK4)
      & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k2_tarski(sK2,sK3) != k1_tarski(sK4)
    & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f29])).

fof(f56,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f58])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f49,f59])).

fof(f73,plain,(
    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f56,f59,f60])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f60,f60])).

fof(f57,plain,(
    k2_tarski(sK2,sK3) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK3) != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f57,f59,f60])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f79,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f80,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f79])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f77,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f78,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f77])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_626,plain,
    ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_627,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1059,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_626,c_627])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_291,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_801,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X0
    | k3_enumset1(sK2,sK2,sK2,sK2,sK3) != X0
    | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_917,plain,
    ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_enumset1(sK2,sK2,sK2,sK2,sK3)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
    | k3_enumset1(sK2,sK2,sK2,sK2,sK3) != k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_290,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_918,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_1576,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1059,c_21,c_917,c_918])).

cnf(c_15,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_632,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1589,plain,
    ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_632])).

cnf(c_14,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_633,plain,
    ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_638,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_640,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1073,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_638,c_640])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_639,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1072,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_639,c_640])).

cnf(c_1691,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1072])).

cnf(c_3811,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1073,c_1691])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_642,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5884,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3811,c_642])).

cnf(c_6161,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_5884])).

cnf(c_6201,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1589,c_6161])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:37:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.90/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/0.92  
% 1.90/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.90/0.92  
% 1.90/0.92  ------  iProver source info
% 1.90/0.92  
% 1.90/0.92  git: date: 2020-06-30 10:37:57 +0100
% 1.90/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.90/0.92  git: non_committed_changes: false
% 1.90/0.92  git: last_make_outside_of_git: false
% 1.90/0.92  
% 1.90/0.92  ------ 
% 1.90/0.92  
% 1.90/0.92  ------ Input Options
% 1.90/0.92  
% 1.90/0.92  --out_options                           all
% 1.90/0.92  --tptp_safe_out                         true
% 1.90/0.92  --problem_path                          ""
% 1.90/0.92  --include_path                          ""
% 1.90/0.92  --clausifier                            res/vclausify_rel
% 1.90/0.92  --clausifier_options                    --mode clausify
% 1.90/0.92  --stdin                                 false
% 1.90/0.92  --stats_out                             all
% 1.90/0.92  
% 1.90/0.92  ------ General Options
% 1.90/0.92  
% 1.90/0.92  --fof                                   false
% 1.90/0.92  --time_out_real                         305.
% 1.90/0.92  --time_out_virtual                      -1.
% 1.90/0.92  --symbol_type_check                     false
% 1.90/0.92  --clausify_out                          false
% 1.90/0.92  --sig_cnt_out                           false
% 1.90/0.92  --trig_cnt_out                          false
% 1.90/0.92  --trig_cnt_out_tolerance                1.
% 1.90/0.92  --trig_cnt_out_sk_spl                   false
% 1.90/0.92  --abstr_cl_out                          false
% 1.90/0.92  
% 1.90/0.92  ------ Global Options
% 1.90/0.92  
% 1.90/0.92  --schedule                              default
% 1.90/0.92  --add_important_lit                     false
% 1.90/0.92  --prop_solver_per_cl                    1000
% 1.90/0.92  --min_unsat_core                        false
% 1.90/0.92  --soft_assumptions                      false
% 1.90/0.92  --soft_lemma_size                       3
% 1.90/0.92  --prop_impl_unit_size                   0
% 1.90/0.92  --prop_impl_unit                        []
% 1.90/0.92  --share_sel_clauses                     true
% 1.90/0.92  --reset_solvers                         false
% 1.90/0.92  --bc_imp_inh                            [conj_cone]
% 1.90/0.92  --conj_cone_tolerance                   3.
% 1.90/0.92  --extra_neg_conj                        none
% 1.90/0.92  --large_theory_mode                     true
% 1.90/0.92  --prolific_symb_bound                   200
% 1.90/0.92  --lt_threshold                          2000
% 1.90/0.92  --clause_weak_htbl                      true
% 1.90/0.92  --gc_record_bc_elim                     false
% 1.90/0.92  
% 1.90/0.92  ------ Preprocessing Options
% 1.90/0.92  
% 1.90/0.92  --preprocessing_flag                    true
% 1.90/0.92  --time_out_prep_mult                    0.1
% 1.90/0.92  --splitting_mode                        input
% 1.90/0.92  --splitting_grd                         true
% 1.90/0.92  --splitting_cvd                         false
% 1.90/0.92  --splitting_cvd_svl                     false
% 1.90/0.92  --splitting_nvd                         32
% 1.90/0.92  --sub_typing                            true
% 1.90/0.92  --prep_gs_sim                           true
% 1.90/0.92  --prep_unflatten                        true
% 1.90/0.92  --prep_res_sim                          true
% 1.90/0.92  --prep_upred                            true
% 1.90/0.92  --prep_sem_filter                       exhaustive
% 1.90/0.92  --prep_sem_filter_out                   false
% 1.90/0.92  --pred_elim                             true
% 1.90/0.92  --res_sim_input                         true
% 1.90/0.92  --eq_ax_congr_red                       true
% 1.90/0.92  --pure_diseq_elim                       true
% 1.90/0.92  --brand_transform                       false
% 1.90/0.92  --non_eq_to_eq                          false
% 1.90/0.92  --prep_def_merge                        true
% 1.90/0.92  --prep_def_merge_prop_impl              false
% 1.90/0.92  --prep_def_merge_mbd                    true
% 1.90/0.92  --prep_def_merge_tr_red                 false
% 1.90/0.92  --prep_def_merge_tr_cl                  false
% 1.90/0.92  --smt_preprocessing                     true
% 1.90/0.92  --smt_ac_axioms                         fast
% 1.90/0.92  --preprocessed_out                      false
% 1.90/0.92  --preprocessed_stats                    false
% 1.90/0.92  
% 1.90/0.92  ------ Abstraction refinement Options
% 1.90/0.92  
% 1.90/0.92  --abstr_ref                             []
% 1.90/0.92  --abstr_ref_prep                        false
% 1.90/0.92  --abstr_ref_until_sat                   false
% 1.90/0.92  --abstr_ref_sig_restrict                funpre
% 1.90/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/0.92  --abstr_ref_under                       []
% 1.90/0.92  
% 1.90/0.92  ------ SAT Options
% 1.90/0.92  
% 1.90/0.92  --sat_mode                              false
% 1.90/0.92  --sat_fm_restart_options                ""
% 1.90/0.92  --sat_gr_def                            false
% 1.90/0.92  --sat_epr_types                         true
% 1.90/0.92  --sat_non_cyclic_types                  false
% 1.90/0.92  --sat_finite_models                     false
% 1.90/0.92  --sat_fm_lemmas                         false
% 1.90/0.92  --sat_fm_prep                           false
% 1.90/0.92  --sat_fm_uc_incr                        true
% 1.90/0.92  --sat_out_model                         small
% 1.90/0.92  --sat_out_clauses                       false
% 1.90/0.92  
% 1.90/0.92  ------ QBF Options
% 1.90/0.92  
% 1.90/0.92  --qbf_mode                              false
% 1.90/0.92  --qbf_elim_univ                         false
% 1.90/0.92  --qbf_dom_inst                          none
% 1.90/0.92  --qbf_dom_pre_inst                      false
% 1.90/0.92  --qbf_sk_in                             false
% 1.90/0.92  --qbf_pred_elim                         true
% 1.90/0.92  --qbf_split                             512
% 1.90/0.92  
% 1.90/0.92  ------ BMC1 Options
% 1.90/0.92  
% 1.90/0.92  --bmc1_incremental                      false
% 1.90/0.92  --bmc1_axioms                           reachable_all
% 1.90/0.92  --bmc1_min_bound                        0
% 1.90/0.92  --bmc1_max_bound                        -1
% 1.90/0.92  --bmc1_max_bound_default                -1
% 1.90/0.92  --bmc1_symbol_reachability              true
% 1.90/0.92  --bmc1_property_lemmas                  false
% 1.90/0.92  --bmc1_k_induction                      false
% 1.90/0.92  --bmc1_non_equiv_states                 false
% 1.90/0.92  --bmc1_deadlock                         false
% 1.90/0.92  --bmc1_ucm                              false
% 1.90/0.92  --bmc1_add_unsat_core                   none
% 1.90/0.92  --bmc1_unsat_core_children              false
% 1.90/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/0.92  --bmc1_out_stat                         full
% 1.90/0.92  --bmc1_ground_init                      false
% 1.90/0.92  --bmc1_pre_inst_next_state              false
% 1.90/0.92  --bmc1_pre_inst_state                   false
% 1.90/0.92  --bmc1_pre_inst_reach_state             false
% 1.90/0.92  --bmc1_out_unsat_core                   false
% 1.90/0.92  --bmc1_aig_witness_out                  false
% 1.90/0.92  --bmc1_verbose                          false
% 1.90/0.92  --bmc1_dump_clauses_tptp                false
% 1.90/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.90/0.92  --bmc1_dump_file                        -
% 1.90/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.90/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.90/0.92  --bmc1_ucm_extend_mode                  1
% 1.90/0.92  --bmc1_ucm_init_mode                    2
% 1.90/0.92  --bmc1_ucm_cone_mode                    none
% 1.90/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.90/0.92  --bmc1_ucm_relax_model                  4
% 1.90/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.90/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/0.92  --bmc1_ucm_layered_model                none
% 1.90/0.92  --bmc1_ucm_max_lemma_size               10
% 1.90/0.92  
% 1.90/0.92  ------ AIG Options
% 1.90/0.92  
% 1.90/0.92  --aig_mode                              false
% 1.90/0.92  
% 1.90/0.92  ------ Instantiation Options
% 1.90/0.92  
% 1.90/0.92  --instantiation_flag                    true
% 1.90/0.92  --inst_sos_flag                         false
% 1.90/0.92  --inst_sos_phase                        true
% 1.90/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/0.92  --inst_lit_sel_side                     num_symb
% 1.90/0.92  --inst_solver_per_active                1400
% 1.90/0.92  --inst_solver_calls_frac                1.
% 1.90/0.92  --inst_passive_queue_type               priority_queues
% 1.90/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/0.92  --inst_passive_queues_freq              [25;2]
% 1.90/0.92  --inst_dismatching                      true
% 1.90/0.92  --inst_eager_unprocessed_to_passive     true
% 1.90/0.92  --inst_prop_sim_given                   true
% 1.90/0.92  --inst_prop_sim_new                     false
% 1.90/0.92  --inst_subs_new                         false
% 1.90/0.92  --inst_eq_res_simp                      false
% 1.90/0.92  --inst_subs_given                       false
% 1.90/0.92  --inst_orphan_elimination               true
% 1.90/0.92  --inst_learning_loop_flag               true
% 1.90/0.92  --inst_learning_start                   3000
% 1.90/0.92  --inst_learning_factor                  2
% 1.90/0.92  --inst_start_prop_sim_after_learn       3
% 1.90/0.92  --inst_sel_renew                        solver
% 1.90/0.92  --inst_lit_activity_flag                true
% 1.90/0.92  --inst_restr_to_given                   false
% 1.90/0.92  --inst_activity_threshold               500
% 1.90/0.92  --inst_out_proof                        true
% 1.90/0.92  
% 1.90/0.92  ------ Resolution Options
% 1.90/0.92  
% 1.90/0.92  --resolution_flag                       true
% 1.90/0.92  --res_lit_sel                           adaptive
% 1.90/0.92  --res_lit_sel_side                      none
% 1.90/0.92  --res_ordering                          kbo
% 1.90/0.92  --res_to_prop_solver                    active
% 1.90/0.92  --res_prop_simpl_new                    false
% 1.90/0.92  --res_prop_simpl_given                  true
% 1.90/0.92  --res_passive_queue_type                priority_queues
% 1.90/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/0.92  --res_passive_queues_freq               [15;5]
% 1.90/0.92  --res_forward_subs                      full
% 1.90/0.92  --res_backward_subs                     full
% 1.90/0.92  --res_forward_subs_resolution           true
% 1.90/0.92  --res_backward_subs_resolution          true
% 1.90/0.92  --res_orphan_elimination                true
% 1.90/0.92  --res_time_limit                        2.
% 1.90/0.92  --res_out_proof                         true
% 1.90/0.92  
% 1.90/0.92  ------ Superposition Options
% 1.90/0.92  
% 1.90/0.92  --superposition_flag                    true
% 1.90/0.92  --sup_passive_queue_type                priority_queues
% 1.90/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.90/0.92  --demod_completeness_check              fast
% 1.90/0.92  --demod_use_ground                      true
% 1.90/0.92  --sup_to_prop_solver                    passive
% 1.90/0.92  --sup_prop_simpl_new                    true
% 1.90/0.92  --sup_prop_simpl_given                  true
% 1.90/0.92  --sup_fun_splitting                     false
% 1.90/0.92  --sup_smt_interval                      50000
% 1.90/0.92  
% 1.90/0.92  ------ Superposition Simplification Setup
% 1.90/0.92  
% 1.90/0.92  --sup_indices_passive                   []
% 1.90/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.92  --sup_full_bw                           [BwDemod]
% 1.90/0.92  --sup_immed_triv                        [TrivRules]
% 1.90/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.92  --sup_immed_bw_main                     []
% 1.90/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.92  
% 1.90/0.92  ------ Combination Options
% 1.90/0.92  
% 1.90/0.92  --comb_res_mult                         3
% 1.90/0.92  --comb_sup_mult                         2
% 1.90/0.92  --comb_inst_mult                        10
% 1.90/0.92  
% 1.90/0.92  ------ Debug Options
% 1.90/0.92  
% 1.90/0.92  --dbg_backtrace                         false
% 1.90/0.92  --dbg_dump_prop_clauses                 false
% 1.90/0.92  --dbg_dump_prop_clauses_file            -
% 1.90/0.92  --dbg_out_stat                          false
% 1.90/0.92  ------ Parsing...
% 1.90/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.90/0.92  
% 1.90/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.90/0.92  
% 1.90/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.90/0.92  
% 1.90/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.90/0.92  ------ Proving...
% 1.90/0.92  ------ Problem Properties 
% 1.90/0.92  
% 1.90/0.92  
% 1.90/0.92  clauses                                 23
% 1.90/0.92  conjectures                             2
% 1.90/0.92  EPR                                     1
% 1.90/0.92  Horn                                    16
% 1.90/0.92  unary                                   10
% 1.90/0.92  binary                                  3
% 1.90/0.92  lits                                    50
% 1.90/0.92  lits eq                                 21
% 1.90/0.92  fd_pure                                 0
% 1.90/0.92  fd_pseudo                               0
% 1.90/0.92  fd_cond                                 0
% 1.90/0.92  fd_pseudo_cond                          8
% 1.90/0.92  AC symbols                              0
% 1.90/0.92  
% 1.90/0.92  ------ Schedule dynamic 5 is on 
% 1.90/0.92  
% 1.90/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.90/0.92  
% 1.90/0.92  
% 1.90/0.92  ------ 
% 1.90/0.92  Current options:
% 1.90/0.92  ------ 
% 1.90/0.92  
% 1.90/0.92  ------ Input Options
% 1.90/0.92  
% 1.90/0.92  --out_options                           all
% 1.90/0.92  --tptp_safe_out                         true
% 1.90/0.92  --problem_path                          ""
% 1.90/0.92  --include_path                          ""
% 1.90/0.92  --clausifier                            res/vclausify_rel
% 1.90/0.92  --clausifier_options                    --mode clausify
% 1.90/0.92  --stdin                                 false
% 1.90/0.92  --stats_out                             all
% 1.90/0.92  
% 1.90/0.92  ------ General Options
% 1.90/0.92  
% 1.90/0.92  --fof                                   false
% 1.90/0.92  --time_out_real                         305.
% 1.90/0.92  --time_out_virtual                      -1.
% 1.90/0.92  --symbol_type_check                     false
% 1.90/0.92  --clausify_out                          false
% 1.90/0.92  --sig_cnt_out                           false
% 1.90/0.92  --trig_cnt_out                          false
% 1.90/0.92  --trig_cnt_out_tolerance                1.
% 1.90/0.92  --trig_cnt_out_sk_spl                   false
% 1.90/0.92  --abstr_cl_out                          false
% 1.90/0.92  
% 1.90/0.92  ------ Global Options
% 1.90/0.92  
% 1.90/0.92  --schedule                              default
% 1.90/0.92  --add_important_lit                     false
% 1.90/0.92  --prop_solver_per_cl                    1000
% 1.90/0.92  --min_unsat_core                        false
% 1.90/0.92  --soft_assumptions                      false
% 1.90/0.92  --soft_lemma_size                       3
% 1.90/0.92  --prop_impl_unit_size                   0
% 1.90/0.92  --prop_impl_unit                        []
% 1.90/0.92  --share_sel_clauses                     true
% 1.90/0.92  --reset_solvers                         false
% 1.90/0.92  --bc_imp_inh                            [conj_cone]
% 1.90/0.92  --conj_cone_tolerance                   3.
% 1.90/0.92  --extra_neg_conj                        none
% 1.90/0.92  --large_theory_mode                     true
% 1.90/0.92  --prolific_symb_bound                   200
% 1.90/0.92  --lt_threshold                          2000
% 1.90/0.92  --clause_weak_htbl                      true
% 1.90/0.92  --gc_record_bc_elim                     false
% 1.90/0.92  
% 1.90/0.92  ------ Preprocessing Options
% 1.90/0.92  
% 1.90/0.92  --preprocessing_flag                    true
% 1.90/0.92  --time_out_prep_mult                    0.1
% 1.90/0.92  --splitting_mode                        input
% 1.90/0.92  --splitting_grd                         true
% 1.90/0.92  --splitting_cvd                         false
% 1.90/0.92  --splitting_cvd_svl                     false
% 1.90/0.92  --splitting_nvd                         32
% 1.90/0.92  --sub_typing                            true
% 1.90/0.92  --prep_gs_sim                           true
% 1.90/0.92  --prep_unflatten                        true
% 1.90/0.92  --prep_res_sim                          true
% 1.90/0.92  --prep_upred                            true
% 1.90/0.92  --prep_sem_filter                       exhaustive
% 1.90/0.92  --prep_sem_filter_out                   false
% 1.90/0.92  --pred_elim                             true
% 1.90/0.92  --res_sim_input                         true
% 1.90/0.92  --eq_ax_congr_red                       true
% 1.90/0.92  --pure_diseq_elim                       true
% 1.90/0.92  --brand_transform                       false
% 1.90/0.92  --non_eq_to_eq                          false
% 1.90/0.92  --prep_def_merge                        true
% 1.90/0.92  --prep_def_merge_prop_impl              false
% 1.90/0.92  --prep_def_merge_mbd                    true
% 1.90/0.92  --prep_def_merge_tr_red                 false
% 1.90/0.92  --prep_def_merge_tr_cl                  false
% 1.90/0.92  --smt_preprocessing                     true
% 1.90/0.92  --smt_ac_axioms                         fast
% 1.90/0.92  --preprocessed_out                      false
% 1.90/0.92  --preprocessed_stats                    false
% 1.90/0.92  
% 1.90/0.92  ------ Abstraction refinement Options
% 1.90/0.92  
% 1.90/0.92  --abstr_ref                             []
% 1.90/0.92  --abstr_ref_prep                        false
% 1.90/0.92  --abstr_ref_until_sat                   false
% 1.90/0.92  --abstr_ref_sig_restrict                funpre
% 1.90/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/0.92  --abstr_ref_under                       []
% 1.90/0.92  
% 1.90/0.92  ------ SAT Options
% 1.90/0.92  
% 1.90/0.92  --sat_mode                              false
% 1.90/0.92  --sat_fm_restart_options                ""
% 1.90/0.92  --sat_gr_def                            false
% 1.90/0.92  --sat_epr_types                         true
% 1.90/0.92  --sat_non_cyclic_types                  false
% 1.90/0.92  --sat_finite_models                     false
% 1.90/0.92  --sat_fm_lemmas                         false
% 1.90/0.92  --sat_fm_prep                           false
% 1.90/0.92  --sat_fm_uc_incr                        true
% 1.90/0.92  --sat_out_model                         small
% 1.90/0.92  --sat_out_clauses                       false
% 1.90/0.92  
% 1.90/0.92  ------ QBF Options
% 1.90/0.92  
% 1.90/0.92  --qbf_mode                              false
% 1.90/0.92  --qbf_elim_univ                         false
% 1.90/0.92  --qbf_dom_inst                          none
% 1.90/0.92  --qbf_dom_pre_inst                      false
% 1.90/0.92  --qbf_sk_in                             false
% 1.90/0.92  --qbf_pred_elim                         true
% 1.90/0.92  --qbf_split                             512
% 1.90/0.92  
% 1.90/0.92  ------ BMC1 Options
% 1.90/0.92  
% 1.90/0.92  --bmc1_incremental                      false
% 1.90/0.92  --bmc1_axioms                           reachable_all
% 1.90/0.92  --bmc1_min_bound                        0
% 1.90/0.92  --bmc1_max_bound                        -1
% 1.90/0.92  --bmc1_max_bound_default                -1
% 1.90/0.92  --bmc1_symbol_reachability              true
% 1.90/0.92  --bmc1_property_lemmas                  false
% 1.90/0.92  --bmc1_k_induction                      false
% 1.90/0.92  --bmc1_non_equiv_states                 false
% 1.90/0.92  --bmc1_deadlock                         false
% 1.90/0.92  --bmc1_ucm                              false
% 1.90/0.92  --bmc1_add_unsat_core                   none
% 1.90/0.92  --bmc1_unsat_core_children              false
% 1.90/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/0.92  --bmc1_out_stat                         full
% 1.90/0.92  --bmc1_ground_init                      false
% 1.90/0.92  --bmc1_pre_inst_next_state              false
% 1.90/0.92  --bmc1_pre_inst_state                   false
% 1.90/0.92  --bmc1_pre_inst_reach_state             false
% 1.90/0.92  --bmc1_out_unsat_core                   false
% 1.90/0.92  --bmc1_aig_witness_out                  false
% 1.90/0.92  --bmc1_verbose                          false
% 1.90/0.92  --bmc1_dump_clauses_tptp                false
% 1.90/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.90/0.92  --bmc1_dump_file                        -
% 1.90/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.90/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.90/0.92  --bmc1_ucm_extend_mode                  1
% 1.90/0.92  --bmc1_ucm_init_mode                    2
% 1.90/0.92  --bmc1_ucm_cone_mode                    none
% 1.90/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.90/0.92  --bmc1_ucm_relax_model                  4
% 1.90/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.90/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/0.92  --bmc1_ucm_layered_model                none
% 1.90/0.92  --bmc1_ucm_max_lemma_size               10
% 1.90/0.92  
% 1.90/0.92  ------ AIG Options
% 1.90/0.92  
% 1.90/0.92  --aig_mode                              false
% 1.90/0.92  
% 1.90/0.92  ------ Instantiation Options
% 1.90/0.92  
% 1.90/0.92  --instantiation_flag                    true
% 1.90/0.92  --inst_sos_flag                         false
% 1.90/0.92  --inst_sos_phase                        true
% 1.90/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/0.92  --inst_lit_sel_side                     none
% 1.90/0.92  --inst_solver_per_active                1400
% 1.90/0.92  --inst_solver_calls_frac                1.
% 1.90/0.92  --inst_passive_queue_type               priority_queues
% 1.90/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/0.92  --inst_passive_queues_freq              [25;2]
% 1.90/0.92  --inst_dismatching                      true
% 1.90/0.92  --inst_eager_unprocessed_to_passive     true
% 1.90/0.92  --inst_prop_sim_given                   true
% 1.90/0.92  --inst_prop_sim_new                     false
% 1.90/0.92  --inst_subs_new                         false
% 1.90/0.92  --inst_eq_res_simp                      false
% 1.90/0.92  --inst_subs_given                       false
% 1.90/0.92  --inst_orphan_elimination               true
% 1.90/0.92  --inst_learning_loop_flag               true
% 1.90/0.92  --inst_learning_start                   3000
% 1.90/0.92  --inst_learning_factor                  2
% 1.90/0.92  --inst_start_prop_sim_after_learn       3
% 1.90/0.92  --inst_sel_renew                        solver
% 1.90/0.92  --inst_lit_activity_flag                true
% 1.90/0.92  --inst_restr_to_given                   false
% 1.90/0.92  --inst_activity_threshold               500
% 1.90/0.92  --inst_out_proof                        true
% 1.90/0.92  
% 1.90/0.92  ------ Resolution Options
% 1.90/0.92  
% 1.90/0.92  --resolution_flag                       false
% 1.90/0.92  --res_lit_sel                           adaptive
% 1.90/0.92  --res_lit_sel_side                      none
% 1.90/0.92  --res_ordering                          kbo
% 1.90/0.92  --res_to_prop_solver                    active
% 1.90/0.92  --res_prop_simpl_new                    false
% 1.90/0.92  --res_prop_simpl_given                  true
% 1.90/0.92  --res_passive_queue_type                priority_queues
% 1.90/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/0.92  --res_passive_queues_freq               [15;5]
% 1.90/0.92  --res_forward_subs                      full
% 1.90/0.92  --res_backward_subs                     full
% 1.90/0.92  --res_forward_subs_resolution           true
% 1.90/0.92  --res_backward_subs_resolution          true
% 1.90/0.92  --res_orphan_elimination                true
% 1.90/0.92  --res_time_limit                        2.
% 1.90/0.92  --res_out_proof                         true
% 1.90/0.92  
% 1.90/0.92  ------ Superposition Options
% 1.90/0.92  
% 1.90/0.92  --superposition_flag                    true
% 1.90/0.92  --sup_passive_queue_type                priority_queues
% 1.90/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.90/0.92  --demod_completeness_check              fast
% 1.90/0.92  --demod_use_ground                      true
% 1.90/0.92  --sup_to_prop_solver                    passive
% 1.90/0.92  --sup_prop_simpl_new                    true
% 1.90/0.92  --sup_prop_simpl_given                  true
% 1.90/0.92  --sup_fun_splitting                     false
% 1.90/0.92  --sup_smt_interval                      50000
% 1.90/0.92  
% 1.90/0.92  ------ Superposition Simplification Setup
% 1.90/0.92  
% 1.90/0.92  --sup_indices_passive                   []
% 1.90/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.92  --sup_full_bw                           [BwDemod]
% 1.90/0.92  --sup_immed_triv                        [TrivRules]
% 1.90/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.92  --sup_immed_bw_main                     []
% 1.90/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.92  
% 1.90/0.92  ------ Combination Options
% 1.90/0.92  
% 1.90/0.92  --comb_res_mult                         3
% 1.90/0.92  --comb_sup_mult                         2
% 1.90/0.92  --comb_inst_mult                        10
% 1.90/0.92  
% 1.90/0.92  ------ Debug Options
% 1.90/0.92  
% 1.90/0.92  --dbg_backtrace                         false
% 1.90/0.92  --dbg_dump_prop_clauses                 false
% 1.90/0.92  --dbg_dump_prop_clauses_file            -
% 1.90/0.92  --dbg_out_stat                          false
% 1.90/0.92  
% 1.90/0.92  
% 1.90/0.92  
% 1.90/0.92  
% 1.90/0.92  ------ Proving...
% 1.90/0.92  
% 1.90/0.92  
% 1.90/0.92  % SZS status Theorem for theBenchmark.p
% 1.90/0.92  
% 1.90/0.92   Resolution empty clause
% 1.90/0.92  
% 1.90/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 1.90/0.92  
% 1.90/0.92  fof(f12,conjecture,(
% 1.90/0.92    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f13,negated_conjecture,(
% 1.90/0.92    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 1.90/0.92    inference(negated_conjecture,[],[f12])).
% 1.90/0.92  
% 1.90/0.92  fof(f16,plain,(
% 1.90/0.92    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.90/0.92    inference(ennf_transformation,[],[f13])).
% 1.90/0.92  
% 1.90/0.92  fof(f29,plain,(
% 1.90/0.92    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK2,sK3) != k1_tarski(sK4) & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)))),
% 1.90/0.92    introduced(choice_axiom,[])).
% 1.90/0.92  
% 1.90/0.92  fof(f30,plain,(
% 1.90/0.92    k2_tarski(sK2,sK3) != k1_tarski(sK4) & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4))),
% 1.90/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f29])).
% 1.90/0.92  
% 1.90/0.92  fof(f56,plain,(
% 1.90/0.92    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4))),
% 1.90/0.92    inference(cnf_transformation,[],[f30])).
% 1.90/0.92  
% 1.90/0.92  fof(f7,axiom,(
% 1.90/0.92    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f49,plain,(
% 1.90/0.92    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.90/0.92    inference(cnf_transformation,[],[f7])).
% 1.90/0.92  
% 1.90/0.92  fof(f8,axiom,(
% 1.90/0.92    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f50,plain,(
% 1.90/0.92    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.90/0.92    inference(cnf_transformation,[],[f8])).
% 1.90/0.92  
% 1.90/0.92  fof(f9,axiom,(
% 1.90/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f51,plain,(
% 1.90/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.90/0.92    inference(cnf_transformation,[],[f9])).
% 1.90/0.92  
% 1.90/0.92  fof(f10,axiom,(
% 1.90/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f52,plain,(
% 1.90/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.90/0.92    inference(cnf_transformation,[],[f10])).
% 1.90/0.92  
% 1.90/0.92  fof(f58,plain,(
% 1.90/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.90/0.92    inference(definition_unfolding,[],[f51,f52])).
% 1.90/0.92  
% 1.90/0.92  fof(f59,plain,(
% 1.90/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.90/0.92    inference(definition_unfolding,[],[f50,f58])).
% 1.90/0.92  
% 1.90/0.92  fof(f60,plain,(
% 1.90/0.92    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.90/0.92    inference(definition_unfolding,[],[f49,f59])).
% 1.90/0.92  
% 1.90/0.92  fof(f73,plain,(
% 1.90/0.92    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4))),
% 1.90/0.92    inference(definition_unfolding,[],[f56,f59,f60])).
% 1.90/0.92  
% 1.90/0.92  fof(f11,axiom,(
% 1.90/0.92    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f27,plain,(
% 1.90/0.92    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.90/0.92    inference(nnf_transformation,[],[f11])).
% 1.90/0.92  
% 1.90/0.92  fof(f28,plain,(
% 1.90/0.92    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.90/0.92    inference(flattening,[],[f27])).
% 1.90/0.92  
% 1.90/0.92  fof(f53,plain,(
% 1.90/0.92    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.90/0.92    inference(cnf_transformation,[],[f28])).
% 1.90/0.92  
% 1.90/0.92  fof(f71,plain,(
% 1.90/0.92    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 1.90/0.92    inference(definition_unfolding,[],[f53,f60,f60])).
% 1.90/0.92  
% 1.90/0.92  fof(f57,plain,(
% 1.90/0.92    k2_tarski(sK2,sK3) != k1_tarski(sK4)),
% 1.90/0.92    inference(cnf_transformation,[],[f30])).
% 1.90/0.92  
% 1.90/0.92  fof(f72,plain,(
% 1.90/0.92    k3_enumset1(sK2,sK2,sK2,sK2,sK3) != k3_enumset1(sK4,sK4,sK4,sK4,sK4)),
% 1.90/0.92    inference(definition_unfolding,[],[f57,f59,f60])).
% 1.90/0.92  
% 1.90/0.92  fof(f6,axiom,(
% 1.90/0.92    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f15,plain,(
% 1.90/0.92    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.90/0.92    inference(ennf_transformation,[],[f6])).
% 1.90/0.92  
% 1.90/0.92  fof(f22,plain,(
% 1.90/0.92    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.90/0.92    inference(nnf_transformation,[],[f15])).
% 1.90/0.92  
% 1.90/0.92  fof(f23,plain,(
% 1.90/0.92    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.90/0.92    inference(flattening,[],[f22])).
% 1.90/0.92  
% 1.90/0.92  fof(f24,plain,(
% 1.90/0.92    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.90/0.92    inference(rectify,[],[f23])).
% 1.90/0.92  
% 1.90/0.92  fof(f25,plain,(
% 1.90/0.92    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 1.90/0.92    introduced(choice_axiom,[])).
% 1.90/0.92  
% 1.90/0.92  fof(f26,plain,(
% 1.90/0.92    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.90/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 1.90/0.92  
% 1.90/0.92  fof(f43,plain,(
% 1.90/0.92    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.90/0.92    inference(cnf_transformation,[],[f26])).
% 1.90/0.92  
% 1.90/0.92  fof(f66,plain,(
% 1.90/0.92    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.90/0.92    inference(definition_unfolding,[],[f43,f58])).
% 1.90/0.92  
% 1.90/0.92  fof(f79,plain,(
% 1.90/0.92    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X5,X2) != X3) )),
% 1.90/0.92    inference(equality_resolution,[],[f66])).
% 1.90/0.92  
% 1.90/0.92  fof(f80,plain,(
% 1.90/0.92    ( ! [X2,X0,X5] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X5,X2))) )),
% 1.90/0.92    inference(equality_resolution,[],[f79])).
% 1.90/0.92  
% 1.90/0.92  fof(f44,plain,(
% 1.90/0.92    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.90/0.92    inference(cnf_transformation,[],[f26])).
% 1.90/0.92  
% 1.90/0.92  fof(f65,plain,(
% 1.90/0.92    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.90/0.92    inference(definition_unfolding,[],[f44,f58])).
% 1.90/0.92  
% 1.90/0.92  fof(f77,plain,(
% 1.90/0.92    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X5) != X3) )),
% 1.90/0.92    inference(equality_resolution,[],[f65])).
% 1.90/0.92  
% 1.90/0.92  fof(f78,plain,(
% 1.90/0.92    ( ! [X0,X5,X1] : (r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X5))) )),
% 1.90/0.92    inference(equality_resolution,[],[f77])).
% 1.90/0.92  
% 1.90/0.92  fof(f5,axiom,(
% 1.90/0.92    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f40,plain,(
% 1.90/0.92    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.90/0.92    inference(cnf_transformation,[],[f5])).
% 1.90/0.92  
% 1.90/0.92  fof(f3,axiom,(
% 1.90/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f14,plain,(
% 1.90/0.92    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.90/0.92    inference(ennf_transformation,[],[f3])).
% 1.90/0.92  
% 1.90/0.92  fof(f38,plain,(
% 1.90/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.90/0.92    inference(cnf_transformation,[],[f14])).
% 1.90/0.92  
% 1.90/0.92  fof(f1,axiom,(
% 1.90/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f31,plain,(
% 1.90/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.90/0.92    inference(cnf_transformation,[],[f1])).
% 1.90/0.92  
% 1.90/0.92  fof(f4,axiom,(
% 1.90/0.92    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f39,plain,(
% 1.90/0.92    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.90/0.92    inference(cnf_transformation,[],[f4])).
% 1.90/0.92  
% 1.90/0.92  fof(f2,axiom,(
% 1.90/0.92    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.90/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.92  
% 1.90/0.92  fof(f17,plain,(
% 1.90/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.90/0.92    inference(nnf_transformation,[],[f2])).
% 1.90/0.92  
% 1.90/0.92  fof(f18,plain,(
% 1.90/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.90/0.92    inference(flattening,[],[f17])).
% 1.90/0.92  
% 1.90/0.92  fof(f19,plain,(
% 1.90/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.90/0.92    inference(rectify,[],[f18])).
% 1.90/0.92  
% 1.90/0.92  fof(f20,plain,(
% 1.90/0.92    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.90/0.92    introduced(choice_axiom,[])).
% 1.90/0.92  
% 1.90/0.92  fof(f21,plain,(
% 1.90/0.92    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.90/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 1.90/0.92  
% 1.90/0.92  fof(f33,plain,(
% 1.90/0.92    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.90/0.92    inference(cnf_transformation,[],[f21])).
% 1.90/0.92  
% 1.90/0.92  fof(f75,plain,(
% 1.90/0.92    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.90/0.92    inference(equality_resolution,[],[f33])).
% 1.90/0.92  
% 1.90/0.92  cnf(c_22,negated_conjecture,
% 1.90/0.92      ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) ),
% 1.90/0.92      inference(cnf_transformation,[],[f73]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_626,plain,
% 1.90/0.92      ( r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK3),k3_enumset1(sK4,sK4,sK4,sK4,sK4)) = iProver_top ),
% 1.90/0.92      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_20,plain,
% 1.90/0.92      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 1.90/0.92      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 1.90/0.92      | k1_xboole_0 = X0 ),
% 1.90/0.92      inference(cnf_transformation,[],[f71]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_627,plain,
% 1.90/0.92      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 1.90/0.92      | k1_xboole_0 = X1
% 1.90/0.92      | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 1.90/0.92      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_1059,plain,
% 1.90/0.92      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) = k3_enumset1(sK2,sK2,sK2,sK2,sK3)
% 1.90/0.92      | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_626,c_627]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_21,negated_conjecture,
% 1.90/0.92      ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) != k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 1.90/0.92      inference(cnf_transformation,[],[f72]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_291,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_801,plain,
% 1.90/0.92      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != X0
% 1.90/0.92      | k3_enumset1(sK2,sK2,sK2,sK2,sK3) != X0
% 1.90/0.92      | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK4) ),
% 1.90/0.92      inference(instantiation,[status(thm)],[c_291]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_917,plain,
% 1.90/0.92      ( k3_enumset1(sK4,sK4,sK4,sK4,sK4) != k3_enumset1(sK2,sK2,sK2,sK2,sK3)
% 1.90/0.92      | k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k3_enumset1(sK4,sK4,sK4,sK4,sK4)
% 1.90/0.92      | k3_enumset1(sK2,sK2,sK2,sK2,sK3) != k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
% 1.90/0.92      inference(instantiation,[status(thm)],[c_801]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_290,plain,( X0 = X0 ),theory(equality) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_918,plain,
% 1.90/0.92      ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k3_enumset1(sK2,sK2,sK2,sK2,sK3) ),
% 1.90/0.92      inference(instantiation,[status(thm)],[c_290]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_1576,plain,
% 1.90/0.92      ( k3_enumset1(sK2,sK2,sK2,sK2,sK3) = k1_xboole_0 ),
% 1.90/0.92      inference(global_propositional_subsumption,
% 1.90/0.92                [status(thm)],
% 1.90/0.92                [c_1059,c_21,c_917,c_918]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_15,plain,
% 1.90/0.92      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) ),
% 1.90/0.92      inference(cnf_transformation,[],[f80]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_632,plain,
% 1.90/0.92      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X0,X2)) = iProver_top ),
% 1.90/0.92      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_1589,plain,
% 1.90/0.92      ( r2_hidden(sK2,k1_xboole_0) = iProver_top ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_1576,c_632]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_14,plain,
% 1.90/0.92      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
% 1.90/0.92      inference(cnf_transformation,[],[f78]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_633,plain,
% 1.90/0.92      ( r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) = iProver_top ),
% 1.90/0.92      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_9,plain,
% 1.90/0.92      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 1.90/0.92      inference(cnf_transformation,[],[f40]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_638,plain,
% 1.90/0.92      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 1.90/0.92      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_7,plain,
% 1.90/0.92      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.90/0.92      inference(cnf_transformation,[],[f38]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_640,plain,
% 1.90/0.92      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 1.90/0.92      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_1073,plain,
% 1.90/0.92      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_638,c_640]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_0,plain,
% 1.90/0.92      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 1.90/0.92      inference(cnf_transformation,[],[f31]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_8,plain,
% 1.90/0.92      ( r1_tarski(k1_xboole_0,X0) ),
% 1.90/0.92      inference(cnf_transformation,[],[f39]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_639,plain,
% 1.90/0.92      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.90/0.92      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_1072,plain,
% 1.90/0.92      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_639,c_640]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_1691,plain,
% 1.90/0.92      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_0,c_1072]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_3811,plain,
% 1.90/0.92      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_1073,c_1691]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_5,plain,
% 1.90/0.92      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 1.90/0.92      inference(cnf_transformation,[],[f75]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_642,plain,
% 1.90/0.92      ( r2_hidden(X0,X1) != iProver_top
% 1.90/0.92      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 1.90/0.92      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_5884,plain,
% 1.90/0.92      ( r2_hidden(X0,X1) != iProver_top
% 1.90/0.92      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_3811,c_642]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_6161,plain,
% 1.90/0.92      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_633,c_5884]) ).
% 1.90/0.92  
% 1.90/0.92  cnf(c_6201,plain,
% 1.90/0.92      ( $false ),
% 1.90/0.92      inference(superposition,[status(thm)],[c_1589,c_6161]) ).
% 1.90/0.92  
% 1.90/0.92  
% 1.90/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 1.90/0.92  
% 1.90/0.92  ------                               Statistics
% 1.90/0.92  
% 1.90/0.92  ------ General
% 1.90/0.92  
% 1.90/0.92  abstr_ref_over_cycles:                  0
% 1.90/0.92  abstr_ref_under_cycles:                 0
% 1.90/0.92  gc_basic_clause_elim:                   0
% 1.90/0.92  forced_gc_time:                         0
% 1.90/0.92  parsing_time:                           0.008
% 1.90/0.92  unif_index_cands_time:                  0.
% 1.90/0.92  unif_index_add_time:                    0.
% 1.90/0.92  orderings_time:                         0.
% 1.90/0.92  out_proof_time:                         0.005
% 1.90/0.92  total_time:                             0.207
% 1.90/0.92  num_of_symbols:                         42
% 1.90/0.92  num_of_terms:                           8716
% 1.90/0.92  
% 1.90/0.92  ------ Preprocessing
% 1.90/0.92  
% 1.90/0.92  num_of_splits:                          0
% 1.90/0.92  num_of_split_atoms:                     0
% 1.90/0.92  num_of_reused_defs:                     0
% 1.90/0.92  num_eq_ax_congr_red:                    22
% 1.90/0.92  num_of_sem_filtered_clauses:            1
% 1.90/0.92  num_of_subtypes:                        0
% 1.90/0.92  monotx_restored_types:                  0
% 1.90/0.92  sat_num_of_epr_types:                   0
% 1.90/0.92  sat_num_of_non_cyclic_types:            0
% 1.90/0.92  sat_guarded_non_collapsed_types:        0
% 1.90/0.92  num_pure_diseq_elim:                    0
% 1.90/0.92  simp_replaced_by:                       0
% 1.90/0.92  res_preprocessed:                       80
% 1.90/0.92  prep_upred:                             0
% 1.90/0.92  prep_unflattend:                        17
% 1.90/0.92  smt_new_axioms:                         0
% 1.90/0.92  pred_elim_cands:                        2
% 1.90/0.92  pred_elim:                              0
% 1.90/0.92  pred_elim_cl:                           0
% 1.90/0.92  pred_elim_cycles:                       1
% 1.90/0.92  merged_defs:                            0
% 1.90/0.92  merged_defs_ncl:                        0
% 1.90/0.92  bin_hyper_res:                          0
% 1.90/0.92  prep_cycles:                            3
% 1.90/0.92  pred_elim_time:                         0.001
% 1.90/0.92  splitting_time:                         0.
% 1.90/0.92  sem_filter_time:                        0.
% 1.90/0.92  monotx_time:                            0.
% 1.90/0.92  subtype_inf_time:                       0.
% 1.90/0.92  
% 1.90/0.92  ------ Problem properties
% 1.90/0.92  
% 1.90/0.92  clauses:                                23
% 1.90/0.92  conjectures:                            2
% 1.90/0.92  epr:                                    1
% 1.90/0.92  horn:                                   16
% 1.90/0.92  ground:                                 2
% 1.90/0.92  unary:                                  10
% 1.90/0.92  binary:                                 3
% 1.90/0.92  lits:                                   50
% 1.90/0.92  lits_eq:                                21
% 1.90/0.92  fd_pure:                                0
% 1.90/0.92  fd_pseudo:                              0
% 1.90/0.92  fd_cond:                                0
% 1.90/0.92  fd_pseudo_cond:                         8
% 1.90/0.92  ac_symbols:                             0
% 1.90/0.92  
% 1.90/0.92  ------ Propositional Solver
% 1.90/0.92  
% 1.90/0.92  prop_solver_calls:                      23
% 1.90/0.92  prop_fast_solver_calls:                 514
% 1.90/0.92  smt_solver_calls:                       0
% 1.90/0.92  smt_fast_solver_calls:                  0
% 1.90/0.92  prop_num_of_clauses:                    2437
% 1.90/0.92  prop_preprocess_simplified:             7224
% 1.90/0.92  prop_fo_subsumed:                       2
% 1.90/0.92  prop_solver_time:                       0.
% 1.90/0.92  smt_solver_time:                        0.
% 1.90/0.92  smt_fast_solver_time:                   0.
% 1.90/0.92  prop_fast_solver_time:                  0.
% 1.90/0.92  prop_unsat_core_time:                   0.
% 1.90/0.92  
% 1.90/0.92  ------ QBF
% 1.90/0.92  
% 1.90/0.92  qbf_q_res:                              0
% 1.90/0.92  qbf_num_tautologies:                    0
% 1.90/0.92  qbf_prep_cycles:                        0
% 1.90/0.92  
% 1.90/0.92  ------ BMC1
% 1.90/0.92  
% 1.90/0.92  bmc1_current_bound:                     -1
% 1.90/0.92  bmc1_last_solved_bound:                 -1
% 1.90/0.92  bmc1_unsat_core_size:                   -1
% 1.90/0.92  bmc1_unsat_core_parents_size:           -1
% 1.90/0.92  bmc1_merge_next_fun:                    0
% 1.90/0.92  bmc1_unsat_core_clauses_time:           0.
% 1.90/0.92  
% 1.90/0.92  ------ Instantiation
% 1.90/0.92  
% 1.90/0.92  inst_num_of_clauses:                    741
% 1.90/0.92  inst_num_in_passive:                    350
% 1.90/0.92  inst_num_in_active:                     212
% 1.90/0.92  inst_num_in_unprocessed:                179
% 1.90/0.92  inst_num_of_loops:                      260
% 1.90/0.92  inst_num_of_learning_restarts:          0
% 1.90/0.92  inst_num_moves_active_passive:          47
% 1.90/0.92  inst_lit_activity:                      0
% 1.90/0.92  inst_lit_activity_moves:                0
% 1.90/0.92  inst_num_tautologies:                   0
% 1.90/0.92  inst_num_prop_implied:                  0
% 1.90/0.92  inst_num_existing_simplified:           0
% 1.90/0.92  inst_num_eq_res_simplified:             0
% 1.90/0.92  inst_num_child_elim:                    0
% 1.90/0.92  inst_num_of_dismatching_blockings:      293
% 1.90/0.92  inst_num_of_non_proper_insts:           651
% 1.90/0.92  inst_num_of_duplicates:                 0
% 1.90/0.92  inst_inst_num_from_inst_to_res:         0
% 1.90/0.92  inst_dismatching_checking_time:         0.
% 1.90/0.92  
% 1.90/0.92  ------ Resolution
% 1.90/0.92  
% 1.90/0.92  res_num_of_clauses:                     0
% 1.90/0.92  res_num_in_passive:                     0
% 1.90/0.92  res_num_in_active:                      0
% 1.90/0.92  res_num_of_loops:                       83
% 1.90/0.92  res_forward_subset_subsumed:            199
% 1.90/0.92  res_backward_subset_subsumed:           0
% 1.90/0.92  res_forward_subsumed:                   1
% 1.90/0.92  res_backward_subsumed:                  0
% 1.90/0.92  res_forward_subsumption_resolution:     0
% 1.90/0.92  res_backward_subsumption_resolution:    0
% 1.90/0.92  res_clause_to_clause_subsumption:       361
% 1.90/0.92  res_orphan_elimination:                 0
% 1.90/0.92  res_tautology_del:                      16
% 1.90/0.92  res_num_eq_res_simplified:              0
% 1.90/0.92  res_num_sel_changes:                    0
% 1.90/0.92  res_moves_from_active_to_pass:          0
% 1.90/0.92  
% 1.90/0.92  ------ Superposition
% 1.90/0.92  
% 1.90/0.92  sup_time_total:                         0.
% 1.90/0.92  sup_time_generating:                    0.
% 1.90/0.92  sup_time_sim_full:                      0.
% 1.90/0.92  sup_time_sim_immed:                     0.
% 1.90/0.92  
% 1.90/0.92  sup_num_of_clauses:                     88
% 1.90/0.92  sup_num_in_active:                      41
% 1.90/0.92  sup_num_in_passive:                     47
% 1.90/0.92  sup_num_of_loops:                       51
% 1.90/0.92  sup_fw_superposition:                   58
% 1.90/0.92  sup_bw_superposition:                   97
% 1.90/0.92  sup_immediate_simplified:               35
% 1.90/0.92  sup_given_eliminated:                   1
% 1.90/0.92  comparisons_done:                       0
% 1.90/0.92  comparisons_avoided:                    52
% 1.90/0.92  
% 1.90/0.92  ------ Simplifications
% 1.90/0.92  
% 1.90/0.92  
% 1.90/0.92  sim_fw_subset_subsumed:                 20
% 1.90/0.92  sim_bw_subset_subsumed:                 3
% 1.90/0.92  sim_fw_subsumed:                        10
% 1.90/0.92  sim_bw_subsumed:                        5
% 1.90/0.92  sim_fw_subsumption_res:                 1
% 1.90/0.92  sim_bw_subsumption_res:                 0
% 1.90/0.92  sim_tautology_del:                      9
% 1.90/0.92  sim_eq_tautology_del:                   9
% 1.90/0.92  sim_eq_res_simp:                        1
% 1.90/0.92  sim_fw_demodulated:                     3
% 1.90/0.92  sim_bw_demodulated:                     9
% 1.90/0.92  sim_light_normalised:                   0
% 1.90/0.92  sim_joinable_taut:                      0
% 1.90/0.92  sim_joinable_simp:                      0
% 1.90/0.92  sim_ac_normalised:                      0
% 1.90/0.92  sim_smt_subsumption:                    0
% 1.90/0.92  
%------------------------------------------------------------------------------
