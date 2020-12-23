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
% DateTime   : Thu Dec  3 11:33:32 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 172 expanded)
%              Number of clauses        :   25 (  32 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  241 ( 534 expanded)
%              Number of equality atoms :  135 ( 359 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f67,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f19])).

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
    inference(flattening,[],[f28])).

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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f86,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f75])).

fof(f87,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK2,sK4)
      & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r2_hidden(sK2,sK4)
    & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f33])).

fof(f61,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f82,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f83,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f82])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_14,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_559,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_727,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_559])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_557,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_555,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_567,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1747,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r1_tarski(sK4,k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_567])).

cnf(c_1765,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r2_hidden(sK4,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_1747])).

cnf(c_12,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_561,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_878,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_561])).

cnf(c_1856,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1765,c_878])).

cnf(c_1858,plain,
    ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1856,c_557])).

cnf(c_2423,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_1858])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_568,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11361,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_727,c_568])).

cnf(c_16424,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2423,c_11361])).

cnf(c_19,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16424,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.37/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.37/1.50  
% 7.37/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.37/1.50  
% 7.37/1.50  ------  iProver source info
% 7.37/1.50  
% 7.37/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.37/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.37/1.50  git: non_committed_changes: false
% 7.37/1.50  git: last_make_outside_of_git: false
% 7.37/1.50  
% 7.37/1.50  ------ 
% 7.37/1.50  
% 7.37/1.50  ------ Input Options
% 7.37/1.50  
% 7.37/1.50  --out_options                           all
% 7.37/1.50  --tptp_safe_out                         true
% 7.37/1.50  --problem_path                          ""
% 7.37/1.50  --include_path                          ""
% 7.37/1.50  --clausifier                            res/vclausify_rel
% 7.37/1.50  --clausifier_options                    --mode clausify
% 7.37/1.50  --stdin                                 false
% 7.37/1.50  --stats_out                             all
% 7.37/1.50  
% 7.37/1.50  ------ General Options
% 7.37/1.50  
% 7.37/1.50  --fof                                   false
% 7.37/1.50  --time_out_real                         305.
% 7.37/1.50  --time_out_virtual                      -1.
% 7.37/1.50  --symbol_type_check                     false
% 7.37/1.50  --clausify_out                          false
% 7.37/1.50  --sig_cnt_out                           false
% 7.37/1.50  --trig_cnt_out                          false
% 7.37/1.50  --trig_cnt_out_tolerance                1.
% 7.37/1.50  --trig_cnt_out_sk_spl                   false
% 7.37/1.50  --abstr_cl_out                          false
% 7.37/1.50  
% 7.37/1.50  ------ Global Options
% 7.37/1.50  
% 7.37/1.50  --schedule                              default
% 7.37/1.50  --add_important_lit                     false
% 7.37/1.50  --prop_solver_per_cl                    1000
% 7.37/1.50  --min_unsat_core                        false
% 7.37/1.50  --soft_assumptions                      false
% 7.37/1.50  --soft_lemma_size                       3
% 7.37/1.50  --prop_impl_unit_size                   0
% 7.37/1.50  --prop_impl_unit                        []
% 7.37/1.50  --share_sel_clauses                     true
% 7.37/1.50  --reset_solvers                         false
% 7.37/1.50  --bc_imp_inh                            [conj_cone]
% 7.37/1.50  --conj_cone_tolerance                   3.
% 7.37/1.50  --extra_neg_conj                        none
% 7.37/1.50  --large_theory_mode                     true
% 7.37/1.50  --prolific_symb_bound                   200
% 7.37/1.50  --lt_threshold                          2000
% 7.37/1.50  --clause_weak_htbl                      true
% 7.37/1.50  --gc_record_bc_elim                     false
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing Options
% 7.37/1.50  
% 7.37/1.50  --preprocessing_flag                    true
% 7.37/1.50  --time_out_prep_mult                    0.1
% 7.37/1.50  --splitting_mode                        input
% 7.37/1.50  --splitting_grd                         true
% 7.37/1.50  --splitting_cvd                         false
% 7.37/1.50  --splitting_cvd_svl                     false
% 7.37/1.50  --splitting_nvd                         32
% 7.37/1.50  --sub_typing                            true
% 7.37/1.50  --prep_gs_sim                           true
% 7.37/1.50  --prep_unflatten                        true
% 7.37/1.50  --prep_res_sim                          true
% 7.37/1.50  --prep_upred                            true
% 7.37/1.50  --prep_sem_filter                       exhaustive
% 7.37/1.50  --prep_sem_filter_out                   false
% 7.37/1.50  --pred_elim                             true
% 7.37/1.50  --res_sim_input                         true
% 7.37/1.50  --eq_ax_congr_red                       true
% 7.37/1.50  --pure_diseq_elim                       true
% 7.37/1.50  --brand_transform                       false
% 7.37/1.50  --non_eq_to_eq                          false
% 7.37/1.50  --prep_def_merge                        true
% 7.37/1.50  --prep_def_merge_prop_impl              false
% 7.37/1.50  --prep_def_merge_mbd                    true
% 7.37/1.50  --prep_def_merge_tr_red                 false
% 7.37/1.50  --prep_def_merge_tr_cl                  false
% 7.37/1.50  --smt_preprocessing                     true
% 7.37/1.50  --smt_ac_axioms                         fast
% 7.37/1.50  --preprocessed_out                      false
% 7.37/1.50  --preprocessed_stats                    false
% 7.37/1.50  
% 7.37/1.50  ------ Abstraction refinement Options
% 7.37/1.50  
% 7.37/1.50  --abstr_ref                             []
% 7.37/1.50  --abstr_ref_prep                        false
% 7.37/1.50  --abstr_ref_until_sat                   false
% 7.37/1.50  --abstr_ref_sig_restrict                funpre
% 7.37/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.50  --abstr_ref_under                       []
% 7.37/1.50  
% 7.37/1.50  ------ SAT Options
% 7.37/1.50  
% 7.37/1.50  --sat_mode                              false
% 7.37/1.50  --sat_fm_restart_options                ""
% 7.37/1.50  --sat_gr_def                            false
% 7.37/1.50  --sat_epr_types                         true
% 7.37/1.50  --sat_non_cyclic_types                  false
% 7.37/1.50  --sat_finite_models                     false
% 7.37/1.50  --sat_fm_lemmas                         false
% 7.37/1.50  --sat_fm_prep                           false
% 7.37/1.50  --sat_fm_uc_incr                        true
% 7.37/1.50  --sat_out_model                         small
% 7.37/1.50  --sat_out_clauses                       false
% 7.37/1.50  
% 7.37/1.50  ------ QBF Options
% 7.37/1.50  
% 7.37/1.50  --qbf_mode                              false
% 7.37/1.50  --qbf_elim_univ                         false
% 7.37/1.50  --qbf_dom_inst                          none
% 7.37/1.50  --qbf_dom_pre_inst                      false
% 7.37/1.50  --qbf_sk_in                             false
% 7.37/1.50  --qbf_pred_elim                         true
% 7.37/1.50  --qbf_split                             512
% 7.37/1.50  
% 7.37/1.50  ------ BMC1 Options
% 7.37/1.50  
% 7.37/1.50  --bmc1_incremental                      false
% 7.37/1.50  --bmc1_axioms                           reachable_all
% 7.37/1.50  --bmc1_min_bound                        0
% 7.37/1.50  --bmc1_max_bound                        -1
% 7.37/1.50  --bmc1_max_bound_default                -1
% 7.37/1.50  --bmc1_symbol_reachability              true
% 7.37/1.50  --bmc1_property_lemmas                  false
% 7.37/1.50  --bmc1_k_induction                      false
% 7.37/1.50  --bmc1_non_equiv_states                 false
% 7.37/1.50  --bmc1_deadlock                         false
% 7.37/1.50  --bmc1_ucm                              false
% 7.37/1.50  --bmc1_add_unsat_core                   none
% 7.37/1.50  --bmc1_unsat_core_children              false
% 7.37/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.50  --bmc1_out_stat                         full
% 7.37/1.50  --bmc1_ground_init                      false
% 7.37/1.50  --bmc1_pre_inst_next_state              false
% 7.37/1.50  --bmc1_pre_inst_state                   false
% 7.37/1.50  --bmc1_pre_inst_reach_state             false
% 7.37/1.50  --bmc1_out_unsat_core                   false
% 7.37/1.50  --bmc1_aig_witness_out                  false
% 7.37/1.50  --bmc1_verbose                          false
% 7.37/1.50  --bmc1_dump_clauses_tptp                false
% 7.37/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.50  --bmc1_dump_file                        -
% 7.37/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.50  --bmc1_ucm_extend_mode                  1
% 7.37/1.50  --bmc1_ucm_init_mode                    2
% 7.37/1.50  --bmc1_ucm_cone_mode                    none
% 7.37/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.50  --bmc1_ucm_relax_model                  4
% 7.37/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.50  --bmc1_ucm_layered_model                none
% 7.37/1.50  --bmc1_ucm_max_lemma_size               10
% 7.37/1.50  
% 7.37/1.50  ------ AIG Options
% 7.37/1.50  
% 7.37/1.50  --aig_mode                              false
% 7.37/1.50  
% 7.37/1.50  ------ Instantiation Options
% 7.37/1.50  
% 7.37/1.50  --instantiation_flag                    true
% 7.37/1.50  --inst_sos_flag                         false
% 7.37/1.50  --inst_sos_phase                        true
% 7.37/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.50  --inst_lit_sel_side                     num_symb
% 7.37/1.50  --inst_solver_per_active                1400
% 7.37/1.50  --inst_solver_calls_frac                1.
% 7.37/1.50  --inst_passive_queue_type               priority_queues
% 7.37/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.50  --inst_passive_queues_freq              [25;2]
% 7.37/1.50  --inst_dismatching                      true
% 7.37/1.50  --inst_eager_unprocessed_to_passive     true
% 7.37/1.50  --inst_prop_sim_given                   true
% 7.37/1.50  --inst_prop_sim_new                     false
% 7.37/1.50  --inst_subs_new                         false
% 7.37/1.50  --inst_eq_res_simp                      false
% 7.37/1.50  --inst_subs_given                       false
% 7.37/1.50  --inst_orphan_elimination               true
% 7.37/1.50  --inst_learning_loop_flag               true
% 7.37/1.50  --inst_learning_start                   3000
% 7.37/1.50  --inst_learning_factor                  2
% 7.37/1.50  --inst_start_prop_sim_after_learn       3
% 7.37/1.50  --inst_sel_renew                        solver
% 7.37/1.50  --inst_lit_activity_flag                true
% 7.37/1.50  --inst_restr_to_given                   false
% 7.37/1.50  --inst_activity_threshold               500
% 7.37/1.50  --inst_out_proof                        true
% 7.37/1.50  
% 7.37/1.50  ------ Resolution Options
% 7.37/1.50  
% 7.37/1.50  --resolution_flag                       true
% 7.37/1.50  --res_lit_sel                           adaptive
% 7.37/1.50  --res_lit_sel_side                      none
% 7.37/1.50  --res_ordering                          kbo
% 7.37/1.50  --res_to_prop_solver                    active
% 7.37/1.50  --res_prop_simpl_new                    false
% 7.37/1.50  --res_prop_simpl_given                  true
% 7.37/1.50  --res_passive_queue_type                priority_queues
% 7.37/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.50  --res_passive_queues_freq               [15;5]
% 7.37/1.50  --res_forward_subs                      full
% 7.37/1.50  --res_backward_subs                     full
% 7.37/1.50  --res_forward_subs_resolution           true
% 7.37/1.50  --res_backward_subs_resolution          true
% 7.37/1.50  --res_orphan_elimination                true
% 7.37/1.50  --res_time_limit                        2.
% 7.37/1.50  --res_out_proof                         true
% 7.37/1.50  
% 7.37/1.50  ------ Superposition Options
% 7.37/1.50  
% 7.37/1.50  --superposition_flag                    true
% 7.37/1.50  --sup_passive_queue_type                priority_queues
% 7.37/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.50  --demod_completeness_check              fast
% 7.37/1.50  --demod_use_ground                      true
% 7.37/1.50  --sup_to_prop_solver                    passive
% 7.37/1.50  --sup_prop_simpl_new                    true
% 7.37/1.50  --sup_prop_simpl_given                  true
% 7.37/1.50  --sup_fun_splitting                     false
% 7.37/1.50  --sup_smt_interval                      50000
% 7.37/1.50  
% 7.37/1.50  ------ Superposition Simplification Setup
% 7.37/1.50  
% 7.37/1.50  --sup_indices_passive                   []
% 7.37/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.50  --sup_full_bw                           [BwDemod]
% 7.37/1.50  --sup_immed_triv                        [TrivRules]
% 7.37/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.50  --sup_immed_bw_main                     []
% 7.37/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.50  
% 7.37/1.50  ------ Combination Options
% 7.37/1.50  
% 7.37/1.50  --comb_res_mult                         3
% 7.37/1.50  --comb_sup_mult                         2
% 7.37/1.50  --comb_inst_mult                        10
% 7.37/1.50  
% 7.37/1.50  ------ Debug Options
% 7.37/1.50  
% 7.37/1.50  --dbg_backtrace                         false
% 7.37/1.50  --dbg_dump_prop_clauses                 false
% 7.37/1.50  --dbg_dump_prop_clauses_file            -
% 7.37/1.50  --dbg_out_stat                          false
% 7.37/1.50  ------ Parsing...
% 7.37/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.37/1.50  ------ Proving...
% 7.37/1.50  ------ Problem Properties 
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  clauses                                 20
% 7.37/1.50  conjectures                             2
% 7.37/1.50  EPR                                     4
% 7.37/1.50  Horn                                    17
% 7.37/1.50  unary                                   10
% 7.37/1.50  binary                                  3
% 7.37/1.50  lits                                    40
% 7.37/1.50  lits eq                                 18
% 7.37/1.50  fd_pure                                 0
% 7.37/1.50  fd_pseudo                               0
% 7.37/1.50  fd_cond                                 0
% 7.37/1.50  fd_pseudo_cond                          5
% 7.37/1.50  AC symbols                              0
% 7.37/1.50  
% 7.37/1.50  ------ Schedule dynamic 5 is on 
% 7.37/1.50  
% 7.37/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  ------ 
% 7.37/1.50  Current options:
% 7.37/1.50  ------ 
% 7.37/1.50  
% 7.37/1.50  ------ Input Options
% 7.37/1.50  
% 7.37/1.50  --out_options                           all
% 7.37/1.50  --tptp_safe_out                         true
% 7.37/1.50  --problem_path                          ""
% 7.37/1.50  --include_path                          ""
% 7.37/1.50  --clausifier                            res/vclausify_rel
% 7.37/1.50  --clausifier_options                    --mode clausify
% 7.37/1.50  --stdin                                 false
% 7.37/1.50  --stats_out                             all
% 7.37/1.50  
% 7.37/1.50  ------ General Options
% 7.37/1.50  
% 7.37/1.50  --fof                                   false
% 7.37/1.50  --time_out_real                         305.
% 7.37/1.50  --time_out_virtual                      -1.
% 7.37/1.50  --symbol_type_check                     false
% 7.37/1.50  --clausify_out                          false
% 7.37/1.50  --sig_cnt_out                           false
% 7.37/1.50  --trig_cnt_out                          false
% 7.37/1.50  --trig_cnt_out_tolerance                1.
% 7.37/1.50  --trig_cnt_out_sk_spl                   false
% 7.37/1.50  --abstr_cl_out                          false
% 7.37/1.50  
% 7.37/1.50  ------ Global Options
% 7.37/1.50  
% 7.37/1.50  --schedule                              default
% 7.37/1.50  --add_important_lit                     false
% 7.37/1.50  --prop_solver_per_cl                    1000
% 7.37/1.50  --min_unsat_core                        false
% 7.37/1.50  --soft_assumptions                      false
% 7.37/1.50  --soft_lemma_size                       3
% 7.37/1.50  --prop_impl_unit_size                   0
% 7.37/1.50  --prop_impl_unit                        []
% 7.37/1.50  --share_sel_clauses                     true
% 7.37/1.50  --reset_solvers                         false
% 7.37/1.50  --bc_imp_inh                            [conj_cone]
% 7.37/1.50  --conj_cone_tolerance                   3.
% 7.37/1.50  --extra_neg_conj                        none
% 7.37/1.50  --large_theory_mode                     true
% 7.37/1.50  --prolific_symb_bound                   200
% 7.37/1.50  --lt_threshold                          2000
% 7.37/1.50  --clause_weak_htbl                      true
% 7.37/1.50  --gc_record_bc_elim                     false
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing Options
% 7.37/1.50  
% 7.37/1.50  --preprocessing_flag                    true
% 7.37/1.50  --time_out_prep_mult                    0.1
% 7.37/1.50  --splitting_mode                        input
% 7.37/1.50  --splitting_grd                         true
% 7.37/1.50  --splitting_cvd                         false
% 7.37/1.50  --splitting_cvd_svl                     false
% 7.37/1.50  --splitting_nvd                         32
% 7.37/1.50  --sub_typing                            true
% 7.37/1.50  --prep_gs_sim                           true
% 7.37/1.50  --prep_unflatten                        true
% 7.37/1.50  --prep_res_sim                          true
% 7.37/1.50  --prep_upred                            true
% 7.37/1.50  --prep_sem_filter                       exhaustive
% 7.37/1.50  --prep_sem_filter_out                   false
% 7.37/1.50  --pred_elim                             true
% 7.37/1.50  --res_sim_input                         true
% 7.37/1.50  --eq_ax_congr_red                       true
% 7.37/1.50  --pure_diseq_elim                       true
% 7.37/1.50  --brand_transform                       false
% 7.37/1.50  --non_eq_to_eq                          false
% 7.37/1.50  --prep_def_merge                        true
% 7.37/1.50  --prep_def_merge_prop_impl              false
% 7.37/1.50  --prep_def_merge_mbd                    true
% 7.37/1.50  --prep_def_merge_tr_red                 false
% 7.37/1.50  --prep_def_merge_tr_cl                  false
% 7.37/1.50  --smt_preprocessing                     true
% 7.37/1.50  --smt_ac_axioms                         fast
% 7.37/1.50  --preprocessed_out                      false
% 7.37/1.50  --preprocessed_stats                    false
% 7.37/1.50  
% 7.37/1.50  ------ Abstraction refinement Options
% 7.37/1.50  
% 7.37/1.50  --abstr_ref                             []
% 7.37/1.50  --abstr_ref_prep                        false
% 7.37/1.50  --abstr_ref_until_sat                   false
% 7.37/1.50  --abstr_ref_sig_restrict                funpre
% 7.37/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.50  --abstr_ref_under                       []
% 7.37/1.50  
% 7.37/1.50  ------ SAT Options
% 7.37/1.50  
% 7.37/1.50  --sat_mode                              false
% 7.37/1.50  --sat_fm_restart_options                ""
% 7.37/1.50  --sat_gr_def                            false
% 7.37/1.50  --sat_epr_types                         true
% 7.37/1.50  --sat_non_cyclic_types                  false
% 7.37/1.50  --sat_finite_models                     false
% 7.37/1.50  --sat_fm_lemmas                         false
% 7.37/1.50  --sat_fm_prep                           false
% 7.37/1.50  --sat_fm_uc_incr                        true
% 7.37/1.50  --sat_out_model                         small
% 7.37/1.50  --sat_out_clauses                       false
% 7.37/1.50  
% 7.37/1.50  ------ QBF Options
% 7.37/1.50  
% 7.37/1.50  --qbf_mode                              false
% 7.37/1.50  --qbf_elim_univ                         false
% 7.37/1.50  --qbf_dom_inst                          none
% 7.37/1.50  --qbf_dom_pre_inst                      false
% 7.37/1.50  --qbf_sk_in                             false
% 7.37/1.50  --qbf_pred_elim                         true
% 7.37/1.50  --qbf_split                             512
% 7.37/1.50  
% 7.37/1.50  ------ BMC1 Options
% 7.37/1.50  
% 7.37/1.50  --bmc1_incremental                      false
% 7.37/1.50  --bmc1_axioms                           reachable_all
% 7.37/1.50  --bmc1_min_bound                        0
% 7.37/1.50  --bmc1_max_bound                        -1
% 7.37/1.50  --bmc1_max_bound_default                -1
% 7.37/1.50  --bmc1_symbol_reachability              true
% 7.37/1.50  --bmc1_property_lemmas                  false
% 7.37/1.50  --bmc1_k_induction                      false
% 7.37/1.50  --bmc1_non_equiv_states                 false
% 7.37/1.50  --bmc1_deadlock                         false
% 7.37/1.50  --bmc1_ucm                              false
% 7.37/1.50  --bmc1_add_unsat_core                   none
% 7.37/1.50  --bmc1_unsat_core_children              false
% 7.37/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.50  --bmc1_out_stat                         full
% 7.37/1.50  --bmc1_ground_init                      false
% 7.37/1.50  --bmc1_pre_inst_next_state              false
% 7.37/1.50  --bmc1_pre_inst_state                   false
% 7.37/1.50  --bmc1_pre_inst_reach_state             false
% 7.37/1.50  --bmc1_out_unsat_core                   false
% 7.37/1.50  --bmc1_aig_witness_out                  false
% 7.37/1.50  --bmc1_verbose                          false
% 7.37/1.50  --bmc1_dump_clauses_tptp                false
% 7.37/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.50  --bmc1_dump_file                        -
% 7.37/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.50  --bmc1_ucm_extend_mode                  1
% 7.37/1.50  --bmc1_ucm_init_mode                    2
% 7.37/1.50  --bmc1_ucm_cone_mode                    none
% 7.37/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.50  --bmc1_ucm_relax_model                  4
% 7.37/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.50  --bmc1_ucm_layered_model                none
% 7.37/1.50  --bmc1_ucm_max_lemma_size               10
% 7.37/1.50  
% 7.37/1.50  ------ AIG Options
% 7.37/1.50  
% 7.37/1.50  --aig_mode                              false
% 7.37/1.50  
% 7.37/1.50  ------ Instantiation Options
% 7.37/1.50  
% 7.37/1.50  --instantiation_flag                    true
% 7.37/1.50  --inst_sos_flag                         false
% 7.37/1.50  --inst_sos_phase                        true
% 7.37/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.50  --inst_lit_sel_side                     none
% 7.37/1.50  --inst_solver_per_active                1400
% 7.37/1.50  --inst_solver_calls_frac                1.
% 7.37/1.50  --inst_passive_queue_type               priority_queues
% 7.37/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.50  --inst_passive_queues_freq              [25;2]
% 7.37/1.50  --inst_dismatching                      true
% 7.37/1.50  --inst_eager_unprocessed_to_passive     true
% 7.37/1.50  --inst_prop_sim_given                   true
% 7.37/1.50  --inst_prop_sim_new                     false
% 7.37/1.50  --inst_subs_new                         false
% 7.37/1.50  --inst_eq_res_simp                      false
% 7.37/1.50  --inst_subs_given                       false
% 7.37/1.50  --inst_orphan_elimination               true
% 7.37/1.50  --inst_learning_loop_flag               true
% 7.37/1.50  --inst_learning_start                   3000
% 7.37/1.50  --inst_learning_factor                  2
% 7.37/1.50  --inst_start_prop_sim_after_learn       3
% 7.37/1.50  --inst_sel_renew                        solver
% 7.37/1.50  --inst_lit_activity_flag                true
% 7.37/1.50  --inst_restr_to_given                   false
% 7.37/1.50  --inst_activity_threshold               500
% 7.37/1.50  --inst_out_proof                        true
% 7.37/1.50  
% 7.37/1.50  ------ Resolution Options
% 7.37/1.50  
% 7.37/1.50  --resolution_flag                       false
% 7.37/1.50  --res_lit_sel                           adaptive
% 7.37/1.50  --res_lit_sel_side                      none
% 7.37/1.50  --res_ordering                          kbo
% 7.37/1.50  --res_to_prop_solver                    active
% 7.37/1.50  --res_prop_simpl_new                    false
% 7.37/1.50  --res_prop_simpl_given                  true
% 7.37/1.50  --res_passive_queue_type                priority_queues
% 7.37/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.50  --res_passive_queues_freq               [15;5]
% 7.37/1.50  --res_forward_subs                      full
% 7.37/1.50  --res_backward_subs                     full
% 7.37/1.50  --res_forward_subs_resolution           true
% 7.37/1.50  --res_backward_subs_resolution          true
% 7.37/1.50  --res_orphan_elimination                true
% 7.37/1.50  --res_time_limit                        2.
% 7.37/1.50  --res_out_proof                         true
% 7.37/1.50  
% 7.37/1.50  ------ Superposition Options
% 7.37/1.50  
% 7.37/1.50  --superposition_flag                    true
% 7.37/1.50  --sup_passive_queue_type                priority_queues
% 7.37/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.50  --demod_completeness_check              fast
% 7.37/1.50  --demod_use_ground                      true
% 7.37/1.50  --sup_to_prop_solver                    passive
% 7.37/1.50  --sup_prop_simpl_new                    true
% 7.37/1.50  --sup_prop_simpl_given                  true
% 7.37/1.50  --sup_fun_splitting                     false
% 7.37/1.50  --sup_smt_interval                      50000
% 7.37/1.50  
% 7.37/1.50  ------ Superposition Simplification Setup
% 7.37/1.50  
% 7.37/1.50  --sup_indices_passive                   []
% 7.37/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.50  --sup_full_bw                           [BwDemod]
% 7.37/1.50  --sup_immed_triv                        [TrivRules]
% 7.37/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.50  --sup_immed_bw_main                     []
% 7.37/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.50  
% 7.37/1.50  ------ Combination Options
% 7.37/1.50  
% 7.37/1.50  --comb_res_mult                         3
% 7.37/1.50  --comb_sup_mult                         2
% 7.37/1.50  --comb_inst_mult                        10
% 7.37/1.50  
% 7.37/1.50  ------ Debug Options
% 7.37/1.50  
% 7.37/1.50  --dbg_backtrace                         false
% 7.37/1.50  --dbg_dump_prop_clauses                 false
% 7.37/1.50  --dbg_dump_prop_clauses_file            -
% 7.37/1.50  --dbg_out_stat                          false
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  ------ Proving...
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  % SZS status Theorem for theBenchmark.p
% 7.37/1.50  
% 7.37/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.37/1.50  
% 7.37/1.50  fof(f8,axiom,(
% 7.37/1.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f53,plain,(
% 7.37/1.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f8])).
% 7.37/1.50  
% 7.37/1.50  fof(f9,axiom,(
% 7.37/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f54,plain,(
% 7.37/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f9])).
% 7.37/1.50  
% 7.37/1.50  fof(f10,axiom,(
% 7.37/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f55,plain,(
% 7.37/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f10])).
% 7.37/1.50  
% 7.37/1.50  fof(f11,axiom,(
% 7.37/1.50    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f56,plain,(
% 7.37/1.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f11])).
% 7.37/1.50  
% 7.37/1.50  fof(f12,axiom,(
% 7.37/1.50    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f57,plain,(
% 7.37/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f12])).
% 7.37/1.50  
% 7.37/1.50  fof(f63,plain,(
% 7.37/1.50    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.37/1.50    inference(definition_unfolding,[],[f56,f57])).
% 7.37/1.50  
% 7.37/1.50  fof(f64,plain,(
% 7.37/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 7.37/1.50    inference(definition_unfolding,[],[f55,f63])).
% 7.37/1.50  
% 7.37/1.50  fof(f65,plain,(
% 7.37/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 7.37/1.50    inference(definition_unfolding,[],[f54,f64])).
% 7.37/1.50  
% 7.37/1.50  fof(f67,plain,(
% 7.37/1.50    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.37/1.50    inference(definition_unfolding,[],[f53,f65])).
% 7.37/1.50  
% 7.37/1.50  fof(f3,axiom,(
% 7.37/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f19,plain,(
% 7.37/1.50    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.37/1.50    inference(ennf_transformation,[],[f3])).
% 7.37/1.50  
% 7.37/1.50  fof(f28,plain,(
% 7.37/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.37/1.50    inference(nnf_transformation,[],[f19])).
% 7.37/1.50  
% 7.37/1.50  fof(f29,plain,(
% 7.37/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.37/1.50    inference(flattening,[],[f28])).
% 7.37/1.50  
% 7.37/1.50  fof(f30,plain,(
% 7.37/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.37/1.50    inference(rectify,[],[f29])).
% 7.37/1.50  
% 7.37/1.50  fof(f31,plain,(
% 7.37/1.50    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.37/1.50    introduced(choice_axiom,[])).
% 7.37/1.50  
% 7.37/1.50  fof(f32,plain,(
% 7.37/1.50    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.37/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 7.37/1.50  
% 7.37/1.50  fof(f42,plain,(
% 7.37/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.37/1.50    inference(cnf_transformation,[],[f32])).
% 7.37/1.50  
% 7.37/1.50  fof(f75,plain,(
% 7.37/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.37/1.50    inference(definition_unfolding,[],[f42,f65])).
% 7.37/1.50  
% 7.37/1.50  fof(f86,plain,(
% 7.37/1.50    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.37/1.50    inference(equality_resolution,[],[f75])).
% 7.37/1.50  
% 7.37/1.50  fof(f87,plain,(
% 7.37/1.50    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 7.37/1.50    inference(equality_resolution,[],[f86])).
% 7.37/1.50  
% 7.37/1.50  fof(f14,axiom,(
% 7.37/1.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f20,plain,(
% 7.37/1.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 7.37/1.50    inference(ennf_transformation,[],[f14])).
% 7.37/1.50  
% 7.37/1.50  fof(f59,plain,(
% 7.37/1.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f20])).
% 7.37/1.50  
% 7.37/1.50  fof(f16,conjecture,(
% 7.37/1.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f17,negated_conjecture,(
% 7.37/1.50    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 7.37/1.50    inference(negated_conjecture,[],[f16])).
% 7.37/1.50  
% 7.37/1.50  fof(f21,plain,(
% 7.37/1.50    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 7.37/1.50    inference(ennf_transformation,[],[f17])).
% 7.37/1.50  
% 7.37/1.50  fof(f33,plain,(
% 7.37/1.50    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4))),
% 7.37/1.50    introduced(choice_axiom,[])).
% 7.37/1.50  
% 7.37/1.50  fof(f34,plain,(
% 7.37/1.50    ~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 7.37/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f33])).
% 7.37/1.50  
% 7.37/1.50  fof(f61,plain,(
% 7.37/1.50    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 7.37/1.50    inference(cnf_transformation,[],[f34])).
% 7.37/1.50  
% 7.37/1.50  fof(f15,axiom,(
% 7.37/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f60,plain,(
% 7.37/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.37/1.50    inference(cnf_transformation,[],[f15])).
% 7.37/1.50  
% 7.37/1.50  fof(f79,plain,(
% 7.37/1.50    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4)),
% 7.37/1.50    inference(definition_unfolding,[],[f61,f60])).
% 7.37/1.50  
% 7.37/1.50  fof(f2,axiom,(
% 7.37/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f26,plain,(
% 7.37/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.37/1.50    inference(nnf_transformation,[],[f2])).
% 7.37/1.50  
% 7.37/1.50  fof(f27,plain,(
% 7.37/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.37/1.50    inference(flattening,[],[f26])).
% 7.37/1.50  
% 7.37/1.50  fof(f40,plain,(
% 7.37/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f27])).
% 7.37/1.50  
% 7.37/1.50  fof(f44,plain,(
% 7.37/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.37/1.50    inference(cnf_transformation,[],[f32])).
% 7.37/1.50  
% 7.37/1.50  fof(f73,plain,(
% 7.37/1.50    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.37/1.50    inference(definition_unfolding,[],[f44,f65])).
% 7.37/1.50  
% 7.37/1.50  fof(f82,plain,(
% 7.37/1.50    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 7.37/1.50    inference(equality_resolution,[],[f73])).
% 7.37/1.50  
% 7.37/1.50  fof(f83,plain,(
% 7.37/1.50    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 7.37/1.50    inference(equality_resolution,[],[f82])).
% 7.37/1.50  
% 7.37/1.50  fof(f1,axiom,(
% 7.37/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.37/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.50  
% 7.37/1.50  fof(f18,plain,(
% 7.37/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.37/1.50    inference(ennf_transformation,[],[f1])).
% 7.37/1.50  
% 7.37/1.50  fof(f22,plain,(
% 7.37/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.37/1.50    inference(nnf_transformation,[],[f18])).
% 7.37/1.50  
% 7.37/1.50  fof(f23,plain,(
% 7.37/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.37/1.50    inference(rectify,[],[f22])).
% 7.37/1.50  
% 7.37/1.50  fof(f24,plain,(
% 7.37/1.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.37/1.50    introduced(choice_axiom,[])).
% 7.37/1.50  
% 7.37/1.50  fof(f25,plain,(
% 7.37/1.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.37/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 7.37/1.50  
% 7.37/1.50  fof(f35,plain,(
% 7.37/1.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.37/1.50    inference(cnf_transformation,[],[f25])).
% 7.37/1.50  
% 7.37/1.50  fof(f62,plain,(
% 7.37/1.50    ~r2_hidden(sK2,sK4)),
% 7.37/1.50    inference(cnf_transformation,[],[f34])).
% 7.37/1.50  
% 7.37/1.50  cnf(c_0,plain,
% 7.37/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 7.37/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_14,plain,
% 7.37/1.50      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 7.37/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_559,plain,
% 7.37/1.50      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_727,plain,
% 7.37/1.50      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_0,c_559]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_18,plain,
% 7.37/1.50      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 7.37/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_557,plain,
% 7.37/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.37/1.50      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_20,negated_conjecture,
% 7.37/1.50      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
% 7.37/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_555,plain,
% 7.37/1.50      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_5,plain,
% 7.37/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.37/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_567,plain,
% 7.37/1.50      ( X0 = X1
% 7.37/1.50      | r1_tarski(X1,X0) != iProver_top
% 7.37/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1747,plain,
% 7.37/1.50      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 7.37/1.50      | r1_tarski(sK4,k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_555,c_567]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1765,plain,
% 7.37/1.50      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 7.37/1.50      | r2_hidden(sK4,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_557,c_1747]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_12,plain,
% 7.37/1.50      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 7.37/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_561,plain,
% 7.37/1.50      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_878,plain,
% 7.37/1.50      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_0,c_561]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1856,plain,
% 7.37/1.50      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4 ),
% 7.37/1.50      inference(forward_subsumption_resolution,
% 7.37/1.50                [status(thm)],
% 7.37/1.50                [c_1765,c_878]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_1858,plain,
% 7.37/1.50      ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top
% 7.37/1.50      | r1_tarski(X0,sK4) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_1856,c_557]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_2423,plain,
% 7.37/1.50      ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_727,c_1858]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_4,plain,
% 7.37/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.37/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_568,plain,
% 7.37/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.37/1.50      | r2_hidden(X0,X2) = iProver_top
% 7.37/1.50      | r1_tarski(X1,X2) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_11361,plain,
% 7.37/1.50      ( r2_hidden(X0,X1) = iProver_top
% 7.37/1.50      | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_727,c_568]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_16424,plain,
% 7.37/1.50      ( r2_hidden(sK2,sK4) = iProver_top ),
% 7.37/1.50      inference(superposition,[status(thm)],[c_2423,c_11361]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_19,negated_conjecture,
% 7.37/1.50      ( ~ r2_hidden(sK2,sK4) ),
% 7.37/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(c_22,plain,
% 7.37/1.50      ( r2_hidden(sK2,sK4) != iProver_top ),
% 7.37/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.37/1.50  
% 7.37/1.50  cnf(contradiction,plain,
% 7.37/1.50      ( $false ),
% 7.37/1.50      inference(minisat,[status(thm)],[c_16424,c_22]) ).
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.37/1.50  
% 7.37/1.50  ------                               Statistics
% 7.37/1.50  
% 7.37/1.50  ------ General
% 7.37/1.50  
% 7.37/1.50  abstr_ref_over_cycles:                  0
% 7.37/1.50  abstr_ref_under_cycles:                 0
% 7.37/1.50  gc_basic_clause_elim:                   0
% 7.37/1.50  forced_gc_time:                         0
% 7.37/1.50  parsing_time:                           0.039
% 7.37/1.50  unif_index_cands_time:                  0.
% 7.37/1.50  unif_index_add_time:                    0.
% 7.37/1.50  orderings_time:                         0.
% 7.37/1.50  out_proof_time:                         0.007
% 7.37/1.50  total_time:                             0.54
% 7.37/1.50  num_of_symbols:                         41
% 7.37/1.50  num_of_terms:                           23638
% 7.37/1.50  
% 7.37/1.50  ------ Preprocessing
% 7.37/1.50  
% 7.37/1.50  num_of_splits:                          0
% 7.37/1.50  num_of_split_atoms:                     0
% 7.37/1.50  num_of_reused_defs:                     0
% 7.37/1.50  num_eq_ax_congr_red:                    39
% 7.37/1.50  num_of_sem_filtered_clauses:            1
% 7.37/1.50  num_of_subtypes:                        0
% 7.37/1.50  monotx_restored_types:                  0
% 7.37/1.50  sat_num_of_epr_types:                   0
% 7.37/1.50  sat_num_of_non_cyclic_types:            0
% 7.37/1.50  sat_guarded_non_collapsed_types:        0
% 7.37/1.50  num_pure_diseq_elim:                    0
% 7.37/1.50  simp_replaced_by:                       0
% 7.37/1.50  res_preprocessed:                       93
% 7.37/1.50  prep_upred:                             0
% 7.37/1.50  prep_unflattend:                        0
% 7.37/1.50  smt_new_axioms:                         0
% 7.37/1.50  pred_elim_cands:                        2
% 7.37/1.50  pred_elim:                              0
% 7.37/1.50  pred_elim_cl:                           0
% 7.37/1.50  pred_elim_cycles:                       2
% 7.37/1.50  merged_defs:                            0
% 7.37/1.50  merged_defs_ncl:                        0
% 7.37/1.50  bin_hyper_res:                          0
% 7.37/1.50  prep_cycles:                            4
% 7.37/1.50  pred_elim_time:                         0.
% 7.37/1.50  splitting_time:                         0.
% 7.37/1.50  sem_filter_time:                        0.
% 7.37/1.50  monotx_time:                            0.001
% 7.37/1.50  subtype_inf_time:                       0.
% 7.37/1.50  
% 7.37/1.50  ------ Problem properties
% 7.37/1.50  
% 7.37/1.50  clauses:                                20
% 7.37/1.50  conjectures:                            2
% 7.37/1.50  epr:                                    4
% 7.37/1.50  horn:                                   17
% 7.37/1.50  ground:                                 2
% 7.37/1.50  unary:                                  10
% 7.37/1.50  binary:                                 3
% 7.37/1.50  lits:                                   40
% 7.37/1.50  lits_eq:                                18
% 7.37/1.50  fd_pure:                                0
% 7.37/1.50  fd_pseudo:                              0
% 7.37/1.50  fd_cond:                                0
% 7.37/1.50  fd_pseudo_cond:                         5
% 7.37/1.50  ac_symbols:                             0
% 7.37/1.50  
% 7.37/1.50  ------ Propositional Solver
% 7.37/1.50  
% 7.37/1.50  prop_solver_calls:                      28
% 7.37/1.50  prop_fast_solver_calls:                 572
% 7.37/1.50  smt_solver_calls:                       0
% 7.37/1.50  smt_fast_solver_calls:                  0
% 7.37/1.50  prop_num_of_clauses:                    5052
% 7.37/1.50  prop_preprocess_simplified:             13148
% 7.37/1.50  prop_fo_subsumed:                       0
% 7.37/1.50  prop_solver_time:                       0.
% 7.37/1.50  smt_solver_time:                        0.
% 7.37/1.50  smt_fast_solver_time:                   0.
% 7.37/1.50  prop_fast_solver_time:                  0.
% 7.37/1.50  prop_unsat_core_time:                   0.
% 7.37/1.50  
% 7.37/1.50  ------ QBF
% 7.37/1.50  
% 7.37/1.50  qbf_q_res:                              0
% 7.37/1.50  qbf_num_tautologies:                    0
% 7.37/1.50  qbf_prep_cycles:                        0
% 7.37/1.50  
% 7.37/1.50  ------ BMC1
% 7.37/1.50  
% 7.37/1.50  bmc1_current_bound:                     -1
% 7.37/1.50  bmc1_last_solved_bound:                 -1
% 7.37/1.50  bmc1_unsat_core_size:                   -1
% 7.37/1.50  bmc1_unsat_core_parents_size:           -1
% 7.37/1.50  bmc1_merge_next_fun:                    0
% 7.37/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.37/1.50  
% 7.37/1.50  ------ Instantiation
% 7.37/1.50  
% 7.37/1.50  inst_num_of_clauses:                    1440
% 7.37/1.50  inst_num_in_passive:                    567
% 7.37/1.50  inst_num_in_active:                     407
% 7.37/1.50  inst_num_in_unprocessed:                468
% 7.37/1.50  inst_num_of_loops:                      560
% 7.37/1.50  inst_num_of_learning_restarts:          0
% 7.37/1.50  inst_num_moves_active_passive:          152
% 7.37/1.50  inst_lit_activity:                      0
% 7.37/1.50  inst_lit_activity_moves:                0
% 7.37/1.50  inst_num_tautologies:                   0
% 7.37/1.50  inst_num_prop_implied:                  0
% 7.37/1.50  inst_num_existing_simplified:           0
% 7.37/1.50  inst_num_eq_res_simplified:             0
% 7.37/1.50  inst_num_child_elim:                    0
% 7.37/1.50  inst_num_of_dismatching_blockings:      2627
% 7.37/1.50  inst_num_of_non_proper_insts:           1793
% 7.37/1.50  inst_num_of_duplicates:                 0
% 7.37/1.50  inst_inst_num_from_inst_to_res:         0
% 7.37/1.50  inst_dismatching_checking_time:         0.
% 7.37/1.50  
% 7.37/1.50  ------ Resolution
% 7.37/1.50  
% 7.37/1.50  res_num_of_clauses:                     0
% 7.37/1.50  res_num_in_passive:                     0
% 7.37/1.50  res_num_in_active:                      0
% 7.37/1.50  res_num_of_loops:                       97
% 7.37/1.50  res_forward_subset_subsumed:            141
% 7.37/1.50  res_backward_subset_subsumed:           6
% 7.37/1.50  res_forward_subsumed:                   0
% 7.37/1.50  res_backward_subsumed:                  0
% 7.37/1.50  res_forward_subsumption_resolution:     0
% 7.37/1.50  res_backward_subsumption_resolution:    0
% 7.37/1.50  res_clause_to_clause_subsumption:       3049
% 7.37/1.50  res_orphan_elimination:                 0
% 7.37/1.50  res_tautology_del:                      41
% 7.37/1.50  res_num_eq_res_simplified:              0
% 7.37/1.50  res_num_sel_changes:                    0
% 7.37/1.50  res_moves_from_active_to_pass:          0
% 7.37/1.50  
% 7.37/1.50  ------ Superposition
% 7.37/1.50  
% 7.37/1.50  sup_time_total:                         0.
% 7.37/1.50  sup_time_generating:                    0.
% 7.37/1.50  sup_time_sim_full:                      0.
% 7.37/1.50  sup_time_sim_immed:                     0.
% 7.37/1.50  
% 7.37/1.50  sup_num_of_clauses:                     340
% 7.37/1.50  sup_num_in_active:                      94
% 7.37/1.50  sup_num_in_passive:                     246
% 7.37/1.50  sup_num_of_loops:                       110
% 7.37/1.50  sup_fw_superposition:                   1053
% 7.37/1.50  sup_bw_superposition:                   958
% 7.37/1.50  sup_immediate_simplified:               153
% 7.37/1.50  sup_given_eliminated:                   0
% 7.37/1.50  comparisons_done:                       0
% 7.37/1.50  comparisons_avoided:                    48
% 7.37/1.50  
% 7.37/1.50  ------ Simplifications
% 7.37/1.50  
% 7.37/1.50  
% 7.37/1.50  sim_fw_subset_subsumed:                 0
% 7.37/1.50  sim_bw_subset_subsumed:                 1
% 7.37/1.50  sim_fw_subsumed:                        10
% 7.37/1.50  sim_bw_subsumed:                        4
% 7.37/1.50  sim_fw_subsumption_res:                 1
% 7.37/1.50  sim_bw_subsumption_res:                 0
% 7.37/1.50  sim_tautology_del:                      0
% 7.37/1.50  sim_eq_tautology_del:                   24
% 7.37/1.50  sim_eq_res_simp:                        0
% 7.37/1.50  sim_fw_demodulated:                     78
% 7.37/1.50  sim_bw_demodulated:                     19
% 7.37/1.50  sim_light_normalised:                   68
% 7.37/1.50  sim_joinable_taut:                      0
% 7.37/1.50  sim_joinable_simp:                      0
% 7.37/1.50  sim_ac_normalised:                      0
% 7.37/1.50  sim_smt_subsumption:                    0
% 7.37/1.50  
%------------------------------------------------------------------------------
