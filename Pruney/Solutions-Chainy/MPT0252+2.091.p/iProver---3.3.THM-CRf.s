%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:35 EST 2020

% Result     : Theorem 31.48s
% Output     : CNFRefutation 31.48s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 178 expanded)
%              Number of clauses        :   27 (  34 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  249 ( 542 expanded)
%              Number of equality atoms :  135 ( 359 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f69,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f55,f67])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f24])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f86,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f87,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f86])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK2,sK4)
      & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r2_hidden(sK2,sK4)
    & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f36])).

fof(f63,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f81,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f82,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f75])).

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

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_13,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_558,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_718,plain,
    ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_558])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_556,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_554,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_180,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_5,c_6])).

cnf(c_553,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1755,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r1_tarski(sK4,k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_553])).

cnf(c_1773,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
    | r2_hidden(sK4,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_556,c_1755])).

cnf(c_11,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_560,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_871,plain,
    ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_560])).

cnf(c_1778,plain,
    ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1773,c_871])).

cnf(c_1781,plain,
    ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top
    | r1_tarski(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_556])).

cnf(c_2453,plain,
    ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_1781])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_565,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7348,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_565])).

cnf(c_90165,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2453,c_7348])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_90165,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 31.48/4.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.48/4.51  
% 31.48/4.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.48/4.51  
% 31.48/4.51  ------  iProver source info
% 31.48/4.51  
% 31.48/4.51  git: date: 2020-06-30 10:37:57 +0100
% 31.48/4.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.48/4.51  git: non_committed_changes: false
% 31.48/4.51  git: last_make_outside_of_git: false
% 31.48/4.51  
% 31.48/4.51  ------ 
% 31.48/4.51  
% 31.48/4.51  ------ Input Options
% 31.48/4.51  
% 31.48/4.51  --out_options                           all
% 31.48/4.51  --tptp_safe_out                         true
% 31.48/4.51  --problem_path                          ""
% 31.48/4.51  --include_path                          ""
% 31.48/4.51  --clausifier                            res/vclausify_rel
% 31.48/4.51  --clausifier_options                    --mode clausify
% 31.48/4.51  --stdin                                 false
% 31.48/4.51  --stats_out                             all
% 31.48/4.51  
% 31.48/4.51  ------ General Options
% 31.48/4.51  
% 31.48/4.51  --fof                                   false
% 31.48/4.51  --time_out_real                         305.
% 31.48/4.51  --time_out_virtual                      -1.
% 31.48/4.51  --symbol_type_check                     false
% 31.48/4.51  --clausify_out                          false
% 31.48/4.51  --sig_cnt_out                           false
% 31.48/4.51  --trig_cnt_out                          false
% 31.48/4.51  --trig_cnt_out_tolerance                1.
% 31.48/4.51  --trig_cnt_out_sk_spl                   false
% 31.48/4.51  --abstr_cl_out                          false
% 31.48/4.51  
% 31.48/4.51  ------ Global Options
% 31.48/4.51  
% 31.48/4.51  --schedule                              default
% 31.48/4.51  --add_important_lit                     false
% 31.48/4.51  --prop_solver_per_cl                    1000
% 31.48/4.51  --min_unsat_core                        false
% 31.48/4.51  --soft_assumptions                      false
% 31.48/4.51  --soft_lemma_size                       3
% 31.48/4.51  --prop_impl_unit_size                   0
% 31.48/4.51  --prop_impl_unit                        []
% 31.48/4.51  --share_sel_clauses                     true
% 31.48/4.51  --reset_solvers                         false
% 31.48/4.51  --bc_imp_inh                            [conj_cone]
% 31.48/4.51  --conj_cone_tolerance                   3.
% 31.48/4.51  --extra_neg_conj                        none
% 31.48/4.51  --large_theory_mode                     true
% 31.48/4.51  --prolific_symb_bound                   200
% 31.48/4.51  --lt_threshold                          2000
% 31.48/4.51  --clause_weak_htbl                      true
% 31.48/4.51  --gc_record_bc_elim                     false
% 31.48/4.51  
% 31.48/4.51  ------ Preprocessing Options
% 31.48/4.51  
% 31.48/4.51  --preprocessing_flag                    true
% 31.48/4.51  --time_out_prep_mult                    0.1
% 31.48/4.51  --splitting_mode                        input
% 31.48/4.51  --splitting_grd                         true
% 31.48/4.51  --splitting_cvd                         false
% 31.48/4.51  --splitting_cvd_svl                     false
% 31.48/4.51  --splitting_nvd                         32
% 31.48/4.51  --sub_typing                            true
% 31.48/4.51  --prep_gs_sim                           true
% 31.48/4.51  --prep_unflatten                        true
% 31.48/4.51  --prep_res_sim                          true
% 31.48/4.51  --prep_upred                            true
% 31.48/4.51  --prep_sem_filter                       exhaustive
% 31.48/4.51  --prep_sem_filter_out                   false
% 31.48/4.51  --pred_elim                             true
% 31.48/4.51  --res_sim_input                         true
% 31.48/4.51  --eq_ax_congr_red                       true
% 31.48/4.51  --pure_diseq_elim                       true
% 31.48/4.51  --brand_transform                       false
% 31.48/4.51  --non_eq_to_eq                          false
% 31.48/4.51  --prep_def_merge                        true
% 31.48/4.51  --prep_def_merge_prop_impl              false
% 31.48/4.51  --prep_def_merge_mbd                    true
% 31.48/4.51  --prep_def_merge_tr_red                 false
% 31.48/4.51  --prep_def_merge_tr_cl                  false
% 31.48/4.51  --smt_preprocessing                     true
% 31.48/4.51  --smt_ac_axioms                         fast
% 31.48/4.51  --preprocessed_out                      false
% 31.48/4.51  --preprocessed_stats                    false
% 31.48/4.51  
% 31.48/4.51  ------ Abstraction refinement Options
% 31.48/4.51  
% 31.48/4.51  --abstr_ref                             []
% 31.48/4.51  --abstr_ref_prep                        false
% 31.48/4.51  --abstr_ref_until_sat                   false
% 31.48/4.51  --abstr_ref_sig_restrict                funpre
% 31.48/4.51  --abstr_ref_af_restrict_to_split_sk     false
% 31.48/4.51  --abstr_ref_under                       []
% 31.48/4.51  
% 31.48/4.51  ------ SAT Options
% 31.48/4.51  
% 31.48/4.51  --sat_mode                              false
% 31.48/4.51  --sat_fm_restart_options                ""
% 31.48/4.51  --sat_gr_def                            false
% 31.48/4.51  --sat_epr_types                         true
% 31.48/4.51  --sat_non_cyclic_types                  false
% 31.48/4.51  --sat_finite_models                     false
% 31.48/4.51  --sat_fm_lemmas                         false
% 31.48/4.51  --sat_fm_prep                           false
% 31.48/4.51  --sat_fm_uc_incr                        true
% 31.48/4.51  --sat_out_model                         small
% 31.48/4.51  --sat_out_clauses                       false
% 31.48/4.51  
% 31.48/4.51  ------ QBF Options
% 31.48/4.51  
% 31.48/4.51  --qbf_mode                              false
% 31.48/4.51  --qbf_elim_univ                         false
% 31.48/4.51  --qbf_dom_inst                          none
% 31.48/4.51  --qbf_dom_pre_inst                      false
% 31.48/4.51  --qbf_sk_in                             false
% 31.48/4.51  --qbf_pred_elim                         true
% 31.48/4.51  --qbf_split                             512
% 31.48/4.51  
% 31.48/4.51  ------ BMC1 Options
% 31.48/4.51  
% 31.48/4.51  --bmc1_incremental                      false
% 31.48/4.51  --bmc1_axioms                           reachable_all
% 31.48/4.51  --bmc1_min_bound                        0
% 31.48/4.51  --bmc1_max_bound                        -1
% 31.48/4.51  --bmc1_max_bound_default                -1
% 31.48/4.51  --bmc1_symbol_reachability              true
% 31.48/4.51  --bmc1_property_lemmas                  false
% 31.48/4.51  --bmc1_k_induction                      false
% 31.48/4.51  --bmc1_non_equiv_states                 false
% 31.48/4.51  --bmc1_deadlock                         false
% 31.48/4.51  --bmc1_ucm                              false
% 31.48/4.51  --bmc1_add_unsat_core                   none
% 31.48/4.51  --bmc1_unsat_core_children              false
% 31.48/4.51  --bmc1_unsat_core_extrapolate_axioms    false
% 31.48/4.51  --bmc1_out_stat                         full
% 31.48/4.51  --bmc1_ground_init                      false
% 31.48/4.51  --bmc1_pre_inst_next_state              false
% 31.48/4.51  --bmc1_pre_inst_state                   false
% 31.48/4.51  --bmc1_pre_inst_reach_state             false
% 31.48/4.51  --bmc1_out_unsat_core                   false
% 31.48/4.51  --bmc1_aig_witness_out                  false
% 31.48/4.51  --bmc1_verbose                          false
% 31.48/4.51  --bmc1_dump_clauses_tptp                false
% 31.48/4.51  --bmc1_dump_unsat_core_tptp             false
% 31.48/4.51  --bmc1_dump_file                        -
% 31.48/4.51  --bmc1_ucm_expand_uc_limit              128
% 31.48/4.51  --bmc1_ucm_n_expand_iterations          6
% 31.48/4.51  --bmc1_ucm_extend_mode                  1
% 31.48/4.51  --bmc1_ucm_init_mode                    2
% 31.48/4.51  --bmc1_ucm_cone_mode                    none
% 31.48/4.51  --bmc1_ucm_reduced_relation_type        0
% 31.48/4.51  --bmc1_ucm_relax_model                  4
% 31.48/4.51  --bmc1_ucm_full_tr_after_sat            true
% 31.48/4.51  --bmc1_ucm_expand_neg_assumptions       false
% 31.48/4.51  --bmc1_ucm_layered_model                none
% 31.48/4.51  --bmc1_ucm_max_lemma_size               10
% 31.48/4.51  
% 31.48/4.51  ------ AIG Options
% 31.48/4.51  
% 31.48/4.51  --aig_mode                              false
% 31.48/4.51  
% 31.48/4.51  ------ Instantiation Options
% 31.48/4.51  
% 31.48/4.51  --instantiation_flag                    true
% 31.48/4.51  --inst_sos_flag                         false
% 31.48/4.51  --inst_sos_phase                        true
% 31.48/4.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.48/4.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.48/4.51  --inst_lit_sel_side                     num_symb
% 31.48/4.51  --inst_solver_per_active                1400
% 31.48/4.51  --inst_solver_calls_frac                1.
% 31.48/4.51  --inst_passive_queue_type               priority_queues
% 31.48/4.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.48/4.51  --inst_passive_queues_freq              [25;2]
% 31.48/4.51  --inst_dismatching                      true
% 31.48/4.51  --inst_eager_unprocessed_to_passive     true
% 31.48/4.51  --inst_prop_sim_given                   true
% 31.48/4.51  --inst_prop_sim_new                     false
% 31.48/4.51  --inst_subs_new                         false
% 31.48/4.51  --inst_eq_res_simp                      false
% 31.48/4.51  --inst_subs_given                       false
% 31.48/4.51  --inst_orphan_elimination               true
% 31.48/4.51  --inst_learning_loop_flag               true
% 31.48/4.51  --inst_learning_start                   3000
% 31.48/4.51  --inst_learning_factor                  2
% 31.48/4.51  --inst_start_prop_sim_after_learn       3
% 31.48/4.51  --inst_sel_renew                        solver
% 31.48/4.51  --inst_lit_activity_flag                true
% 31.48/4.51  --inst_restr_to_given                   false
% 31.48/4.51  --inst_activity_threshold               500
% 31.48/4.51  --inst_out_proof                        true
% 31.48/4.51  
% 31.48/4.51  ------ Resolution Options
% 31.48/4.51  
% 31.48/4.51  --resolution_flag                       true
% 31.48/4.51  --res_lit_sel                           adaptive
% 31.48/4.51  --res_lit_sel_side                      none
% 31.48/4.51  --res_ordering                          kbo
% 31.48/4.51  --res_to_prop_solver                    active
% 31.48/4.51  --res_prop_simpl_new                    false
% 31.48/4.51  --res_prop_simpl_given                  true
% 31.48/4.51  --res_passive_queue_type                priority_queues
% 31.48/4.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.48/4.51  --res_passive_queues_freq               [15;5]
% 31.48/4.51  --res_forward_subs                      full
% 31.48/4.51  --res_backward_subs                     full
% 31.48/4.51  --res_forward_subs_resolution           true
% 31.48/4.51  --res_backward_subs_resolution          true
% 31.48/4.51  --res_orphan_elimination                true
% 31.48/4.51  --res_time_limit                        2.
% 31.48/4.51  --res_out_proof                         true
% 31.48/4.51  
% 31.48/4.51  ------ Superposition Options
% 31.48/4.51  
% 31.48/4.51  --superposition_flag                    true
% 31.48/4.51  --sup_passive_queue_type                priority_queues
% 31.48/4.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.48/4.51  --sup_passive_queues_freq               [8;1;4]
% 31.48/4.51  --demod_completeness_check              fast
% 31.48/4.51  --demod_use_ground                      true
% 31.48/4.51  --sup_to_prop_solver                    passive
% 31.48/4.51  --sup_prop_simpl_new                    true
% 31.48/4.51  --sup_prop_simpl_given                  true
% 31.48/4.51  --sup_fun_splitting                     false
% 31.48/4.51  --sup_smt_interval                      50000
% 31.48/4.51  
% 31.48/4.51  ------ Superposition Simplification Setup
% 31.48/4.51  
% 31.48/4.51  --sup_indices_passive                   []
% 31.48/4.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.48/4.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.48/4.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.48/4.51  --sup_full_triv                         [TrivRules;PropSubs]
% 31.48/4.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.48/4.51  --sup_full_bw                           [BwDemod]
% 31.48/4.51  --sup_immed_triv                        [TrivRules]
% 31.48/4.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.48/4.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.48/4.51  --sup_immed_bw_main                     []
% 31.48/4.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.48/4.51  --sup_input_triv                        [Unflattening;TrivRules]
% 31.48/4.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.48/4.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.48/4.51  
% 31.48/4.51  ------ Combination Options
% 31.48/4.51  
% 31.48/4.51  --comb_res_mult                         3
% 31.48/4.51  --comb_sup_mult                         2
% 31.48/4.51  --comb_inst_mult                        10
% 31.48/4.51  
% 31.48/4.51  ------ Debug Options
% 31.48/4.51  
% 31.48/4.51  --dbg_backtrace                         false
% 31.48/4.51  --dbg_dump_prop_clauses                 false
% 31.48/4.51  --dbg_dump_prop_clauses_file            -
% 31.48/4.51  --dbg_out_stat                          false
% 31.48/4.51  ------ Parsing...
% 31.48/4.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.48/4.51  
% 31.48/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 31.48/4.51  
% 31.48/4.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.48/4.51  
% 31.48/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.48/4.51  ------ Proving...
% 31.48/4.51  ------ Problem Properties 
% 31.48/4.51  
% 31.48/4.51  
% 31.48/4.51  clauses                                 19
% 31.48/4.51  conjectures                             2
% 31.48/4.51  EPR                                     3
% 31.48/4.51  Horn                                    16
% 31.48/4.51  unary                                   9
% 31.48/4.51  binary                                  3
% 31.48/4.51  lits                                    39
% 31.48/4.51  lits eq                                 18
% 31.48/4.51  fd_pure                                 0
% 31.48/4.51  fd_pseudo                               0
% 31.48/4.51  fd_cond                                 0
% 31.48/4.51  fd_pseudo_cond                          5
% 31.48/4.51  AC symbols                              0
% 31.48/4.51  
% 31.48/4.51  ------ Schedule dynamic 5 is on 
% 31.48/4.51  
% 31.48/4.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.48/4.51  
% 31.48/4.51  
% 31.48/4.51  ------ 
% 31.48/4.51  Current options:
% 31.48/4.51  ------ 
% 31.48/4.51  
% 31.48/4.51  ------ Input Options
% 31.48/4.51  
% 31.48/4.51  --out_options                           all
% 31.48/4.51  --tptp_safe_out                         true
% 31.48/4.51  --problem_path                          ""
% 31.48/4.51  --include_path                          ""
% 31.48/4.51  --clausifier                            res/vclausify_rel
% 31.48/4.51  --clausifier_options                    --mode clausify
% 31.48/4.51  --stdin                                 false
% 31.48/4.51  --stats_out                             all
% 31.48/4.51  
% 31.48/4.51  ------ General Options
% 31.48/4.51  
% 31.48/4.51  --fof                                   false
% 31.48/4.51  --time_out_real                         305.
% 31.48/4.51  --time_out_virtual                      -1.
% 31.48/4.51  --symbol_type_check                     false
% 31.48/4.51  --clausify_out                          false
% 31.48/4.51  --sig_cnt_out                           false
% 31.48/4.51  --trig_cnt_out                          false
% 31.48/4.51  --trig_cnt_out_tolerance                1.
% 31.48/4.51  --trig_cnt_out_sk_spl                   false
% 31.48/4.51  --abstr_cl_out                          false
% 31.48/4.51  
% 31.48/4.51  ------ Global Options
% 31.48/4.51  
% 31.48/4.51  --schedule                              default
% 31.48/4.51  --add_important_lit                     false
% 31.48/4.51  --prop_solver_per_cl                    1000
% 31.48/4.51  --min_unsat_core                        false
% 31.48/4.51  --soft_assumptions                      false
% 31.48/4.51  --soft_lemma_size                       3
% 31.48/4.51  --prop_impl_unit_size                   0
% 31.48/4.51  --prop_impl_unit                        []
% 31.48/4.51  --share_sel_clauses                     true
% 31.48/4.51  --reset_solvers                         false
% 31.48/4.51  --bc_imp_inh                            [conj_cone]
% 31.48/4.51  --conj_cone_tolerance                   3.
% 31.48/4.51  --extra_neg_conj                        none
% 31.48/4.51  --large_theory_mode                     true
% 31.48/4.51  --prolific_symb_bound                   200
% 31.48/4.51  --lt_threshold                          2000
% 31.48/4.51  --clause_weak_htbl                      true
% 31.48/4.51  --gc_record_bc_elim                     false
% 31.48/4.51  
% 31.48/4.51  ------ Preprocessing Options
% 31.48/4.51  
% 31.48/4.51  --preprocessing_flag                    true
% 31.48/4.51  --time_out_prep_mult                    0.1
% 31.48/4.51  --splitting_mode                        input
% 31.48/4.51  --splitting_grd                         true
% 31.48/4.51  --splitting_cvd                         false
% 31.48/4.51  --splitting_cvd_svl                     false
% 31.48/4.51  --splitting_nvd                         32
% 31.48/4.51  --sub_typing                            true
% 31.48/4.51  --prep_gs_sim                           true
% 31.48/4.51  --prep_unflatten                        true
% 31.48/4.51  --prep_res_sim                          true
% 31.48/4.51  --prep_upred                            true
% 31.48/4.51  --prep_sem_filter                       exhaustive
% 31.48/4.51  --prep_sem_filter_out                   false
% 31.48/4.51  --pred_elim                             true
% 31.48/4.51  --res_sim_input                         true
% 31.48/4.51  --eq_ax_congr_red                       true
% 31.48/4.51  --pure_diseq_elim                       true
% 31.48/4.51  --brand_transform                       false
% 31.48/4.51  --non_eq_to_eq                          false
% 31.48/4.51  --prep_def_merge                        true
% 31.48/4.51  --prep_def_merge_prop_impl              false
% 31.48/4.51  --prep_def_merge_mbd                    true
% 31.48/4.51  --prep_def_merge_tr_red                 false
% 31.48/4.51  --prep_def_merge_tr_cl                  false
% 31.48/4.51  --smt_preprocessing                     true
% 31.48/4.51  --smt_ac_axioms                         fast
% 31.48/4.51  --preprocessed_out                      false
% 31.48/4.51  --preprocessed_stats                    false
% 31.48/4.51  
% 31.48/4.51  ------ Abstraction refinement Options
% 31.48/4.51  
% 31.48/4.51  --abstr_ref                             []
% 31.48/4.51  --abstr_ref_prep                        false
% 31.48/4.51  --abstr_ref_until_sat                   false
% 31.48/4.51  --abstr_ref_sig_restrict                funpre
% 31.48/4.51  --abstr_ref_af_restrict_to_split_sk     false
% 31.48/4.51  --abstr_ref_under                       []
% 31.48/4.51  
% 31.48/4.51  ------ SAT Options
% 31.48/4.51  
% 31.48/4.51  --sat_mode                              false
% 31.48/4.51  --sat_fm_restart_options                ""
% 31.48/4.51  --sat_gr_def                            false
% 31.48/4.51  --sat_epr_types                         true
% 31.48/4.51  --sat_non_cyclic_types                  false
% 31.48/4.51  --sat_finite_models                     false
% 31.48/4.51  --sat_fm_lemmas                         false
% 31.48/4.51  --sat_fm_prep                           false
% 31.48/4.51  --sat_fm_uc_incr                        true
% 31.48/4.51  --sat_out_model                         small
% 31.48/4.51  --sat_out_clauses                       false
% 31.48/4.51  
% 31.48/4.51  ------ QBF Options
% 31.48/4.51  
% 31.48/4.51  --qbf_mode                              false
% 31.48/4.51  --qbf_elim_univ                         false
% 31.48/4.51  --qbf_dom_inst                          none
% 31.48/4.51  --qbf_dom_pre_inst                      false
% 31.48/4.51  --qbf_sk_in                             false
% 31.48/4.51  --qbf_pred_elim                         true
% 31.48/4.51  --qbf_split                             512
% 31.48/4.51  
% 31.48/4.51  ------ BMC1 Options
% 31.48/4.51  
% 31.48/4.51  --bmc1_incremental                      false
% 31.48/4.51  --bmc1_axioms                           reachable_all
% 31.48/4.51  --bmc1_min_bound                        0
% 31.48/4.51  --bmc1_max_bound                        -1
% 31.48/4.51  --bmc1_max_bound_default                -1
% 31.48/4.51  --bmc1_symbol_reachability              true
% 31.48/4.51  --bmc1_property_lemmas                  false
% 31.48/4.51  --bmc1_k_induction                      false
% 31.48/4.51  --bmc1_non_equiv_states                 false
% 31.48/4.51  --bmc1_deadlock                         false
% 31.48/4.51  --bmc1_ucm                              false
% 31.48/4.51  --bmc1_add_unsat_core                   none
% 31.48/4.51  --bmc1_unsat_core_children              false
% 31.48/4.51  --bmc1_unsat_core_extrapolate_axioms    false
% 31.48/4.51  --bmc1_out_stat                         full
% 31.48/4.51  --bmc1_ground_init                      false
% 31.48/4.51  --bmc1_pre_inst_next_state              false
% 31.48/4.51  --bmc1_pre_inst_state                   false
% 31.48/4.51  --bmc1_pre_inst_reach_state             false
% 31.48/4.51  --bmc1_out_unsat_core                   false
% 31.48/4.51  --bmc1_aig_witness_out                  false
% 31.48/4.51  --bmc1_verbose                          false
% 31.48/4.51  --bmc1_dump_clauses_tptp                false
% 31.48/4.51  --bmc1_dump_unsat_core_tptp             false
% 31.48/4.51  --bmc1_dump_file                        -
% 31.48/4.51  --bmc1_ucm_expand_uc_limit              128
% 31.48/4.51  --bmc1_ucm_n_expand_iterations          6
% 31.48/4.51  --bmc1_ucm_extend_mode                  1
% 31.48/4.51  --bmc1_ucm_init_mode                    2
% 31.48/4.51  --bmc1_ucm_cone_mode                    none
% 31.48/4.51  --bmc1_ucm_reduced_relation_type        0
% 31.48/4.51  --bmc1_ucm_relax_model                  4
% 31.48/4.51  --bmc1_ucm_full_tr_after_sat            true
% 31.48/4.51  --bmc1_ucm_expand_neg_assumptions       false
% 31.48/4.51  --bmc1_ucm_layered_model                none
% 31.48/4.51  --bmc1_ucm_max_lemma_size               10
% 31.48/4.51  
% 31.48/4.51  ------ AIG Options
% 31.48/4.51  
% 31.48/4.51  --aig_mode                              false
% 31.48/4.51  
% 31.48/4.51  ------ Instantiation Options
% 31.48/4.51  
% 31.48/4.51  --instantiation_flag                    true
% 31.48/4.51  --inst_sos_flag                         false
% 31.48/4.51  --inst_sos_phase                        true
% 31.48/4.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.48/4.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.48/4.51  --inst_lit_sel_side                     none
% 31.48/4.51  --inst_solver_per_active                1400
% 31.48/4.51  --inst_solver_calls_frac                1.
% 31.48/4.51  --inst_passive_queue_type               priority_queues
% 31.48/4.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.48/4.51  --inst_passive_queues_freq              [25;2]
% 31.48/4.51  --inst_dismatching                      true
% 31.48/4.51  --inst_eager_unprocessed_to_passive     true
% 31.48/4.51  --inst_prop_sim_given                   true
% 31.48/4.51  --inst_prop_sim_new                     false
% 31.48/4.51  --inst_subs_new                         false
% 31.48/4.51  --inst_eq_res_simp                      false
% 31.48/4.51  --inst_subs_given                       false
% 31.48/4.51  --inst_orphan_elimination               true
% 31.48/4.51  --inst_learning_loop_flag               true
% 31.48/4.51  --inst_learning_start                   3000
% 31.48/4.51  --inst_learning_factor                  2
% 31.48/4.51  --inst_start_prop_sim_after_learn       3
% 31.48/4.51  --inst_sel_renew                        solver
% 31.48/4.51  --inst_lit_activity_flag                true
% 31.48/4.51  --inst_restr_to_given                   false
% 31.48/4.51  --inst_activity_threshold               500
% 31.48/4.51  --inst_out_proof                        true
% 31.48/4.51  
% 31.48/4.51  ------ Resolution Options
% 31.48/4.51  
% 31.48/4.51  --resolution_flag                       false
% 31.48/4.51  --res_lit_sel                           adaptive
% 31.48/4.51  --res_lit_sel_side                      none
% 31.48/4.51  --res_ordering                          kbo
% 31.48/4.51  --res_to_prop_solver                    active
% 31.48/4.51  --res_prop_simpl_new                    false
% 31.48/4.51  --res_prop_simpl_given                  true
% 31.48/4.51  --res_passive_queue_type                priority_queues
% 31.48/4.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.48/4.51  --res_passive_queues_freq               [15;5]
% 31.48/4.51  --res_forward_subs                      full
% 31.48/4.51  --res_backward_subs                     full
% 31.48/4.51  --res_forward_subs_resolution           true
% 31.48/4.51  --res_backward_subs_resolution          true
% 31.48/4.51  --res_orphan_elimination                true
% 31.48/4.51  --res_time_limit                        2.
% 31.48/4.51  --res_out_proof                         true
% 31.48/4.51  
% 31.48/4.51  ------ Superposition Options
% 31.48/4.51  
% 31.48/4.51  --superposition_flag                    true
% 31.48/4.51  --sup_passive_queue_type                priority_queues
% 31.48/4.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.48/4.51  --sup_passive_queues_freq               [8;1;4]
% 31.48/4.51  --demod_completeness_check              fast
% 31.48/4.51  --demod_use_ground                      true
% 31.48/4.51  --sup_to_prop_solver                    passive
% 31.48/4.51  --sup_prop_simpl_new                    true
% 31.48/4.51  --sup_prop_simpl_given                  true
% 31.48/4.51  --sup_fun_splitting                     false
% 31.48/4.51  --sup_smt_interval                      50000
% 31.48/4.51  
% 31.48/4.51  ------ Superposition Simplification Setup
% 31.48/4.51  
% 31.48/4.51  --sup_indices_passive                   []
% 31.48/4.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.48/4.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.48/4.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.48/4.51  --sup_full_triv                         [TrivRules;PropSubs]
% 31.48/4.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.48/4.51  --sup_full_bw                           [BwDemod]
% 31.48/4.51  --sup_immed_triv                        [TrivRules]
% 31.48/4.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.48/4.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.48/4.51  --sup_immed_bw_main                     []
% 31.48/4.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.48/4.51  --sup_input_triv                        [Unflattening;TrivRules]
% 31.48/4.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.48/4.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.48/4.51  
% 31.48/4.51  ------ Combination Options
% 31.48/4.51  
% 31.48/4.51  --comb_res_mult                         3
% 31.48/4.51  --comb_sup_mult                         2
% 31.48/4.51  --comb_inst_mult                        10
% 31.48/4.51  
% 31.48/4.51  ------ Debug Options
% 31.48/4.51  
% 31.48/4.51  --dbg_backtrace                         false
% 31.48/4.51  --dbg_dump_prop_clauses                 false
% 31.48/4.51  --dbg_dump_prop_clauses_file            -
% 31.48/4.51  --dbg_out_stat                          false
% 31.48/4.51  
% 31.48/4.51  
% 31.48/4.51  
% 31.48/4.51  
% 31.48/4.51  ------ Proving...
% 31.48/4.51  
% 31.48/4.51  
% 31.48/4.51  % SZS status Theorem for theBenchmark.p
% 31.48/4.51  
% 31.48/4.51  % SZS output start CNFRefutation for theBenchmark.p
% 31.48/4.51  
% 31.48/4.51  fof(f9,axiom,(
% 31.48/4.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f55,plain,(
% 31.48/4.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f9])).
% 31.48/4.51  
% 31.48/4.51  fof(f10,axiom,(
% 31.48/4.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f56,plain,(
% 31.48/4.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f10])).
% 31.48/4.51  
% 31.48/4.51  fof(f11,axiom,(
% 31.48/4.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f57,plain,(
% 31.48/4.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f11])).
% 31.48/4.51  
% 31.48/4.51  fof(f12,axiom,(
% 31.48/4.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f58,plain,(
% 31.48/4.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f12])).
% 31.48/4.51  
% 31.48/4.51  fof(f13,axiom,(
% 31.48/4.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f59,plain,(
% 31.48/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f13])).
% 31.48/4.51  
% 31.48/4.51  fof(f65,plain,(
% 31.48/4.51    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 31.48/4.51    inference(definition_unfolding,[],[f58,f59])).
% 31.48/4.51  
% 31.48/4.51  fof(f66,plain,(
% 31.48/4.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 31.48/4.51    inference(definition_unfolding,[],[f57,f65])).
% 31.48/4.51  
% 31.48/4.51  fof(f67,plain,(
% 31.48/4.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 31.48/4.51    inference(definition_unfolding,[],[f56,f66])).
% 31.48/4.51  
% 31.48/4.51  fof(f69,plain,(
% 31.48/4.51    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 31.48/4.51    inference(definition_unfolding,[],[f55,f67])).
% 31.48/4.51  
% 31.48/4.51  fof(f4,axiom,(
% 31.48/4.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f24,plain,(
% 31.48/4.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 31.48/4.51    inference(ennf_transformation,[],[f4])).
% 31.48/4.51  
% 31.48/4.51  fof(f31,plain,(
% 31.48/4.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 31.48/4.51    inference(nnf_transformation,[],[f24])).
% 31.48/4.51  
% 31.48/4.51  fof(f32,plain,(
% 31.48/4.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 31.48/4.51    inference(flattening,[],[f31])).
% 31.48/4.51  
% 31.48/4.51  fof(f33,plain,(
% 31.48/4.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 31.48/4.51    inference(rectify,[],[f32])).
% 31.48/4.51  
% 31.48/4.51  fof(f34,plain,(
% 31.48/4.51    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 31.48/4.51    introduced(choice_axiom,[])).
% 31.48/4.51  
% 31.48/4.51  fof(f35,plain,(
% 31.48/4.51    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 31.48/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 31.48/4.51  
% 31.48/4.51  fof(f44,plain,(
% 31.48/4.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 31.48/4.51    inference(cnf_transformation,[],[f35])).
% 31.48/4.51  
% 31.48/4.51  fof(f77,plain,(
% 31.48/4.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 31.48/4.51    inference(definition_unfolding,[],[f44,f67])).
% 31.48/4.51  
% 31.48/4.51  fof(f86,plain,(
% 31.48/4.51    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 31.48/4.51    inference(equality_resolution,[],[f77])).
% 31.48/4.51  
% 31.48/4.51  fof(f87,plain,(
% 31.48/4.51    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 31.48/4.51    inference(equality_resolution,[],[f86])).
% 31.48/4.51  
% 31.48/4.51  fof(f15,axiom,(
% 31.48/4.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f25,plain,(
% 31.48/4.51    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 31.48/4.51    inference(ennf_transformation,[],[f15])).
% 31.48/4.51  
% 31.48/4.51  fof(f61,plain,(
% 31.48/4.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f25])).
% 31.48/4.51  
% 31.48/4.51  fof(f17,conjecture,(
% 31.48/4.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f18,negated_conjecture,(
% 31.48/4.51    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 31.48/4.51    inference(negated_conjecture,[],[f17])).
% 31.48/4.51  
% 31.48/4.51  fof(f26,plain,(
% 31.48/4.51    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 31.48/4.51    inference(ennf_transformation,[],[f18])).
% 31.48/4.51  
% 31.48/4.51  fof(f36,plain,(
% 31.48/4.51    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4))),
% 31.48/4.51    introduced(choice_axiom,[])).
% 31.48/4.51  
% 31.48/4.51  fof(f37,plain,(
% 31.48/4.51    ~r2_hidden(sK2,sK4) & r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 31.48/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f36])).
% 31.48/4.51  
% 31.48/4.51  fof(f63,plain,(
% 31.48/4.51    r1_tarski(k2_xboole_0(k2_tarski(sK2,sK3),sK4),sK4)),
% 31.48/4.51    inference(cnf_transformation,[],[f37])).
% 31.48/4.51  
% 31.48/4.51  fof(f16,axiom,(
% 31.48/4.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f62,plain,(
% 31.48/4.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 31.48/4.51    inference(cnf_transformation,[],[f16])).
% 31.48/4.51  
% 31.48/4.51  fof(f81,plain,(
% 31.48/4.51    r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4)),
% 31.48/4.51    inference(definition_unfolding,[],[f63,f62])).
% 31.48/4.51  
% 31.48/4.51  fof(f2,axiom,(
% 31.48/4.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f19,plain,(
% 31.48/4.51    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 31.48/4.51    inference(unused_predicate_definition_removal,[],[f2])).
% 31.48/4.51  
% 31.48/4.51  fof(f21,plain,(
% 31.48/4.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 31.48/4.51    inference(ennf_transformation,[],[f19])).
% 31.48/4.51  
% 31.48/4.51  fof(f22,plain,(
% 31.48/4.51    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 31.48/4.51    inference(flattening,[],[f21])).
% 31.48/4.51  
% 31.48/4.51  fof(f41,plain,(
% 31.48/4.51    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f22])).
% 31.48/4.51  
% 31.48/4.51  fof(f3,axiom,(
% 31.48/4.51    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f23,plain,(
% 31.48/4.51    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 31.48/4.51    inference(ennf_transformation,[],[f3])).
% 31.48/4.51  
% 31.48/4.51  fof(f42,plain,(
% 31.48/4.51    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f23])).
% 31.48/4.51  
% 31.48/4.51  fof(f46,plain,(
% 31.48/4.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 31.48/4.51    inference(cnf_transformation,[],[f35])).
% 31.48/4.51  
% 31.48/4.51  fof(f75,plain,(
% 31.48/4.51    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 31.48/4.51    inference(definition_unfolding,[],[f46,f67])).
% 31.48/4.51  
% 31.48/4.51  fof(f82,plain,(
% 31.48/4.51    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 31.48/4.51    inference(equality_resolution,[],[f75])).
% 31.48/4.51  
% 31.48/4.51  fof(f83,plain,(
% 31.48/4.51    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 31.48/4.51    inference(equality_resolution,[],[f82])).
% 31.48/4.51  
% 31.48/4.51  fof(f1,axiom,(
% 31.48/4.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 31.48/4.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.48/4.51  
% 31.48/4.51  fof(f20,plain,(
% 31.48/4.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 31.48/4.51    inference(ennf_transformation,[],[f1])).
% 31.48/4.51  
% 31.48/4.51  fof(f27,plain,(
% 31.48/4.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 31.48/4.51    inference(nnf_transformation,[],[f20])).
% 31.48/4.51  
% 31.48/4.51  fof(f28,plain,(
% 31.48/4.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.48/4.51    inference(rectify,[],[f27])).
% 31.48/4.51  
% 31.48/4.51  fof(f29,plain,(
% 31.48/4.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 31.48/4.51    introduced(choice_axiom,[])).
% 31.48/4.51  
% 31.48/4.51  fof(f30,plain,(
% 31.48/4.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 31.48/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 31.48/4.51  
% 31.48/4.51  fof(f38,plain,(
% 31.48/4.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 31.48/4.51    inference(cnf_transformation,[],[f30])).
% 31.48/4.51  
% 31.48/4.51  fof(f64,plain,(
% 31.48/4.51    ~r2_hidden(sK2,sK4)),
% 31.48/4.51    inference(cnf_transformation,[],[f37])).
% 31.48/4.51  
% 31.48/4.51  cnf(c_0,plain,
% 31.48/4.51      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
% 31.48/4.51      inference(cnf_transformation,[],[f69]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_13,plain,
% 31.48/4.51      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 31.48/4.51      inference(cnf_transformation,[],[f87]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_558,plain,
% 31.48/4.51      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 31.48/4.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_718,plain,
% 31.48/4.51      ( r2_hidden(X0,k2_tarski(X0,X1)) = iProver_top ),
% 31.48/4.51      inference(superposition,[status(thm)],[c_0,c_558]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_17,plain,
% 31.48/4.51      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 31.48/4.51      inference(cnf_transformation,[],[f61]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_556,plain,
% 31.48/4.51      ( r2_hidden(X0,X1) != iProver_top
% 31.48/4.51      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 31.48/4.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_19,negated_conjecture,
% 31.48/4.51      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) ),
% 31.48/4.51      inference(cnf_transformation,[],[f81]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_554,plain,
% 31.48/4.51      ( r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)),sK4) = iProver_top ),
% 31.48/4.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_5,plain,
% 31.48/4.51      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 31.48/4.51      inference(cnf_transformation,[],[f41]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_6,plain,
% 31.48/4.51      ( ~ r2_xboole_0(X0,X1) | ~ r1_tarski(X1,X0) ),
% 31.48/4.51      inference(cnf_transformation,[],[f42]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_180,plain,
% 31.48/4.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 31.48/4.51      inference(resolution,[status(thm)],[c_5,c_6]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_553,plain,
% 31.48/4.51      ( X0 = X1
% 31.48/4.51      | r1_tarski(X0,X1) != iProver_top
% 31.48/4.51      | r1_tarski(X1,X0) != iProver_top ),
% 31.48/4.51      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_1755,plain,
% 31.48/4.51      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 31.48/4.51      | r1_tarski(sK4,k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4))) != iProver_top ),
% 31.48/4.51      inference(superposition,[status(thm)],[c_554,c_553]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_1773,plain,
% 31.48/4.51      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4
% 31.48/4.51      | r2_hidden(sK4,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top ),
% 31.48/4.51      inference(superposition,[status(thm)],[c_556,c_1755]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_11,plain,
% 31.48/4.51      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 31.48/4.51      inference(cnf_transformation,[],[f83]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_560,plain,
% 31.48/4.51      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 31.48/4.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_871,plain,
% 31.48/4.51      ( r2_hidden(X0,k2_tarski(X1,X0)) = iProver_top ),
% 31.48/4.51      inference(superposition,[status(thm)],[c_0,c_560]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_1778,plain,
% 31.48/4.51      ( k3_tarski(k2_tarski(k2_tarski(sK2,sK3),sK4)) = sK4 ),
% 31.48/4.51      inference(forward_subsumption_resolution,
% 31.48/4.51                [status(thm)],
% 31.48/4.51                [c_1773,c_871]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_1781,plain,
% 31.48/4.51      ( r2_hidden(X0,k2_tarski(k2_tarski(sK2,sK3),sK4)) != iProver_top
% 31.48/4.51      | r1_tarski(X0,sK4) = iProver_top ),
% 31.48/4.51      inference(superposition,[status(thm)],[c_1778,c_556]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_2453,plain,
% 31.48/4.51      ( r1_tarski(k2_tarski(sK2,sK3),sK4) = iProver_top ),
% 31.48/4.51      inference(superposition,[status(thm)],[c_718,c_1781]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_4,plain,
% 31.48/4.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 31.48/4.51      inference(cnf_transformation,[],[f38]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_565,plain,
% 31.48/4.51      ( r2_hidden(X0,X1) != iProver_top
% 31.48/4.51      | r2_hidden(X0,X2) = iProver_top
% 31.48/4.51      | r1_tarski(X1,X2) != iProver_top ),
% 31.48/4.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_7348,plain,
% 31.48/4.51      ( r2_hidden(X0,X1) = iProver_top
% 31.48/4.51      | r1_tarski(k2_tarski(X0,X2),X1) != iProver_top ),
% 31.48/4.51      inference(superposition,[status(thm)],[c_718,c_565]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_90165,plain,
% 31.48/4.51      ( r2_hidden(sK2,sK4) = iProver_top ),
% 31.48/4.51      inference(superposition,[status(thm)],[c_2453,c_7348]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_18,negated_conjecture,
% 31.48/4.51      ( ~ r2_hidden(sK2,sK4) ),
% 31.48/4.51      inference(cnf_transformation,[],[f64]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(c_21,plain,
% 31.48/4.51      ( r2_hidden(sK2,sK4) != iProver_top ),
% 31.48/4.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.48/4.51  
% 31.48/4.51  cnf(contradiction,plain,
% 31.48/4.51      ( $false ),
% 31.48/4.51      inference(minisat,[status(thm)],[c_90165,c_21]) ).
% 31.48/4.51  
% 31.48/4.51  
% 31.48/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.48/4.51  
% 31.48/4.51  ------                               Statistics
% 31.48/4.51  
% 31.48/4.51  ------ General
% 31.48/4.51  
% 31.48/4.51  abstr_ref_over_cycles:                  0
% 31.48/4.51  abstr_ref_under_cycles:                 0
% 31.48/4.51  gc_basic_clause_elim:                   0
% 31.48/4.51  forced_gc_time:                         0
% 31.48/4.51  parsing_time:                           0.01
% 31.48/4.51  unif_index_cands_time:                  0.
% 31.48/4.51  unif_index_add_time:                    0.
% 31.48/4.51  orderings_time:                         0.
% 31.48/4.51  out_proof_time:                         0.01
% 31.48/4.51  total_time:                             3.858
% 31.48/4.51  num_of_symbols:                         42
% 31.48/4.51  num_of_terms:                           90274
% 31.48/4.51  
% 31.48/4.51  ------ Preprocessing
% 31.48/4.51  
% 31.48/4.51  num_of_splits:                          0
% 31.48/4.51  num_of_split_atoms:                     0
% 31.48/4.51  num_of_reused_defs:                     0
% 31.48/4.51  num_eq_ax_congr_red:                    41
% 31.48/4.51  num_of_sem_filtered_clauses:            1
% 31.48/4.51  num_of_subtypes:                        0
% 31.48/4.51  monotx_restored_types:                  0
% 31.48/4.51  sat_num_of_epr_types:                   0
% 31.48/4.51  sat_num_of_non_cyclic_types:            0
% 31.48/4.51  sat_guarded_non_collapsed_types:        0
% 31.48/4.51  num_pure_diseq_elim:                    0
% 31.48/4.51  simp_replaced_by:                       0
% 31.48/4.51  res_preprocessed:                       90
% 31.48/4.51  prep_upred:                             0
% 31.48/4.51  prep_unflattend:                        0
% 31.48/4.51  smt_new_axioms:                         0
% 31.48/4.51  pred_elim_cands:                        2
% 31.48/4.51  pred_elim:                              1
% 31.48/4.51  pred_elim_cl:                           1
% 31.48/4.51  pred_elim_cycles:                       3
% 31.48/4.51  merged_defs:                            0
% 31.48/4.51  merged_defs_ncl:                        0
% 31.48/4.51  bin_hyper_res:                          0
% 31.48/4.51  prep_cycles:                            4
% 31.48/4.51  pred_elim_time:                         0.
% 31.48/4.51  splitting_time:                         0.
% 31.48/4.51  sem_filter_time:                        0.
% 31.48/4.51  monotx_time:                            0.001
% 31.48/4.51  subtype_inf_time:                       0.
% 31.48/4.51  
% 31.48/4.51  ------ Problem properties
% 31.48/4.51  
% 31.48/4.51  clauses:                                19
% 31.48/4.51  conjectures:                            2
% 31.48/4.51  epr:                                    3
% 31.48/4.51  horn:                                   16
% 31.48/4.51  ground:                                 2
% 31.48/4.51  unary:                                  9
% 31.48/4.51  binary:                                 3
% 31.48/4.51  lits:                                   39
% 31.48/4.51  lits_eq:                                18
% 31.48/4.51  fd_pure:                                0
% 31.48/4.51  fd_pseudo:                              0
% 31.48/4.51  fd_cond:                                0
% 31.48/4.51  fd_pseudo_cond:                         5
% 31.48/4.51  ac_symbols:                             0
% 31.48/4.51  
% 31.48/4.51  ------ Propositional Solver
% 31.48/4.51  
% 31.48/4.51  prop_solver_calls:                      31
% 31.48/4.51  prop_fast_solver_calls:                 816
% 31.48/4.51  smt_solver_calls:                       0
% 31.48/4.51  smt_fast_solver_calls:                  0
% 31.48/4.51  prop_num_of_clauses:                    19074
% 31.48/4.51  prop_preprocess_simplified:             42476
% 31.48/4.51  prop_fo_subsumed:                       0
% 31.48/4.51  prop_solver_time:                       0.
% 31.48/4.51  smt_solver_time:                        0.
% 31.48/4.51  smt_fast_solver_time:                   0.
% 31.48/4.51  prop_fast_solver_time:                  0.
% 31.48/4.51  prop_unsat_core_time:                   0.002
% 31.48/4.51  
% 31.48/4.51  ------ QBF
% 31.48/4.51  
% 31.48/4.51  qbf_q_res:                              0
% 31.48/4.51  qbf_num_tautologies:                    0
% 31.48/4.51  qbf_prep_cycles:                        0
% 31.48/4.51  
% 31.48/4.51  ------ BMC1
% 31.48/4.51  
% 31.48/4.51  bmc1_current_bound:                     -1
% 31.48/4.51  bmc1_last_solved_bound:                 -1
% 31.48/4.51  bmc1_unsat_core_size:                   -1
% 31.48/4.51  bmc1_unsat_core_parents_size:           -1
% 31.48/4.51  bmc1_merge_next_fun:                    0
% 31.48/4.51  bmc1_unsat_core_clauses_time:           0.
% 31.48/4.51  
% 31.48/4.51  ------ Instantiation
% 31.48/4.51  
% 31.48/4.51  inst_num_of_clauses:                    5161
% 31.48/4.51  inst_num_in_passive:                    2694
% 31.48/4.51  inst_num_in_active:                     1140
% 31.48/4.51  inst_num_in_unprocessed:                1329
% 31.48/4.51  inst_num_of_loops:                      1490
% 31.48/4.51  inst_num_of_learning_restarts:          0
% 31.48/4.51  inst_num_moves_active_passive:          349
% 31.48/4.51  inst_lit_activity:                      0
% 31.48/4.51  inst_lit_activity_moves:                0
% 31.48/4.51  inst_num_tautologies:                   0
% 31.48/4.51  inst_num_prop_implied:                  0
% 31.48/4.51  inst_num_existing_simplified:           0
% 31.48/4.51  inst_num_eq_res_simplified:             0
% 31.48/4.51  inst_num_child_elim:                    0
% 31.48/4.51  inst_num_of_dismatching_blockings:      10508
% 31.48/4.51  inst_num_of_non_proper_insts:           6546
% 31.48/4.51  inst_num_of_duplicates:                 0
% 31.48/4.51  inst_inst_num_from_inst_to_res:         0
% 31.48/4.51  inst_dismatching_checking_time:         0.
% 31.48/4.51  
% 31.48/4.51  ------ Resolution
% 31.48/4.51  
% 31.48/4.51  res_num_of_clauses:                     0
% 31.48/4.51  res_num_in_passive:                     0
% 31.48/4.51  res_num_in_active:                      0
% 31.48/4.51  res_num_of_loops:                       94
% 31.48/4.51  res_forward_subset_subsumed:            715
% 31.48/4.51  res_backward_subset_subsumed:           6
% 31.48/4.51  res_forward_subsumed:                   0
% 31.48/4.51  res_backward_subsumed:                  0
% 31.48/4.51  res_forward_subsumption_resolution:     0
% 31.48/4.51  res_backward_subsumption_resolution:    0
% 31.48/4.51  res_clause_to_clause_subsumption:       77221
% 31.48/4.51  res_orphan_elimination:                 0
% 31.48/4.51  res_tautology_del:                      473
% 31.48/4.51  res_num_eq_res_simplified:              0
% 31.48/4.51  res_num_sel_changes:                    0
% 31.48/4.51  res_moves_from_active_to_pass:          0
% 31.48/4.51  
% 31.48/4.51  ------ Superposition
% 31.48/4.51  
% 31.48/4.51  sup_time_total:                         0.
% 31.48/4.51  sup_time_generating:                    0.
% 31.48/4.51  sup_time_sim_full:                      0.
% 31.48/4.51  sup_time_sim_immed:                     0.
% 31.48/4.51  
% 31.48/4.51  sup_num_of_clauses:                     1977
% 31.48/4.51  sup_num_in_active:                      281
% 31.48/4.51  sup_num_in_passive:                     1696
% 31.48/4.51  sup_num_of_loops:                       297
% 31.48/4.51  sup_fw_superposition:                   13732
% 31.48/4.51  sup_bw_superposition:                   14035
% 31.48/4.51  sup_immediate_simplified:               1578
% 31.48/4.51  sup_given_eliminated:                   0
% 31.48/4.51  comparisons_done:                       0
% 31.48/4.51  comparisons_avoided:                    84
% 31.48/4.51  
% 31.48/4.51  ------ Simplifications
% 31.48/4.51  
% 31.48/4.51  
% 31.48/4.51  sim_fw_subset_subsumed:                 5
% 31.48/4.51  sim_bw_subset_subsumed:                 1
% 31.48/4.51  sim_fw_subsumed:                        155
% 31.48/4.51  sim_bw_subsumed:                        26
% 31.48/4.51  sim_fw_subsumption_res:                 1
% 31.48/4.51  sim_bw_subsumption_res:                 0
% 31.48/4.51  sim_tautology_del:                      0
% 31.48/4.51  sim_eq_tautology_del:                   91
% 31.48/4.51  sim_eq_res_simp:                        0
% 31.48/4.51  sim_fw_demodulated:                     574
% 31.48/4.51  sim_bw_demodulated:                     96
% 31.48/4.51  sim_light_normalised:                   778
% 31.48/4.51  sim_joinable_taut:                      0
% 31.48/4.51  sim_joinable_simp:                      0
% 31.48/4.51  sim_ac_normalised:                      0
% 31.48/4.51  sim_smt_subsumption:                    0
% 31.48/4.51  
%------------------------------------------------------------------------------
