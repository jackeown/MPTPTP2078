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
% DateTime   : Thu Dec  3 11:38:00 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 254 expanded)
%              Number of clauses        :   26 (  59 expanded)
%              Number of leaves         :   16 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  215 ( 820 expanded)
%              Number of equality atoms :   71 ( 219 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f38])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f66])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f72,f66])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f82,f82])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f44])).

fof(f81,plain,(
    k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4 ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f83])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f84])).

fof(f100,plain,(
    k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) != sK4 ),
    inference(definition_unfolding,[],[f81,f82,f66,f85,f85])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f85])).

fof(f80,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1006,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1007,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1014,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2889,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r2_hidden(sK2(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1007,c_1014])).

cnf(c_15406,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1006,c_2889])).

cnf(c_24,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1000,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15523,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_15406,c_1000])).

cnf(c_16089,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_15523,c_15523])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_16098,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_15523,c_0])).

cnf(c_16176,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_16089,c_16098])).

cnf(c_28,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) != sK4 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_16077,plain,
    ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK4 ),
    inference(demodulation,[status(thm)],[c_15523,c_28])).

cnf(c_36606,plain,
    ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) != sK4 ),
    inference(demodulation,[status(thm)],[c_16176,c_16077])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1834,plain,
    ( ~ r1_tarski(X0,sK4)
    | k5_xboole_0(X0,k5_xboole_0(sK4,k3_xboole_0(sK4,X0))) = sK4 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2820,plain,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),sK4)
    | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(X0,X0,X0,X0,X0)))) = sK4 ),
    inference(instantiation,[status(thm)],[c_1834])).

cnf(c_2824,plain,
    ( ~ r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)
    | k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sK4 ),
    inference(instantiation,[status(thm)],[c_2820])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1285,plain,
    ( ~ r2_hidden(sK3,sK4)
    | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36606,c_2824,c_1285,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.77/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.77/1.48  
% 7.77/1.48  ------  iProver source info
% 7.77/1.48  
% 7.77/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.77/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.77/1.48  git: non_committed_changes: false
% 7.77/1.48  git: last_make_outside_of_git: false
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    --mode clausify
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             sel
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         604.99
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              none
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           false
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             false
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         false
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     num_symb
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       true
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     false
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   []
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_full_bw                           [BwDemod]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  ------ Parsing...
% 7.77/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.77/1.48  ------ Proving...
% 7.77/1.48  ------ Problem Properties 
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  clauses                                 29
% 7.77/1.48  conjectures                             2
% 7.77/1.48  EPR                                     5
% 7.77/1.48  Horn                                    19
% 7.77/1.48  unary                                   6
% 7.77/1.48  binary                                  12
% 7.77/1.48  lits                                    64
% 7.77/1.48  lits eq                                 12
% 7.77/1.48  fd_pure                                 0
% 7.77/1.48  fd_pseudo                               0
% 7.77/1.48  fd_cond                                 0
% 7.77/1.48  fd_pseudo_cond                          4
% 7.77/1.48  AC symbols                              0
% 7.77/1.48  
% 7.77/1.48  ------ Input Options Time Limit: Unbounded
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ 
% 7.77/1.48  Current options:
% 7.77/1.48  ------ 
% 7.77/1.48  
% 7.77/1.48  ------ Input Options
% 7.77/1.48  
% 7.77/1.48  --out_options                           all
% 7.77/1.48  --tptp_safe_out                         true
% 7.77/1.48  --problem_path                          ""
% 7.77/1.48  --include_path                          ""
% 7.77/1.48  --clausifier                            res/vclausify_rel
% 7.77/1.48  --clausifier_options                    --mode clausify
% 7.77/1.48  --stdin                                 false
% 7.77/1.48  --stats_out                             sel
% 7.77/1.48  
% 7.77/1.48  ------ General Options
% 7.77/1.48  
% 7.77/1.48  --fof                                   false
% 7.77/1.48  --time_out_real                         604.99
% 7.77/1.48  --time_out_virtual                      -1.
% 7.77/1.48  --symbol_type_check                     false
% 7.77/1.48  --clausify_out                          false
% 7.77/1.48  --sig_cnt_out                           false
% 7.77/1.48  --trig_cnt_out                          false
% 7.77/1.48  --trig_cnt_out_tolerance                1.
% 7.77/1.48  --trig_cnt_out_sk_spl                   false
% 7.77/1.48  --abstr_cl_out                          false
% 7.77/1.48  
% 7.77/1.48  ------ Global Options
% 7.77/1.48  
% 7.77/1.48  --schedule                              none
% 7.77/1.48  --add_important_lit                     false
% 7.77/1.48  --prop_solver_per_cl                    1000
% 7.77/1.48  --min_unsat_core                        false
% 7.77/1.48  --soft_assumptions                      false
% 7.77/1.48  --soft_lemma_size                       3
% 7.77/1.48  --prop_impl_unit_size                   0
% 7.77/1.48  --prop_impl_unit                        []
% 7.77/1.48  --share_sel_clauses                     true
% 7.77/1.48  --reset_solvers                         false
% 7.77/1.48  --bc_imp_inh                            [conj_cone]
% 7.77/1.48  --conj_cone_tolerance                   3.
% 7.77/1.48  --extra_neg_conj                        none
% 7.77/1.48  --large_theory_mode                     true
% 7.77/1.48  --prolific_symb_bound                   200
% 7.77/1.48  --lt_threshold                          2000
% 7.77/1.48  --clause_weak_htbl                      true
% 7.77/1.48  --gc_record_bc_elim                     false
% 7.77/1.48  
% 7.77/1.48  ------ Preprocessing Options
% 7.77/1.48  
% 7.77/1.48  --preprocessing_flag                    true
% 7.77/1.48  --time_out_prep_mult                    0.1
% 7.77/1.48  --splitting_mode                        input
% 7.77/1.48  --splitting_grd                         true
% 7.77/1.48  --splitting_cvd                         false
% 7.77/1.48  --splitting_cvd_svl                     false
% 7.77/1.48  --splitting_nvd                         32
% 7.77/1.48  --sub_typing                            true
% 7.77/1.48  --prep_gs_sim                           false
% 7.77/1.48  --prep_unflatten                        true
% 7.77/1.48  --prep_res_sim                          true
% 7.77/1.48  --prep_upred                            true
% 7.77/1.48  --prep_sem_filter                       exhaustive
% 7.77/1.48  --prep_sem_filter_out                   false
% 7.77/1.48  --pred_elim                             false
% 7.77/1.48  --res_sim_input                         true
% 7.77/1.48  --eq_ax_congr_red                       true
% 7.77/1.48  --pure_diseq_elim                       true
% 7.77/1.48  --brand_transform                       false
% 7.77/1.48  --non_eq_to_eq                          false
% 7.77/1.48  --prep_def_merge                        true
% 7.77/1.48  --prep_def_merge_prop_impl              false
% 7.77/1.48  --prep_def_merge_mbd                    true
% 7.77/1.48  --prep_def_merge_tr_red                 false
% 7.77/1.48  --prep_def_merge_tr_cl                  false
% 7.77/1.48  --smt_preprocessing                     true
% 7.77/1.48  --smt_ac_axioms                         fast
% 7.77/1.48  --preprocessed_out                      false
% 7.77/1.48  --preprocessed_stats                    false
% 7.77/1.48  
% 7.77/1.48  ------ Abstraction refinement Options
% 7.77/1.48  
% 7.77/1.48  --abstr_ref                             []
% 7.77/1.48  --abstr_ref_prep                        false
% 7.77/1.48  --abstr_ref_until_sat                   false
% 7.77/1.48  --abstr_ref_sig_restrict                funpre
% 7.77/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.48  --abstr_ref_under                       []
% 7.77/1.48  
% 7.77/1.48  ------ SAT Options
% 7.77/1.48  
% 7.77/1.48  --sat_mode                              false
% 7.77/1.48  --sat_fm_restart_options                ""
% 7.77/1.48  --sat_gr_def                            false
% 7.77/1.48  --sat_epr_types                         true
% 7.77/1.48  --sat_non_cyclic_types                  false
% 7.77/1.48  --sat_finite_models                     false
% 7.77/1.48  --sat_fm_lemmas                         false
% 7.77/1.48  --sat_fm_prep                           false
% 7.77/1.48  --sat_fm_uc_incr                        true
% 7.77/1.48  --sat_out_model                         small
% 7.77/1.48  --sat_out_clauses                       false
% 7.77/1.48  
% 7.77/1.48  ------ QBF Options
% 7.77/1.48  
% 7.77/1.48  --qbf_mode                              false
% 7.77/1.48  --qbf_elim_univ                         false
% 7.77/1.48  --qbf_dom_inst                          none
% 7.77/1.48  --qbf_dom_pre_inst                      false
% 7.77/1.48  --qbf_sk_in                             false
% 7.77/1.48  --qbf_pred_elim                         true
% 7.77/1.48  --qbf_split                             512
% 7.77/1.48  
% 7.77/1.48  ------ BMC1 Options
% 7.77/1.48  
% 7.77/1.48  --bmc1_incremental                      false
% 7.77/1.48  --bmc1_axioms                           reachable_all
% 7.77/1.48  --bmc1_min_bound                        0
% 7.77/1.48  --bmc1_max_bound                        -1
% 7.77/1.48  --bmc1_max_bound_default                -1
% 7.77/1.48  --bmc1_symbol_reachability              true
% 7.77/1.48  --bmc1_property_lemmas                  false
% 7.77/1.48  --bmc1_k_induction                      false
% 7.77/1.48  --bmc1_non_equiv_states                 false
% 7.77/1.48  --bmc1_deadlock                         false
% 7.77/1.48  --bmc1_ucm                              false
% 7.77/1.48  --bmc1_add_unsat_core                   none
% 7.77/1.48  --bmc1_unsat_core_children              false
% 7.77/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.48  --bmc1_out_stat                         full
% 7.77/1.48  --bmc1_ground_init                      false
% 7.77/1.48  --bmc1_pre_inst_next_state              false
% 7.77/1.48  --bmc1_pre_inst_state                   false
% 7.77/1.48  --bmc1_pre_inst_reach_state             false
% 7.77/1.48  --bmc1_out_unsat_core                   false
% 7.77/1.48  --bmc1_aig_witness_out                  false
% 7.77/1.48  --bmc1_verbose                          false
% 7.77/1.48  --bmc1_dump_clauses_tptp                false
% 7.77/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.48  --bmc1_dump_file                        -
% 7.77/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.48  --bmc1_ucm_extend_mode                  1
% 7.77/1.48  --bmc1_ucm_init_mode                    2
% 7.77/1.48  --bmc1_ucm_cone_mode                    none
% 7.77/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.48  --bmc1_ucm_relax_model                  4
% 7.77/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.48  --bmc1_ucm_layered_model                none
% 7.77/1.48  --bmc1_ucm_max_lemma_size               10
% 7.77/1.48  
% 7.77/1.48  ------ AIG Options
% 7.77/1.48  
% 7.77/1.48  --aig_mode                              false
% 7.77/1.48  
% 7.77/1.48  ------ Instantiation Options
% 7.77/1.48  
% 7.77/1.48  --instantiation_flag                    true
% 7.77/1.48  --inst_sos_flag                         false
% 7.77/1.48  --inst_sos_phase                        true
% 7.77/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.48  --inst_lit_sel_side                     num_symb
% 7.77/1.48  --inst_solver_per_active                1400
% 7.77/1.48  --inst_solver_calls_frac                1.
% 7.77/1.48  --inst_passive_queue_type               priority_queues
% 7.77/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.48  --inst_passive_queues_freq              [25;2]
% 7.77/1.48  --inst_dismatching                      true
% 7.77/1.48  --inst_eager_unprocessed_to_passive     true
% 7.77/1.48  --inst_prop_sim_given                   true
% 7.77/1.48  --inst_prop_sim_new                     false
% 7.77/1.48  --inst_subs_new                         false
% 7.77/1.48  --inst_eq_res_simp                      false
% 7.77/1.48  --inst_subs_given                       false
% 7.77/1.48  --inst_orphan_elimination               true
% 7.77/1.48  --inst_learning_loop_flag               true
% 7.77/1.48  --inst_learning_start                   3000
% 7.77/1.48  --inst_learning_factor                  2
% 7.77/1.48  --inst_start_prop_sim_after_learn       3
% 7.77/1.48  --inst_sel_renew                        solver
% 7.77/1.48  --inst_lit_activity_flag                true
% 7.77/1.48  --inst_restr_to_given                   false
% 7.77/1.48  --inst_activity_threshold               500
% 7.77/1.48  --inst_out_proof                        true
% 7.77/1.48  
% 7.77/1.48  ------ Resolution Options
% 7.77/1.48  
% 7.77/1.48  --resolution_flag                       true
% 7.77/1.48  --res_lit_sel                           adaptive
% 7.77/1.48  --res_lit_sel_side                      none
% 7.77/1.48  --res_ordering                          kbo
% 7.77/1.48  --res_to_prop_solver                    active
% 7.77/1.48  --res_prop_simpl_new                    false
% 7.77/1.48  --res_prop_simpl_given                  true
% 7.77/1.48  --res_passive_queue_type                priority_queues
% 7.77/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.48  --res_passive_queues_freq               [15;5]
% 7.77/1.48  --res_forward_subs                      full
% 7.77/1.48  --res_backward_subs                     full
% 7.77/1.48  --res_forward_subs_resolution           true
% 7.77/1.48  --res_backward_subs_resolution          true
% 7.77/1.48  --res_orphan_elimination                true
% 7.77/1.48  --res_time_limit                        2.
% 7.77/1.48  --res_out_proof                         true
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Options
% 7.77/1.48  
% 7.77/1.48  --superposition_flag                    true
% 7.77/1.48  --sup_passive_queue_type                priority_queues
% 7.77/1.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.48  --sup_passive_queues_freq               [1;4]
% 7.77/1.48  --demod_completeness_check              fast
% 7.77/1.48  --demod_use_ground                      true
% 7.77/1.48  --sup_to_prop_solver                    passive
% 7.77/1.48  --sup_prop_simpl_new                    true
% 7.77/1.48  --sup_prop_simpl_given                  true
% 7.77/1.48  --sup_fun_splitting                     false
% 7.77/1.48  --sup_smt_interval                      50000
% 7.77/1.48  
% 7.77/1.48  ------ Superposition Simplification Setup
% 7.77/1.48  
% 7.77/1.48  --sup_indices_passive                   []
% 7.77/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_full_bw                           [BwDemod]
% 7.77/1.48  --sup_immed_triv                        [TrivRules]
% 7.77/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_immed_bw_main                     []
% 7.77/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.77/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.77/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.77/1.48  
% 7.77/1.48  ------ Combination Options
% 7.77/1.48  
% 7.77/1.48  --comb_res_mult                         3
% 7.77/1.48  --comb_sup_mult                         2
% 7.77/1.48  --comb_inst_mult                        10
% 7.77/1.48  
% 7.77/1.48  ------ Debug Options
% 7.77/1.48  
% 7.77/1.48  --dbg_backtrace                         false
% 7.77/1.48  --dbg_dump_prop_clauses                 false
% 7.77/1.48  --dbg_dump_prop_clauses_file            -
% 7.77/1.48  --dbg_out_stat                          false
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  ------ Proving...
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS status Theorem for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  fof(f5,axiom,(
% 7.77/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f21,plain,(
% 7.77/1.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.77/1.48    inference(rectify,[],[f5])).
% 7.77/1.48  
% 7.77/1.48  fof(f24,plain,(
% 7.77/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.77/1.48    inference(ennf_transformation,[],[f21])).
% 7.77/1.48  
% 7.77/1.48  fof(f38,plain,(
% 7.77/1.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f39,plain,(
% 7.77/1.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f38])).
% 7.77/1.48  
% 7.77/1.48  fof(f60,plain,(
% 7.77/1.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f61,plain,(
% 7.77/1.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f39])).
% 7.77/1.48  
% 7.77/1.48  fof(f3,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f32,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.77/1.48    inference(nnf_transformation,[],[f3])).
% 7.77/1.48  
% 7.77/1.48  fof(f33,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.77/1.48    inference(flattening,[],[f32])).
% 7.77/1.48  
% 7.77/1.48  fof(f34,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.77/1.48    inference(rectify,[],[f33])).
% 7.77/1.48  
% 7.77/1.48  fof(f35,plain,(
% 7.77/1.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f36,plain,(
% 7.77/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 7.77/1.48  
% 7.77/1.48  fof(f51,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.77/1.48    inference(cnf_transformation,[],[f36])).
% 7.77/1.48  
% 7.77/1.48  fof(f7,axiom,(
% 7.77/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f66,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f7])).
% 7.77/1.48  
% 7.77/1.48  fof(f91,plain,(
% 7.77/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.77/1.48    inference(definition_unfolding,[],[f51,f66])).
% 7.77/1.48  
% 7.77/1.48  fof(f102,plain,(
% 7.77/1.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.77/1.48    inference(equality_resolution,[],[f91])).
% 7.77/1.48  
% 7.77/1.48  fof(f11,axiom,(
% 7.77/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f42,plain,(
% 7.77/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 7.77/1.48    inference(nnf_transformation,[],[f11])).
% 7.77/1.48  
% 7.77/1.48  fof(f70,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f42])).
% 7.77/1.48  
% 7.77/1.48  fof(f96,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f70,f66])).
% 7.77/1.48  
% 7.77/1.48  fof(f1,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f46,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f1])).
% 7.77/1.48  
% 7.77/1.48  fof(f12,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f72,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.77/1.48    inference(cnf_transformation,[],[f12])).
% 7.77/1.48  
% 7.77/1.48  fof(f82,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.77/1.48    inference(definition_unfolding,[],[f72,f66])).
% 7.77/1.48  
% 7.77/1.48  fof(f86,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.77/1.48    inference(definition_unfolding,[],[f46,f82,f82])).
% 7.77/1.48  
% 7.77/1.48  fof(f19,conjecture,(
% 7.77/1.48    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f20,negated_conjecture,(
% 7.77/1.48    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 7.77/1.48    inference(negated_conjecture,[],[f19])).
% 7.77/1.48  
% 7.77/1.48  fof(f27,plain,(
% 7.77/1.48    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 7.77/1.48    inference(ennf_transformation,[],[f20])).
% 7.77/1.48  
% 7.77/1.48  fof(f44,plain,(
% 7.77/1.48    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4 & r2_hidden(sK3,sK4))),
% 7.77/1.48    introduced(choice_axiom,[])).
% 7.77/1.48  
% 7.77/1.48  fof(f45,plain,(
% 7.77/1.48    k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4 & r2_hidden(sK3,sK4)),
% 7.77/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f44])).
% 7.77/1.48  
% 7.77/1.48  fof(f81,plain,(
% 7.77/1.48    k2_xboole_0(k4_xboole_0(sK4,k1_tarski(sK3)),k1_tarski(sK3)) != sK4),
% 7.77/1.48    inference(cnf_transformation,[],[f45])).
% 7.77/1.48  
% 7.77/1.48  fof(f13,axiom,(
% 7.77/1.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f73,plain,(
% 7.77/1.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f13])).
% 7.77/1.48  
% 7.77/1.48  fof(f14,axiom,(
% 7.77/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f74,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f14])).
% 7.77/1.48  
% 7.77/1.48  fof(f15,axiom,(
% 7.77/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f75,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f15])).
% 7.77/1.48  
% 7.77/1.48  fof(f16,axiom,(
% 7.77/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f76,plain,(
% 7.77/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f16])).
% 7.77/1.48  
% 7.77/1.48  fof(f83,plain,(
% 7.77/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f75,f76])).
% 7.77/1.48  
% 7.77/1.48  fof(f84,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f74,f83])).
% 7.77/1.48  
% 7.77/1.48  fof(f85,plain,(
% 7.77/1.48    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f73,f84])).
% 7.77/1.48  
% 7.77/1.48  fof(f100,plain,(
% 7.77/1.48    k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) != sK4),
% 7.77/1.48    inference(definition_unfolding,[],[f81,f82,f66,f85,f85])).
% 7.77/1.48  
% 7.77/1.48  fof(f8,axiom,(
% 7.77/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f25,plain,(
% 7.77/1.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.77/1.48    inference(ennf_transformation,[],[f8])).
% 7.77/1.48  
% 7.77/1.48  fof(f67,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f25])).
% 7.77/1.48  
% 7.77/1.48  fof(f93,plain,(
% 7.77/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f67,f82])).
% 7.77/1.48  
% 7.77/1.48  fof(f17,axiom,(
% 7.77/1.48    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 7.77/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.48  
% 7.77/1.48  fof(f43,plain,(
% 7.77/1.48    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 7.77/1.48    inference(nnf_transformation,[],[f17])).
% 7.77/1.48  
% 7.77/1.48  fof(f78,plain,(
% 7.77/1.48    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.77/1.48    inference(cnf_transformation,[],[f43])).
% 7.77/1.48  
% 7.77/1.48  fof(f97,plain,(
% 7.77/1.48    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 7.77/1.48    inference(definition_unfolding,[],[f78,f85])).
% 7.77/1.48  
% 7.77/1.48  fof(f80,plain,(
% 7.77/1.48    r2_hidden(sK3,sK4)),
% 7.77/1.48    inference(cnf_transformation,[],[f45])).
% 7.77/1.48  
% 7.77/1.48  cnf(c_16,plain,
% 7.77/1.48      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 7.77/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1006,plain,
% 7.77/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 7.77/1.48      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_15,plain,
% 7.77/1.48      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1007,plain,
% 7.77/1.48      ( r1_xboole_0(X0,X1) = iProver_top
% 7.77/1.48      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_8,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,X1)
% 7.77/1.48      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f102]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1014,plain,
% 7.77/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.77/1.48      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2889,plain,
% 7.77/1.48      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 7.77/1.48      | r2_hidden(sK2(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X2) != iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1007,c_1014]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_15406,plain,
% 7.77/1.48      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = iProver_top ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_1006,c_2889]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_24,plain,
% 7.77/1.48      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 7.77/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1000,plain,
% 7.77/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 7.77/1.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.77/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_15523,plain,
% 7.77/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_15406,c_1000]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_16089,plain,
% 7.77/1.48      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_15523,c_15523]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_0,plain,
% 7.77/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 7.77/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_16098,plain,
% 7.77/1.48      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0) ),
% 7.77/1.48      inference(superposition,[status(thm)],[c_15523,c_0]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_16176,plain,
% 7.77/1.48      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_16089,c_16098]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_28,negated_conjecture,
% 7.77/1.48      ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))))) != sK4 ),
% 7.77/1.48      inference(cnf_transformation,[],[f100]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_16077,plain,
% 7.77/1.48      ( k5_xboole_0(k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3))),k3_enumset1(sK3,sK3,sK3,sK3,sK3)) != sK4 ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_15523,c_28]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_36606,plain,
% 7.77/1.48      ( k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) != sK4 ),
% 7.77/1.48      inference(demodulation,[status(thm)],[c_16176,c_16077]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_20,plain,
% 7.77/1.48      ( ~ r1_tarski(X0,X1)
% 7.77/1.48      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 7.77/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1834,plain,
% 7.77/1.48      ( ~ r1_tarski(X0,sK4)
% 7.77/1.48      | k5_xboole_0(X0,k5_xboole_0(sK4,k3_xboole_0(sK4,X0))) = sK4 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_20]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2820,plain,
% 7.77/1.48      ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),sK4)
% 7.77/1.48      | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(X0,X0,X0,X0,X0)))) = sK4 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_1834]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_2824,plain,
% 7.77/1.48      ( ~ r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4)
% 7.77/1.48      | k5_xboole_0(k3_enumset1(sK3,sK3,sK3,sK3,sK3),k5_xboole_0(sK4,k3_xboole_0(sK4,k3_enumset1(sK3,sK3,sK3,sK3,sK3)))) = sK4 ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_2820]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_25,plain,
% 7.77/1.48      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 7.77/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_1285,plain,
% 7.77/1.48      ( ~ r2_hidden(sK3,sK4)
% 7.77/1.48      | r1_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK3),sK4) ),
% 7.77/1.48      inference(instantiation,[status(thm)],[c_25]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(c_29,negated_conjecture,
% 7.77/1.48      ( r2_hidden(sK3,sK4) ),
% 7.77/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.77/1.48  
% 7.77/1.48  cnf(contradiction,plain,
% 7.77/1.48      ( $false ),
% 7.77/1.48      inference(minisat,[status(thm)],[c_36606,c_2824,c_1285,c_29]) ).
% 7.77/1.48  
% 7.77/1.48  
% 7.77/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.77/1.48  
% 7.77/1.48  ------                               Statistics
% 7.77/1.48  
% 7.77/1.48  ------ Selected
% 7.77/1.48  
% 7.77/1.48  total_time:                             0.871
% 7.77/1.48  
%------------------------------------------------------------------------------
