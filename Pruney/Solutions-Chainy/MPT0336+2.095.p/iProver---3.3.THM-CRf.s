%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:49 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 141 expanded)
%              Number of clauses        :   39 (  44 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  187 ( 341 expanded)
%              Number of equality atoms :   60 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
      & r1_xboole_0(sK3,sK2)
      & r2_hidden(sK4,sK3)
      & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f26])).

fof(f46,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f56,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f46,f33,f51])).

fof(f48,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f45,f51])).

fof(f47,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f22])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f33,f33])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f40,f33])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_596,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_598,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_612,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1501,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_612])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_601,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_597,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_611,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4350,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_597,c_611])).

cnf(c_4728,plain,
    ( k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = X0
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_601,c_4350])).

cnf(c_4819,plain,
    ( k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = sK2 ),
    inference(superposition,[status(thm)],[c_1501,c_4728])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_603,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4947,plain,
    ( r1_tarski(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4819,c_603])).

cnf(c_6311,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_4947])).

cnf(c_6315,plain,
    ( r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6311,c_612])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_604,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6400,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_6315,c_604])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_602,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_876,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_602])).

cnf(c_6616,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6400,c_876])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_839,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_840,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_762,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_1,c_15])).

cnf(c_763,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_726,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_727,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
    | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6616,c_840,c_763,c_727,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.71/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.00  
% 3.71/1.00  ------  iProver source info
% 3.71/1.00  
% 3.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.00  git: non_committed_changes: false
% 3.71/1.00  git: last_make_outside_of_git: false
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  ------ Parsing...
% 3.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.00  ------ Proving...
% 3.71/1.00  ------ Problem Properties 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  clauses                                 18
% 3.71/1.00  conjectures                             4
% 3.71/1.00  EPR                                     4
% 3.71/1.00  Horn                                    15
% 3.71/1.00  unary                                   6
% 3.71/1.00  binary                                  10
% 3.71/1.00  lits                                    32
% 3.71/1.00  lits eq                                 5
% 3.71/1.00  fd_pure                                 0
% 3.71/1.00  fd_pseudo                               0
% 3.71/1.00  fd_cond                                 0
% 3.71/1.00  fd_pseudo_cond                          0
% 3.71/1.00  AC symbols                              0
% 3.71/1.00  
% 3.71/1.00  ------ Input Options Time Limit: Unbounded
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  Current options:
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ Proving...
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS status Theorem for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  fof(f13,conjecture,(
% 3.71/1.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f14,negated_conjecture,(
% 3.71/1.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.71/1.00    inference(negated_conjecture,[],[f13])).
% 3.71/1.00  
% 3.71/1.00  fof(f20,plain,(
% 3.71/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.71/1.00    inference(ennf_transformation,[],[f14])).
% 3.71/1.00  
% 3.71/1.00  fof(f21,plain,(
% 3.71/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.71/1.00    inference(flattening,[],[f20])).
% 3.71/1.00  
% 3.71/1.00  fof(f26,plain,(
% 3.71/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f27,plain,(
% 3.71/1.00    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f26])).
% 3.71/1.00  
% 3.71/1.00  fof(f46,plain,(
% 3.71/1.00    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 3.71/1.00    inference(cnf_transformation,[],[f27])).
% 3.71/1.00  
% 3.71/1.00  fof(f4,axiom,(
% 3.71/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f33,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f4])).
% 3.71/1.00  
% 3.71/1.00  fof(f9,axiom,(
% 3.71/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f41,plain,(
% 3.71/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f9])).
% 3.71/1.00  
% 3.71/1.00  fof(f10,axiom,(
% 3.71/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f42,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f10])).
% 3.71/1.00  
% 3.71/1.00  fof(f11,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f43,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f11])).
% 3.71/1.00  
% 3.71/1.00  fof(f50,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f42,f43])).
% 3.71/1.00  
% 3.71/1.00  fof(f51,plain,(
% 3.71/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f41,f50])).
% 3.71/1.00  
% 3.71/1.00  fof(f56,plain,(
% 3.71/1.00    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),
% 3.71/1.00    inference(definition_unfolding,[],[f46,f33,f51])).
% 3.71/1.00  
% 3.71/1.00  fof(f48,plain,(
% 3.71/1.00    r1_xboole_0(sK3,sK2)),
% 3.71/1.00    inference(cnf_transformation,[],[f27])).
% 3.71/1.00  
% 3.71/1.00  fof(f2,axiom,(
% 3.71/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f16,plain,(
% 3.71/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.71/1.00    inference(ennf_transformation,[],[f2])).
% 3.71/1.00  
% 3.71/1.00  fof(f29,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f16])).
% 3.71/1.00  
% 3.71/1.00  fof(f12,axiom,(
% 3.71/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f25,plain,(
% 3.71/1.00    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.71/1.00    inference(nnf_transformation,[],[f12])).
% 3.71/1.00  
% 3.71/1.00  fof(f45,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f25])).
% 3.71/1.00  
% 3.71/1.00  fof(f54,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f45,f51])).
% 3.71/1.00  
% 3.71/1.00  fof(f47,plain,(
% 3.71/1.00    r2_hidden(sK4,sK3)),
% 3.71/1.00    inference(cnf_transformation,[],[f27])).
% 3.71/1.00  
% 3.71/1.00  fof(f3,axiom,(
% 3.71/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f15,plain,(
% 3.71/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.71/1.00    inference(rectify,[],[f3])).
% 3.71/1.00  
% 3.71/1.00  fof(f17,plain,(
% 3.71/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.71/1.00    inference(ennf_transformation,[],[f15])).
% 3.71/1.00  
% 3.71/1.00  fof(f22,plain,(
% 3.71/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f23,plain,(
% 3.71/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f22])).
% 3.71/1.00  
% 3.71/1.00  fof(f32,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f23])).
% 3.71/1.00  
% 3.71/1.00  fof(f7,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f19,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.71/1.00    inference(ennf_transformation,[],[f7])).
% 3.71/1.00  
% 3.71/1.00  fof(f39,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f19])).
% 3.71/1.00  
% 3.71/1.00  fof(f6,axiom,(
% 3.71/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f24,plain,(
% 3.71/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.71/1.00    inference(nnf_transformation,[],[f6])).
% 3.71/1.00  
% 3.71/1.00  fof(f37,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f24])).
% 3.71/1.00  
% 3.71/1.00  fof(f1,axiom,(
% 3.71/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f28,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f1])).
% 3.71/1.00  
% 3.71/1.00  fof(f52,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.71/1.00    inference(definition_unfolding,[],[f28,f33,f33])).
% 3.71/1.00  
% 3.71/1.00  fof(f8,axiom,(
% 3.71/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f40,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f8])).
% 3.71/1.00  
% 3.71/1.00  fof(f53,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f40,f33])).
% 3.71/1.00  
% 3.71/1.00  fof(f5,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f18,plain,(
% 3.71/1.00    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.71/1.00    inference(ennf_transformation,[],[f5])).
% 3.71/1.00  
% 3.71/1.00  fof(f34,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f18])).
% 3.71/1.00  
% 3.71/1.00  fof(f49,plain,(
% 3.71/1.00    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 3.71/1.00    inference(cnf_transformation,[],[f27])).
% 3.71/1.00  
% 3.71/1.00  cnf(c_17,negated_conjecture,
% 3.71/1.00      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_596,plain,
% 3.71/1.00      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_15,negated_conjecture,
% 3.71/1.00      ( r1_xboole_0(sK3,sK2) ),
% 3.71/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_598,plain,
% 3.71/1.00      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1,plain,
% 3.71/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_612,plain,
% 3.71/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.71/1.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1501,plain,
% 3.71/1.00      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_598,c_612]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12,plain,
% 3.71/1.00      ( r2_hidden(X0,X1)
% 3.71/1.00      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 3.71/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_601,plain,
% 3.71/1.00      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 3.71/1.00      | r2_hidden(X1,X0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_16,negated_conjecture,
% 3.71/1.00      ( r2_hidden(sK4,sK3) ),
% 3.71/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_597,plain,
% 3.71/1.00      ( r2_hidden(sK4,sK3) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2,plain,
% 3.71/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_611,plain,
% 3.71/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.71/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.71/1.00      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4350,plain,
% 3.71/1.00      ( r2_hidden(sK4,X0) != iProver_top
% 3.71/1.00      | r1_xboole_0(X0,sK3) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_597,c_611]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4728,plain,
% 3.71/1.00      ( k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4)) = X0
% 3.71/1.00      | r1_xboole_0(X0,sK3) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_601,c_4350]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4819,plain,
% 3.71/1.00      ( k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4)) = sK2 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1501,c_4728]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_603,plain,
% 3.71/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.71/1.00      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4947,plain,
% 3.71/1.00      ( r1_tarski(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 3.71/1.00      | r1_xboole_0(X0,sK2) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4819,c_603]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6311,plain,
% 3.71/1.00      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_596,c_4947]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6315,plain,
% 3.71/1.00      ( r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_6311,c_612]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9,plain,
% 3.71/1.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_604,plain,
% 3.71/1.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6400,plain,
% 3.71/1.00      ( k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sK2 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_6315,c_604]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_0,plain,
% 3.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11,plain,
% 3.71/1.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_602,plain,
% 3.71/1.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_876,plain,
% 3.71/1.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X1) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_0,c_602]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6616,plain,
% 3.71/1.00      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_6400,c_876]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7,plain,
% 3.71/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.71/1.00      | ~ r1_xboole_0(X0,X2)
% 3.71/1.00      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_839,plain,
% 3.71/1.00      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
% 3.71/1.00      | ~ r1_xboole_0(sK2,sK3)
% 3.71/1.00      | ~ r1_xboole_0(sK2,sK1) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_840,plain,
% 3.71/1.00      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
% 3.71/1.00      | r1_xboole_0(sK2,sK3) != iProver_top
% 3.71/1.00      | r1_xboole_0(sK2,sK1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_762,plain,
% 3.71/1.00      ( r1_xboole_0(sK2,sK3) ),
% 3.71/1.00      inference(resolution,[status(thm)],[c_1,c_15]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_763,plain,
% 3.71/1.00      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_726,plain,
% 3.71/1.00      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
% 3.71/1.00      | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_727,plain,
% 3.71/1.00      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
% 3.71/1.00      | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_14,negated_conjecture,
% 3.71/1.00      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 3.71/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_21,plain,
% 3.71/1.00      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(contradiction,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(minisat,[status(thm)],[c_6616,c_840,c_763,c_727,c_21]) ).
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  ------                               Statistics
% 3.71/1.00  
% 3.71/1.00  ------ Selected
% 3.71/1.00  
% 3.71/1.00  total_time:                             0.222
% 3.71/1.00  
%------------------------------------------------------------------------------
