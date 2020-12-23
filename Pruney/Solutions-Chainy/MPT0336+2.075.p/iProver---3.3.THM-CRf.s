%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:45 EST 2020

% Result     : Theorem 23.45s
% Output     : CNFRefutation 23.45s
% Verified   : 
% Statistics : Number of formulae       :  309 (1455254 expanded)
%              Number of clauses        :  245 (376663 expanded)
%              Number of leaves         :   19 (387466 expanded)
%              Depth                    :   40
%              Number of atoms          :  455 (2623528 expanded)
%              Number of equality atoms :  285 (1133890 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :   12 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f31])).

fof(f36,plain,
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

fof(f37,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    & r1_xboole_0(sK3,sK2)
    & r2_hidden(sK4,sK3)
    & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f36])).

fof(f62,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f20,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f60,f46,f65])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f46,f46])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f43,f46,f46,f46,f46])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_710,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_727,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2172,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_710,c_727])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_712,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_715,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2995,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_715])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_709,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_726,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9633,plain,
    ( r2_hidden(sK4,X0) != iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_726])).

cnf(c_52463,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2995,c_9633])).

cnf(c_57982,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(superposition,[status(thm)],[c_2172,c_52463])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_708,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_723,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4690,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_708,c_723])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1906,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_11306,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_4690,c_1906])).

cnf(c_58173,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_57982,c_11306])).

cnf(c_11349,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) ),
    inference(superposition,[status(thm)],[c_1906,c_0])).

cnf(c_49528,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_11349,c_4690])).

cnf(c_1734,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_710,c_715])).

cnf(c_11287,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_1734,c_1906])).

cnf(c_1927,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_1933,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
    inference(demodulation,[status(thm)],[c_1927,c_5])).

cnf(c_25777,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)))),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,sK3),X0)))))) ),
    inference(superposition,[status(thm)],[c_11287,c_1933])).

cnf(c_2533,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_2172,c_715])).

cnf(c_2675,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2533,c_0])).

cnf(c_2676,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK3,sK3) ),
    inference(light_normalisation,[status(thm)],[c_2675,c_1734])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_722,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2674,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2533,c_722])).

cnf(c_4696,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2674,c_723])).

cnf(c_4701,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4696,c_2676])).

cnf(c_1367,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_722])).

cnf(c_2405,plain,
    ( r1_tarski(k4_xboole_0(sK3,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1367])).

cnf(c_4694,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),sK2)) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[status(thm)],[c_2405,c_723])).

cnf(c_1920,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_19722,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),X0)))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),X0)) ),
    inference(superposition,[status(thm)],[c_4694,c_1920])).

cnf(c_2803,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
    inference(superposition,[status(thm)],[c_2676,c_5])).

cnf(c_20098,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_19722,c_2803])).

cnf(c_26327,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_25777,c_2533,c_2676,c_4701,c_20098])).

cnf(c_51031,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_49528,c_26327])).

cnf(c_51103,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_51031,c_49528])).

cnf(c_58178,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_58173,c_51103])).

cnf(c_1917,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_718,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6237,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_718])).

cnf(c_7605,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4690,c_6237])).

cnf(c_6250,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4690,c_718])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_717,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6624,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6250,c_717])).

cnf(c_1929,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1367])).

cnf(c_4876,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4690,c_1929])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_714,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4882,plain,
    ( r1_tarski(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4690,c_714])).

cnf(c_6849,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4876,c_4882])).

cnf(c_9489,plain,
    ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7605,c_6624,c_6849])).

cnf(c_9496,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = X0 ),
    inference(superposition,[status(thm)],[c_9489,c_715])).

cnf(c_4865,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0)) ),
    inference(superposition,[status(thm)],[c_4690,c_5])).

cnf(c_11395,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0)) ),
    inference(superposition,[status(thm)],[c_1906,c_4865])).

cnf(c_11496,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0)) = k4_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_11395,c_4690,c_9496])).

cnf(c_13101,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11496,c_1906])).

cnf(c_13236,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
    inference(demodulation,[status(thm)],[c_13101,c_9496])).

cnf(c_28518,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK2)))) = X0 ),
    inference(demodulation,[status(thm)],[c_9496,c_13236])).

cnf(c_28519,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_28518,c_2676])).

cnf(c_3413,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK3,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_714])).

cnf(c_3228,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_1929])).

cnf(c_3411,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_xboole_0(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_714])).

cnf(c_3583,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_3411])).

cnf(c_6247,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK3,sK3)) = iProver_top
    | r1_xboole_0(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1734,c_718])).

cnf(c_6426,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK3,sK3)) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6247,c_717])).

cnf(c_19595,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK3,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3413,c_3583,c_6426])).

cnf(c_19602,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK3,sK3)) = X0 ),
    inference(superposition,[status(thm)],[c_19595,c_715])).

cnf(c_28520,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK1,sK1)) = X0 ),
    inference(demodulation,[status(thm)],[c_28519,c_19602])).

cnf(c_28606,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) ),
    inference(superposition,[status(thm)],[c_28520,c_1917])).

cnf(c_1930,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_28624,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_28520,c_1930])).

cnf(c_9495,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9489,c_727])).

cnf(c_25586,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK2))),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9495,c_13236])).

cnf(c_25587,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25586,c_2676])).

cnf(c_25588,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK1),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_25587,c_19602])).

cnf(c_25593,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_25588,c_715])).

cnf(c_28710,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_28624,c_25593])).

cnf(c_28608,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1))))) ),
    inference(superposition,[status(thm)],[c_28520,c_5])).

cnf(c_28732,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_28608,c_28520,c_28710])).

cnf(c_28734,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(demodulation,[status(thm)],[c_28606,c_28520,c_28710,c_28732])).

cnf(c_28735,plain,
    ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_28734])).

cnf(c_1728,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1367])).

cnf(c_3176,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1728])).

cnf(c_4688,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_722,c_723])).

cnf(c_18214,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3176,c_4688])).

cnf(c_18232,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4690,c_18214])).

cnf(c_19371,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_18232,c_723])).

cnf(c_14240,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
    inference(superposition,[status(thm)],[c_11306,c_1906])).

cnf(c_1914,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_14937,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(superposition,[status(thm)],[c_4690,c_1914])).

cnf(c_4880,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_4690,c_5])).

cnf(c_14938,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(superposition,[status(thm)],[c_4880,c_1914])).

cnf(c_15297,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(light_normalisation,[status(thm)],[c_14938,c_4880])).

cnf(c_5078,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),X0)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_4880,c_5])).

cnf(c_5093,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
    inference(demodulation,[status(thm)],[c_5078,c_1917])).

cnf(c_15298,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
    inference(demodulation,[status(thm)],[c_15297,c_1917,c_5093])).

cnf(c_15300,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),X0))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
    inference(demodulation,[status(thm)],[c_14937,c_15298])).

cnf(c_15301,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
    inference(light_normalisation,[status(thm)],[c_15300,c_4690])).

cnf(c_15302,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
    inference(demodulation,[status(thm)],[c_15301,c_14240])).

cnf(c_15304,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
    inference(demodulation,[status(thm)],[c_15302,c_15298])).

cnf(c_14919,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
    inference(superposition,[status(thm)],[c_11306,c_1914])).

cnf(c_15319,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) ),
    inference(light_normalisation,[status(thm)],[c_14919,c_14240])).

cnf(c_19372,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_19371,c_14240,c_15304,c_15319])).

cnf(c_19373,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_19372,c_4690])).

cnf(c_11288,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)))) ),
    inference(superposition,[status(thm)],[c_2676,c_1906])).

cnf(c_11538,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_11288,c_4701])).

cnf(c_19374,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_19373,c_11538])).

cnf(c_29777,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_19374,c_1914])).

cnf(c_1932,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_22417,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(superposition,[status(thm)],[c_11306,c_1932])).

cnf(c_22750,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
    inference(light_normalisation,[status(thm)],[c_22417,c_4690,c_15304])).

cnf(c_24768,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
    inference(superposition,[status(thm)],[c_22750,c_11306])).

cnf(c_24773,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) ),
    inference(demodulation,[status(thm)],[c_24768,c_4688])).

cnf(c_28571,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X0)))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) ),
    inference(superposition,[status(thm)],[c_28520,c_1920])).

cnf(c_29277,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_28571,c_25593])).

cnf(c_2403,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) ),
    inference(superposition,[status(thm)],[c_1734,c_5])).

cnf(c_2822,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_2403,c_0])).

cnf(c_24651,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK3,sK3))))))) ),
    inference(superposition,[status(thm)],[c_2822,c_22750])).

cnf(c_11052,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),X0)))) = k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),X0)) ),
    inference(superposition,[status(thm)],[c_4701,c_5])).

cnf(c_11092,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_11052,c_2403,c_2676])).

cnf(c_25147,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK2))) ),
    inference(demodulation,[status(thm)],[c_24651,c_11092,c_13236,c_14240,c_19602,c_24773])).

cnf(c_25148,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))) ),
    inference(light_normalisation,[status(thm)],[c_25147,c_2676])).

cnf(c_9862,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_0,c_2822])).

cnf(c_17525,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(sK3,sK3))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))))) ),
    inference(superposition,[status(thm)],[c_1917,c_9862])).

cnf(c_17657,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK3,sK3))))) ),
    inference(demodulation,[status(thm)],[c_17525,c_1917])).

cnf(c_25149,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))))))) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_25148,c_17657,c_19602])).

cnf(c_17227,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
    inference(superposition,[status(thm)],[c_4694,c_1930])).

cnf(c_25150,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))))) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_25149,c_17227])).

cnf(c_25151,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_25150,c_19602])).

cnf(c_29278,plain,
    ( k4_xboole_0(sK1,sK1) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_29277,c_25151,c_25593,c_28735])).

cnf(c_29814,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_29777,c_2676,c_13236,c_19602,c_24773,c_29278])).

cnf(c_29985,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sP0_iProver_split) ),
    inference(superposition,[status(thm)],[c_29814,c_0])).

cnf(c_30052,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sP0_iProver_split) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_29985,c_19374])).

cnf(c_11277,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_0,c_1906])).

cnf(c_27634,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) ),
    inference(superposition,[status(thm)],[c_0,c_11277])).

cnf(c_53568,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(superposition,[status(thm)],[c_11306,c_27634])).

cnf(c_27930,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[status(thm)],[c_11277,c_0])).

cnf(c_55434,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_4690,c_27930])).

cnf(c_14100,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_0,c_11306])).

cnf(c_56615,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
    inference(demodulation,[status(thm)],[c_55434,c_1917,c_14100])).

cnf(c_53746,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))))) ),
    inference(superposition,[status(thm)],[c_27634,c_1932])).

cnf(c_56004,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) ),
    inference(superposition,[status(thm)],[c_27930,c_1932])).

cnf(c_11297,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_0,c_1906])).

cnf(c_53494,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))))) ),
    inference(superposition,[status(thm)],[c_11297,c_27634])).

cnf(c_53794,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),X2)) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
    inference(superposition,[status(thm)],[c_27634,c_11349])).

cnf(c_54469,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
    inference(light_normalisation,[status(thm)],[c_53794,c_4688])).

cnf(c_54900,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(demodulation,[status(thm)],[c_53494,c_54469])).

cnf(c_28747,plain,
    ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
    inference(demodulation,[status(thm)],[c_28735,c_28520])).

cnf(c_54901,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_54900,c_4688,c_28735,c_28747])).

cnf(c_56317,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_56004,c_1917,c_54901])).

cnf(c_57272,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_53746,c_56317])).

cnf(c_57273,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)) ),
    inference(demodulation,[status(thm)],[c_57272,c_54901])).

cnf(c_53736,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))))) ),
    inference(superposition,[status(thm)],[c_27634,c_1932])).

cnf(c_54036,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))))) ),
    inference(superposition,[status(thm)],[c_27634,c_1933])).

cnf(c_55682,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),X4)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4)))))) ),
    inference(superposition,[status(thm)],[c_27930,c_1933])).

cnf(c_55741,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X3)))))) ),
    inference(superposition,[status(thm)],[c_27930,c_11349])).

cnf(c_56473,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),X4)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X4)))))))) ),
    inference(demodulation,[status(thm)],[c_55682,c_55741])).

cnf(c_54075,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))))) ),
    inference(superposition,[status(thm)],[c_27634,c_11277])).

cnf(c_55020,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(demodulation,[status(thm)],[c_54901,c_27634])).

cnf(c_56828,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_54075,c_54901,c_55020])).

cnf(c_56861,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) ),
    inference(demodulation,[status(thm)],[c_54036,c_56473,c_56828])).

cnf(c_56862,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(demodulation,[status(thm)],[c_56861,c_1917,c_55020])).

cnf(c_57281,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_53736,c_56317,c_56862,c_57273])).

cnf(c_57282,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_57281,c_28735,c_28747,c_54901])).

cnf(c_53919,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),X3))))) ),
    inference(superposition,[status(thm)],[c_27634,c_1932])).

cnf(c_57003,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),X3) ),
    inference(demodulation,[status(thm)],[c_53919,c_56317])).

cnf(c_57004,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3) ),
    inference(demodulation,[status(thm)],[c_57003,c_1932,c_54901,c_55020])).

cnf(c_53929,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))))))) ),
    inference(superposition,[status(thm)],[c_27634,c_1914])).

cnf(c_56991,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))))) ),
    inference(demodulation,[status(thm)],[c_53929,c_56828])).

cnf(c_56992,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) ),
    inference(demodulation,[status(thm)],[c_56991,c_54901,c_55020])).

cnf(c_57005,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3) ),
    inference(demodulation,[status(thm)],[c_57004,c_56992])).

cnf(c_57292,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_57282,c_57005])).

cnf(c_57293,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_57282,c_57004])).

cnf(c_54114,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X2,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))))) ),
    inference(superposition,[status(thm)],[c_27634,c_1920])).

cnf(c_56775,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))))) ),
    inference(light_normalisation,[status(thm)],[c_54114,c_54901])).

cnf(c_56776,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_56775,c_54901,c_55020])).

cnf(c_56830,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) ),
    inference(demodulation,[status(thm)],[c_56828,c_56776])).

cnf(c_57296,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) ),
    inference(demodulation,[status(thm)],[c_57282,c_56830])).

cnf(c_57315,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
    inference(demodulation,[status(thm)],[c_57293,c_57282,c_57296])).

cnf(c_53756,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X3))))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X0))))))) ),
    inference(superposition,[status(thm)],[c_27634,c_1917])).

cnf(c_53810,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X3))))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))))) ),
    inference(superposition,[status(thm)],[c_27634,c_1920])).

cnf(c_57148,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),X3))))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,X1)))))) ),
    inference(light_normalisation,[status(thm)],[c_53810,c_54901])).

cnf(c_57149,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))) ),
    inference(demodulation,[status(thm)],[c_57148,c_54901,c_55020])).

cnf(c_57216,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))))) ),
    inference(demodulation,[status(thm)],[c_53756,c_57149])).

cnf(c_57217,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X3))) ),
    inference(demodulation,[status(thm)],[c_57216,c_54901])).

cnf(c_55707,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) ),
    inference(superposition,[status(thm)],[c_27930,c_1917])).

cnf(c_57221,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) ),
    inference(demodulation,[status(thm)],[c_57217,c_55707])).

cnf(c_55726,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X3,k4_xboole_0(X3,X1))))))) ),
    inference(superposition,[status(thm)],[c_27930,c_11277])).

cnf(c_57244,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) ),
    inference(demodulation,[status(thm)],[c_57221,c_55726])).

cnf(c_57330,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))) ),
    inference(demodulation,[status(thm)],[c_57315,c_57244])).

cnf(c_57513,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_53568,c_56615,c_57273,c_57292,c_57330])).

cnf(c_57322,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(demodulation,[status(thm)],[c_57315,c_57221])).

cnf(c_57514,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
    inference(demodulation,[status(thm)],[c_57513,c_57322])).

cnf(c_57515,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sP0_iProver_split ),
    inference(light_normalisation,[status(thm)],[c_57514,c_29814])).

cnf(c_58179,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sP0_iProver_split ),
    inference(demodulation,[status(thm)],[c_58178,c_1917,c_28735,c_30052,c_57515])).

cnf(c_17585,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1917,c_4690])).

cnf(c_5546,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X0,X1)) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_717])).

cnf(c_46682,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))),sK2))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17585,c_5546])).

cnf(c_46756,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))),sK2))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_46682,c_17585])).

cnf(c_46757,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_46756,c_4688,c_17585])).

cnf(c_4879,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_4690,c_5])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_716,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1949,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_716])).

cnf(c_30252,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4879,c_1949])).

cnf(c_30450,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30252,c_4690])).

cnf(c_30451,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sP0_iProver_split
    | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_30450,c_2676,c_13236,c_19602,c_29278])).

cnf(c_1547,plain,
    ( r1_xboole_0(X0,sK2)
    | ~ r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_16851,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_1547])).

cnf(c_16855,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) = iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16851])).

cnf(c_1517,plain,
    ( r1_xboole_0(X0,sK2)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5407,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_5408,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
    | r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5407])).

cnf(c_1590,plain,
    ( ~ r1_xboole_0(X0,sK2)
    | r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3678,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_3679,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top
    | r1_xboole_0(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3678])).

cnf(c_1216,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1217,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1216])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_894,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
    | ~ r1_xboole_0(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_895,plain,
    ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_774,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_775,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
    | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_25,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58179,c_46757,c_30451,c_16855,c_5408,c_3679,c_1217,c_895,c_775,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.45/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.45/3.50  
% 23.45/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.45/3.50  
% 23.45/3.50  ------  iProver source info
% 23.45/3.50  
% 23.45/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.45/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.45/3.50  git: non_committed_changes: false
% 23.45/3.50  git: last_make_outside_of_git: false
% 23.45/3.50  
% 23.45/3.50  ------ 
% 23.45/3.50  
% 23.45/3.50  ------ Input Options
% 23.45/3.50  
% 23.45/3.50  --out_options                           all
% 23.45/3.50  --tptp_safe_out                         true
% 23.45/3.50  --problem_path                          ""
% 23.45/3.50  --include_path                          ""
% 23.45/3.50  --clausifier                            res/vclausify_rel
% 23.45/3.50  --clausifier_options                    ""
% 23.45/3.50  --stdin                                 false
% 23.45/3.50  --stats_out                             all
% 23.45/3.50  
% 23.45/3.50  ------ General Options
% 23.45/3.50  
% 23.45/3.50  --fof                                   false
% 23.45/3.50  --time_out_real                         305.
% 23.45/3.50  --time_out_virtual                      -1.
% 23.45/3.50  --symbol_type_check                     false
% 23.45/3.50  --clausify_out                          false
% 23.45/3.50  --sig_cnt_out                           false
% 23.45/3.50  --trig_cnt_out                          false
% 23.45/3.50  --trig_cnt_out_tolerance                1.
% 23.45/3.50  --trig_cnt_out_sk_spl                   false
% 23.45/3.50  --abstr_cl_out                          false
% 23.45/3.50  
% 23.45/3.50  ------ Global Options
% 23.45/3.50  
% 23.45/3.50  --schedule                              default
% 23.45/3.50  --add_important_lit                     false
% 23.45/3.50  --prop_solver_per_cl                    1000
% 23.45/3.50  --min_unsat_core                        false
% 23.45/3.50  --soft_assumptions                      false
% 23.45/3.50  --soft_lemma_size                       3
% 23.45/3.50  --prop_impl_unit_size                   0
% 23.45/3.50  --prop_impl_unit                        []
% 23.45/3.50  --share_sel_clauses                     true
% 23.45/3.50  --reset_solvers                         false
% 23.45/3.50  --bc_imp_inh                            [conj_cone]
% 23.45/3.50  --conj_cone_tolerance                   3.
% 23.45/3.50  --extra_neg_conj                        none
% 23.45/3.50  --large_theory_mode                     true
% 23.45/3.50  --prolific_symb_bound                   200
% 23.45/3.50  --lt_threshold                          2000
% 23.45/3.50  --clause_weak_htbl                      true
% 23.45/3.50  --gc_record_bc_elim                     false
% 23.45/3.50  
% 23.45/3.50  ------ Preprocessing Options
% 23.45/3.50  
% 23.45/3.50  --preprocessing_flag                    true
% 23.45/3.50  --time_out_prep_mult                    0.1
% 23.45/3.50  --splitting_mode                        input
% 23.45/3.50  --splitting_grd                         true
% 23.45/3.50  --splitting_cvd                         false
% 23.45/3.50  --splitting_cvd_svl                     false
% 23.45/3.50  --splitting_nvd                         32
% 23.45/3.50  --sub_typing                            true
% 23.45/3.50  --prep_gs_sim                           true
% 23.45/3.50  --prep_unflatten                        true
% 23.45/3.50  --prep_res_sim                          true
% 23.45/3.50  --prep_upred                            true
% 23.45/3.50  --prep_sem_filter                       exhaustive
% 23.45/3.50  --prep_sem_filter_out                   false
% 23.45/3.50  --pred_elim                             true
% 23.45/3.50  --res_sim_input                         true
% 23.45/3.50  --eq_ax_congr_red                       true
% 23.45/3.50  --pure_diseq_elim                       true
% 23.45/3.50  --brand_transform                       false
% 23.45/3.50  --non_eq_to_eq                          false
% 23.45/3.50  --prep_def_merge                        true
% 23.45/3.50  --prep_def_merge_prop_impl              false
% 23.45/3.50  --prep_def_merge_mbd                    true
% 23.45/3.50  --prep_def_merge_tr_red                 false
% 23.45/3.50  --prep_def_merge_tr_cl                  false
% 23.45/3.50  --smt_preprocessing                     true
% 23.45/3.50  --smt_ac_axioms                         fast
% 23.45/3.50  --preprocessed_out                      false
% 23.45/3.50  --preprocessed_stats                    false
% 23.45/3.50  
% 23.45/3.50  ------ Abstraction refinement Options
% 23.45/3.50  
% 23.45/3.50  --abstr_ref                             []
% 23.45/3.50  --abstr_ref_prep                        false
% 23.45/3.50  --abstr_ref_until_sat                   false
% 23.45/3.50  --abstr_ref_sig_restrict                funpre
% 23.45/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.45/3.50  --abstr_ref_under                       []
% 23.45/3.50  
% 23.45/3.50  ------ SAT Options
% 23.45/3.50  
% 23.45/3.50  --sat_mode                              false
% 23.45/3.50  --sat_fm_restart_options                ""
% 23.45/3.50  --sat_gr_def                            false
% 23.45/3.50  --sat_epr_types                         true
% 23.45/3.50  --sat_non_cyclic_types                  false
% 23.45/3.50  --sat_finite_models                     false
% 23.45/3.50  --sat_fm_lemmas                         false
% 23.45/3.50  --sat_fm_prep                           false
% 23.45/3.50  --sat_fm_uc_incr                        true
% 23.45/3.50  --sat_out_model                         small
% 23.45/3.50  --sat_out_clauses                       false
% 23.45/3.50  
% 23.45/3.50  ------ QBF Options
% 23.45/3.50  
% 23.45/3.50  --qbf_mode                              false
% 23.45/3.50  --qbf_elim_univ                         false
% 23.45/3.50  --qbf_dom_inst                          none
% 23.45/3.50  --qbf_dom_pre_inst                      false
% 23.45/3.50  --qbf_sk_in                             false
% 23.45/3.50  --qbf_pred_elim                         true
% 23.45/3.50  --qbf_split                             512
% 23.45/3.50  
% 23.45/3.50  ------ BMC1 Options
% 23.45/3.50  
% 23.45/3.50  --bmc1_incremental                      false
% 23.45/3.50  --bmc1_axioms                           reachable_all
% 23.45/3.50  --bmc1_min_bound                        0
% 23.45/3.50  --bmc1_max_bound                        -1
% 23.45/3.50  --bmc1_max_bound_default                -1
% 23.45/3.50  --bmc1_symbol_reachability              true
% 23.45/3.50  --bmc1_property_lemmas                  false
% 23.45/3.50  --bmc1_k_induction                      false
% 23.45/3.50  --bmc1_non_equiv_states                 false
% 23.45/3.50  --bmc1_deadlock                         false
% 23.45/3.50  --bmc1_ucm                              false
% 23.45/3.50  --bmc1_add_unsat_core                   none
% 23.45/3.50  --bmc1_unsat_core_children              false
% 23.45/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.45/3.50  --bmc1_out_stat                         full
% 23.45/3.50  --bmc1_ground_init                      false
% 23.45/3.50  --bmc1_pre_inst_next_state              false
% 23.45/3.50  --bmc1_pre_inst_state                   false
% 23.45/3.50  --bmc1_pre_inst_reach_state             false
% 23.45/3.50  --bmc1_out_unsat_core                   false
% 23.45/3.50  --bmc1_aig_witness_out                  false
% 23.45/3.50  --bmc1_verbose                          false
% 23.45/3.50  --bmc1_dump_clauses_tptp                false
% 23.45/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.45/3.50  --bmc1_dump_file                        -
% 23.45/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.45/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.45/3.50  --bmc1_ucm_extend_mode                  1
% 23.45/3.50  --bmc1_ucm_init_mode                    2
% 23.45/3.50  --bmc1_ucm_cone_mode                    none
% 23.45/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.45/3.50  --bmc1_ucm_relax_model                  4
% 23.45/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.45/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.45/3.50  --bmc1_ucm_layered_model                none
% 23.45/3.50  --bmc1_ucm_max_lemma_size               10
% 23.45/3.50  
% 23.45/3.50  ------ AIG Options
% 23.45/3.50  
% 23.45/3.50  --aig_mode                              false
% 23.45/3.50  
% 23.45/3.50  ------ Instantiation Options
% 23.45/3.50  
% 23.45/3.50  --instantiation_flag                    true
% 23.45/3.50  --inst_sos_flag                         true
% 23.45/3.50  --inst_sos_phase                        true
% 23.45/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.45/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.45/3.50  --inst_lit_sel_side                     num_symb
% 23.45/3.50  --inst_solver_per_active                1400
% 23.45/3.50  --inst_solver_calls_frac                1.
% 23.45/3.50  --inst_passive_queue_type               priority_queues
% 23.45/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.45/3.50  --inst_passive_queues_freq              [25;2]
% 23.45/3.50  --inst_dismatching                      true
% 23.45/3.50  --inst_eager_unprocessed_to_passive     true
% 23.45/3.50  --inst_prop_sim_given                   true
% 23.45/3.50  --inst_prop_sim_new                     false
% 23.45/3.50  --inst_subs_new                         false
% 23.45/3.50  --inst_eq_res_simp                      false
% 23.45/3.50  --inst_subs_given                       false
% 23.45/3.50  --inst_orphan_elimination               true
% 23.45/3.50  --inst_learning_loop_flag               true
% 23.45/3.50  --inst_learning_start                   3000
% 23.45/3.50  --inst_learning_factor                  2
% 23.45/3.50  --inst_start_prop_sim_after_learn       3
% 23.45/3.50  --inst_sel_renew                        solver
% 23.45/3.50  --inst_lit_activity_flag                true
% 23.45/3.50  --inst_restr_to_given                   false
% 23.45/3.50  --inst_activity_threshold               500
% 23.45/3.50  --inst_out_proof                        true
% 23.45/3.50  
% 23.45/3.50  ------ Resolution Options
% 23.45/3.50  
% 23.45/3.50  --resolution_flag                       true
% 23.45/3.50  --res_lit_sel                           adaptive
% 23.45/3.50  --res_lit_sel_side                      none
% 23.45/3.50  --res_ordering                          kbo
% 23.45/3.50  --res_to_prop_solver                    active
% 23.45/3.50  --res_prop_simpl_new                    false
% 23.45/3.50  --res_prop_simpl_given                  true
% 23.45/3.50  --res_passive_queue_type                priority_queues
% 23.45/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.45/3.50  --res_passive_queues_freq               [15;5]
% 23.45/3.50  --res_forward_subs                      full
% 23.45/3.50  --res_backward_subs                     full
% 23.45/3.50  --res_forward_subs_resolution           true
% 23.45/3.50  --res_backward_subs_resolution          true
% 23.45/3.50  --res_orphan_elimination                true
% 23.45/3.50  --res_time_limit                        2.
% 23.45/3.50  --res_out_proof                         true
% 23.45/3.50  
% 23.45/3.50  ------ Superposition Options
% 23.45/3.50  
% 23.45/3.50  --superposition_flag                    true
% 23.45/3.50  --sup_passive_queue_type                priority_queues
% 23.45/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.45/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.45/3.50  --demod_completeness_check              fast
% 23.45/3.50  --demod_use_ground                      true
% 23.45/3.50  --sup_to_prop_solver                    passive
% 23.45/3.50  --sup_prop_simpl_new                    true
% 23.45/3.50  --sup_prop_simpl_given                  true
% 23.45/3.50  --sup_fun_splitting                     true
% 23.45/3.50  --sup_smt_interval                      50000
% 23.45/3.50  
% 23.45/3.50  ------ Superposition Simplification Setup
% 23.45/3.50  
% 23.45/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.45/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.45/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.45/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.45/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.45/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.45/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.45/3.50  --sup_immed_triv                        [TrivRules]
% 23.45/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.45/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.45/3.50  --sup_immed_bw_main                     []
% 23.45/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.45/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.45/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.45/3.50  --sup_input_bw                          []
% 23.45/3.50  
% 23.45/3.50  ------ Combination Options
% 23.45/3.50  
% 23.45/3.50  --comb_res_mult                         3
% 23.45/3.50  --comb_sup_mult                         2
% 23.45/3.50  --comb_inst_mult                        10
% 23.45/3.50  
% 23.45/3.50  ------ Debug Options
% 23.45/3.50  
% 23.45/3.50  --dbg_backtrace                         false
% 23.45/3.50  --dbg_dump_prop_clauses                 false
% 23.45/3.50  --dbg_dump_prop_clauses_file            -
% 23.45/3.50  --dbg_out_stat                          false
% 23.45/3.50  ------ Parsing...
% 23.45/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.45/3.50  
% 23.45/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.45/3.50  
% 23.45/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.45/3.50  
% 23.45/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.45/3.50  ------ Proving...
% 23.45/3.50  ------ Problem Properties 
% 23.45/3.50  
% 23.45/3.50  
% 23.45/3.50  clauses                                 22
% 23.45/3.50  conjectures                             4
% 23.45/3.50  EPR                                     4
% 23.45/3.50  Horn                                    19
% 23.45/3.50  unary                                   7
% 23.45/3.50  binary                                  12
% 23.45/3.50  lits                                    40
% 23.45/3.50  lits eq                                 5
% 23.45/3.50  fd_pure                                 0
% 23.45/3.50  fd_pseudo                               0
% 23.45/3.50  fd_cond                                 0
% 23.45/3.50  fd_pseudo_cond                          0
% 23.45/3.50  AC symbols                              0
% 23.45/3.50  
% 23.45/3.50  ------ Schedule dynamic 5 is on 
% 23.45/3.50  
% 23.45/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.45/3.50  
% 23.45/3.50  
% 23.45/3.50  ------ 
% 23.45/3.50  Current options:
% 23.45/3.50  ------ 
% 23.45/3.50  
% 23.45/3.50  ------ Input Options
% 23.45/3.50  
% 23.45/3.50  --out_options                           all
% 23.45/3.50  --tptp_safe_out                         true
% 23.45/3.50  --problem_path                          ""
% 23.45/3.50  --include_path                          ""
% 23.45/3.50  --clausifier                            res/vclausify_rel
% 23.45/3.50  --clausifier_options                    ""
% 23.45/3.50  --stdin                                 false
% 23.45/3.50  --stats_out                             all
% 23.45/3.50  
% 23.45/3.50  ------ General Options
% 23.45/3.50  
% 23.45/3.50  --fof                                   false
% 23.45/3.50  --time_out_real                         305.
% 23.45/3.50  --time_out_virtual                      -1.
% 23.45/3.50  --symbol_type_check                     false
% 23.45/3.50  --clausify_out                          false
% 23.45/3.50  --sig_cnt_out                           false
% 23.45/3.50  --trig_cnt_out                          false
% 23.45/3.50  --trig_cnt_out_tolerance                1.
% 23.45/3.50  --trig_cnt_out_sk_spl                   false
% 23.45/3.50  --abstr_cl_out                          false
% 23.45/3.50  
% 23.45/3.50  ------ Global Options
% 23.45/3.50  
% 23.45/3.50  --schedule                              default
% 23.45/3.50  --add_important_lit                     false
% 23.45/3.50  --prop_solver_per_cl                    1000
% 23.45/3.50  --min_unsat_core                        false
% 23.45/3.50  --soft_assumptions                      false
% 23.45/3.50  --soft_lemma_size                       3
% 23.45/3.50  --prop_impl_unit_size                   0
% 23.45/3.50  --prop_impl_unit                        []
% 23.45/3.50  --share_sel_clauses                     true
% 23.45/3.50  --reset_solvers                         false
% 23.45/3.50  --bc_imp_inh                            [conj_cone]
% 23.45/3.50  --conj_cone_tolerance                   3.
% 23.45/3.50  --extra_neg_conj                        none
% 23.45/3.50  --large_theory_mode                     true
% 23.45/3.50  --prolific_symb_bound                   200
% 23.45/3.50  --lt_threshold                          2000
% 23.45/3.50  --clause_weak_htbl                      true
% 23.45/3.50  --gc_record_bc_elim                     false
% 23.45/3.50  
% 23.45/3.50  ------ Preprocessing Options
% 23.45/3.50  
% 23.45/3.50  --preprocessing_flag                    true
% 23.45/3.50  --time_out_prep_mult                    0.1
% 23.45/3.50  --splitting_mode                        input
% 23.45/3.50  --splitting_grd                         true
% 23.45/3.50  --splitting_cvd                         false
% 23.45/3.50  --splitting_cvd_svl                     false
% 23.45/3.50  --splitting_nvd                         32
% 23.45/3.50  --sub_typing                            true
% 23.45/3.50  --prep_gs_sim                           true
% 23.45/3.50  --prep_unflatten                        true
% 23.45/3.50  --prep_res_sim                          true
% 23.45/3.50  --prep_upred                            true
% 23.45/3.50  --prep_sem_filter                       exhaustive
% 23.45/3.50  --prep_sem_filter_out                   false
% 23.45/3.50  --pred_elim                             true
% 23.45/3.50  --res_sim_input                         true
% 23.45/3.50  --eq_ax_congr_red                       true
% 23.45/3.50  --pure_diseq_elim                       true
% 23.45/3.50  --brand_transform                       false
% 23.45/3.50  --non_eq_to_eq                          false
% 23.45/3.50  --prep_def_merge                        true
% 23.45/3.50  --prep_def_merge_prop_impl              false
% 23.45/3.50  --prep_def_merge_mbd                    true
% 23.45/3.50  --prep_def_merge_tr_red                 false
% 23.45/3.50  --prep_def_merge_tr_cl                  false
% 23.45/3.50  --smt_preprocessing                     true
% 23.45/3.50  --smt_ac_axioms                         fast
% 23.45/3.50  --preprocessed_out                      false
% 23.45/3.50  --preprocessed_stats                    false
% 23.45/3.50  
% 23.45/3.50  ------ Abstraction refinement Options
% 23.45/3.50  
% 23.45/3.50  --abstr_ref                             []
% 23.45/3.50  --abstr_ref_prep                        false
% 23.45/3.50  --abstr_ref_until_sat                   false
% 23.45/3.50  --abstr_ref_sig_restrict                funpre
% 23.45/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.45/3.50  --abstr_ref_under                       []
% 23.45/3.50  
% 23.45/3.50  ------ SAT Options
% 23.45/3.50  
% 23.45/3.50  --sat_mode                              false
% 23.45/3.50  --sat_fm_restart_options                ""
% 23.45/3.50  --sat_gr_def                            false
% 23.45/3.50  --sat_epr_types                         true
% 23.45/3.50  --sat_non_cyclic_types                  false
% 23.45/3.50  --sat_finite_models                     false
% 23.45/3.50  --sat_fm_lemmas                         false
% 23.45/3.50  --sat_fm_prep                           false
% 23.45/3.50  --sat_fm_uc_incr                        true
% 23.45/3.50  --sat_out_model                         small
% 23.45/3.50  --sat_out_clauses                       false
% 23.45/3.50  
% 23.45/3.50  ------ QBF Options
% 23.45/3.50  
% 23.45/3.50  --qbf_mode                              false
% 23.45/3.50  --qbf_elim_univ                         false
% 23.45/3.50  --qbf_dom_inst                          none
% 23.45/3.50  --qbf_dom_pre_inst                      false
% 23.45/3.50  --qbf_sk_in                             false
% 23.45/3.50  --qbf_pred_elim                         true
% 23.45/3.50  --qbf_split                             512
% 23.45/3.50  
% 23.45/3.50  ------ BMC1 Options
% 23.45/3.50  
% 23.45/3.50  --bmc1_incremental                      false
% 23.45/3.50  --bmc1_axioms                           reachable_all
% 23.45/3.50  --bmc1_min_bound                        0
% 23.45/3.50  --bmc1_max_bound                        -1
% 23.45/3.50  --bmc1_max_bound_default                -1
% 23.45/3.50  --bmc1_symbol_reachability              true
% 23.45/3.50  --bmc1_property_lemmas                  false
% 23.45/3.50  --bmc1_k_induction                      false
% 23.45/3.50  --bmc1_non_equiv_states                 false
% 23.45/3.50  --bmc1_deadlock                         false
% 23.45/3.50  --bmc1_ucm                              false
% 23.45/3.50  --bmc1_add_unsat_core                   none
% 23.45/3.50  --bmc1_unsat_core_children              false
% 23.45/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.45/3.50  --bmc1_out_stat                         full
% 23.45/3.50  --bmc1_ground_init                      false
% 23.45/3.50  --bmc1_pre_inst_next_state              false
% 23.45/3.50  --bmc1_pre_inst_state                   false
% 23.45/3.50  --bmc1_pre_inst_reach_state             false
% 23.45/3.50  --bmc1_out_unsat_core                   false
% 23.45/3.50  --bmc1_aig_witness_out                  false
% 23.45/3.50  --bmc1_verbose                          false
% 23.45/3.50  --bmc1_dump_clauses_tptp                false
% 23.45/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.45/3.50  --bmc1_dump_file                        -
% 23.45/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.45/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.45/3.50  --bmc1_ucm_extend_mode                  1
% 23.45/3.50  --bmc1_ucm_init_mode                    2
% 23.45/3.50  --bmc1_ucm_cone_mode                    none
% 23.45/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.45/3.50  --bmc1_ucm_relax_model                  4
% 23.45/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.45/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.45/3.50  --bmc1_ucm_layered_model                none
% 23.45/3.50  --bmc1_ucm_max_lemma_size               10
% 23.45/3.50  
% 23.45/3.50  ------ AIG Options
% 23.45/3.50  
% 23.45/3.50  --aig_mode                              false
% 23.45/3.50  
% 23.45/3.50  ------ Instantiation Options
% 23.45/3.50  
% 23.45/3.50  --instantiation_flag                    true
% 23.45/3.50  --inst_sos_flag                         true
% 23.45/3.50  --inst_sos_phase                        true
% 23.45/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.45/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.45/3.50  --inst_lit_sel_side                     none
% 23.45/3.50  --inst_solver_per_active                1400
% 23.45/3.50  --inst_solver_calls_frac                1.
% 23.45/3.50  --inst_passive_queue_type               priority_queues
% 23.45/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.45/3.50  --inst_passive_queues_freq              [25;2]
% 23.45/3.50  --inst_dismatching                      true
% 23.45/3.50  --inst_eager_unprocessed_to_passive     true
% 23.45/3.50  --inst_prop_sim_given                   true
% 23.45/3.50  --inst_prop_sim_new                     false
% 23.45/3.50  --inst_subs_new                         false
% 23.45/3.50  --inst_eq_res_simp                      false
% 23.45/3.50  --inst_subs_given                       false
% 23.45/3.50  --inst_orphan_elimination               true
% 23.45/3.50  --inst_learning_loop_flag               true
% 23.45/3.50  --inst_learning_start                   3000
% 23.45/3.50  --inst_learning_factor                  2
% 23.45/3.50  --inst_start_prop_sim_after_learn       3
% 23.45/3.50  --inst_sel_renew                        solver
% 23.45/3.50  --inst_lit_activity_flag                true
% 23.45/3.50  --inst_restr_to_given                   false
% 23.45/3.50  --inst_activity_threshold               500
% 23.45/3.50  --inst_out_proof                        true
% 23.45/3.50  
% 23.45/3.50  ------ Resolution Options
% 23.45/3.50  
% 23.45/3.50  --resolution_flag                       false
% 23.45/3.50  --res_lit_sel                           adaptive
% 23.45/3.50  --res_lit_sel_side                      none
% 23.45/3.50  --res_ordering                          kbo
% 23.45/3.50  --res_to_prop_solver                    active
% 23.45/3.50  --res_prop_simpl_new                    false
% 23.45/3.50  --res_prop_simpl_given                  true
% 23.45/3.50  --res_passive_queue_type                priority_queues
% 23.45/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.45/3.50  --res_passive_queues_freq               [15;5]
% 23.45/3.50  --res_forward_subs                      full
% 23.45/3.50  --res_backward_subs                     full
% 23.45/3.50  --res_forward_subs_resolution           true
% 23.45/3.50  --res_backward_subs_resolution          true
% 23.45/3.50  --res_orphan_elimination                true
% 23.45/3.50  --res_time_limit                        2.
% 23.45/3.50  --res_out_proof                         true
% 23.45/3.50  
% 23.45/3.50  ------ Superposition Options
% 23.45/3.50  
% 23.45/3.50  --superposition_flag                    true
% 23.45/3.50  --sup_passive_queue_type                priority_queues
% 23.45/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.45/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.45/3.50  --demod_completeness_check              fast
% 23.45/3.50  --demod_use_ground                      true
% 23.45/3.50  --sup_to_prop_solver                    passive
% 23.45/3.50  --sup_prop_simpl_new                    true
% 23.45/3.50  --sup_prop_simpl_given                  true
% 23.45/3.50  --sup_fun_splitting                     true
% 23.45/3.50  --sup_smt_interval                      50000
% 23.45/3.50  
% 23.45/3.50  ------ Superposition Simplification Setup
% 23.45/3.50  
% 23.45/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.45/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.45/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.45/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.45/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.45/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.45/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.45/3.50  --sup_immed_triv                        [TrivRules]
% 23.45/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.45/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.45/3.50  --sup_immed_bw_main                     []
% 23.45/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.45/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.45/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.45/3.50  --sup_input_bw                          []
% 23.45/3.50  
% 23.45/3.50  ------ Combination Options
% 23.45/3.50  
% 23.45/3.50  --comb_res_mult                         3
% 23.45/3.50  --comb_sup_mult                         2
% 23.45/3.50  --comb_inst_mult                        10
% 23.45/3.50  
% 23.45/3.50  ------ Debug Options
% 23.45/3.50  
% 23.45/3.50  --dbg_backtrace                         false
% 23.45/3.50  --dbg_dump_prop_clauses                 false
% 23.45/3.50  --dbg_dump_prop_clauses_file            -
% 23.45/3.50  --dbg_out_stat                          false
% 23.45/3.50  
% 23.45/3.50  
% 23.45/3.50  
% 23.45/3.50  
% 23.45/3.50  ------ Proving...
% 23.45/3.50  
% 23.45/3.50  
% 23.45/3.50  % SZS status Theorem for theBenchmark.p
% 23.45/3.50  
% 23.45/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.45/3.50  
% 23.45/3.50  fof(f18,conjecture,(
% 23.45/3.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f19,negated_conjecture,(
% 23.45/3.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 23.45/3.50    inference(negated_conjecture,[],[f18])).
% 23.45/3.50  
% 23.45/3.50  fof(f31,plain,(
% 23.45/3.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 23.45/3.50    inference(ennf_transformation,[],[f19])).
% 23.45/3.50  
% 23.45/3.50  fof(f32,plain,(
% 23.45/3.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 23.45/3.50    inference(flattening,[],[f31])).
% 23.45/3.50  
% 23.45/3.50  fof(f36,plain,(
% 23.45/3.50    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4)))),
% 23.45/3.50    introduced(choice_axiom,[])).
% 23.45/3.50  
% 23.45/3.50  fof(f37,plain,(
% 23.45/3.50    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) & r1_xboole_0(sK3,sK2) & r2_hidden(sK4,sK3) & r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 23.45/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f32,f36])).
% 23.45/3.50  
% 23.45/3.50  fof(f62,plain,(
% 23.45/3.50    r1_xboole_0(sK3,sK2)),
% 23.45/3.50    inference(cnf_transformation,[],[f37])).
% 23.45/3.50  
% 23.45/3.50  fof(f2,axiom,(
% 23.45/3.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f21,plain,(
% 23.45/3.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 23.45/3.50    inference(ennf_transformation,[],[f2])).
% 23.45/3.50  
% 23.45/3.50  fof(f39,plain,(
% 23.45/3.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f21])).
% 23.45/3.50  
% 23.45/3.50  fof(f17,axiom,(
% 23.45/3.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f30,plain,(
% 23.45/3.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 23.45/3.50    inference(ennf_transformation,[],[f17])).
% 23.45/3.50  
% 23.45/3.50  fof(f59,plain,(
% 23.45/3.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f30])).
% 23.45/3.50  
% 23.45/3.50  fof(f14,axiom,(
% 23.45/3.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f56,plain,(
% 23.45/3.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f14])).
% 23.45/3.50  
% 23.45/3.50  fof(f15,axiom,(
% 23.45/3.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f57,plain,(
% 23.45/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f15])).
% 23.45/3.50  
% 23.45/3.50  fof(f16,axiom,(
% 23.45/3.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f58,plain,(
% 23.45/3.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f16])).
% 23.45/3.50  
% 23.45/3.50  fof(f64,plain,(
% 23.45/3.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.45/3.50    inference(definition_unfolding,[],[f57,f58])).
% 23.45/3.50  
% 23.45/3.50  fof(f65,plain,(
% 23.45/3.50    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.45/3.50    inference(definition_unfolding,[],[f56,f64])).
% 23.45/3.50  
% 23.45/3.50  fof(f71,plain,(
% 23.45/3.50    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 23.45/3.50    inference(definition_unfolding,[],[f59,f65])).
% 23.45/3.50  
% 23.45/3.50  fof(f11,axiom,(
% 23.45/3.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f35,plain,(
% 23.45/3.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 23.45/3.50    inference(nnf_transformation,[],[f11])).
% 23.45/3.50  
% 23.45/3.50  fof(f52,plain,(
% 23.45/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f35])).
% 23.45/3.50  
% 23.45/3.50  fof(f61,plain,(
% 23.45/3.50    r2_hidden(sK4,sK3)),
% 23.45/3.50    inference(cnf_transformation,[],[f37])).
% 23.45/3.50  
% 23.45/3.50  fof(f3,axiom,(
% 23.45/3.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f20,plain,(
% 23.45/3.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.45/3.50    inference(rectify,[],[f3])).
% 23.45/3.50  
% 23.45/3.50  fof(f22,plain,(
% 23.45/3.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 23.45/3.50    inference(ennf_transformation,[],[f20])).
% 23.45/3.50  
% 23.45/3.50  fof(f33,plain,(
% 23.45/3.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.45/3.50    introduced(choice_axiom,[])).
% 23.45/3.50  
% 23.45/3.50  fof(f34,plain,(
% 23.45/3.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 23.45/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).
% 23.45/3.50  
% 23.45/3.50  fof(f42,plain,(
% 23.45/3.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f34])).
% 23.45/3.50  
% 23.45/3.50  fof(f60,plain,(
% 23.45/3.50    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK4))),
% 23.45/3.50    inference(cnf_transformation,[],[f37])).
% 23.45/3.50  
% 23.45/3.50  fof(f7,axiom,(
% 23.45/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f46,plain,(
% 23.45/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.45/3.50    inference(cnf_transformation,[],[f7])).
% 23.45/3.50  
% 23.45/3.50  fof(f72,plain,(
% 23.45/3.50    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),
% 23.45/3.50    inference(definition_unfolding,[],[f60,f46,f65])).
% 23.45/3.50  
% 23.45/3.50  fof(f5,axiom,(
% 23.45/3.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f23,plain,(
% 23.45/3.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 23.45/3.50    inference(ennf_transformation,[],[f5])).
% 23.45/3.50  
% 23.45/3.50  fof(f44,plain,(
% 23.45/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f23])).
% 23.45/3.50  
% 23.45/3.50  fof(f68,plain,(
% 23.45/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 23.45/3.50    inference(definition_unfolding,[],[f44,f46])).
% 23.45/3.50  
% 23.45/3.50  fof(f1,axiom,(
% 23.45/3.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f38,plain,(
% 23.45/3.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f1])).
% 23.45/3.50  
% 23.45/3.50  fof(f66,plain,(
% 23.45/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 23.45/3.50    inference(definition_unfolding,[],[f38,f46,f46])).
% 23.45/3.50  
% 23.45/3.50  fof(f4,axiom,(
% 23.45/3.50    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f43,plain,(
% 23.45/3.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f4])).
% 23.45/3.50  
% 23.45/3.50  fof(f67,plain,(
% 23.45/3.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) )),
% 23.45/3.50    inference(definition_unfolding,[],[f43,f46,f46,f46,f46])).
% 23.45/3.50  
% 23.45/3.50  fof(f6,axiom,(
% 23.45/3.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f45,plain,(
% 23.45/3.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f6])).
% 23.45/3.50  
% 23.45/3.50  fof(f9,axiom,(
% 23.45/3.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f25,plain,(
% 23.45/3.50    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 23.45/3.50    inference(ennf_transformation,[],[f9])).
% 23.45/3.50  
% 23.45/3.50  fof(f50,plain,(
% 23.45/3.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 23.45/3.50    inference(cnf_transformation,[],[f25])).
% 23.45/3.50  
% 23.45/3.50  fof(f69,plain,(
% 23.45/3.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 23.45/3.50    inference(definition_unfolding,[],[f50,f46])).
% 23.45/3.50  
% 23.45/3.50  fof(f10,axiom,(
% 23.45/3.50    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f26,plain,(
% 23.45/3.50    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 23.45/3.50    inference(ennf_transformation,[],[f10])).
% 23.45/3.50  
% 23.45/3.50  fof(f51,plain,(
% 23.45/3.50    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f26])).
% 23.45/3.50  
% 23.45/3.50  fof(f70,plain,(
% 23.45/3.50    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 23.45/3.50    inference(definition_unfolding,[],[f51,f46])).
% 23.45/3.50  
% 23.45/3.50  fof(f12,axiom,(
% 23.45/3.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f27,plain,(
% 23.45/3.50    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 23.45/3.50    inference(ennf_transformation,[],[f12])).
% 23.45/3.50  
% 23.45/3.50  fof(f54,plain,(
% 23.45/3.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 23.45/3.50    inference(cnf_transformation,[],[f27])).
% 23.45/3.50  
% 23.45/3.50  fof(f53,plain,(
% 23.45/3.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 23.45/3.50    inference(cnf_transformation,[],[f35])).
% 23.45/3.50  
% 23.45/3.50  fof(f8,axiom,(
% 23.45/3.50    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 23.45/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.45/3.50  
% 23.45/3.50  fof(f24,plain,(
% 23.45/3.50    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 23.45/3.50    inference(ennf_transformation,[],[f8])).
% 23.45/3.50  
% 23.45/3.50  fof(f47,plain,(
% 23.45/3.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 23.45/3.50    inference(cnf_transformation,[],[f24])).
% 23.45/3.50  
% 23.45/3.50  fof(f63,plain,(
% 23.45/3.50    ~r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 23.45/3.50    inference(cnf_transformation,[],[f37])).
% 23.45/3.50  
% 23.45/3.50  cnf(c_19,negated_conjecture,
% 23.45/3.50      ( r1_xboole_0(sK3,sK2) ),
% 23.45/3.50      inference(cnf_transformation,[],[f62]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_710,plain,
% 23.45/3.50      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1,plain,
% 23.45/3.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 23.45/3.50      inference(cnf_transformation,[],[f39]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_727,plain,
% 23.45/3.50      ( r1_xboole_0(X0,X1) != iProver_top
% 23.45/3.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2172,plain,
% 23.45/3.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_710,c_727]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_17,plain,
% 23.45/3.50      ( r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ),
% 23.45/3.50      inference(cnf_transformation,[],[f71]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_712,plain,
% 23.45/3.50      ( r2_hidden(X0,X1) = iProver_top
% 23.45/3.50      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_14,plain,
% 23.45/3.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 23.45/3.50      inference(cnf_transformation,[],[f52]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_715,plain,
% 23.45/3.50      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2995,plain,
% 23.45/3.50      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = k2_enumset1(X0,X0,X0,X0)
% 23.45/3.50      | r2_hidden(X0,X1) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_712,c_715]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_20,negated_conjecture,
% 23.45/3.50      ( r2_hidden(sK4,sK3) ),
% 23.45/3.50      inference(cnf_transformation,[],[f61]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_709,plain,
% 23.45/3.50      ( r2_hidden(sK4,sK3) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2,plain,
% 23.45/3.50      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 23.45/3.50      inference(cnf_transformation,[],[f42]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_726,plain,
% 23.45/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.45/3.50      | r2_hidden(X0,X2) != iProver_top
% 23.45/3.50      | r1_xboole_0(X2,X1) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_9633,plain,
% 23.45/3.50      ( r2_hidden(sK4,X0) != iProver_top
% 23.45/3.50      | r1_xboole_0(X0,sK3) != iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_709,c_726]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_52463,plain,
% 23.45/3.50      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0) = k2_enumset1(sK4,sK4,sK4,sK4)
% 23.45/3.50      | r1_xboole_0(X0,sK3) != iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2995,c_9633]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57982,plain,
% 23.45/3.50      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK2) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2172,c_52463]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_21,negated_conjecture,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 23.45/3.50      inference(cnf_transformation,[],[f72]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_708,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_6,plain,
% 23.45/3.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 23.45/3.50      inference(cnf_transformation,[],[f68]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_723,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 23.45/3.50      | r1_tarski(X0,X1) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4690,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_708,c_723]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_0,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.45/3.50      inference(cnf_transformation,[],[f66]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_5,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
% 23.45/3.50      inference(cnf_transformation,[],[f67]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1906,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11306,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_1906]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_58173,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_57982,c_11306]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11349,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1906,c_0]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_49528,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11349,c_4690]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1734,plain,
% 23.45/3.50      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_710,c_715]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11287,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1734,c_1906]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1927,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1933,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X3)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_1927,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25777,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)))),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,sK3),k4_xboole_0(k4_xboole_0(sK2,sK3),X0)))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11287,c_1933]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2533,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2172,c_715]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2675,plain,
% 23.45/3.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,sK2) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2533,c_0]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2676,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,sK2) = k4_xboole_0(sK3,sK3) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_2675,c_1734]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_7,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 23.45/3.50      inference(cnf_transformation,[],[f45]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_722,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2674,plain,
% 23.45/3.50      ( r1_tarski(sK2,sK2) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2533,c_722]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4696,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2674,c_723]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4701,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)) = sK2 ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_4696,c_2676]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1367,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_722]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2405,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(sK3,sK3),sK2) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1734,c_1367]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4694,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),sK2)) = k4_xboole_0(sK3,sK3) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2405,c_723]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1920,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_19722,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),X0)))) = k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),X0)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4694,c_1920]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2803,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)),X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2676,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_20098,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_19722,c_2803]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_26327,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 23.45/3.50      inference(light_normalisation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_25777,c_2533,c_2676,c_4701,c_20098]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_51031,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK1)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_49528,c_26327]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_51103,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_51031,c_49528]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_58178,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK4)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_58173,c_51103]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1917,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11,plain,
% 23.45/3.50      ( ~ r1_xboole_0(X0,X1)
% 23.45/3.50      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 23.45/3.50      inference(cnf_transformation,[],[f69]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_718,plain,
% 23.45/3.50      ( r1_xboole_0(X0,X1) != iProver_top
% 23.45/3.50      | r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_6237,plain,
% 23.45/3.50      ( r1_xboole_0(X0,X1) != iProver_top
% 23.45/3.50      | r1_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_718]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_7605,plain,
% 23.45/3.50      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
% 23.45/3.50      | r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_6237]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_6250,plain,
% 23.45/3.50      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top
% 23.45/3.50      | r1_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_718]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_12,plain,
% 23.45/3.50      ( r1_xboole_0(X0,X1)
% 23.45/3.50      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 23.45/3.50      inference(cnf_transformation,[],[f70]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_717,plain,
% 23.45/3.50      ( r1_xboole_0(X0,X1) = iProver_top
% 23.45/3.50      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_6624,plain,
% 23.45/3.50      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top
% 23.45/3.50      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_6250,c_717]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1929,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))),X2) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_5,c_1367]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4876,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_1929]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_15,plain,
% 23.45/3.50      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 23.45/3.50      inference(cnf_transformation,[],[f54]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_714,plain,
% 23.45/3.50      ( r1_tarski(X0,X1) != iProver_top
% 23.45/3.50      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4882,plain,
% 23.45/3.50      ( r1_tarski(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))) != iProver_top
% 23.45/3.50      | r1_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_714]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_6849,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4876,c_4882]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_9489,plain,
% 23.45/3.50      ( r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = iProver_top ),
% 23.45/3.50      inference(global_propositional_subsumption,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_7605,c_6624,c_6849]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_9496,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = X0 ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_9489,c_715]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4865,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)),X0)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11395,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1906,c_4865]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11496,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0)) = k4_xboole_0(X0,X0) ),
% 23.45/3.50      inference(light_normalisation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_11395,c_4690,c_9496]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_13101,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11496,c_1906]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_13236,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_13101,c_9496]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28518,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK2)))) = X0 ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_9496,c_13236]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28519,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3)))) = X0 ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_28518,c_2676]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_3413,plain,
% 23.45/3.50      ( r1_tarski(X0,sK2) != iProver_top
% 23.45/3.50      | r1_xboole_0(X0,k4_xboole_0(sK3,sK3)) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2676,c_714]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_3228,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))),sK2) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1734,c_1929]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_3411,plain,
% 23.45/3.50      ( r1_tarski(X0,sK2) != iProver_top
% 23.45/3.50      | r1_xboole_0(X0,sK3) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1734,c_714]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_3583,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))),sK3) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_3228,c_3411]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_6247,plain,
% 23.45/3.50      ( r1_xboole_0(X0,k4_xboole_0(sK3,sK3)) = iProver_top
% 23.45/3.50      | r1_xboole_0(X0,sK3) != iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1734,c_718]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_6426,plain,
% 23.45/3.50      ( r1_xboole_0(X0,k4_xboole_0(sK3,sK3)) = iProver_top
% 23.45/3.50      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))),sK3) != iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_6247,c_717]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_19595,plain,
% 23.45/3.50      ( r1_xboole_0(X0,k4_xboole_0(sK3,sK3)) = iProver_top ),
% 23.45/3.50      inference(global_propositional_subsumption,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_3413,c_3583,c_6426]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_19602,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(sK3,sK3)) = X0 ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_19595,c_715]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28520,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(sK1,sK1)) = X0 ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_28519,c_19602]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28606,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,sK1))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_28520,c_1917]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1930,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X0)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28624,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_28520,c_1930]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_9495,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),X0) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_9489,c_727]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25586,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK2))),X0) = iProver_top ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_9495,c_13236]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25587,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))),X0) = iProver_top ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_25586,c_2676]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25588,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK1,sK1),X0) = iProver_top ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_25587,c_19602]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25593,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,sK1),X0) = k4_xboole_0(sK1,sK1) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_25588,c_715]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28710,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(sK1,sK1) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_28624,c_25593]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28608,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK1,sK1))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_28520,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28732,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X0) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_28608,c_28520,c_28710]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28734,plain,
% 23.45/3.50      ( k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_28606,c_28520,c_28710,c_28732]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28735,plain,
% 23.45/3.50      ( k4_xboole_0(X0,X0) = sP0_iProver_split ),
% 23.45/3.50      inference(splitting,
% 23.45/3.50                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 23.45/3.50                [c_28734]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1728,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_1367]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_3176,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_1728]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4688,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_722,c_723]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_18214,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_3176,c_4688]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_18232,plain,
% 23.45/3.50      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_18214]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_19371,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_18232,c_723]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_14240,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11306,c_1906]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1914,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_14937,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_1914]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4880,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_14938,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))))),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4880,c_1914]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_15297,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_14938,c_4880]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_5078,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_enumset1(sK4,sK4,sK4,sK4))),X0)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4880,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_5093,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_5078,c_1917]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_15298,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_15297,c_1917,c_5093]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_15300,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),X0))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_14937,c_15298]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_15301,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_15300,c_4690]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_15302,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_15301,c_14240]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_15304,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_15302,c_15298]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_14919,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11306,c_1914]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_15319,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,X0))))) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_14919,c_14240]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_19372,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_19371,c_14240,c_15304,c_15319]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_19373,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_19372,c_4690]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11288,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK3,sK3)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2676,c_1906]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11538,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) = k4_xboole_0(X0,k4_xboole_0(X0,sK2)) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_11288,c_4701]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_19374,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_19373,c_11538]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_29777,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_19374,c_1914]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1932,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_22417,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),X0))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11306,c_1932]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_22750,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
% 23.45/3.50      inference(light_normalisation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_22417,c_4690,c_15304]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_24768,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_22750,c_11306]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_24773,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_24768,c_4688]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28571,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X0)))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),X0)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_28520,c_1920]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_29277,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)))) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_28571,c_25593]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2403,plain,
% 23.45/3.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),X0)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1734,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_2822,plain,
% 23.45/3.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2403,c_0]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_24651,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK3,sK3))))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_2822,c_22750]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11052,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK3,sK3),X0)))) = k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),X0)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4701,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11092,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) ),
% 23.45/3.50      inference(light_normalisation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_11052,c_2403,c_2676]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25147,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK2))) ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_24651,c_11092,c_13236,c_14240,c_19602,c_24773]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25148,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_25147,c_2676]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_9862,plain,
% 23.45/3.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_2822]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_17525,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(sK3,sK3))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1917,c_9862]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_17657,plain,
% 23.45/3.50      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,sK2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(sK3,sK3))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_17525,c_1917]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25149,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))))))) = k4_xboole_0(sK1,sK1) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_25148,c_17657,c_19602]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_17227,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK3,sK3))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4694,c_1930]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25150,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK3,sK3))))) = k4_xboole_0(sK1,sK1) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_25149,c_17227]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25151,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) = k4_xboole_0(sK1,sK1) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_25150,c_19602]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_29278,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,sK1) = sP0_iProver_split ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_29277,c_25151,c_25593,c_28735]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_29814,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) = sP0_iProver_split ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_29777,c_2676,c_13236,c_19602,c_24773,c_29278]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_29985,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sP0_iProver_split) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_29814,c_0]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_30052,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sP0_iProver_split) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_29985,c_19374]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11277,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_1906]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_27634,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_11277]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53568,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11306,c_27634]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_27930,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11277,c_0]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_55434,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_27930]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_14100,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_11306]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56615,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_55434,c_1917,c_14100]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53746,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_1932]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56004,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27930,c_1932]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_11297,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_1906]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53494,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_11297,c_27634]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53794,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),X2)) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_11349]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_54469,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_53794,c_4688]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_54900,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_53494,c_54469]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_28747,plain,
% 23.45/3.50      ( k4_xboole_0(X0,sP0_iProver_split) = X0 ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_28735,c_28520]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_54901,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 23.45/3.50      inference(light_normalisation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_54900,c_4688,c_28735,c_28747]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56317,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_56004,c_1917,c_54901]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57272,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X0)))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_53746,c_56317]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57273,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X2)) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57272,c_54901]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53736,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_1932]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_54036,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_1933]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_55682,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),X4)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X4)))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27930,c_1933]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_55741,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X3)))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27930,c_11349]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56473,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))))),X4)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,X4)))))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_55682,c_55741]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_54075,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_11277]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_55020,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_54901,c_27634]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56828,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_54075,c_54901,c_55020]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56861,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_54036,c_56473,c_56828]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56862,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_56861,c_1917,c_55020]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57281,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X0))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_53736,c_56317,c_56862,c_57273]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57282,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 23.45/3.50      inference(light_normalisation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_57281,c_28735,c_28747,c_54901]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53919,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),X3))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_1932]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57003,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),X3) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_53919,c_56317]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57004,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3) ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_57003,c_1932,c_54901,c_55020]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53929,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_1914]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56991,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_53929,c_56828]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56992,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_56991,c_54901,c_55020]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57005,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))),X3) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57004,c_56992]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57292,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57282,c_57005]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57293,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57282,c_57004]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_54114,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X2,X3)))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_1920]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56775,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))))) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_54114,c_54901]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56776,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_56775,c_54901,c_55020]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_56830,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_56828,c_56776]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57296,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X3)) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57282,c_56830]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57315,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X2)),X3) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57293,c_57282,c_57296]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53756,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X3))))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X0))))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_1917]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_53810,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X3))))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27634,c_1920]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57148,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),X3))))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X0,X1)))))) ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_53810,c_54901]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57149,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X2),X3))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57148,c_54901,c_55020]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57216,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X1,X2))))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_53756,c_57149]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57217,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X3))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X0)),X3))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57216,c_54901]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_55707,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27930,c_1917]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57221,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57217,c_55707]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_55726,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X3,k4_xboole_0(X3,X1))))))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_27930,c_11277]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57244,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57221,c_55726]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57330,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X3))) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57315,c_57244]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57513,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_53568,c_56615,c_57273,c_57292,c_57330]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57322,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57315,c_57221]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57514,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1) ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_57513,c_57322]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_57515,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = sP0_iProver_split ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_57514,c_29814]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_58179,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sP0_iProver_split ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_58178,c_1917,c_28735,c_30052,c_57515]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_17585,plain,
% 23.45/3.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4))))) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_1917,c_4690]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_5546,plain,
% 23.45/3.50      ( r1_xboole_0(X0,k4_xboole_0(X0,X1)) = iProver_top
% 23.45/3.50      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) != iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_0,c_717]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_46682,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))),sK2))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
% 23.45/3.50      | r1_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_17585,c_5546]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_46756,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK4,sK4,sK4,sK4)))),sK2))),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
% 23.45/3.50      | r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_46682,c_17585]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_46757,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
% 23.45/3.50      | r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 23.45/3.50      inference(demodulation,[status(thm)],[c_46756,c_4688,c_17585]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_4879,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4690,c_5]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_13,plain,
% 23.45/3.50      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 23.45/3.50      inference(cnf_transformation,[],[f53]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_716,plain,
% 23.45/3.50      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1949,plain,
% 23.45/3.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
% 23.45/3.50      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_5,c_716]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_30252,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 23.45/3.50      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k2_enumset1(sK4,sK4,sK4,sK4)))) = iProver_top ),
% 23.45/3.50      inference(superposition,[status(thm)],[c_4879,c_1949]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_30450,plain,
% 23.45/3.50      ( k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
% 23.45/3.50      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 23.45/3.50      inference(light_normalisation,[status(thm)],[c_30252,c_4690]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_30451,plain,
% 23.45/3.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sP0_iProver_split
% 23.45/3.50      | r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 23.45/3.50      inference(demodulation,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_30450,c_2676,c_13236,c_19602,c_29278]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1547,plain,
% 23.45/3.50      ( r1_xboole_0(X0,sK2) | ~ r1_xboole_0(sK2,X0) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_1]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_16851,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
% 23.45/3.50      | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_1547]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_16855,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) = iProver_top
% 23.45/3.50      | r1_xboole_0(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_16851]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1517,plain,
% 23.45/3.50      ( r1_xboole_0(X0,sK2)
% 23.45/3.50      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),sK2) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_12]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_5407,plain,
% 23.45/3.50      ( ~ r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
% 23.45/3.50      | r1_xboole_0(sK1,sK2) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_1517]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_5408,plain,
% 23.45/3.50      ( r1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
% 23.45/3.50      | r1_xboole_0(sK1,sK2) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_5407]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1590,plain,
% 23.45/3.50      ( ~ r1_xboole_0(X0,sK2) | r1_xboole_0(sK2,X0) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_1]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_3678,plain,
% 23.45/3.50      ( r1_xboole_0(sK2,sK1) | ~ r1_xboole_0(sK1,sK2) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_1590]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_3679,plain,
% 23.45/3.50      ( r1_xboole_0(sK2,sK1) = iProver_top
% 23.45/3.50      | r1_xboole_0(sK1,sK2) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_3678]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1216,plain,
% 23.45/3.50      ( r1_xboole_0(sK2,sK3) | ~ r1_xboole_0(sK3,sK2) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_1]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_1217,plain,
% 23.45/3.50      ( r1_xboole_0(sK2,sK3) = iProver_top
% 23.45/3.50      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_1216]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_10,plain,
% 23.45/3.50      ( ~ r1_xboole_0(X0,X1)
% 23.45/3.50      | ~ r1_xboole_0(X0,X2)
% 23.45/3.50      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.45/3.50      inference(cnf_transformation,[],[f47]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_894,plain,
% 23.45/3.50      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3))
% 23.45/3.50      | ~ r1_xboole_0(sK2,sK3)
% 23.45/3.50      | ~ r1_xboole_0(sK2,sK1) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_10]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_895,plain,
% 23.45/3.50      ( r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
% 23.45/3.50      | r1_xboole_0(sK2,sK3) != iProver_top
% 23.45/3.50      | r1_xboole_0(sK2,sK1) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_774,plain,
% 23.45/3.50      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2)
% 23.45/3.50      | ~ r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
% 23.45/3.50      inference(instantiation,[status(thm)],[c_1]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_775,plain,
% 23.45/3.50      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) = iProver_top
% 23.45/3.50      | r1_xboole_0(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_18,negated_conjecture,
% 23.45/3.50      ( ~ r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
% 23.45/3.50      inference(cnf_transformation,[],[f63]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_25,plain,
% 23.45/3.50      ( r1_xboole_0(k2_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(c_24,plain,
% 23.45/3.50      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 23.45/3.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.45/3.50  
% 23.45/3.50  cnf(contradiction,plain,
% 23.45/3.50      ( $false ),
% 23.45/3.50      inference(minisat,
% 23.45/3.50                [status(thm)],
% 23.45/3.50                [c_58179,c_46757,c_30451,c_16855,c_5408,c_3679,c_1217,
% 23.45/3.50                 c_895,c_775,c_25,c_24]) ).
% 23.45/3.50  
% 23.45/3.50  
% 23.45/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.45/3.50  
% 23.45/3.50  ------                               Statistics
% 23.45/3.50  
% 23.45/3.50  ------ General
% 23.45/3.50  
% 23.45/3.50  abstr_ref_over_cycles:                  0
% 23.45/3.50  abstr_ref_under_cycles:                 0
% 23.45/3.50  gc_basic_clause_elim:                   0
% 23.45/3.50  forced_gc_time:                         0
% 23.45/3.50  parsing_time:                           0.01
% 23.45/3.50  unif_index_cands_time:                  0.
% 23.45/3.50  unif_index_add_time:                    0.
% 23.45/3.50  orderings_time:                         0.
% 23.45/3.50  out_proof_time:                         0.022
% 23.45/3.50  total_time:                             2.598
% 23.45/3.50  num_of_symbols:                         43
% 23.45/3.50  num_of_terms:                           127496
% 23.45/3.50  
% 23.45/3.50  ------ Preprocessing
% 23.45/3.50  
% 23.45/3.50  num_of_splits:                          0
% 23.45/3.50  num_of_split_atoms:                     1
% 23.45/3.50  num_of_reused_defs:                     0
% 23.45/3.50  num_eq_ax_congr_red:                    4
% 23.45/3.50  num_of_sem_filtered_clauses:            1
% 23.45/3.50  num_of_subtypes:                        0
% 23.45/3.50  monotx_restored_types:                  0
% 23.45/3.50  sat_num_of_epr_types:                   0
% 23.45/3.50  sat_num_of_non_cyclic_types:            0
% 23.45/3.50  sat_guarded_non_collapsed_types:        0
% 23.45/3.50  num_pure_diseq_elim:                    0
% 23.45/3.50  simp_replaced_by:                       0
% 23.45/3.50  res_preprocessed:                       83
% 23.45/3.50  prep_upred:                             0
% 23.45/3.50  prep_unflattend:                        0
% 23.45/3.50  smt_new_axioms:                         0
% 23.45/3.50  pred_elim_cands:                        3
% 23.45/3.50  pred_elim:                              0
% 23.45/3.50  pred_elim_cl:                           0
% 23.45/3.50  pred_elim_cycles:                       1
% 23.45/3.50  merged_defs:                            6
% 23.45/3.50  merged_defs_ncl:                        0
% 23.45/3.50  bin_hyper_res:                          6
% 23.45/3.50  prep_cycles:                            3
% 23.45/3.50  pred_elim_time:                         0.
% 23.45/3.50  splitting_time:                         0.
% 23.45/3.50  sem_filter_time:                        0.
% 23.45/3.50  monotx_time:                            0.001
% 23.45/3.50  subtype_inf_time:                       0.
% 23.45/3.50  
% 23.45/3.50  ------ Problem properties
% 23.45/3.50  
% 23.45/3.50  clauses:                                22
% 23.45/3.50  conjectures:                            4
% 23.45/3.50  epr:                                    4
% 23.45/3.50  horn:                                   19
% 23.45/3.50  ground:                                 4
% 23.45/3.50  unary:                                  7
% 23.45/3.50  binary:                                 12
% 23.45/3.50  lits:                                   40
% 23.45/3.50  lits_eq:                                5
% 23.45/3.50  fd_pure:                                0
% 23.45/3.50  fd_pseudo:                              0
% 23.45/3.50  fd_cond:                                0
% 23.45/3.50  fd_pseudo_cond:                         0
% 23.45/3.50  ac_symbols:                             0
% 23.45/3.50  
% 23.45/3.50  ------ Propositional Solver
% 23.45/3.50  
% 23.45/3.50  prop_solver_calls:                      26
% 23.45/3.50  prop_fast_solver_calls:                 695
% 23.45/3.50  smt_solver_calls:                       0
% 23.45/3.50  smt_fast_solver_calls:                  0
% 23.45/3.50  prop_num_of_clauses:                    22864
% 23.45/3.50  prop_preprocess_simplified:             19576
% 23.45/3.50  prop_fo_subsumed:                       5
% 23.45/3.50  prop_solver_time:                       0.
% 23.45/3.50  smt_solver_time:                        0.
% 23.45/3.50  smt_fast_solver_time:                   0.
% 23.45/3.50  prop_fast_solver_time:                  0.
% 23.45/3.50  prop_unsat_core_time:                   0.002
% 23.45/3.50  
% 23.45/3.50  ------ QBF
% 23.45/3.50  
% 23.45/3.50  qbf_q_res:                              0
% 23.45/3.50  qbf_num_tautologies:                    0
% 23.45/3.50  qbf_prep_cycles:                        0
% 23.45/3.50  
% 23.45/3.50  ------ BMC1
% 23.45/3.50  
% 23.45/3.50  bmc1_current_bound:                     -1
% 23.45/3.50  bmc1_last_solved_bound:                 -1
% 23.45/3.50  bmc1_unsat_core_size:                   -1
% 23.45/3.50  bmc1_unsat_core_parents_size:           -1
% 23.45/3.50  bmc1_merge_next_fun:                    0
% 23.45/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.45/3.50  
% 23.45/3.50  ------ Instantiation
% 23.45/3.50  
% 23.45/3.50  inst_num_of_clauses:                    2265
% 23.45/3.50  inst_num_in_passive:                    961
% 23.45/3.50  inst_num_in_active:                     986
% 23.45/3.50  inst_num_in_unprocessed:                318
% 23.45/3.50  inst_num_of_loops:                      1070
% 23.45/3.50  inst_num_of_learning_restarts:          0
% 23.45/3.50  inst_num_moves_active_passive:          84
% 23.45/3.50  inst_lit_activity:                      0
% 23.45/3.50  inst_lit_activity_moves:                0
% 23.45/3.50  inst_num_tautologies:                   0
% 23.45/3.50  inst_num_prop_implied:                  0
% 23.45/3.50  inst_num_existing_simplified:           0
% 23.45/3.50  inst_num_eq_res_simplified:             0
% 23.45/3.50  inst_num_child_elim:                    0
% 23.45/3.50  inst_num_of_dismatching_blockings:      1397
% 23.45/3.50  inst_num_of_non_proper_insts:           2362
% 23.45/3.50  inst_num_of_duplicates:                 0
% 23.45/3.50  inst_inst_num_from_inst_to_res:         0
% 23.45/3.50  inst_dismatching_checking_time:         0.
% 23.45/3.50  
% 23.45/3.50  ------ Resolution
% 23.45/3.50  
% 23.45/3.50  res_num_of_clauses:                     0
% 23.45/3.50  res_num_in_passive:                     0
% 23.45/3.50  res_num_in_active:                      0
% 23.45/3.50  res_num_of_loops:                       86
% 23.45/3.50  res_forward_subset_subsumed:            84
% 23.45/3.50  res_backward_subset_subsumed:           0
% 23.45/3.50  res_forward_subsumed:                   0
% 23.45/3.50  res_backward_subsumed:                  0
% 23.45/3.50  res_forward_subsumption_resolution:     0
% 23.45/3.50  res_backward_subsumption_resolution:    0
% 23.45/3.50  res_clause_to_clause_subsumption:       148021
% 23.45/3.50  res_orphan_elimination:                 0
% 23.45/3.50  res_tautology_del:                      99
% 23.45/3.50  res_num_eq_res_simplified:              0
% 23.45/3.50  res_num_sel_changes:                    0
% 23.45/3.50  res_moves_from_active_to_pass:          0
% 23.45/3.50  
% 23.45/3.50  ------ Superposition
% 23.45/3.50  
% 23.45/3.50  sup_time_total:                         0.
% 23.45/3.50  sup_time_generating:                    0.
% 23.45/3.50  sup_time_sim_full:                      0.
% 23.45/3.50  sup_time_sim_immed:                     0.
% 23.45/3.50  
% 23.45/3.50  sup_num_of_clauses:                     5099
% 23.45/3.50  sup_num_in_active:                      198
% 23.45/3.50  sup_num_in_passive:                     4901
% 23.45/3.50  sup_num_of_loops:                       212
% 23.45/3.50  sup_fw_superposition:                   8928
% 23.45/3.50  sup_bw_superposition:                   9042
% 23.45/3.50  sup_immediate_simplified:               9916
% 23.45/3.50  sup_given_eliminated:                   4
% 23.45/3.50  comparisons_done:                       0
% 23.45/3.50  comparisons_avoided:                    0
% 23.45/3.50  
% 23.45/3.50  ------ Simplifications
% 23.45/3.50  
% 23.45/3.50  
% 23.45/3.50  sim_fw_subset_subsumed:                 56
% 23.45/3.50  sim_bw_subset_subsumed:                 20
% 23.45/3.50  sim_fw_subsumed:                        1962
% 23.45/3.50  sim_bw_subsumed:                        493
% 23.45/3.50  sim_fw_subsumption_res:                 0
% 23.45/3.50  sim_bw_subsumption_res:                 0
% 23.45/3.50  sim_tautology_del:                      264
% 23.45/3.50  sim_eq_tautology_del:                   598
% 23.45/3.50  sim_eq_res_simp:                        38
% 23.45/3.50  sim_fw_demodulated:                     8702
% 23.45/3.50  sim_bw_demodulated:                     605
% 23.45/3.50  sim_light_normalised:                   4304
% 23.45/3.50  sim_joinable_taut:                      0
% 23.45/3.50  sim_joinable_simp:                      0
% 23.45/3.50  sim_ac_normalised:                      0
% 23.45/3.50  sim_smt_subsumption:                    0
% 23.45/3.50  
%------------------------------------------------------------------------------
