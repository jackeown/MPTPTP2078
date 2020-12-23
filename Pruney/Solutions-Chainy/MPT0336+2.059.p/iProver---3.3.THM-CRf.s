%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:43 EST 2020

% Result     : Theorem 15.53s
% Output     : CNFRefutation 15.53s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 217 expanded)
%              Number of clauses        :   51 (  72 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  223 ( 498 expanded)
%              Number of equality atoms :   87 ( 160 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f24])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f31])).

fof(f52,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f54])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f58,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f16,plain,(
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

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f56])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_540,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_551,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_995,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_540,c_551])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_552,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1174,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_552])).

cnf(c_3205,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_1174])).

cnf(c_3250,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3205,c_551])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_546,plain,
    ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2039,plain,
    ( r2_hidden(sK1(X0,X1),k3_xboole_0(X1,X0)) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_546])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_538,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_545,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_991,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = k3_enumset1(sK5,sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_538,c_545])).

cnf(c_9,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_547,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2404,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_547])).

cnf(c_2547,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k2_xboole_0(X1,X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2404])).

cnf(c_3477,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_2547])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_19,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_693,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK4)
    | ~ r1_xboole_0(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_694,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_696,plain,
    ( r2_hidden(sK5,sK3) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r1_xboole_0(sK4,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_822,plain,
    ( r2_hidden(X0,sK3)
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_823,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_825,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_544,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1858,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_544])).

cnf(c_2747,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),X3),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1858,c_2547])).

cnf(c_16545,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top
    | r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_2747])).

cnf(c_29006,plain,
    ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3477,c_18,c_19,c_696,c_825,c_16545])).

cnf(c_29018,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_29006])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_543,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_29448,plain,
    ( k3_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_29018,c_543])).

cnf(c_30959,plain,
    ( k3_xboole_0(sK3,X0) != k1_xboole_0
    | r1_xboole_0(k2_xboole_0(sK2,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_29448,c_1174])).

cnf(c_62846,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3250,c_30959])).

cnf(c_13,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62846,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 15.53/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.53/2.48  
% 15.53/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.53/2.48  
% 15.53/2.48  ------  iProver source info
% 15.53/2.48  
% 15.53/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.53/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.53/2.48  git: non_committed_changes: false
% 15.53/2.48  git: last_make_outside_of_git: false
% 15.53/2.48  
% 15.53/2.48  ------ 
% 15.53/2.48  
% 15.53/2.48  ------ Input Options
% 15.53/2.48  
% 15.53/2.48  --out_options                           all
% 15.53/2.48  --tptp_safe_out                         true
% 15.53/2.48  --problem_path                          ""
% 15.53/2.48  --include_path                          ""
% 15.53/2.48  --clausifier                            res/vclausify_rel
% 15.53/2.48  --clausifier_options                    --mode clausify
% 15.53/2.48  --stdin                                 false
% 15.53/2.48  --stats_out                             sel
% 15.53/2.48  
% 15.53/2.48  ------ General Options
% 15.53/2.48  
% 15.53/2.48  --fof                                   false
% 15.53/2.48  --time_out_real                         604.99
% 15.53/2.48  --time_out_virtual                      -1.
% 15.53/2.48  --symbol_type_check                     false
% 15.53/2.48  --clausify_out                          false
% 15.53/2.48  --sig_cnt_out                           false
% 15.53/2.48  --trig_cnt_out                          false
% 15.53/2.48  --trig_cnt_out_tolerance                1.
% 15.53/2.48  --trig_cnt_out_sk_spl                   false
% 15.53/2.48  --abstr_cl_out                          false
% 15.53/2.48  
% 15.53/2.48  ------ Global Options
% 15.53/2.48  
% 15.53/2.48  --schedule                              none
% 15.53/2.48  --add_important_lit                     false
% 15.53/2.48  --prop_solver_per_cl                    1000
% 15.53/2.48  --min_unsat_core                        false
% 15.53/2.48  --soft_assumptions                      false
% 15.53/2.48  --soft_lemma_size                       3
% 15.53/2.48  --prop_impl_unit_size                   0
% 15.53/2.48  --prop_impl_unit                        []
% 15.53/2.48  --share_sel_clauses                     true
% 15.53/2.48  --reset_solvers                         false
% 15.53/2.48  --bc_imp_inh                            [conj_cone]
% 15.53/2.48  --conj_cone_tolerance                   3.
% 15.53/2.48  --extra_neg_conj                        none
% 15.53/2.48  --large_theory_mode                     true
% 15.53/2.48  --prolific_symb_bound                   200
% 15.53/2.48  --lt_threshold                          2000
% 15.53/2.48  --clause_weak_htbl                      true
% 15.53/2.48  --gc_record_bc_elim                     false
% 15.53/2.48  
% 15.53/2.48  ------ Preprocessing Options
% 15.53/2.48  
% 15.53/2.48  --preprocessing_flag                    true
% 15.53/2.48  --time_out_prep_mult                    0.1
% 15.53/2.48  --splitting_mode                        input
% 15.53/2.48  --splitting_grd                         true
% 15.53/2.48  --splitting_cvd                         false
% 15.53/2.48  --splitting_cvd_svl                     false
% 15.53/2.48  --splitting_nvd                         32
% 15.53/2.48  --sub_typing                            true
% 15.53/2.48  --prep_gs_sim                           false
% 15.53/2.48  --prep_unflatten                        true
% 15.53/2.48  --prep_res_sim                          true
% 15.53/2.48  --prep_upred                            true
% 15.53/2.48  --prep_sem_filter                       exhaustive
% 15.53/2.48  --prep_sem_filter_out                   false
% 15.53/2.48  --pred_elim                             false
% 15.53/2.48  --res_sim_input                         true
% 15.53/2.48  --eq_ax_congr_red                       true
% 15.53/2.48  --pure_diseq_elim                       true
% 15.53/2.48  --brand_transform                       false
% 15.53/2.48  --non_eq_to_eq                          false
% 15.53/2.48  --prep_def_merge                        true
% 15.53/2.48  --prep_def_merge_prop_impl              false
% 15.53/2.48  --prep_def_merge_mbd                    true
% 15.53/2.48  --prep_def_merge_tr_red                 false
% 15.53/2.48  --prep_def_merge_tr_cl                  false
% 15.53/2.48  --smt_preprocessing                     true
% 15.53/2.48  --smt_ac_axioms                         fast
% 15.53/2.48  --preprocessed_out                      false
% 15.53/2.48  --preprocessed_stats                    false
% 15.53/2.48  
% 15.53/2.48  ------ Abstraction refinement Options
% 15.53/2.48  
% 15.53/2.48  --abstr_ref                             []
% 15.53/2.48  --abstr_ref_prep                        false
% 15.53/2.48  --abstr_ref_until_sat                   false
% 15.53/2.48  --abstr_ref_sig_restrict                funpre
% 15.53/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.53/2.48  --abstr_ref_under                       []
% 15.53/2.48  
% 15.53/2.48  ------ SAT Options
% 15.53/2.48  
% 15.53/2.48  --sat_mode                              false
% 15.53/2.48  --sat_fm_restart_options                ""
% 15.53/2.48  --sat_gr_def                            false
% 15.53/2.48  --sat_epr_types                         true
% 15.53/2.48  --sat_non_cyclic_types                  false
% 15.53/2.48  --sat_finite_models                     false
% 15.53/2.48  --sat_fm_lemmas                         false
% 15.53/2.48  --sat_fm_prep                           false
% 15.53/2.48  --sat_fm_uc_incr                        true
% 15.53/2.48  --sat_out_model                         small
% 15.53/2.48  --sat_out_clauses                       false
% 15.53/2.48  
% 15.53/2.48  ------ QBF Options
% 15.53/2.48  
% 15.53/2.48  --qbf_mode                              false
% 15.53/2.48  --qbf_elim_univ                         false
% 15.53/2.48  --qbf_dom_inst                          none
% 15.53/2.48  --qbf_dom_pre_inst                      false
% 15.53/2.48  --qbf_sk_in                             false
% 15.53/2.48  --qbf_pred_elim                         true
% 15.53/2.48  --qbf_split                             512
% 15.53/2.48  
% 15.53/2.48  ------ BMC1 Options
% 15.53/2.48  
% 15.53/2.48  --bmc1_incremental                      false
% 15.53/2.48  --bmc1_axioms                           reachable_all
% 15.53/2.48  --bmc1_min_bound                        0
% 15.53/2.48  --bmc1_max_bound                        -1
% 15.53/2.48  --bmc1_max_bound_default                -1
% 15.53/2.48  --bmc1_symbol_reachability              true
% 15.53/2.48  --bmc1_property_lemmas                  false
% 15.53/2.48  --bmc1_k_induction                      false
% 15.53/2.48  --bmc1_non_equiv_states                 false
% 15.53/2.48  --bmc1_deadlock                         false
% 15.53/2.48  --bmc1_ucm                              false
% 15.53/2.48  --bmc1_add_unsat_core                   none
% 15.53/2.48  --bmc1_unsat_core_children              false
% 15.53/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.53/2.48  --bmc1_out_stat                         full
% 15.53/2.48  --bmc1_ground_init                      false
% 15.53/2.48  --bmc1_pre_inst_next_state              false
% 15.53/2.48  --bmc1_pre_inst_state                   false
% 15.53/2.48  --bmc1_pre_inst_reach_state             false
% 15.53/2.48  --bmc1_out_unsat_core                   false
% 15.53/2.48  --bmc1_aig_witness_out                  false
% 15.53/2.48  --bmc1_verbose                          false
% 15.53/2.48  --bmc1_dump_clauses_tptp                false
% 15.53/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.53/2.48  --bmc1_dump_file                        -
% 15.53/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.53/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.53/2.48  --bmc1_ucm_extend_mode                  1
% 15.53/2.48  --bmc1_ucm_init_mode                    2
% 15.53/2.48  --bmc1_ucm_cone_mode                    none
% 15.53/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.53/2.48  --bmc1_ucm_relax_model                  4
% 15.53/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.53/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.53/2.48  --bmc1_ucm_layered_model                none
% 15.53/2.48  --bmc1_ucm_max_lemma_size               10
% 15.53/2.48  
% 15.53/2.48  ------ AIG Options
% 15.53/2.48  
% 15.53/2.48  --aig_mode                              false
% 15.53/2.48  
% 15.53/2.48  ------ Instantiation Options
% 15.53/2.48  
% 15.53/2.48  --instantiation_flag                    true
% 15.53/2.48  --inst_sos_flag                         false
% 15.53/2.48  --inst_sos_phase                        true
% 15.53/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.53/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.53/2.48  --inst_lit_sel_side                     num_symb
% 15.53/2.48  --inst_solver_per_active                1400
% 15.53/2.48  --inst_solver_calls_frac                1.
% 15.53/2.48  --inst_passive_queue_type               priority_queues
% 15.53/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.53/2.48  --inst_passive_queues_freq              [25;2]
% 15.53/2.48  --inst_dismatching                      true
% 15.53/2.48  --inst_eager_unprocessed_to_passive     true
% 15.53/2.48  --inst_prop_sim_given                   true
% 15.53/2.48  --inst_prop_sim_new                     false
% 15.53/2.48  --inst_subs_new                         false
% 15.53/2.48  --inst_eq_res_simp                      false
% 15.53/2.48  --inst_subs_given                       false
% 15.53/2.48  --inst_orphan_elimination               true
% 15.53/2.48  --inst_learning_loop_flag               true
% 15.53/2.48  --inst_learning_start                   3000
% 15.53/2.48  --inst_learning_factor                  2
% 15.53/2.48  --inst_start_prop_sim_after_learn       3
% 15.53/2.48  --inst_sel_renew                        solver
% 15.53/2.48  --inst_lit_activity_flag                true
% 15.53/2.48  --inst_restr_to_given                   false
% 15.53/2.48  --inst_activity_threshold               500
% 15.53/2.48  --inst_out_proof                        true
% 15.53/2.48  
% 15.53/2.48  ------ Resolution Options
% 15.53/2.48  
% 15.53/2.48  --resolution_flag                       true
% 15.53/2.48  --res_lit_sel                           adaptive
% 15.53/2.48  --res_lit_sel_side                      none
% 15.53/2.48  --res_ordering                          kbo
% 15.53/2.48  --res_to_prop_solver                    active
% 15.53/2.48  --res_prop_simpl_new                    false
% 15.53/2.48  --res_prop_simpl_given                  true
% 15.53/2.48  --res_passive_queue_type                priority_queues
% 15.53/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.53/2.48  --res_passive_queues_freq               [15;5]
% 15.53/2.48  --res_forward_subs                      full
% 15.53/2.48  --res_backward_subs                     full
% 15.53/2.48  --res_forward_subs_resolution           true
% 15.53/2.48  --res_backward_subs_resolution          true
% 15.53/2.48  --res_orphan_elimination                true
% 15.53/2.48  --res_time_limit                        2.
% 15.53/2.48  --res_out_proof                         true
% 15.53/2.48  
% 15.53/2.48  ------ Superposition Options
% 15.53/2.48  
% 15.53/2.48  --superposition_flag                    true
% 15.53/2.48  --sup_passive_queue_type                priority_queues
% 15.53/2.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.53/2.48  --sup_passive_queues_freq               [1;4]
% 15.53/2.48  --demod_completeness_check              fast
% 15.53/2.48  --demod_use_ground                      true
% 15.53/2.48  --sup_to_prop_solver                    passive
% 15.53/2.48  --sup_prop_simpl_new                    true
% 15.53/2.48  --sup_prop_simpl_given                  true
% 15.53/2.48  --sup_fun_splitting                     false
% 15.53/2.48  --sup_smt_interval                      50000
% 15.53/2.48  
% 15.53/2.48  ------ Superposition Simplification Setup
% 15.53/2.48  
% 15.53/2.48  --sup_indices_passive                   []
% 15.53/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.53/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.53/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.53/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.53/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.53/2.48  --sup_full_bw                           [BwDemod]
% 15.53/2.48  --sup_immed_triv                        [TrivRules]
% 15.53/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.53/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.53/2.48  --sup_immed_bw_main                     []
% 15.53/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.53/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.53/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.53/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.53/2.48  
% 15.53/2.48  ------ Combination Options
% 15.53/2.48  
% 15.53/2.48  --comb_res_mult                         3
% 15.53/2.48  --comb_sup_mult                         2
% 15.53/2.48  --comb_inst_mult                        10
% 15.53/2.48  
% 15.53/2.48  ------ Debug Options
% 15.53/2.48  
% 15.53/2.48  --dbg_backtrace                         false
% 15.53/2.48  --dbg_dump_prop_clauses                 false
% 15.53/2.48  --dbg_dump_prop_clauses_file            -
% 15.53/2.48  --dbg_out_stat                          false
% 15.53/2.48  ------ Parsing...
% 15.53/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.53/2.48  
% 15.53/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.53/2.48  
% 15.53/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.53/2.48  
% 15.53/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.53/2.48  ------ Proving...
% 15.53/2.48  ------ Problem Properties 
% 15.53/2.48  
% 15.53/2.48  
% 15.53/2.48  clauses                                 17
% 15.53/2.48  conjectures                             4
% 15.53/2.48  EPR                                     3
% 15.53/2.48  Horn                                    13
% 15.53/2.48  unary                                   6
% 15.53/2.48  binary                                  10
% 15.53/2.48  lits                                    29
% 15.53/2.48  lits eq                                 6
% 15.53/2.48  fd_pure                                 0
% 15.53/2.48  fd_pseudo                               0
% 15.53/2.48  fd_cond                                 0
% 15.53/2.48  fd_pseudo_cond                          0
% 15.53/2.48  AC symbols                              0
% 15.53/2.48  
% 15.53/2.48  ------ Input Options Time Limit: Unbounded
% 15.53/2.48  
% 15.53/2.48  
% 15.53/2.48  ------ 
% 15.53/2.48  Current options:
% 15.53/2.48  ------ 
% 15.53/2.48  
% 15.53/2.48  ------ Input Options
% 15.53/2.48  
% 15.53/2.48  --out_options                           all
% 15.53/2.48  --tptp_safe_out                         true
% 15.53/2.48  --problem_path                          ""
% 15.53/2.48  --include_path                          ""
% 15.53/2.48  --clausifier                            res/vclausify_rel
% 15.53/2.48  --clausifier_options                    --mode clausify
% 15.53/2.48  --stdin                                 false
% 15.53/2.48  --stats_out                             sel
% 15.53/2.48  
% 15.53/2.48  ------ General Options
% 15.53/2.48  
% 15.53/2.48  --fof                                   false
% 15.53/2.48  --time_out_real                         604.99
% 15.53/2.48  --time_out_virtual                      -1.
% 15.53/2.48  --symbol_type_check                     false
% 15.53/2.48  --clausify_out                          false
% 15.53/2.48  --sig_cnt_out                           false
% 15.53/2.48  --trig_cnt_out                          false
% 15.53/2.48  --trig_cnt_out_tolerance                1.
% 15.53/2.48  --trig_cnt_out_sk_spl                   false
% 15.53/2.48  --abstr_cl_out                          false
% 15.53/2.48  
% 15.53/2.48  ------ Global Options
% 15.53/2.48  
% 15.53/2.48  --schedule                              none
% 15.53/2.48  --add_important_lit                     false
% 15.53/2.48  --prop_solver_per_cl                    1000
% 15.53/2.48  --min_unsat_core                        false
% 15.53/2.48  --soft_assumptions                      false
% 15.53/2.48  --soft_lemma_size                       3
% 15.53/2.48  --prop_impl_unit_size                   0
% 15.53/2.48  --prop_impl_unit                        []
% 15.53/2.48  --share_sel_clauses                     true
% 15.53/2.48  --reset_solvers                         false
% 15.53/2.48  --bc_imp_inh                            [conj_cone]
% 15.53/2.48  --conj_cone_tolerance                   3.
% 15.53/2.48  --extra_neg_conj                        none
% 15.53/2.48  --large_theory_mode                     true
% 15.53/2.48  --prolific_symb_bound                   200
% 15.53/2.48  --lt_threshold                          2000
% 15.53/2.48  --clause_weak_htbl                      true
% 15.53/2.48  --gc_record_bc_elim                     false
% 15.53/2.48  
% 15.53/2.48  ------ Preprocessing Options
% 15.53/2.48  
% 15.53/2.48  --preprocessing_flag                    true
% 15.53/2.48  --time_out_prep_mult                    0.1
% 15.53/2.48  --splitting_mode                        input
% 15.53/2.48  --splitting_grd                         true
% 15.53/2.48  --splitting_cvd                         false
% 15.53/2.48  --splitting_cvd_svl                     false
% 15.53/2.48  --splitting_nvd                         32
% 15.53/2.48  --sub_typing                            true
% 15.53/2.48  --prep_gs_sim                           false
% 15.53/2.48  --prep_unflatten                        true
% 15.53/2.48  --prep_res_sim                          true
% 15.53/2.48  --prep_upred                            true
% 15.53/2.48  --prep_sem_filter                       exhaustive
% 15.53/2.48  --prep_sem_filter_out                   false
% 15.53/2.48  --pred_elim                             false
% 15.53/2.48  --res_sim_input                         true
% 15.53/2.48  --eq_ax_congr_red                       true
% 15.53/2.48  --pure_diseq_elim                       true
% 15.53/2.48  --brand_transform                       false
% 15.53/2.48  --non_eq_to_eq                          false
% 15.53/2.48  --prep_def_merge                        true
% 15.53/2.48  --prep_def_merge_prop_impl              false
% 15.53/2.48  --prep_def_merge_mbd                    true
% 15.53/2.48  --prep_def_merge_tr_red                 false
% 15.53/2.48  --prep_def_merge_tr_cl                  false
% 15.53/2.48  --smt_preprocessing                     true
% 15.53/2.48  --smt_ac_axioms                         fast
% 15.53/2.48  --preprocessed_out                      false
% 15.53/2.48  --preprocessed_stats                    false
% 15.53/2.48  
% 15.53/2.48  ------ Abstraction refinement Options
% 15.53/2.48  
% 15.53/2.48  --abstr_ref                             []
% 15.53/2.48  --abstr_ref_prep                        false
% 15.53/2.48  --abstr_ref_until_sat                   false
% 15.53/2.48  --abstr_ref_sig_restrict                funpre
% 15.53/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.53/2.48  --abstr_ref_under                       []
% 15.53/2.48  
% 15.53/2.48  ------ SAT Options
% 15.53/2.48  
% 15.53/2.48  --sat_mode                              false
% 15.53/2.48  --sat_fm_restart_options                ""
% 15.53/2.48  --sat_gr_def                            false
% 15.53/2.48  --sat_epr_types                         true
% 15.53/2.48  --sat_non_cyclic_types                  false
% 15.53/2.48  --sat_finite_models                     false
% 15.53/2.48  --sat_fm_lemmas                         false
% 15.53/2.48  --sat_fm_prep                           false
% 15.53/2.48  --sat_fm_uc_incr                        true
% 15.53/2.48  --sat_out_model                         small
% 15.53/2.48  --sat_out_clauses                       false
% 15.53/2.48  
% 15.53/2.48  ------ QBF Options
% 15.53/2.48  
% 15.53/2.48  --qbf_mode                              false
% 15.53/2.48  --qbf_elim_univ                         false
% 15.53/2.48  --qbf_dom_inst                          none
% 15.53/2.48  --qbf_dom_pre_inst                      false
% 15.53/2.48  --qbf_sk_in                             false
% 15.53/2.48  --qbf_pred_elim                         true
% 15.53/2.48  --qbf_split                             512
% 15.53/2.48  
% 15.53/2.48  ------ BMC1 Options
% 15.53/2.48  
% 15.53/2.48  --bmc1_incremental                      false
% 15.53/2.48  --bmc1_axioms                           reachable_all
% 15.53/2.48  --bmc1_min_bound                        0
% 15.53/2.48  --bmc1_max_bound                        -1
% 15.53/2.48  --bmc1_max_bound_default                -1
% 15.53/2.48  --bmc1_symbol_reachability              true
% 15.53/2.48  --bmc1_property_lemmas                  false
% 15.53/2.48  --bmc1_k_induction                      false
% 15.53/2.48  --bmc1_non_equiv_states                 false
% 15.53/2.48  --bmc1_deadlock                         false
% 15.53/2.48  --bmc1_ucm                              false
% 15.53/2.48  --bmc1_add_unsat_core                   none
% 15.53/2.48  --bmc1_unsat_core_children              false
% 15.53/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.53/2.48  --bmc1_out_stat                         full
% 15.53/2.48  --bmc1_ground_init                      false
% 15.53/2.48  --bmc1_pre_inst_next_state              false
% 15.53/2.48  --bmc1_pre_inst_state                   false
% 15.53/2.48  --bmc1_pre_inst_reach_state             false
% 15.53/2.48  --bmc1_out_unsat_core                   false
% 15.53/2.48  --bmc1_aig_witness_out                  false
% 15.53/2.48  --bmc1_verbose                          false
% 15.53/2.48  --bmc1_dump_clauses_tptp                false
% 15.53/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.53/2.48  --bmc1_dump_file                        -
% 15.53/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.53/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.53/2.48  --bmc1_ucm_extend_mode                  1
% 15.53/2.48  --bmc1_ucm_init_mode                    2
% 15.53/2.48  --bmc1_ucm_cone_mode                    none
% 15.53/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.53/2.48  --bmc1_ucm_relax_model                  4
% 15.53/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.53/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.53/2.48  --bmc1_ucm_layered_model                none
% 15.53/2.48  --bmc1_ucm_max_lemma_size               10
% 15.53/2.48  
% 15.53/2.48  ------ AIG Options
% 15.53/2.48  
% 15.53/2.48  --aig_mode                              false
% 15.53/2.48  
% 15.53/2.48  ------ Instantiation Options
% 15.53/2.48  
% 15.53/2.48  --instantiation_flag                    true
% 15.53/2.48  --inst_sos_flag                         false
% 15.53/2.48  --inst_sos_phase                        true
% 15.53/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.53/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.53/2.48  --inst_lit_sel_side                     num_symb
% 15.53/2.48  --inst_solver_per_active                1400
% 15.53/2.48  --inst_solver_calls_frac                1.
% 15.53/2.48  --inst_passive_queue_type               priority_queues
% 15.53/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.53/2.48  --inst_passive_queues_freq              [25;2]
% 15.53/2.48  --inst_dismatching                      true
% 15.53/2.48  --inst_eager_unprocessed_to_passive     true
% 15.53/2.48  --inst_prop_sim_given                   true
% 15.53/2.48  --inst_prop_sim_new                     false
% 15.53/2.48  --inst_subs_new                         false
% 15.53/2.48  --inst_eq_res_simp                      false
% 15.53/2.48  --inst_subs_given                       false
% 15.53/2.48  --inst_orphan_elimination               true
% 15.53/2.48  --inst_learning_loop_flag               true
% 15.53/2.48  --inst_learning_start                   3000
% 15.53/2.48  --inst_learning_factor                  2
% 15.53/2.48  --inst_start_prop_sim_after_learn       3
% 15.53/2.48  --inst_sel_renew                        solver
% 15.53/2.48  --inst_lit_activity_flag                true
% 15.53/2.48  --inst_restr_to_given                   false
% 15.53/2.48  --inst_activity_threshold               500
% 15.53/2.48  --inst_out_proof                        true
% 15.53/2.48  
% 15.53/2.48  ------ Resolution Options
% 15.53/2.48  
% 15.53/2.48  --resolution_flag                       true
% 15.53/2.48  --res_lit_sel                           adaptive
% 15.53/2.48  --res_lit_sel_side                      none
% 15.53/2.48  --res_ordering                          kbo
% 15.53/2.48  --res_to_prop_solver                    active
% 15.53/2.48  --res_prop_simpl_new                    false
% 15.53/2.48  --res_prop_simpl_given                  true
% 15.53/2.48  --res_passive_queue_type                priority_queues
% 15.53/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.53/2.48  --res_passive_queues_freq               [15;5]
% 15.53/2.48  --res_forward_subs                      full
% 15.53/2.48  --res_backward_subs                     full
% 15.53/2.48  --res_forward_subs_resolution           true
% 15.53/2.48  --res_backward_subs_resolution          true
% 15.53/2.48  --res_orphan_elimination                true
% 15.53/2.48  --res_time_limit                        2.
% 15.53/2.48  --res_out_proof                         true
% 15.53/2.48  
% 15.53/2.48  ------ Superposition Options
% 15.53/2.48  
% 15.53/2.48  --superposition_flag                    true
% 15.53/2.48  --sup_passive_queue_type                priority_queues
% 15.53/2.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.53/2.48  --sup_passive_queues_freq               [1;4]
% 15.53/2.48  --demod_completeness_check              fast
% 15.53/2.48  --demod_use_ground                      true
% 15.53/2.48  --sup_to_prop_solver                    passive
% 15.53/2.48  --sup_prop_simpl_new                    true
% 15.53/2.48  --sup_prop_simpl_given                  true
% 15.53/2.48  --sup_fun_splitting                     false
% 15.53/2.48  --sup_smt_interval                      50000
% 15.53/2.48  
% 15.53/2.48  ------ Superposition Simplification Setup
% 15.53/2.48  
% 15.53/2.48  --sup_indices_passive                   []
% 15.53/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.53/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.53/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.53/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.53/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.53/2.48  --sup_full_bw                           [BwDemod]
% 15.53/2.48  --sup_immed_triv                        [TrivRules]
% 15.53/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.53/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.53/2.48  --sup_immed_bw_main                     []
% 15.53/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.53/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.53/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.53/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.53/2.48  
% 15.53/2.48  ------ Combination Options
% 15.53/2.48  
% 15.53/2.48  --comb_res_mult                         3
% 15.53/2.48  --comb_sup_mult                         2
% 15.53/2.48  --comb_inst_mult                        10
% 15.53/2.48  
% 15.53/2.48  ------ Debug Options
% 15.53/2.48  
% 15.53/2.48  --dbg_backtrace                         false
% 15.53/2.48  --dbg_dump_prop_clauses                 false
% 15.53/2.48  --dbg_dump_prop_clauses_file            -
% 15.53/2.48  --dbg_out_stat                          false
% 15.53/2.48  
% 15.53/2.48  
% 15.53/2.48  
% 15.53/2.48  
% 15.53/2.48  ------ Proving...
% 15.53/2.48  
% 15.53/2.48  
% 15.53/2.48  % SZS status Theorem for theBenchmark.p
% 15.53/2.48  
% 15.53/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.53/2.48  
% 15.53/2.48  fof(f14,conjecture,(
% 15.53/2.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f15,negated_conjecture,(
% 15.53/2.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 15.53/2.48    inference(negated_conjecture,[],[f14])).
% 15.53/2.48  
% 15.53/2.48  fof(f24,plain,(
% 15.53/2.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 15.53/2.48    inference(ennf_transformation,[],[f15])).
% 15.53/2.48  
% 15.53/2.48  fof(f25,plain,(
% 15.53/2.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 15.53/2.48    inference(flattening,[],[f24])).
% 15.53/2.48  
% 15.53/2.48  fof(f31,plain,(
% 15.53/2.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 15.53/2.48    introduced(choice_axiom,[])).
% 15.53/2.48  
% 15.53/2.48  fof(f32,plain,(
% 15.53/2.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 15.53/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f31])).
% 15.53/2.48  
% 15.53/2.48  fof(f52,plain,(
% 15.53/2.48    r1_xboole_0(sK4,sK3)),
% 15.53/2.48    inference(cnf_transformation,[],[f32])).
% 15.53/2.48  
% 15.53/2.48  fof(f2,axiom,(
% 15.53/2.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f26,plain,(
% 15.53/2.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.53/2.48    inference(nnf_transformation,[],[f2])).
% 15.53/2.48  
% 15.53/2.48  fof(f34,plain,(
% 15.53/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f26])).
% 15.53/2.48  
% 15.53/2.48  fof(f1,axiom,(
% 15.53/2.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f33,plain,(
% 15.53/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f1])).
% 15.53/2.48  
% 15.53/2.48  fof(f35,plain,(
% 15.53/2.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.53/2.48    inference(cnf_transformation,[],[f26])).
% 15.53/2.48  
% 15.53/2.48  fof(f4,axiom,(
% 15.53/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f17,plain,(
% 15.53/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 15.53/2.48    inference(rectify,[],[f4])).
% 15.53/2.48  
% 15.53/2.48  fof(f19,plain,(
% 15.53/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.53/2.48    inference(ennf_transformation,[],[f17])).
% 15.53/2.48  
% 15.53/2.48  fof(f29,plain,(
% 15.53/2.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 15.53/2.48    introduced(choice_axiom,[])).
% 15.53/2.48  
% 15.53/2.48  fof(f30,plain,(
% 15.53/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 15.53/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f29])).
% 15.53/2.48  
% 15.53/2.48  fof(f39,plain,(
% 15.53/2.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f30])).
% 15.53/2.48  
% 15.53/2.48  fof(f50,plain,(
% 15.53/2.48    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 15.53/2.48    inference(cnf_transformation,[],[f32])).
% 15.53/2.48  
% 15.53/2.48  fof(f9,axiom,(
% 15.53/2.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f45,plain,(
% 15.53/2.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f9])).
% 15.53/2.48  
% 15.53/2.48  fof(f10,axiom,(
% 15.53/2.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f46,plain,(
% 15.53/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f10])).
% 15.53/2.48  
% 15.53/2.48  fof(f11,axiom,(
% 15.53/2.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f47,plain,(
% 15.53/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f11])).
% 15.53/2.48  
% 15.53/2.48  fof(f12,axiom,(
% 15.53/2.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f48,plain,(
% 15.53/2.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f12])).
% 15.53/2.48  
% 15.53/2.48  fof(f54,plain,(
% 15.53/2.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 15.53/2.48    inference(definition_unfolding,[],[f47,f48])).
% 15.53/2.48  
% 15.53/2.48  fof(f55,plain,(
% 15.53/2.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 15.53/2.48    inference(definition_unfolding,[],[f46,f54])).
% 15.53/2.48  
% 15.53/2.48  fof(f56,plain,(
% 15.53/2.48    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 15.53/2.48    inference(definition_unfolding,[],[f45,f55])).
% 15.53/2.48  
% 15.53/2.48  fof(f58,plain,(
% 15.53/2.48    r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5))),
% 15.53/2.48    inference(definition_unfolding,[],[f50,f56])).
% 15.53/2.48  
% 15.53/2.48  fof(f5,axiom,(
% 15.53/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f20,plain,(
% 15.53/2.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.53/2.48    inference(ennf_transformation,[],[f5])).
% 15.53/2.48  
% 15.53/2.48  fof(f41,plain,(
% 15.53/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f20])).
% 15.53/2.48  
% 15.53/2.48  fof(f6,axiom,(
% 15.53/2.48    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f42,plain,(
% 15.53/2.48    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 15.53/2.48    inference(cnf_transformation,[],[f6])).
% 15.53/2.48  
% 15.53/2.48  fof(f40,plain,(
% 15.53/2.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 15.53/2.48    inference(cnf_transformation,[],[f30])).
% 15.53/2.48  
% 15.53/2.48  fof(f51,plain,(
% 15.53/2.48    r2_hidden(sK5,sK4)),
% 15.53/2.48    inference(cnf_transformation,[],[f32])).
% 15.53/2.48  
% 15.53/2.48  fof(f3,axiom,(
% 15.53/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f16,plain,(
% 15.53/2.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 15.53/2.48    inference(rectify,[],[f3])).
% 15.53/2.48  
% 15.53/2.48  fof(f18,plain,(
% 15.53/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 15.53/2.48    inference(ennf_transformation,[],[f16])).
% 15.53/2.48  
% 15.53/2.48  fof(f27,plain,(
% 15.53/2.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.53/2.48    introduced(choice_axiom,[])).
% 15.53/2.48  
% 15.53/2.48  fof(f28,plain,(
% 15.53/2.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 15.53/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f27])).
% 15.53/2.48  
% 15.53/2.48  fof(f38,plain,(
% 15.53/2.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f28])).
% 15.53/2.48  
% 15.53/2.48  fof(f13,axiom,(
% 15.53/2.48    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f23,plain,(
% 15.53/2.48    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 15.53/2.48    inference(ennf_transformation,[],[f13])).
% 15.53/2.48  
% 15.53/2.48  fof(f49,plain,(
% 15.53/2.48    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f23])).
% 15.53/2.48  
% 15.53/2.48  fof(f57,plain,(
% 15.53/2.48    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 15.53/2.48    inference(definition_unfolding,[],[f49,f56])).
% 15.53/2.48  
% 15.53/2.48  fof(f7,axiom,(
% 15.53/2.48    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f21,plain,(
% 15.53/2.48    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 15.53/2.48    inference(ennf_transformation,[],[f7])).
% 15.53/2.48  
% 15.53/2.48  fof(f43,plain,(
% 15.53/2.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 15.53/2.48    inference(cnf_transformation,[],[f21])).
% 15.53/2.48  
% 15.53/2.48  fof(f8,axiom,(
% 15.53/2.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 15.53/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.53/2.48  
% 15.53/2.48  fof(f22,plain,(
% 15.53/2.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 15.53/2.48    inference(ennf_transformation,[],[f8])).
% 15.53/2.48  
% 15.53/2.48  fof(f44,plain,(
% 15.53/2.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 15.53/2.48    inference(cnf_transformation,[],[f22])).
% 15.53/2.48  
% 15.53/2.48  fof(f53,plain,(
% 15.53/2.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 15.53/2.48    inference(cnf_transformation,[],[f32])).
% 15.53/2.48  
% 15.53/2.48  cnf(c_14,negated_conjecture,
% 15.53/2.48      ( r1_xboole_0(sK4,sK3) ),
% 15.53/2.48      inference(cnf_transformation,[],[f52]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_540,plain,
% 15.53/2.48      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_2,plain,
% 15.53/2.48      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.53/2.48      inference(cnf_transformation,[],[f34]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_551,plain,
% 15.53/2.48      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 15.53/2.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_995,plain,
% 15.53/2.48      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_540,c_551]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_0,plain,
% 15.53/2.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.53/2.48      inference(cnf_transformation,[],[f33]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_1,plain,
% 15.53/2.48      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.53/2.48      inference(cnf_transformation,[],[f35]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_552,plain,
% 15.53/2.48      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 15.53/2.48      | r1_xboole_0(X0,X1) = iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_1174,plain,
% 15.53/2.48      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 15.53/2.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_0,c_552]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_3205,plain,
% 15.53/2.48      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_995,c_1174]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_3250,plain,
% 15.53/2.48      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_3205,c_551]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_7,plain,
% 15.53/2.48      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 15.53/2.48      inference(cnf_transformation,[],[f39]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_546,plain,
% 15.53/2.48      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) = iProver_top
% 15.53/2.48      | r1_xboole_0(X0,X1) = iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_2039,plain,
% 15.53/2.48      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X1,X0)) = iProver_top
% 15.53/2.48      | r1_xboole_0(X0,X1) = iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_0,c_546]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_16,negated_conjecture,
% 15.53/2.48      ( r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
% 15.53/2.48      inference(cnf_transformation,[],[f58]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_538,plain,
% 15.53/2.48      ( r1_tarski(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_8,plain,
% 15.53/2.48      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.53/2.48      inference(cnf_transformation,[],[f41]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_545,plain,
% 15.53/2.48      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_991,plain,
% 15.53/2.48      ( k2_xboole_0(k3_xboole_0(sK2,sK3),k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = k3_enumset1(sK5,sK5,sK5,sK5,sK5) ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_538,c_545]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_9,plain,
% 15.53/2.48      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 15.53/2.48      inference(cnf_transformation,[],[f42]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_6,plain,
% 15.53/2.48      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 15.53/2.48      inference(cnf_transformation,[],[f40]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_547,plain,
% 15.53/2.48      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 15.53/2.48      | r1_xboole_0(X1,X2) != iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_2404,plain,
% 15.53/2.48      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 15.53/2.48      | r1_xboole_0(X2,X1) != iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_0,c_547]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_2547,plain,
% 15.53/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.53/2.48      | r1_xboole_0(k2_xboole_0(X1,X2),X1) != iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_9,c_2404]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_3477,plain,
% 15.53/2.48      ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top
% 15.53/2.48      | r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),k3_xboole_0(sK2,sK3)) != iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_991,c_2547]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_15,negated_conjecture,
% 15.53/2.48      ( r2_hidden(sK5,sK4) ),
% 15.53/2.48      inference(cnf_transformation,[],[f51]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_18,plain,
% 15.53/2.48      ( r2_hidden(sK5,sK4) = iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_19,plain,
% 15.53/2.48      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_3,plain,
% 15.53/2.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 15.53/2.48      inference(cnf_transformation,[],[f38]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_693,plain,
% 15.53/2.48      ( ~ r2_hidden(X0,sK3)
% 15.53/2.48      | ~ r2_hidden(X0,sK4)
% 15.53/2.48      | ~ r1_xboole_0(sK4,sK3) ),
% 15.53/2.48      inference(instantiation,[status(thm)],[c_3]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_694,plain,
% 15.53/2.48      ( r2_hidden(X0,sK3) != iProver_top
% 15.53/2.48      | r2_hidden(X0,sK4) != iProver_top
% 15.53/2.48      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_696,plain,
% 15.53/2.48      ( r2_hidden(sK5,sK3) != iProver_top
% 15.53/2.48      | r2_hidden(sK5,sK4) != iProver_top
% 15.53/2.48      | r1_xboole_0(sK4,sK3) != iProver_top ),
% 15.53/2.48      inference(instantiation,[status(thm)],[c_694]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_12,plain,
% 15.53/2.48      ( r2_hidden(X0,X1) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 15.53/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_822,plain,
% 15.53/2.48      ( r2_hidden(X0,sK3)
% 15.53/2.48      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),sK3) ),
% 15.53/2.48      inference(instantiation,[status(thm)],[c_12]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_823,plain,
% 15.53/2.48      ( r2_hidden(X0,sK3) = iProver_top
% 15.53/2.48      | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),sK3) = iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_825,plain,
% 15.53/2.48      ( r2_hidden(sK5,sK3) = iProver_top
% 15.53/2.48      | r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK3) = iProver_top ),
% 15.53/2.48      inference(instantiation,[status(thm)],[c_823]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_10,plain,
% 15.53/2.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 15.53/2.48      inference(cnf_transformation,[],[f43]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_544,plain,
% 15.53/2.48      ( r1_xboole_0(X0,X1) != iProver_top
% 15.53/2.48      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_1858,plain,
% 15.53/2.48      ( r1_xboole_0(X0,X1) != iProver_top
% 15.53/2.48      | r1_xboole_0(X0,k3_xboole_0(X2,X1)) = iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_0,c_544]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_2747,plain,
% 15.53/2.48      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 15.53/2.48      | r1_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),X3),X2) != iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_1858,c_2547]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_16545,plain,
% 15.53/2.48      ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top
% 15.53/2.48      | r1_xboole_0(k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK3) != iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_991,c_2747]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_29006,plain,
% 15.53/2.48      ( r2_hidden(X0,k3_xboole_0(sK2,sK3)) != iProver_top ),
% 15.53/2.48      inference(global_propositional_subsumption,
% 15.53/2.48                [status(thm)],
% 15.53/2.48                [c_3477,c_18,c_19,c_696,c_825,c_16545]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_29018,plain,
% 15.53/2.48      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_2039,c_29006]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_11,plain,
% 15.53/2.48      ( ~ r1_xboole_0(X0,X1)
% 15.53/2.48      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
% 15.53/2.48      inference(cnf_transformation,[],[f44]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_543,plain,
% 15.53/2.48      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
% 15.53/2.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_29448,plain,
% 15.53/2.48      ( k3_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k3_xboole_0(sK3,X0) ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_29018,c_543]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_30959,plain,
% 15.53/2.48      ( k3_xboole_0(sK3,X0) != k1_xboole_0
% 15.53/2.48      | r1_xboole_0(k2_xboole_0(sK2,X0),sK3) = iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_29448,c_1174]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_62846,plain,
% 15.53/2.48      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top ),
% 15.53/2.48      inference(superposition,[status(thm)],[c_3250,c_30959]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_13,negated_conjecture,
% 15.53/2.48      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 15.53/2.48      inference(cnf_transformation,[],[f53]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(c_20,plain,
% 15.53/2.48      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
% 15.53/2.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.53/2.48  
% 15.53/2.48  cnf(contradiction,plain,
% 15.53/2.48      ( $false ),
% 15.53/2.48      inference(minisat,[status(thm)],[c_62846,c_20]) ).
% 15.53/2.48  
% 15.53/2.48  
% 15.53/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.53/2.48  
% 15.53/2.48  ------                               Statistics
% 15.53/2.48  
% 15.53/2.48  ------ Selected
% 15.53/2.48  
% 15.53/2.48  total_time:                             1.77
% 15.53/2.48  
%------------------------------------------------------------------------------
