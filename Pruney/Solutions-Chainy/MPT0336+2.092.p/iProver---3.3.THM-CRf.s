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
% DateTime   : Thu Dec  3 11:38:48 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 390 expanded)
%              Number of clauses        :   58 ( 121 expanded)
%              Number of leaves         :   16 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  242 ( 942 expanded)
%              Number of equality atoms :   82 ( 246 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f40])).

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

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,
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

fof(f31,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f30])).

fof(f51,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f61,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f51,f40,f55])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f40,f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f53,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f52,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f31])).

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
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_666,plain,
    ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_653,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_659,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_660,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1370,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_659,c_660])).

cnf(c_5685,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k1_enumset1(sK5,sK5,sK5))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_653,c_1370])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_667,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3348,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_667])).

cnf(c_6875,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r1_xboole_0(k1_enumset1(sK5,sK5,sK5),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5685,c_3348])).

cnf(c_17,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_655,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_671,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1574,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_671])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k1_enumset1(X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_658,plain,
    ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_654,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_670,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4055,plain,
    ( r2_hidden(sK5,X0) != iProver_top
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_670])).

cnf(c_4684,plain,
    ( k4_xboole_0(X0,k1_enumset1(sK5,sK5,sK5)) = X0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_658,c_4055])).

cnf(c_4868,plain,
    ( k4_xboole_0(sK3,k1_enumset1(sK5,sK5,sK5)) = sK3 ),
    inference(superposition,[status(thm)],[c_1574,c_4684])).

cnf(c_6843,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_4868,c_5685])).

cnf(c_11,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_661,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7069,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6843,c_661])).

cnf(c_7078,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ),
    inference(superposition,[status(thm)],[c_6843,c_0])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_665,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1132,plain,
    ( k4_xboole_0(sK4,sK3) = sK4 ),
    inference(superposition,[status(thm)],[c_655,c_660])).

cnf(c_1777,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_xboole_0(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_659])).

cnf(c_2340,plain,
    ( r1_xboole_0(k4_xboole_0(sK3,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_1777])).

cnf(c_4869,plain,
    ( k4_xboole_0(k4_xboole_0(sK3,X0),k1_enumset1(sK5,sK5,sK5)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2340,c_4684])).

cnf(c_6844,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_4869,c_5685])).

cnf(c_7601,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_0,c_6844])).

cnf(c_9159,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_7078,c_7601])).

cnf(c_9188,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9159,c_3348])).

cnf(c_10053,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6875,c_7069,c_9188])).

cnf(c_10062,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_666,c_10053])).

cnf(c_1265,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1266,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | r1_xboole_0(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_924,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | ~ r1_xboole_0(sK3,sK4)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_925,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
    | r1_xboole_0(sK3,sK4) != iProver_top
    | r1_xboole_0(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_834,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(resolution,[status(thm)],[c_1,c_17])).

cnf(c_835,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_797,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_798,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
    | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_16,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10062,c_1266,c_925,c_835,c_798,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.81/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/1.00  
% 3.81/1.00  ------  iProver source info
% 3.81/1.00  
% 3.81/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.81/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/1.00  git: non_committed_changes: false
% 3.81/1.00  git: last_make_outside_of_git: false
% 3.81/1.00  
% 3.81/1.00  ------ 
% 3.81/1.00  ------ Parsing...
% 3.81/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  ------ Proving...
% 3.81/1.00  ------ Problem Properties 
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  clauses                                 20
% 3.81/1.00  conjectures                             4
% 3.81/1.00  EPR                                     4
% 3.81/1.00  Horn                                    16
% 3.81/1.00  unary                                   6
% 3.81/1.00  binary                                  12
% 3.81/1.00  lits                                    36
% 3.81/1.00  lits eq                                 5
% 3.81/1.00  fd_pure                                 0
% 3.81/1.00  fd_pseudo                               0
% 3.81/1.00  fd_cond                                 0
% 3.81/1.00  fd_pseudo_cond                          0
% 3.81/1.00  AC symbols                              0
% 3.81/1.00  
% 3.81/1.00  ------ Input Options Time Limit: Unbounded
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ 
% 3.81/1.00  Current options:
% 3.81/1.00  ------ 
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  % SZS status Theorem for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  fof(f4,axiom,(
% 3.81/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f16,plain,(
% 3.81/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.81/1.00    inference(rectify,[],[f4])).
% 3.81/1.00  
% 3.81/1.00  fof(f19,plain,(
% 3.81/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.81/1.00    inference(ennf_transformation,[],[f16])).
% 3.81/1.00  
% 3.81/1.00  fof(f26,plain,(
% 3.81/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.81/1.00    introduced(choice_axiom,[])).
% 3.81/1.00  
% 3.81/1.00  fof(f27,plain,(
% 3.81/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.81/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f26])).
% 3.81/1.00  
% 3.81/1.00  fof(f37,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f27])).
% 3.81/1.00  
% 3.81/1.00  fof(f6,axiom,(
% 3.81/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f40,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.81/1.00    inference(cnf_transformation,[],[f6])).
% 3.81/1.00  
% 3.81/1.00  fof(f58,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 3.81/1.00    inference(definition_unfolding,[],[f37,f40])).
% 3.81/1.00  
% 3.81/1.00  fof(f13,conjecture,(
% 3.81/1.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f14,negated_conjecture,(
% 3.81/1.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.81/1.00    inference(negated_conjecture,[],[f13])).
% 3.81/1.00  
% 3.81/1.00  fof(f22,plain,(
% 3.81/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.81/1.00    inference(ennf_transformation,[],[f14])).
% 3.81/1.00  
% 3.81/1.00  fof(f23,plain,(
% 3.81/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.81/1.00    inference(flattening,[],[f22])).
% 3.81/1.00  
% 3.81/1.00  fof(f30,plain,(
% 3.81/1.00    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 3.81/1.00    introduced(choice_axiom,[])).
% 3.81/1.00  
% 3.81/1.00  fof(f31,plain,(
% 3.81/1.00    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 3.81/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f30])).
% 3.81/1.00  
% 3.81/1.00  fof(f51,plain,(
% 3.81/1.00    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 3.81/1.00    inference(cnf_transformation,[],[f31])).
% 3.81/1.00  
% 3.81/1.00  fof(f10,axiom,(
% 3.81/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f47,plain,(
% 3.81/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f10])).
% 3.81/1.00  
% 3.81/1.00  fof(f11,axiom,(
% 3.81/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f48,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f11])).
% 3.81/1.00  
% 3.81/1.00  fof(f55,plain,(
% 3.81/1.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.81/1.00    inference(definition_unfolding,[],[f47,f48])).
% 3.81/1.00  
% 3.81/1.00  fof(f61,plain,(
% 3.81/1.00    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5))),
% 3.81/1.00    inference(definition_unfolding,[],[f51,f40,f55])).
% 3.81/1.00  
% 3.81/1.00  fof(f9,axiom,(
% 3.81/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f21,plain,(
% 3.81/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.81/1.00    inference(ennf_transformation,[],[f9])).
% 3.81/1.00  
% 3.81/1.00  fof(f46,plain,(
% 3.81/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f21])).
% 3.81/1.00  
% 3.81/1.00  fof(f8,axiom,(
% 3.81/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f28,plain,(
% 3.81/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.81/1.00    inference(nnf_transformation,[],[f8])).
% 3.81/1.00  
% 3.81/1.00  fof(f44,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f28])).
% 3.81/1.00  
% 3.81/1.00  fof(f1,axiom,(
% 3.81/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f32,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f1])).
% 3.81/1.00  
% 3.81/1.00  fof(f56,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.81/1.00    inference(definition_unfolding,[],[f32,f40,f40])).
% 3.81/1.00  
% 3.81/1.00  fof(f38,plain,(
% 3.81/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.81/1.00    inference(cnf_transformation,[],[f27])).
% 3.81/1.00  
% 3.81/1.00  fof(f57,plain,(
% 3.81/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.81/1.00    inference(definition_unfolding,[],[f38,f40])).
% 3.81/1.00  
% 3.81/1.00  fof(f53,plain,(
% 3.81/1.00    r1_xboole_0(sK4,sK3)),
% 3.81/1.00    inference(cnf_transformation,[],[f31])).
% 3.81/1.00  
% 3.81/1.00  fof(f2,axiom,(
% 3.81/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f17,plain,(
% 3.81/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.81/1.00    inference(ennf_transformation,[],[f2])).
% 3.81/1.00  
% 3.81/1.00  fof(f33,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f17])).
% 3.81/1.00  
% 3.81/1.00  fof(f12,axiom,(
% 3.81/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f29,plain,(
% 3.81/1.00    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.81/1.00    inference(nnf_transformation,[],[f12])).
% 3.81/1.00  
% 3.81/1.00  fof(f50,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f29])).
% 3.81/1.00  
% 3.81/1.00  fof(f59,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.81/1.00    inference(definition_unfolding,[],[f50,f55])).
% 3.81/1.00  
% 3.81/1.00  fof(f52,plain,(
% 3.81/1.00    r2_hidden(sK5,sK4)),
% 3.81/1.00    inference(cnf_transformation,[],[f31])).
% 3.81/1.00  
% 3.81/1.00  fof(f3,axiom,(
% 3.81/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f15,plain,(
% 3.81/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.81/1.00    inference(rectify,[],[f3])).
% 3.81/1.00  
% 3.81/1.00  fof(f18,plain,(
% 3.81/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.81/1.00    inference(ennf_transformation,[],[f15])).
% 3.81/1.00  
% 3.81/1.00  fof(f24,plain,(
% 3.81/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.81/1.00    introduced(choice_axiom,[])).
% 3.81/1.00  
% 3.81/1.00  fof(f25,plain,(
% 3.81/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.81/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f24])).
% 3.81/1.00  
% 3.81/1.00  fof(f36,plain,(
% 3.81/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f25])).
% 3.81/1.00  
% 3.81/1.00  fof(f45,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.81/1.00    inference(cnf_transformation,[],[f28])).
% 3.81/1.00  
% 3.81/1.00  fof(f5,axiom,(
% 3.81/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f39,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f5])).
% 3.81/1.00  
% 3.81/1.00  fof(f7,axiom,(
% 3.81/1.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.81/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f20,plain,(
% 3.81/1.00    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.81/1.00    inference(ennf_transformation,[],[f7])).
% 3.81/1.00  
% 3.81/1.00  fof(f41,plain,(
% 3.81/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.81/1.00    inference(cnf_transformation,[],[f20])).
% 3.81/1.00  
% 3.81/1.00  fof(f54,plain,(
% 3.81/1.00    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 3.81/1.00    inference(cnf_transformation,[],[f31])).
% 3.81/1.00  
% 3.81/1.00  cnf(c_6,plain,
% 3.81/1.00      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 3.81/1.00      | r1_xboole_0(X0,X1) ),
% 3.81/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_666,plain,
% 3.81/1.00      ( r2_hidden(sK1(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = iProver_top
% 3.81/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_19,negated_conjecture,
% 3.81/1.00      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) ),
% 3.81/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_653,plain,
% 3.81/1.00      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k1_enumset1(sK5,sK5,sK5)) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_13,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 3.81/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_659,plain,
% 3.81/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.81/1.00      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_12,plain,
% 3.81/1.00      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.81/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_660,plain,
% 3.81/1.00      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1370,plain,
% 3.81/1.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0
% 3.81/1.00      | r1_tarski(X0,X2) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_659,c_660]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_5685,plain,
% 3.81/1.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k1_enumset1(sK5,sK5,sK5))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_653,c_1370]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_0,plain,
% 3.81/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.81/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_5,plain,
% 3.81/1.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.81/1.00      | ~ r1_xboole_0(X1,X2) ),
% 3.81/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_667,plain,
% 3.81/1.00      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.81/1.00      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_3348,plain,
% 3.81/1.00      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.81/1.00      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_0,c_667]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_6875,plain,
% 3.81/1.00      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 3.81/1.00      | r1_xboole_0(k1_enumset1(sK5,sK5,sK5),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_5685,c_3348]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_17,negated_conjecture,
% 3.81/1.00      ( r1_xboole_0(sK4,sK3) ),
% 3.81/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_655,plain,
% 3.81/1.00      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1,plain,
% 3.81/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.81/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_671,plain,
% 3.81/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 3.81/1.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1574,plain,
% 3.81/1.00      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_655,c_671]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_14,plain,
% 3.81/1.00      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k1_enumset1(X0,X0,X0)) = X1 ),
% 3.81/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_658,plain,
% 3.81/1.00      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) = X0
% 3.81/1.00      | r2_hidden(X1,X0) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_18,negated_conjecture,
% 3.81/1.00      ( r2_hidden(sK5,sK4) ),
% 3.81/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_654,plain,
% 3.81/1.00      ( r2_hidden(sK5,sK4) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2,plain,
% 3.81/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 3.81/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_670,plain,
% 3.81/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.81/1.00      | r2_hidden(X0,X2) != iProver_top
% 3.81/1.00      | r1_xboole_0(X2,X1) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_4055,plain,
% 3.81/1.00      ( r2_hidden(sK5,X0) != iProver_top
% 3.81/1.00      | r1_xboole_0(X0,sK4) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_654,c_670]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_4684,plain,
% 3.81/1.00      ( k4_xboole_0(X0,k1_enumset1(sK5,sK5,sK5)) = X0
% 3.81/1.00      | r1_xboole_0(X0,sK4) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_658,c_4055]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_4868,plain,
% 3.81/1.00      ( k4_xboole_0(sK3,k1_enumset1(sK5,sK5,sK5)) = sK3 ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_1574,c_4684]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_6843,plain,
% 3.81/1.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_4868,c_5685]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_11,plain,
% 3.81/1.00      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.81/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_661,plain,
% 3.81/1.00      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_7069,plain,
% 3.81/1.00      ( r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) = iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_6843,c_661]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_7078,plain,
% 3.81/1.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) = k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_6843,c_0]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_7,plain,
% 3.81/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.81/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_665,plain,
% 3.81/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1132,plain,
% 3.81/1.00      ( k4_xboole_0(sK4,sK3) = sK4 ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_655,c_660]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1777,plain,
% 3.81/1.00      ( r1_tarski(X0,sK3) != iProver_top
% 3.81/1.00      | r1_xboole_0(X0,sK4) = iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_1132,c_659]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2340,plain,
% 3.81/1.00      ( r1_xboole_0(k4_xboole_0(sK3,X0),sK4) = iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_665,c_1777]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_4869,plain,
% 3.81/1.00      ( k4_xboole_0(k4_xboole_0(sK3,X0),k1_enumset1(sK5,sK5,sK5)) = k4_xboole_0(sK3,X0) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_2340,c_4684]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_6844,plain,
% 3.81/1.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_4869,c_5685]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_7601,plain,
% 3.81/1.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),k4_xboole_0(X0,k4_xboole_0(X0,sK3))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_0,c_6844]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_9159,plain,
% 3.81/1.00      ( k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) ),
% 3.81/1.00      inference(demodulation,[status(thm)],[c_7078,c_7601]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_9188,plain,
% 3.81/1.00      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top
% 3.81/1.00      | r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)),sK3) != iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_9159,c_3348]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_10053,plain,
% 3.81/1.00      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 3.81/1.00      inference(global_propositional_subsumption,
% 3.81/1.00                [status(thm)],
% 3.81/1.00                [c_6875,c_7069,c_9188]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_10062,plain,
% 3.81/1.00      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_666,c_10053]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1265,plain,
% 3.81/1.00      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 3.81/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1266,plain,
% 3.81/1.00      ( r1_xboole_0(sK3,sK2) = iProver_top
% 3.81/1.00      | r1_xboole_0(sK2,sK3) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_10,plain,
% 3.81/1.00      ( ~ r1_xboole_0(X0,X1)
% 3.81/1.00      | ~ r1_xboole_0(X0,X2)
% 3.81/1.00      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.81/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_924,plain,
% 3.81/1.00      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 3.81/1.00      | ~ r1_xboole_0(sK3,sK4)
% 3.81/1.00      | ~ r1_xboole_0(sK3,sK2) ),
% 3.81/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_925,plain,
% 3.81/1.00      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = iProver_top
% 3.81/1.00      | r1_xboole_0(sK3,sK4) != iProver_top
% 3.81/1.00      | r1_xboole_0(sK3,sK2) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_834,plain,
% 3.81/1.00      ( r1_xboole_0(sK3,sK4) ),
% 3.81/1.00      inference(resolution,[status(thm)],[c_1,c_17]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_835,plain,
% 3.81/1.00      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_797,plain,
% 3.81/1.00      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 3.81/1.00      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 3.81/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_798,plain,
% 3.81/1.00      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) = iProver_top
% 3.81/1.00      | r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_16,negated_conjecture,
% 3.81/1.00      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 3.81/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_23,plain,
% 3.81/1.00      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(contradiction,plain,
% 3.81/1.00      ( $false ),
% 3.81/1.00      inference(minisat,
% 3.81/1.00                [status(thm)],
% 3.81/1.00                [c_10062,c_1266,c_925,c_835,c_798,c_23]) ).
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  ------                               Statistics
% 3.81/1.00  
% 3.81/1.00  ------ Selected
% 3.81/1.00  
% 3.81/1.00  total_time:                             0.306
% 3.81/1.00  
%------------------------------------------------------------------------------
