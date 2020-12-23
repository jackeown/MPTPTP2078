%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:04 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  144 (3076 expanded)
%              Number of clauses        :   84 ( 757 expanded)
%              Number of leaves         :   21 ( 802 expanded)
%              Depth                    :   30
%              Number of atoms          :  208 (4497 expanded)
%              Number of equality atoms :  151 (2723 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f18])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).

fof(f53,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f43,f43])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f38,f43,f43,f43])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f42,f55,f55])).

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

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(definition_unfolding,[],[f54,f55,f58,f58])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_157,plain,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_158,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_477,plain,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_480,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_754,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_477,c_480])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1172,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_754,c_1])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1303,plain,
    ( k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1172,c_0])).

cnf(c_7,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1301,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k4_xboole_0(k5_xboole_0(sK1,X0),k4_xboole_0(k5_xboole_0(sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[status(thm)],[c_1172,c_7])).

cnf(c_681,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_14491,plain,
    ( k4_xboole_0(k5_xboole_0(sK1,X0),k4_xboole_0(k5_xboole_0(sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) ),
    inference(demodulation,[status(thm)],[c_1301,c_681])).

cnf(c_14521,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1303,c_14491])).

cnf(c_1167,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_754,c_0])).

cnf(c_1186,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_1167,c_754])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_482,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2615,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_477,c_482])).

cnf(c_1171,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_754,c_0])).

cnf(c_3038,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2615,c_1171])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3422,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_3038,c_13])).

cnf(c_5567,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1186,c_3422])).

cnf(c_1871,plain,
    ( k5_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_754,c_681])).

cnf(c_3034,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(demodulation,[status(thm)],[c_2615,c_1871])).

cnf(c_5594,plain,
    ( k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5567,c_3034,c_3038])).

cnf(c_679,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_5736,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5594,c_679])).

cnf(c_3039,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_2615,c_754])).

cnf(c_5755,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5736,c_3039])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_479,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_752,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_479,c_480])).

cnf(c_4784,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_752,c_681])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4811,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4784,c_12])).

cnf(c_5756,plain,
    ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5755,c_3038,c_3039,c_4811])).

cnf(c_14679,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14521,c_5756])).

cnf(c_1174,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_754,c_7])).

cnf(c_1544,plain,
    ( k5_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_1171,c_1174])).

cnf(c_1612,plain,
    ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(light_normalisation,[status(thm)],[c_1544,c_754,c_1171])).

cnf(c_2181,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1612,c_1])).

cnf(c_3035,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2615,c_1612])).

cnf(c_3232,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3035,c_681])).

cnf(c_3294,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_3232,c_12])).

cnf(c_6973,plain,
    ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2181,c_2615,c_3294])).

cnf(c_1554,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[status(thm)],[c_1174,c_1])).

cnf(c_8337,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_6973,c_1554])).

cnf(c_1874,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_681,c_13])).

cnf(c_8341,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k4_xboole_0(sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_1554,c_1874])).

cnf(c_8347,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(demodulation,[status(thm)],[c_8341,c_0])).

cnf(c_8358,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k4_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(demodulation,[status(thm)],[c_8337,c_8347])).

cnf(c_8360,plain,
    ( k4_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_8358,c_1172,c_1303])).

cnf(c_8810,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[status(thm)],[c_8360,c_681])).

cnf(c_8820,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(light_normalisation,[status(thm)],[c_8810,c_1172])).

cnf(c_10053,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[status(thm)],[c_8820,c_13])).

cnf(c_10059,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10053,c_3038])).

cnf(c_10060,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10059,c_12])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_10368,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_10060,c_11])).

cnf(c_10391,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10368,c_1172,c_3294,c_6973,c_8360])).

cnf(c_770,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_13])).

cnf(c_10392,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_10391,c_12,c_770])).

cnf(c_10393,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_10392,c_1303])).

cnf(c_254,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_1041,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k1_xboole_0)
    | k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != sK1
    | k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_254])).

cnf(c_252,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_550,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != X0
    | k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_945,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != k5_xboole_0(sK1,k1_xboole_0)
    | k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = sK1
    | sK1 != k5_xboole_0(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_732,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_569,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_606,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_731,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) != sK1
    | sK1 = k5_xboole_0(sK1,k1_xboole_0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_576,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_563,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_575,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_563])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14679,c_10393,c_1041,c_945,c_732,c_731,c_576,c_575,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:36:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 3.54/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.99  
% 3.54/0.99  ------  iProver source info
% 3.54/0.99  
% 3.54/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.99  git: non_committed_changes: false
% 3.54/0.99  git: last_make_outside_of_git: false
% 3.54/0.99  
% 3.54/0.99  ------ 
% 3.54/0.99  
% 3.54/0.99  ------ Input Options
% 3.54/0.99  
% 3.54/0.99  --out_options                           all
% 3.54/0.99  --tptp_safe_out                         true
% 3.54/0.99  --problem_path                          ""
% 3.54/0.99  --include_path                          ""
% 3.54/0.99  --clausifier                            res/vclausify_rel
% 3.54/0.99  --clausifier_options                    --mode clausify
% 3.54/0.99  --stdin                                 false
% 3.54/0.99  --stats_out                             all
% 3.54/0.99  
% 3.54/0.99  ------ General Options
% 3.54/0.99  
% 3.54/0.99  --fof                                   false
% 3.54/0.99  --time_out_real                         305.
% 3.54/0.99  --time_out_virtual                      -1.
% 3.54/0.99  --symbol_type_check                     false
% 3.54/0.99  --clausify_out                          false
% 3.54/0.99  --sig_cnt_out                           false
% 3.54/0.99  --trig_cnt_out                          false
% 3.54/0.99  --trig_cnt_out_tolerance                1.
% 3.54/0.99  --trig_cnt_out_sk_spl                   false
% 3.54/0.99  --abstr_cl_out                          false
% 3.54/0.99  
% 3.54/0.99  ------ Global Options
% 3.54/0.99  
% 3.54/0.99  --schedule                              default
% 3.54/0.99  --add_important_lit                     false
% 3.54/0.99  --prop_solver_per_cl                    1000
% 3.54/0.99  --min_unsat_core                        false
% 3.54/0.99  --soft_assumptions                      false
% 3.54/0.99  --soft_lemma_size                       3
% 3.54/0.99  --prop_impl_unit_size                   0
% 3.54/0.99  --prop_impl_unit                        []
% 3.54/0.99  --share_sel_clauses                     true
% 3.54/0.99  --reset_solvers                         false
% 3.54/0.99  --bc_imp_inh                            [conj_cone]
% 3.54/0.99  --conj_cone_tolerance                   3.
% 3.54/0.99  --extra_neg_conj                        none
% 3.54/0.99  --large_theory_mode                     true
% 3.54/0.99  --prolific_symb_bound                   200
% 3.54/0.99  --lt_threshold                          2000
% 3.54/0.99  --clause_weak_htbl                      true
% 3.54/0.99  --gc_record_bc_elim                     false
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing Options
% 3.54/0.99  
% 3.54/0.99  --preprocessing_flag                    true
% 3.54/0.99  --time_out_prep_mult                    0.1
% 3.54/0.99  --splitting_mode                        input
% 3.54/0.99  --splitting_grd                         true
% 3.54/0.99  --splitting_cvd                         false
% 3.54/0.99  --splitting_cvd_svl                     false
% 3.54/0.99  --splitting_nvd                         32
% 3.54/0.99  --sub_typing                            true
% 3.54/0.99  --prep_gs_sim                           true
% 3.54/0.99  --prep_unflatten                        true
% 3.54/0.99  --prep_res_sim                          true
% 3.54/0.99  --prep_upred                            true
% 3.54/0.99  --prep_sem_filter                       exhaustive
% 3.54/0.99  --prep_sem_filter_out                   false
% 3.54/0.99  --pred_elim                             true
% 3.54/0.99  --res_sim_input                         true
% 3.54/0.99  --eq_ax_congr_red                       true
% 3.54/0.99  --pure_diseq_elim                       true
% 3.54/0.99  --brand_transform                       false
% 3.54/0.99  --non_eq_to_eq                          false
% 3.54/0.99  --prep_def_merge                        true
% 3.54/0.99  --prep_def_merge_prop_impl              false
% 3.54/0.99  --prep_def_merge_mbd                    true
% 3.54/0.99  --prep_def_merge_tr_red                 false
% 3.54/0.99  --prep_def_merge_tr_cl                  false
% 3.54/0.99  --smt_preprocessing                     true
% 3.54/0.99  --smt_ac_axioms                         fast
% 3.54/0.99  --preprocessed_out                      false
% 3.54/0.99  --preprocessed_stats                    false
% 3.54/0.99  
% 3.54/0.99  ------ Abstraction refinement Options
% 3.54/0.99  
% 3.54/0.99  --abstr_ref                             []
% 3.54/0.99  --abstr_ref_prep                        false
% 3.54/0.99  --abstr_ref_until_sat                   false
% 3.54/0.99  --abstr_ref_sig_restrict                funpre
% 3.54/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.99  --abstr_ref_under                       []
% 3.54/0.99  
% 3.54/0.99  ------ SAT Options
% 3.54/0.99  
% 3.54/0.99  --sat_mode                              false
% 3.54/0.99  --sat_fm_restart_options                ""
% 3.54/0.99  --sat_gr_def                            false
% 3.54/0.99  --sat_epr_types                         true
% 3.54/0.99  --sat_non_cyclic_types                  false
% 3.54/0.99  --sat_finite_models                     false
% 3.54/0.99  --sat_fm_lemmas                         false
% 3.54/0.99  --sat_fm_prep                           false
% 3.54/0.99  --sat_fm_uc_incr                        true
% 3.54/0.99  --sat_out_model                         small
% 3.54/0.99  --sat_out_clauses                       false
% 3.54/0.99  
% 3.54/0.99  ------ QBF Options
% 3.54/0.99  
% 3.54/0.99  --qbf_mode                              false
% 3.54/0.99  --qbf_elim_univ                         false
% 3.54/0.99  --qbf_dom_inst                          none
% 3.54/0.99  --qbf_dom_pre_inst                      false
% 3.54/0.99  --qbf_sk_in                             false
% 3.54/0.99  --qbf_pred_elim                         true
% 3.54/0.99  --qbf_split                             512
% 3.54/0.99  
% 3.54/0.99  ------ BMC1 Options
% 3.54/0.99  
% 3.54/0.99  --bmc1_incremental                      false
% 3.54/0.99  --bmc1_axioms                           reachable_all
% 3.54/0.99  --bmc1_min_bound                        0
% 3.54/0.99  --bmc1_max_bound                        -1
% 3.54/0.99  --bmc1_max_bound_default                -1
% 3.54/0.99  --bmc1_symbol_reachability              true
% 3.54/0.99  --bmc1_property_lemmas                  false
% 3.54/0.99  --bmc1_k_induction                      false
% 3.54/0.99  --bmc1_non_equiv_states                 false
% 3.54/0.99  --bmc1_deadlock                         false
% 3.54/0.99  --bmc1_ucm                              false
% 3.54/0.99  --bmc1_add_unsat_core                   none
% 3.54/0.99  --bmc1_unsat_core_children              false
% 3.54/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.99  --bmc1_out_stat                         full
% 3.54/0.99  --bmc1_ground_init                      false
% 3.54/0.99  --bmc1_pre_inst_next_state              false
% 3.54/0.99  --bmc1_pre_inst_state                   false
% 3.54/0.99  --bmc1_pre_inst_reach_state             false
% 3.54/0.99  --bmc1_out_unsat_core                   false
% 3.54/0.99  --bmc1_aig_witness_out                  false
% 3.54/0.99  --bmc1_verbose                          false
% 3.54/0.99  --bmc1_dump_clauses_tptp                false
% 3.54/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.99  --bmc1_dump_file                        -
% 3.54/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.99  --bmc1_ucm_extend_mode                  1
% 3.54/0.99  --bmc1_ucm_init_mode                    2
% 3.54/0.99  --bmc1_ucm_cone_mode                    none
% 3.54/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.99  --bmc1_ucm_relax_model                  4
% 3.54/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.99  --bmc1_ucm_layered_model                none
% 3.54/0.99  --bmc1_ucm_max_lemma_size               10
% 3.54/0.99  
% 3.54/0.99  ------ AIG Options
% 3.54/0.99  
% 3.54/0.99  --aig_mode                              false
% 3.54/0.99  
% 3.54/0.99  ------ Instantiation Options
% 3.54/0.99  
% 3.54/0.99  --instantiation_flag                    true
% 3.54/0.99  --inst_sos_flag                         false
% 3.54/0.99  --inst_sos_phase                        true
% 3.54/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.99  --inst_lit_sel_side                     num_symb
% 3.54/0.99  --inst_solver_per_active                1400
% 3.54/0.99  --inst_solver_calls_frac                1.
% 3.54/0.99  --inst_passive_queue_type               priority_queues
% 3.54/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.99  --inst_passive_queues_freq              [25;2]
% 3.54/0.99  --inst_dismatching                      true
% 3.54/0.99  --inst_eager_unprocessed_to_passive     true
% 3.54/0.99  --inst_prop_sim_given                   true
% 3.54/0.99  --inst_prop_sim_new                     false
% 3.54/0.99  --inst_subs_new                         false
% 3.54/0.99  --inst_eq_res_simp                      false
% 3.54/0.99  --inst_subs_given                       false
% 3.54/0.99  --inst_orphan_elimination               true
% 3.54/0.99  --inst_learning_loop_flag               true
% 3.54/0.99  --inst_learning_start                   3000
% 3.54/0.99  --inst_learning_factor                  2
% 3.54/0.99  --inst_start_prop_sim_after_learn       3
% 3.54/0.99  --inst_sel_renew                        solver
% 3.54/0.99  --inst_lit_activity_flag                true
% 3.54/0.99  --inst_restr_to_given                   false
% 3.54/0.99  --inst_activity_threshold               500
% 3.54/0.99  --inst_out_proof                        true
% 3.54/0.99  
% 3.54/0.99  ------ Resolution Options
% 3.54/0.99  
% 3.54/0.99  --resolution_flag                       true
% 3.54/0.99  --res_lit_sel                           adaptive
% 3.54/0.99  --res_lit_sel_side                      none
% 3.54/0.99  --res_ordering                          kbo
% 3.54/0.99  --res_to_prop_solver                    active
% 3.54/0.99  --res_prop_simpl_new                    false
% 3.54/0.99  --res_prop_simpl_given                  true
% 3.54/0.99  --res_passive_queue_type                priority_queues
% 3.54/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.99  --res_passive_queues_freq               [15;5]
% 3.54/0.99  --res_forward_subs                      full
% 3.54/0.99  --res_backward_subs                     full
% 3.54/0.99  --res_forward_subs_resolution           true
% 3.54/0.99  --res_backward_subs_resolution          true
% 3.54/0.99  --res_orphan_elimination                true
% 3.54/0.99  --res_time_limit                        2.
% 3.54/0.99  --res_out_proof                         true
% 3.54/0.99  
% 3.54/0.99  ------ Superposition Options
% 3.54/0.99  
% 3.54/0.99  --superposition_flag                    true
% 3.54/0.99  --sup_passive_queue_type                priority_queues
% 3.54/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.99  --demod_completeness_check              fast
% 3.54/0.99  --demod_use_ground                      true
% 3.54/0.99  --sup_to_prop_solver                    passive
% 3.54/0.99  --sup_prop_simpl_new                    true
% 3.54/0.99  --sup_prop_simpl_given                  true
% 3.54/0.99  --sup_fun_splitting                     false
% 3.54/0.99  --sup_smt_interval                      50000
% 3.54/0.99  
% 3.54/0.99  ------ Superposition Simplification Setup
% 3.54/0.99  
% 3.54/0.99  --sup_indices_passive                   []
% 3.54/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.99  --sup_full_bw                           [BwDemod]
% 3.54/0.99  --sup_immed_triv                        [TrivRules]
% 3.54/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.99  --sup_immed_bw_main                     []
% 3.54/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.99  
% 3.54/0.99  ------ Combination Options
% 3.54/0.99  
% 3.54/0.99  --comb_res_mult                         3
% 3.54/0.99  --comb_sup_mult                         2
% 3.54/0.99  --comb_inst_mult                        10
% 3.54/0.99  
% 3.54/0.99  ------ Debug Options
% 3.54/0.99  
% 3.54/0.99  --dbg_backtrace                         false
% 3.54/0.99  --dbg_dump_prop_clauses                 false
% 3.54/0.99  --dbg_dump_prop_clauses_file            -
% 3.54/0.99  --dbg_out_stat                          false
% 3.54/0.99  ------ Parsing...
% 3.54/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.99  ------ Proving...
% 3.54/0.99  ------ Problem Properties 
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  clauses                                 16
% 3.54/0.99  conjectures                             1
% 3.54/0.99  EPR                                     3
% 3.54/0.99  Horn                                    16
% 3.54/0.99  unary                                   12
% 3.54/0.99  binary                                  3
% 3.54/0.99  lits                                    21
% 3.54/0.99  lits eq                                 12
% 3.54/0.99  fd_pure                                 0
% 3.54/0.99  fd_pseudo                               0
% 3.54/0.99  fd_cond                                 0
% 3.54/0.99  fd_pseudo_cond                          1
% 3.54/0.99  AC symbols                              0
% 3.54/0.99  
% 3.54/0.99  ------ Schedule dynamic 5 is on 
% 3.54/0.99  
% 3.54/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  ------ 
% 3.54/0.99  Current options:
% 3.54/0.99  ------ 
% 3.54/0.99  
% 3.54/0.99  ------ Input Options
% 3.54/0.99  
% 3.54/0.99  --out_options                           all
% 3.54/0.99  --tptp_safe_out                         true
% 3.54/0.99  --problem_path                          ""
% 3.54/0.99  --include_path                          ""
% 3.54/0.99  --clausifier                            res/vclausify_rel
% 3.54/0.99  --clausifier_options                    --mode clausify
% 3.54/0.99  --stdin                                 false
% 3.54/0.99  --stats_out                             all
% 3.54/0.99  
% 3.54/0.99  ------ General Options
% 3.54/0.99  
% 3.54/0.99  --fof                                   false
% 3.54/0.99  --time_out_real                         305.
% 3.54/0.99  --time_out_virtual                      -1.
% 3.54/0.99  --symbol_type_check                     false
% 3.54/0.99  --clausify_out                          false
% 3.54/0.99  --sig_cnt_out                           false
% 3.54/0.99  --trig_cnt_out                          false
% 3.54/0.99  --trig_cnt_out_tolerance                1.
% 3.54/0.99  --trig_cnt_out_sk_spl                   false
% 3.54/0.99  --abstr_cl_out                          false
% 3.54/0.99  
% 3.54/0.99  ------ Global Options
% 3.54/0.99  
% 3.54/0.99  --schedule                              default
% 3.54/0.99  --add_important_lit                     false
% 3.54/0.99  --prop_solver_per_cl                    1000
% 3.54/0.99  --min_unsat_core                        false
% 3.54/0.99  --soft_assumptions                      false
% 3.54/0.99  --soft_lemma_size                       3
% 3.54/0.99  --prop_impl_unit_size                   0
% 3.54/0.99  --prop_impl_unit                        []
% 3.54/0.99  --share_sel_clauses                     true
% 3.54/0.99  --reset_solvers                         false
% 3.54/0.99  --bc_imp_inh                            [conj_cone]
% 3.54/0.99  --conj_cone_tolerance                   3.
% 3.54/0.99  --extra_neg_conj                        none
% 3.54/0.99  --large_theory_mode                     true
% 3.54/0.99  --prolific_symb_bound                   200
% 3.54/0.99  --lt_threshold                          2000
% 3.54/0.99  --clause_weak_htbl                      true
% 3.54/0.99  --gc_record_bc_elim                     false
% 3.54/0.99  
% 3.54/0.99  ------ Preprocessing Options
% 3.54/0.99  
% 3.54/0.99  --preprocessing_flag                    true
% 3.54/0.99  --time_out_prep_mult                    0.1
% 3.54/0.99  --splitting_mode                        input
% 3.54/0.99  --splitting_grd                         true
% 3.54/0.99  --splitting_cvd                         false
% 3.54/0.99  --splitting_cvd_svl                     false
% 3.54/0.99  --splitting_nvd                         32
% 3.54/0.99  --sub_typing                            true
% 3.54/0.99  --prep_gs_sim                           true
% 3.54/0.99  --prep_unflatten                        true
% 3.54/0.99  --prep_res_sim                          true
% 3.54/0.99  --prep_upred                            true
% 3.54/0.99  --prep_sem_filter                       exhaustive
% 3.54/0.99  --prep_sem_filter_out                   false
% 3.54/0.99  --pred_elim                             true
% 3.54/0.99  --res_sim_input                         true
% 3.54/0.99  --eq_ax_congr_red                       true
% 3.54/0.99  --pure_diseq_elim                       true
% 3.54/0.99  --brand_transform                       false
% 3.54/0.99  --non_eq_to_eq                          false
% 3.54/0.99  --prep_def_merge                        true
% 3.54/0.99  --prep_def_merge_prop_impl              false
% 3.54/0.99  --prep_def_merge_mbd                    true
% 3.54/0.99  --prep_def_merge_tr_red                 false
% 3.54/0.99  --prep_def_merge_tr_cl                  false
% 3.54/0.99  --smt_preprocessing                     true
% 3.54/0.99  --smt_ac_axioms                         fast
% 3.54/0.99  --preprocessed_out                      false
% 3.54/0.99  --preprocessed_stats                    false
% 3.54/0.99  
% 3.54/0.99  ------ Abstraction refinement Options
% 3.54/0.99  
% 3.54/0.99  --abstr_ref                             []
% 3.54/0.99  --abstr_ref_prep                        false
% 3.54/0.99  --abstr_ref_until_sat                   false
% 3.54/0.99  --abstr_ref_sig_restrict                funpre
% 3.54/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.54/0.99  --abstr_ref_under                       []
% 3.54/0.99  
% 3.54/0.99  ------ SAT Options
% 3.54/0.99  
% 3.54/0.99  --sat_mode                              false
% 3.54/0.99  --sat_fm_restart_options                ""
% 3.54/0.99  --sat_gr_def                            false
% 3.54/0.99  --sat_epr_types                         true
% 3.54/0.99  --sat_non_cyclic_types                  false
% 3.54/0.99  --sat_finite_models                     false
% 3.54/0.99  --sat_fm_lemmas                         false
% 3.54/0.99  --sat_fm_prep                           false
% 3.54/0.99  --sat_fm_uc_incr                        true
% 3.54/0.99  --sat_out_model                         small
% 3.54/0.99  --sat_out_clauses                       false
% 3.54/0.99  
% 3.54/0.99  ------ QBF Options
% 3.54/0.99  
% 3.54/0.99  --qbf_mode                              false
% 3.54/0.99  --qbf_elim_univ                         false
% 3.54/0.99  --qbf_dom_inst                          none
% 3.54/0.99  --qbf_dom_pre_inst                      false
% 3.54/0.99  --qbf_sk_in                             false
% 3.54/0.99  --qbf_pred_elim                         true
% 3.54/0.99  --qbf_split                             512
% 3.54/0.99  
% 3.54/0.99  ------ BMC1 Options
% 3.54/0.99  
% 3.54/0.99  --bmc1_incremental                      false
% 3.54/0.99  --bmc1_axioms                           reachable_all
% 3.54/0.99  --bmc1_min_bound                        0
% 3.54/0.99  --bmc1_max_bound                        -1
% 3.54/0.99  --bmc1_max_bound_default                -1
% 3.54/0.99  --bmc1_symbol_reachability              true
% 3.54/0.99  --bmc1_property_lemmas                  false
% 3.54/0.99  --bmc1_k_induction                      false
% 3.54/0.99  --bmc1_non_equiv_states                 false
% 3.54/0.99  --bmc1_deadlock                         false
% 3.54/0.99  --bmc1_ucm                              false
% 3.54/0.99  --bmc1_add_unsat_core                   none
% 3.54/0.99  --bmc1_unsat_core_children              false
% 3.54/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.54/0.99  --bmc1_out_stat                         full
% 3.54/0.99  --bmc1_ground_init                      false
% 3.54/0.99  --bmc1_pre_inst_next_state              false
% 3.54/0.99  --bmc1_pre_inst_state                   false
% 3.54/0.99  --bmc1_pre_inst_reach_state             false
% 3.54/0.99  --bmc1_out_unsat_core                   false
% 3.54/0.99  --bmc1_aig_witness_out                  false
% 3.54/0.99  --bmc1_verbose                          false
% 3.54/0.99  --bmc1_dump_clauses_tptp                false
% 3.54/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.54/0.99  --bmc1_dump_file                        -
% 3.54/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.54/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.54/0.99  --bmc1_ucm_extend_mode                  1
% 3.54/0.99  --bmc1_ucm_init_mode                    2
% 3.54/0.99  --bmc1_ucm_cone_mode                    none
% 3.54/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.54/0.99  --bmc1_ucm_relax_model                  4
% 3.54/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.54/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.54/0.99  --bmc1_ucm_layered_model                none
% 3.54/0.99  --bmc1_ucm_max_lemma_size               10
% 3.54/0.99  
% 3.54/0.99  ------ AIG Options
% 3.54/0.99  
% 3.54/0.99  --aig_mode                              false
% 3.54/0.99  
% 3.54/0.99  ------ Instantiation Options
% 3.54/0.99  
% 3.54/0.99  --instantiation_flag                    true
% 3.54/0.99  --inst_sos_flag                         false
% 3.54/0.99  --inst_sos_phase                        true
% 3.54/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.54/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.54/0.99  --inst_lit_sel_side                     none
% 3.54/0.99  --inst_solver_per_active                1400
% 3.54/0.99  --inst_solver_calls_frac                1.
% 3.54/0.99  --inst_passive_queue_type               priority_queues
% 3.54/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.54/0.99  --inst_passive_queues_freq              [25;2]
% 3.54/0.99  --inst_dismatching                      true
% 3.54/0.99  --inst_eager_unprocessed_to_passive     true
% 3.54/0.99  --inst_prop_sim_given                   true
% 3.54/0.99  --inst_prop_sim_new                     false
% 3.54/0.99  --inst_subs_new                         false
% 3.54/0.99  --inst_eq_res_simp                      false
% 3.54/0.99  --inst_subs_given                       false
% 3.54/0.99  --inst_orphan_elimination               true
% 3.54/0.99  --inst_learning_loop_flag               true
% 3.54/0.99  --inst_learning_start                   3000
% 3.54/0.99  --inst_learning_factor                  2
% 3.54/0.99  --inst_start_prop_sim_after_learn       3
% 3.54/0.99  --inst_sel_renew                        solver
% 3.54/0.99  --inst_lit_activity_flag                true
% 3.54/0.99  --inst_restr_to_given                   false
% 3.54/0.99  --inst_activity_threshold               500
% 3.54/0.99  --inst_out_proof                        true
% 3.54/0.99  
% 3.54/0.99  ------ Resolution Options
% 3.54/0.99  
% 3.54/0.99  --resolution_flag                       false
% 3.54/0.99  --res_lit_sel                           adaptive
% 3.54/0.99  --res_lit_sel_side                      none
% 3.54/0.99  --res_ordering                          kbo
% 3.54/0.99  --res_to_prop_solver                    active
% 3.54/0.99  --res_prop_simpl_new                    false
% 3.54/0.99  --res_prop_simpl_given                  true
% 3.54/0.99  --res_passive_queue_type                priority_queues
% 3.54/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.54/0.99  --res_passive_queues_freq               [15;5]
% 3.54/0.99  --res_forward_subs                      full
% 3.54/0.99  --res_backward_subs                     full
% 3.54/0.99  --res_forward_subs_resolution           true
% 3.54/0.99  --res_backward_subs_resolution          true
% 3.54/0.99  --res_orphan_elimination                true
% 3.54/0.99  --res_time_limit                        2.
% 3.54/0.99  --res_out_proof                         true
% 3.54/0.99  
% 3.54/0.99  ------ Superposition Options
% 3.54/0.99  
% 3.54/0.99  --superposition_flag                    true
% 3.54/0.99  --sup_passive_queue_type                priority_queues
% 3.54/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.54/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.54/0.99  --demod_completeness_check              fast
% 3.54/0.99  --demod_use_ground                      true
% 3.54/0.99  --sup_to_prop_solver                    passive
% 3.54/0.99  --sup_prop_simpl_new                    true
% 3.54/0.99  --sup_prop_simpl_given                  true
% 3.54/0.99  --sup_fun_splitting                     false
% 3.54/0.99  --sup_smt_interval                      50000
% 3.54/0.99  
% 3.54/0.99  ------ Superposition Simplification Setup
% 3.54/0.99  
% 3.54/0.99  --sup_indices_passive                   []
% 3.54/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.54/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.54/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.99  --sup_full_bw                           [BwDemod]
% 3.54/0.99  --sup_immed_triv                        [TrivRules]
% 3.54/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.54/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.99  --sup_immed_bw_main                     []
% 3.54/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.54/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.54/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.54/0.99  
% 3.54/0.99  ------ Combination Options
% 3.54/0.99  
% 3.54/0.99  --comb_res_mult                         3
% 3.54/0.99  --comb_sup_mult                         2
% 3.54/0.99  --comb_inst_mult                        10
% 3.54/0.99  
% 3.54/0.99  ------ Debug Options
% 3.54/0.99  
% 3.54/0.99  --dbg_backtrace                         false
% 3.54/0.99  --dbg_dump_prop_clauses                 false
% 3.54/0.99  --dbg_dump_prop_clauses_file            -
% 3.54/0.99  --dbg_out_stat                          false
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  ------ Proving...
% 3.54/0.99  
% 3.54/0.99  
% 3.54/0.99  % SZS status Theorem for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.99  
% 3.54/0.99  fof(f18,axiom,(
% 3.54/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f22,plain,(
% 3.54/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 3.54/0.99    inference(unused_predicate_definition_removal,[],[f18])).
% 3.54/0.99  
% 3.54/0.99  fof(f24,plain,(
% 3.54/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 3.54/0.99    inference(ennf_transformation,[],[f22])).
% 3.54/0.99  
% 3.54/0.99  fof(f51,plain,(
% 3.54/0.99    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f24])).
% 3.54/0.99  
% 3.54/0.99  fof(f14,axiom,(
% 3.54/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f47,plain,(
% 3.54/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f14])).
% 3.54/0.99  
% 3.54/0.99  fof(f15,axiom,(
% 3.54/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f48,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f15])).
% 3.54/0.99  
% 3.54/0.99  fof(f16,axiom,(
% 3.54/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f49,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f16])).
% 3.54/0.99  
% 3.54/0.99  fof(f17,axiom,(
% 3.54/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f50,plain,(
% 3.54/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f17])).
% 3.54/0.99  
% 3.54/0.99  fof(f56,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f49,f50])).
% 3.54/0.99  
% 3.54/0.99  fof(f57,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f48,f56])).
% 3.54/0.99  
% 3.54/0.99  fof(f58,plain,(
% 3.54/0.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f47,f57])).
% 3.54/0.99  
% 3.54/0.99  fof(f64,plain,(
% 3.54/0.99    ( ! [X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f51,f58])).
% 3.54/0.99  
% 3.54/0.99  fof(f20,conjecture,(
% 3.54/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f21,negated_conjecture,(
% 3.54/0.99    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 3.54/0.99    inference(negated_conjecture,[],[f20])).
% 3.54/0.99  
% 3.54/0.99  fof(f25,plain,(
% 3.54/0.99    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 3.54/0.99    inference(ennf_transformation,[],[f21])).
% 3.54/0.99  
% 3.54/0.99  fof(f29,plain,(
% 3.54/0.99    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1))),
% 3.54/0.99    introduced(choice_axiom,[])).
% 3.54/0.99  
% 3.54/0.99  fof(f30,plain,(
% 3.54/0.99    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1 & r2_hidden(sK0,sK1)),
% 3.54/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f29])).
% 3.54/0.99  
% 3.54/0.99  fof(f53,plain,(
% 3.54/0.99    r2_hidden(sK0,sK1)),
% 3.54/0.99    inference(cnf_transformation,[],[f30])).
% 3.54/0.99  
% 3.54/0.99  fof(f6,axiom,(
% 3.54/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f23,plain,(
% 3.54/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.54/0.99    inference(ennf_transformation,[],[f6])).
% 3.54/0.99  
% 3.54/0.99  fof(f39,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f23])).
% 3.54/0.99  
% 3.54/0.99  fof(f10,axiom,(
% 3.54/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f43,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f10])).
% 3.54/0.99  
% 3.54/0.99  fof(f62,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f39,f43])).
% 3.54/0.99  
% 3.54/0.99  fof(f1,axiom,(
% 3.54/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f31,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f1])).
% 3.54/0.99  
% 3.54/0.99  fof(f60,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.54/0.99    inference(definition_unfolding,[],[f31,f43,f43])).
% 3.54/0.99  
% 3.54/0.99  fof(f4,axiom,(
% 3.54/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f37,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f4])).
% 3.54/0.99  
% 3.54/0.99  fof(f59,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.54/0.99    inference(definition_unfolding,[],[f37,f43])).
% 3.54/0.99  
% 3.54/0.99  fof(f5,axiom,(
% 3.54/0.99    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f38,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f5])).
% 3.54/0.99  
% 3.54/0.99  fof(f61,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 3.54/0.99    inference(definition_unfolding,[],[f38,f43,f43,f43])).
% 3.54/0.99  
% 3.54/0.99  fof(f3,axiom,(
% 3.54/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f28,plain,(
% 3.54/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.54/0.99    inference(nnf_transformation,[],[f3])).
% 3.54/0.99  
% 3.54/0.99  fof(f36,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f28])).
% 3.54/0.99  
% 3.54/0.99  fof(f12,axiom,(
% 3.54/0.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f45,plain,(
% 3.54/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f12])).
% 3.54/0.99  
% 3.54/0.99  fof(f7,axiom,(
% 3.54/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f40,plain,(
% 3.54/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f7])).
% 3.54/0.99  
% 3.54/0.99  fof(f11,axiom,(
% 3.54/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f44,plain,(
% 3.54/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.54/0.99    inference(cnf_transformation,[],[f11])).
% 3.54/0.99  
% 3.54/0.99  fof(f9,axiom,(
% 3.54/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f42,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.54/0.99    inference(cnf_transformation,[],[f9])).
% 3.54/0.99  
% 3.54/0.99  fof(f13,axiom,(
% 3.54/0.99    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f46,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f13])).
% 3.54/0.99  
% 3.54/0.99  fof(f55,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 3.54/0.99    inference(definition_unfolding,[],[f46,f43])).
% 3.54/0.99  
% 3.54/0.99  fof(f63,plain,(
% 3.54/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 3.54/0.99    inference(definition_unfolding,[],[f42,f55,f55])).
% 3.54/0.99  
% 3.54/0.99  fof(f2,axiom,(
% 3.54/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.99  
% 3.54/0.99  fof(f26,plain,(
% 3.54/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.99    inference(nnf_transformation,[],[f2])).
% 3.54/0.99  
% 3.54/0.99  fof(f27,plain,(
% 3.54/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.99    inference(flattening,[],[f26])).
% 3.54/0.99  
% 3.54/0.99  fof(f32,plain,(
% 3.54/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.54/0.99    inference(cnf_transformation,[],[f27])).
% 3.54/0.99  
% 3.54/0.99  fof(f68,plain,(
% 3.54/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.54/0.99    inference(equality_resolution,[],[f32])).
% 3.54/0.99  
% 3.54/0.99  fof(f34,plain,(
% 3.54/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.54/0.99    inference(cnf_transformation,[],[f27])).
% 3.54/0.99  
% 3.54/0.99  fof(f54,plain,(
% 3.54/0.99    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) != sK1),
% 3.54/0.99    inference(cnf_transformation,[],[f30])).
% 3.54/0.99  
% 3.54/0.99  fof(f66,plain,(
% 3.54/0.99    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1),
% 3.54/0.99    inference(definition_unfolding,[],[f54,f55,f58,f58])).
% 3.54/0.99  
% 3.54/0.99  cnf(c_14,plain,
% 3.54/0.99      ( ~ r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_17,negated_conjecture,
% 3.54/0.99      ( r2_hidden(sK0,sK1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_157,plain,
% 3.54/0.99      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)
% 3.54/0.99      | sK0 != X0
% 3.54/0.99      | sK1 != X1 ),
% 3.54/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_158,plain,
% 3.54/0.99      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.54/0.99      inference(unflattening,[status(thm)],[c_157]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_477,plain,
% 3.54/0.99      ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_8,plain,
% 3.54/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_480,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.54/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_754,plain,
% 3.54/0.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_477,c_480]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1172,plain,
% 3.54/0.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_754,c_1]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_0,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.54/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1303,plain,
% 3.54/0.99      ( k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1172,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_7,plain,
% 3.54/0.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = k4_xboole_0(k5_xboole_0(X0,X2),k4_xboole_0(k5_xboole_0(X0,X2),X1)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1301,plain,
% 3.54/0.99      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(X0,k4_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k4_xboole_0(k5_xboole_0(sK1,X0),k4_xboole_0(k5_xboole_0(sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1172,c_7]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_681,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_14491,plain,
% 3.54/0.99      ( k4_xboole_0(k5_xboole_0(sK1,X0),k4_xboole_0(k5_xboole_0(sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0) ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_1301,c_681]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_14521,plain,
% 3.54/0.99      ( k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1303,c_14491]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1167,plain,
% 3.54/0.99      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_754,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1186,plain,
% 3.54/0.99      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_1167,c_754]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5,plain,
% 3.54/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_482,plain,
% 3.54/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.54/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_2615,plain,
% 3.54/0.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k1_xboole_0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_477,c_482]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1171,plain,
% 3.54/0.99      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_754,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3038,plain,
% 3.54/0.99      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_2615,c_1171]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_13,plain,
% 3.54/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.54/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3422,plain,
% 3.54/0.99      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_3038,c_13]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5567,plain,
% 3.54/0.99      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1186,c_3422]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1871,plain,
% 3.54/0.99      ( k5_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_754,c_681]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3034,plain,
% 3.54/0.99      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_2615,c_1871]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5594,plain,
% 3.54/0.99      ( k4_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_5567,c_3034,c_3038]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_679,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5736,plain,
% 3.54/0.99      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_5594,c_679]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_3039,plain,
% 3.54/0.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_2615,c_754]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5755,plain,
% 3.54/0.99      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_5736,c_3039]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_9,plain,
% 3.54/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.54/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_479,plain,
% 3.54/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.54/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_752,plain,
% 3.54/0.99      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_479,c_480]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4784,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.54/0.99      inference(superposition,[status(thm)],[c_752,c_681]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_12,plain,
% 3.54/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.54/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_4811,plain,
% 3.54/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_4784,c_12]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_5756,plain,
% 3.54/0.99      ( k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 3.54/0.99      inference(demodulation,[status(thm)],[c_5755,c_3038,c_3039,c_4811]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_14679,plain,
% 3.54/0.99      ( k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k1_xboole_0 ),
% 3.54/0.99      inference(light_normalisation,[status(thm)],[c_14521,c_5756]) ).
% 3.54/0.99  
% 3.54/0.99  cnf(c_1174,plain,
% 3.54/0.99      ( k4_xboole_0(k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1)) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_754,c_7]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1544,plain,
% 3.54/1.00      ( k5_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1171,c_1174]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1612,plain,
% 3.54/1.00      ( k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),k4_xboole_0(k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1),sK1)) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_1544,c_754,c_1171]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2181,plain,
% 3.54/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1612,c_1]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3035,plain,
% 3.54/1.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1)) = k1_xboole_0 ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_2615,c_1612]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3232,plain,
% 3.54/1.00      ( k5_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k1_xboole_0) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_3035,c_681]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_3294,plain,
% 3.54/1.00      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_3232,c_12]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_6973,plain,
% 3.54/1.00      ( k4_xboole_0(sK1,sK1) = k1_xboole_0 ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_2181,c_2615,c_3294]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1554,plain,
% 3.54/1.00      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1174,c_1]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8337,plain,
% 3.54/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_6973,c_1554]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1874,plain,
% 3.54/1.00      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_681,c_13]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8341,plain,
% 3.54/1.00      ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k4_xboole_0(sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_1554,c_1874]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8347,plain,
% 3.54/1.00      ( k5_xboole_0(k4_xboole_0(sK1,X0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(sK1,k5_xboole_0(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_8341,c_0]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8358,plain,
% 3.54/1.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k4_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_8337,c_8347]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8360,plain,
% 3.54/1.00      ( k4_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_8358,c_1172,c_1303]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8810,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_8360,c_681]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_8820,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_8810,c_1172]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10053,plain,
% 3.54/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_8820,c_13]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10059,plain,
% 3.54/1.00      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_10053,c_3038]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10060,plain,
% 3.54/1.00      ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),sK1) = k1_xboole_0 ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_10059,c_12]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_11,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.54/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10368,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k4_xboole_0(sK1,k4_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_10060,c_11]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10391,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
% 3.54/1.00      inference(light_normalisation,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_10368,c_1172,c_3294,c_6973,c_8360]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_770,plain,
% 3.54/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(X0,X1) ),
% 3.54/1.00      inference(superposition,[status(thm)],[c_12,c_13]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10392,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = sK1 ),
% 3.54/1.00      inference(demodulation,[status(thm)],[c_10391,c_12,c_770]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_10393,plain,
% 3.54/1.00      ( k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) = sK1 ),
% 3.54/1.00      inference(light_normalisation,[status(thm)],[c_10392,c_1303]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_254,plain,
% 3.54/1.00      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 3.54/1.00      theory(equality) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_1041,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k1_xboole_0)
% 3.54/1.00      | k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) != sK1
% 3.54/1.00      | k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != k1_xboole_0 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_254]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_252,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_550,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != X0
% 3.54/1.00      | k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = sK1
% 3.54/1.00      | sK1 != X0 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_252]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_945,plain,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != k5_xboole_0(sK1,k1_xboole_0)
% 3.54/1.00      | k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) = sK1
% 3.54/1.00      | sK1 != k5_xboole_0(sK1,k1_xboole_0) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_550]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_732,plain,
% 3.54/1.00      ( k5_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_569,plain,
% 3.54/1.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_252]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_606,plain,
% 3.54/1.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_569]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_731,plain,
% 3.54/1.00      ( k5_xboole_0(sK1,k1_xboole_0) != sK1
% 3.54/1.00      | sK1 = k5_xboole_0(sK1,k1_xboole_0)
% 3.54/1.00      | sK1 != sK1 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_606]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_4,plain,
% 3.54/1.00      ( r1_tarski(X0,X0) ),
% 3.54/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_576,plain,
% 3.54/1.00      ( r1_tarski(sK1,sK1) ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_2,plain,
% 3.54/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.54/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_563,plain,
% 3.54/1.00      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_575,plain,
% 3.54/1.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.54/1.00      inference(instantiation,[status(thm)],[c_563]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(c_16,negated_conjecture,
% 3.54/1.00      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 3.54/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.54/1.00  
% 3.54/1.00  cnf(contradiction,plain,
% 3.54/1.00      ( $false ),
% 3.54/1.00      inference(minisat,
% 3.54/1.00                [status(thm)],
% 3.54/1.00                [c_14679,c_10393,c_1041,c_945,c_732,c_731,c_576,c_575,
% 3.54/1.00                 c_16]) ).
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/1.00  
% 3.54/1.00  ------                               Statistics
% 3.54/1.00  
% 3.54/1.00  ------ General
% 3.54/1.00  
% 3.54/1.00  abstr_ref_over_cycles:                  0
% 3.54/1.00  abstr_ref_under_cycles:                 0
% 3.54/1.00  gc_basic_clause_elim:                   0
% 3.54/1.00  forced_gc_time:                         0
% 3.54/1.00  parsing_time:                           0.009
% 3.54/1.00  unif_index_cands_time:                  0.
% 3.54/1.00  unif_index_add_time:                    0.
% 3.54/1.00  orderings_time:                         0.
% 3.54/1.00  out_proof_time:                         0.011
% 3.54/1.00  total_time:                             0.437
% 3.54/1.00  num_of_symbols:                         40
% 3.54/1.00  num_of_terms:                           17135
% 3.54/1.00  
% 3.54/1.00  ------ Preprocessing
% 3.54/1.00  
% 3.54/1.00  num_of_splits:                          0
% 3.54/1.00  num_of_split_atoms:                     0
% 3.54/1.00  num_of_reused_defs:                     0
% 3.54/1.00  num_eq_ax_congr_red:                    1
% 3.54/1.00  num_of_sem_filtered_clauses:            1
% 3.54/1.00  num_of_subtypes:                        0
% 3.54/1.00  monotx_restored_types:                  0
% 3.54/1.00  sat_num_of_epr_types:                   0
% 3.54/1.00  sat_num_of_non_cyclic_types:            0
% 3.54/1.00  sat_guarded_non_collapsed_types:        0
% 3.54/1.00  num_pure_diseq_elim:                    0
% 3.54/1.00  simp_replaced_by:                       0
% 3.54/1.00  res_preprocessed:                       80
% 3.54/1.00  prep_upred:                             0
% 3.54/1.00  prep_unflattend:                        2
% 3.54/1.00  smt_new_axioms:                         0
% 3.54/1.00  pred_elim_cands:                        1
% 3.54/1.00  pred_elim:                              1
% 3.54/1.00  pred_elim_cl:                           1
% 3.54/1.00  pred_elim_cycles:                       3
% 3.54/1.00  merged_defs:                            8
% 3.54/1.00  merged_defs_ncl:                        0
% 3.54/1.00  bin_hyper_res:                          8
% 3.54/1.00  prep_cycles:                            4
% 3.54/1.00  pred_elim_time:                         0.001
% 3.54/1.00  splitting_time:                         0.
% 3.54/1.00  sem_filter_time:                        0.
% 3.54/1.00  monotx_time:                            0.
% 3.54/1.00  subtype_inf_time:                       0.
% 3.54/1.00  
% 3.54/1.00  ------ Problem properties
% 3.54/1.00  
% 3.54/1.00  clauses:                                16
% 3.54/1.00  conjectures:                            1
% 3.54/1.00  epr:                                    3
% 3.54/1.00  horn:                                   16
% 3.54/1.00  ground:                                 2
% 3.54/1.00  unary:                                  12
% 3.54/1.00  binary:                                 3
% 3.54/1.00  lits:                                   21
% 3.54/1.00  lits_eq:                                12
% 3.54/1.00  fd_pure:                                0
% 3.54/1.00  fd_pseudo:                              0
% 3.54/1.00  fd_cond:                                0
% 3.54/1.00  fd_pseudo_cond:                         1
% 3.54/1.00  ac_symbols:                             0
% 3.54/1.00  
% 3.54/1.00  ------ Propositional Solver
% 3.54/1.00  
% 3.54/1.00  prop_solver_calls:                      32
% 3.54/1.00  prop_fast_solver_calls:                 432
% 3.54/1.00  smt_solver_calls:                       0
% 3.54/1.00  smt_fast_solver_calls:                  0
% 3.54/1.00  prop_num_of_clauses:                    4988
% 3.54/1.00  prop_preprocess_simplified:             7079
% 3.54/1.00  prop_fo_subsumed:                       0
% 3.54/1.00  prop_solver_time:                       0.
% 3.54/1.00  smt_solver_time:                        0.
% 3.54/1.00  smt_fast_solver_time:                   0.
% 3.54/1.00  prop_fast_solver_time:                  0.
% 3.54/1.00  prop_unsat_core_time:                   0.
% 3.54/1.00  
% 3.54/1.00  ------ QBF
% 3.54/1.00  
% 3.54/1.00  qbf_q_res:                              0
% 3.54/1.00  qbf_num_tautologies:                    0
% 3.54/1.00  qbf_prep_cycles:                        0
% 3.54/1.00  
% 3.54/1.00  ------ BMC1
% 3.54/1.00  
% 3.54/1.00  bmc1_current_bound:                     -1
% 3.54/1.00  bmc1_last_solved_bound:                 -1
% 3.54/1.00  bmc1_unsat_core_size:                   -1
% 3.54/1.00  bmc1_unsat_core_parents_size:           -1
% 3.54/1.00  bmc1_merge_next_fun:                    0
% 3.54/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.54/1.00  
% 3.54/1.00  ------ Instantiation
% 3.54/1.00  
% 3.54/1.00  inst_num_of_clauses:                    1310
% 3.54/1.00  inst_num_in_passive:                    293
% 3.54/1.00  inst_num_in_active:                     576
% 3.54/1.00  inst_num_in_unprocessed:                442
% 3.54/1.00  inst_num_of_loops:                      590
% 3.54/1.00  inst_num_of_learning_restarts:          0
% 3.54/1.00  inst_num_moves_active_passive:          7
% 3.54/1.00  inst_lit_activity:                      0
% 3.54/1.00  inst_lit_activity_moves:                0
% 3.54/1.00  inst_num_tautologies:                   0
% 3.54/1.00  inst_num_prop_implied:                  0
% 3.54/1.00  inst_num_existing_simplified:           0
% 3.54/1.00  inst_num_eq_res_simplified:             0
% 3.54/1.00  inst_num_child_elim:                    0
% 3.54/1.00  inst_num_of_dismatching_blockings:      885
% 3.54/1.00  inst_num_of_non_proper_insts:           1608
% 3.54/1.00  inst_num_of_duplicates:                 0
% 3.54/1.00  inst_inst_num_from_inst_to_res:         0
% 3.54/1.00  inst_dismatching_checking_time:         0.
% 3.54/1.00  
% 3.54/1.00  ------ Resolution
% 3.54/1.00  
% 3.54/1.00  res_num_of_clauses:                     0
% 3.54/1.00  res_num_in_passive:                     0
% 3.54/1.00  res_num_in_active:                      0
% 3.54/1.00  res_num_of_loops:                       84
% 3.54/1.00  res_forward_subset_subsumed:            226
% 3.54/1.00  res_backward_subset_subsumed:           6
% 3.54/1.00  res_forward_subsumed:                   0
% 3.54/1.00  res_backward_subsumed:                  0
% 3.54/1.00  res_forward_subsumption_resolution:     0
% 3.54/1.00  res_backward_subsumption_resolution:    0
% 3.54/1.00  res_clause_to_clause_subsumption:       3884
% 3.54/1.00  res_orphan_elimination:                 0
% 3.54/1.00  res_tautology_del:                      108
% 3.54/1.00  res_num_eq_res_simplified:              0
% 3.54/1.00  res_num_sel_changes:                    0
% 3.54/1.00  res_moves_from_active_to_pass:          0
% 3.54/1.00  
% 3.54/1.00  ------ Superposition
% 3.54/1.00  
% 3.54/1.00  sup_time_total:                         0.
% 3.54/1.00  sup_time_generating:                    0.
% 3.54/1.00  sup_time_sim_full:                      0.
% 3.54/1.00  sup_time_sim_immed:                     0.
% 3.54/1.00  
% 3.54/1.00  sup_num_of_clauses:                     805
% 3.54/1.00  sup_num_in_active:                      76
% 3.54/1.00  sup_num_in_passive:                     729
% 3.54/1.00  sup_num_of_loops:                       117
% 3.54/1.00  sup_fw_superposition:                   1141
% 3.54/1.00  sup_bw_superposition:                   1113
% 3.54/1.00  sup_immediate_simplified:               1195
% 3.54/1.00  sup_given_eliminated:                   11
% 3.54/1.00  comparisons_done:                       0
% 3.54/1.00  comparisons_avoided:                    0
% 3.54/1.00  
% 3.54/1.00  ------ Simplifications
% 3.54/1.00  
% 3.54/1.00  
% 3.54/1.00  sim_fw_subset_subsumed:                 3
% 3.54/1.00  sim_bw_subset_subsumed:                 0
% 3.54/1.00  sim_fw_subsumed:                        205
% 3.54/1.00  sim_bw_subsumed:                        4
% 3.54/1.00  sim_fw_subsumption_res:                 0
% 3.54/1.00  sim_bw_subsumption_res:                 0
% 3.54/1.00  sim_tautology_del:                      0
% 3.54/1.00  sim_eq_tautology_del:                   180
% 3.54/1.00  sim_eq_res_simp:                        0
% 3.54/1.00  sim_fw_demodulated:                     478
% 3.54/1.00  sim_bw_demodulated:                     131
% 3.54/1.00  sim_light_normalised:                   734
% 3.54/1.00  sim_joinable_taut:                      0
% 3.54/1.00  sim_joinable_simp:                      0
% 3.54/1.00  sim_ac_normalised:                      0
% 3.54/1.00  sim_smt_subsumption:                    0
% 3.54/1.00  
%------------------------------------------------------------------------------
