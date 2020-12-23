%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:34 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 694 expanded)
%              Number of clauses        :   68 ( 123 expanded)
%              Number of leaves         :   20 ( 181 expanded)
%              Depth                    :   24
%              Number of atoms          :  292 (1375 expanded)
%              Number of equality atoms :  170 ( 789 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).

fof(f58,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f65])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f60,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f59,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(definition_unfolding,[],[f59,f66])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f52,f66,f66,f66])).

fof(f78,plain,(
    ! [X1] : k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f74])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_199,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | k10_relat_1(X1,X0) != k1_xboole_0
    | sK1 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK1))
    | k10_relat_1(sK1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_226,plain,
    ( ~ r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) = k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_227,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
    | k10_relat_1(sK1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_400,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
    | k10_relat_1(sK1,X0) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_227])).

cnf(c_429,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK1))
    | ~ r1_xboole_0(k2_relat_1(sK1),X0)
    | k1_xboole_0 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_200,c_400])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | k1_xboole_0 = k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_98,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | k1_xboole_0 = k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_280,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k2_relat_1(sK1) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_98])).

cnf(c_281,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_94,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | k1_xboole_0 != k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_96,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | k1_xboole_0 != k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_300,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | k2_relat_1(sK1) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_94,c_96])).

cnf(c_301,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_402,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_301])).

cnf(c_432,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) ),
    inference(bin_hyper_res,[status(thm)],[c_281,c_402])).

cnf(c_500,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | ~ r1_xboole_0(k2_relat_1(sK1),X0)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
    | k2_relat_1(sK1) != k2_relat_1(sK1)
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_429,c_432])).

cnf(c_501,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | ~ r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_267,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(resolution,[status(thm)],[c_7,c_94])).

cnf(c_323,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X2
    | k10_relat_1(sK1,X2) != k1_xboole_0
    | k2_relat_1(sK1) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_267,c_200])).

cnf(c_324,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_relat_1(sK1))
    | k10_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_326,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_503,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_501,c_281,c_326])).

cnf(c_833,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_838,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1127,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_833,c_838])).

cnf(c_282,plain,
    ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
    | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_898,plain,
    ( ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
    | r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_899,plain,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) != iProver_top
    | r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_12,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k10_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_214,plain,
    ( r1_xboole_0(k2_relat_1(X0),X1)
    | k10_relat_1(X0,X1) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_215,plain,
    ( r1_xboole_0(k2_relat_1(sK1),X0)
    | k10_relat_1(sK1,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_560,plain,
    ( r1_xboole_0(k2_relat_1(sK1),X0)
    | k10_relat_1(sK1,X0) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_215])).

cnf(c_1030,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_1031,plain,
    ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_1130,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1127,c_282,c_899,c_1031])).

cnf(c_562,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
    | k10_relat_1(sK1,X0) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_227])).

cnf(c_836,plain,
    ( k10_relat_1(sK1,X0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_1238,plain,
    ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1130,c_836])).

cnf(c_514,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | k2_relat_1(sK1) != k2_relat_1(sK1)
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_429,c_402])).

cnf(c_515,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_351,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
    | k10_relat_1(sK1,X0) != k1_xboole_0
    | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | k2_relat_1(sK1) != k2_relat_1(sK1)
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_200,c_301])).

cnf(c_352,plain,
    ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_517,plain,
    ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_352])).

cnf(c_1349,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1238,c_517])).

cnf(c_1350,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1349])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_941,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_942,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_952,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_942,c_4])).

cnf(c_944,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3,c_0])).

cnf(c_946,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_944,c_3])).

cnf(c_953,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_952,c_946])).

cnf(c_957,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_941,c_953])).

cnf(c_9,plain,
    ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1211,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_957,c_9])).

cnf(c_1214,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1350,c_1214])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.67/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/0.92  
% 1.67/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.67/0.92  
% 1.67/0.92  ------  iProver source info
% 1.67/0.92  
% 1.67/0.92  git: date: 2020-06-30 10:37:57 +0100
% 1.67/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.67/0.92  git: non_committed_changes: false
% 1.67/0.92  git: last_make_outside_of_git: false
% 1.67/0.92  
% 1.67/0.92  ------ 
% 1.67/0.92  
% 1.67/0.92  ------ Input Options
% 1.67/0.92  
% 1.67/0.92  --out_options                           all
% 1.67/0.92  --tptp_safe_out                         true
% 1.67/0.92  --problem_path                          ""
% 1.67/0.92  --include_path                          ""
% 1.67/0.92  --clausifier                            res/vclausify_rel
% 1.67/0.92  --clausifier_options                    --mode clausify
% 1.67/0.92  --stdin                                 false
% 1.67/0.92  --stats_out                             all
% 1.67/0.92  
% 1.67/0.92  ------ General Options
% 1.67/0.92  
% 1.67/0.92  --fof                                   false
% 1.67/0.92  --time_out_real                         305.
% 1.67/0.92  --time_out_virtual                      -1.
% 1.67/0.92  --symbol_type_check                     false
% 1.67/0.92  --clausify_out                          false
% 1.67/0.92  --sig_cnt_out                           false
% 1.67/0.92  --trig_cnt_out                          false
% 1.67/0.92  --trig_cnt_out_tolerance                1.
% 1.67/0.92  --trig_cnt_out_sk_spl                   false
% 1.67/0.92  --abstr_cl_out                          false
% 1.67/0.92  
% 1.67/0.92  ------ Global Options
% 1.67/0.92  
% 1.67/0.92  --schedule                              default
% 1.67/0.92  --add_important_lit                     false
% 1.67/0.92  --prop_solver_per_cl                    1000
% 1.67/0.92  --min_unsat_core                        false
% 1.67/0.92  --soft_assumptions                      false
% 1.67/0.92  --soft_lemma_size                       3
% 1.67/0.92  --prop_impl_unit_size                   0
% 1.67/0.92  --prop_impl_unit                        []
% 1.67/0.92  --share_sel_clauses                     true
% 1.67/0.92  --reset_solvers                         false
% 1.67/0.92  --bc_imp_inh                            [conj_cone]
% 1.67/0.92  --conj_cone_tolerance                   3.
% 1.67/0.92  --extra_neg_conj                        none
% 1.67/0.92  --large_theory_mode                     true
% 1.67/0.92  --prolific_symb_bound                   200
% 1.67/0.92  --lt_threshold                          2000
% 1.67/0.92  --clause_weak_htbl                      true
% 1.67/0.92  --gc_record_bc_elim                     false
% 1.67/0.92  
% 1.67/0.92  ------ Preprocessing Options
% 1.67/0.92  
% 1.67/0.92  --preprocessing_flag                    true
% 1.67/0.92  --time_out_prep_mult                    0.1
% 1.67/0.92  --splitting_mode                        input
% 1.67/0.92  --splitting_grd                         true
% 1.67/0.92  --splitting_cvd                         false
% 1.67/0.92  --splitting_cvd_svl                     false
% 1.67/0.92  --splitting_nvd                         32
% 1.67/0.92  --sub_typing                            true
% 1.67/0.92  --prep_gs_sim                           true
% 1.67/0.92  --prep_unflatten                        true
% 1.67/0.92  --prep_res_sim                          true
% 1.67/0.92  --prep_upred                            true
% 1.67/0.92  --prep_sem_filter                       exhaustive
% 1.67/0.92  --prep_sem_filter_out                   false
% 1.67/0.92  --pred_elim                             true
% 1.67/0.92  --res_sim_input                         true
% 1.67/0.92  --eq_ax_congr_red                       true
% 1.67/0.92  --pure_diseq_elim                       true
% 1.67/0.92  --brand_transform                       false
% 1.67/0.92  --non_eq_to_eq                          false
% 1.67/0.92  --prep_def_merge                        true
% 1.67/0.92  --prep_def_merge_prop_impl              false
% 1.67/0.92  --prep_def_merge_mbd                    true
% 1.67/0.92  --prep_def_merge_tr_red                 false
% 1.67/0.92  --prep_def_merge_tr_cl                  false
% 1.67/0.92  --smt_preprocessing                     true
% 1.67/0.92  --smt_ac_axioms                         fast
% 1.67/0.92  --preprocessed_out                      false
% 1.67/0.92  --preprocessed_stats                    false
% 1.67/0.92  
% 1.67/0.92  ------ Abstraction refinement Options
% 1.67/0.92  
% 1.67/0.92  --abstr_ref                             []
% 1.67/0.92  --abstr_ref_prep                        false
% 1.67/0.92  --abstr_ref_until_sat                   false
% 1.67/0.92  --abstr_ref_sig_restrict                funpre
% 1.67/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.67/0.92  --abstr_ref_under                       []
% 1.67/0.92  
% 1.67/0.92  ------ SAT Options
% 1.67/0.92  
% 1.67/0.92  --sat_mode                              false
% 1.67/0.92  --sat_fm_restart_options                ""
% 1.67/0.92  --sat_gr_def                            false
% 1.67/0.92  --sat_epr_types                         true
% 1.67/0.92  --sat_non_cyclic_types                  false
% 1.67/0.92  --sat_finite_models                     false
% 1.67/0.92  --sat_fm_lemmas                         false
% 1.67/0.92  --sat_fm_prep                           false
% 1.67/0.92  --sat_fm_uc_incr                        true
% 1.67/0.92  --sat_out_model                         small
% 1.67/0.92  --sat_out_clauses                       false
% 1.67/0.92  
% 1.67/0.92  ------ QBF Options
% 1.67/0.92  
% 1.67/0.92  --qbf_mode                              false
% 1.67/0.92  --qbf_elim_univ                         false
% 1.67/0.92  --qbf_dom_inst                          none
% 1.67/0.92  --qbf_dom_pre_inst                      false
% 1.67/0.92  --qbf_sk_in                             false
% 1.67/0.92  --qbf_pred_elim                         true
% 1.67/0.92  --qbf_split                             512
% 1.67/0.92  
% 1.67/0.92  ------ BMC1 Options
% 1.67/0.92  
% 1.67/0.92  --bmc1_incremental                      false
% 1.67/0.92  --bmc1_axioms                           reachable_all
% 1.67/0.92  --bmc1_min_bound                        0
% 1.67/0.92  --bmc1_max_bound                        -1
% 1.67/0.92  --bmc1_max_bound_default                -1
% 1.67/0.92  --bmc1_symbol_reachability              true
% 1.67/0.92  --bmc1_property_lemmas                  false
% 1.67/0.92  --bmc1_k_induction                      false
% 1.67/0.92  --bmc1_non_equiv_states                 false
% 1.67/0.92  --bmc1_deadlock                         false
% 1.67/0.92  --bmc1_ucm                              false
% 1.67/0.92  --bmc1_add_unsat_core                   none
% 1.67/0.92  --bmc1_unsat_core_children              false
% 1.67/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.67/0.92  --bmc1_out_stat                         full
% 1.67/0.92  --bmc1_ground_init                      false
% 1.67/0.92  --bmc1_pre_inst_next_state              false
% 1.67/0.92  --bmc1_pre_inst_state                   false
% 1.67/0.92  --bmc1_pre_inst_reach_state             false
% 1.67/0.92  --bmc1_out_unsat_core                   false
% 1.67/0.92  --bmc1_aig_witness_out                  false
% 1.67/0.92  --bmc1_verbose                          false
% 1.67/0.92  --bmc1_dump_clauses_tptp                false
% 1.67/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.67/0.92  --bmc1_dump_file                        -
% 1.67/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.67/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.67/0.92  --bmc1_ucm_extend_mode                  1
% 1.67/0.92  --bmc1_ucm_init_mode                    2
% 1.67/0.92  --bmc1_ucm_cone_mode                    none
% 1.67/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.67/0.92  --bmc1_ucm_relax_model                  4
% 1.67/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.67/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.67/0.92  --bmc1_ucm_layered_model                none
% 1.67/0.92  --bmc1_ucm_max_lemma_size               10
% 1.67/0.92  
% 1.67/0.92  ------ AIG Options
% 1.67/0.92  
% 1.67/0.92  --aig_mode                              false
% 1.67/0.92  
% 1.67/0.92  ------ Instantiation Options
% 1.67/0.92  
% 1.67/0.92  --instantiation_flag                    true
% 1.67/0.92  --inst_sos_flag                         false
% 1.67/0.92  --inst_sos_phase                        true
% 1.67/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.67/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.67/0.92  --inst_lit_sel_side                     num_symb
% 1.67/0.92  --inst_solver_per_active                1400
% 1.67/0.92  --inst_solver_calls_frac                1.
% 1.67/0.92  --inst_passive_queue_type               priority_queues
% 1.67/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.67/0.92  --inst_passive_queues_freq              [25;2]
% 1.67/0.92  --inst_dismatching                      true
% 1.67/0.92  --inst_eager_unprocessed_to_passive     true
% 1.67/0.92  --inst_prop_sim_given                   true
% 1.67/0.92  --inst_prop_sim_new                     false
% 1.67/0.92  --inst_subs_new                         false
% 1.67/0.92  --inst_eq_res_simp                      false
% 1.67/0.92  --inst_subs_given                       false
% 1.67/0.92  --inst_orphan_elimination               true
% 1.67/0.92  --inst_learning_loop_flag               true
% 1.67/0.92  --inst_learning_start                   3000
% 1.67/0.92  --inst_learning_factor                  2
% 1.67/0.92  --inst_start_prop_sim_after_learn       3
% 1.67/0.92  --inst_sel_renew                        solver
% 1.67/0.92  --inst_lit_activity_flag                true
% 1.67/0.92  --inst_restr_to_given                   false
% 1.67/0.92  --inst_activity_threshold               500
% 1.67/0.92  --inst_out_proof                        true
% 1.67/0.92  
% 1.67/0.92  ------ Resolution Options
% 1.67/0.92  
% 1.67/0.92  --resolution_flag                       true
% 1.67/0.92  --res_lit_sel                           adaptive
% 1.67/0.92  --res_lit_sel_side                      none
% 1.67/0.92  --res_ordering                          kbo
% 1.67/0.92  --res_to_prop_solver                    active
% 1.67/0.92  --res_prop_simpl_new                    false
% 1.67/0.92  --res_prop_simpl_given                  true
% 1.67/0.92  --res_passive_queue_type                priority_queues
% 1.67/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.67/0.92  --res_passive_queues_freq               [15;5]
% 1.67/0.92  --res_forward_subs                      full
% 1.67/0.92  --res_backward_subs                     full
% 1.67/0.92  --res_forward_subs_resolution           true
% 1.67/0.92  --res_backward_subs_resolution          true
% 1.67/0.92  --res_orphan_elimination                true
% 1.67/0.92  --res_time_limit                        2.
% 1.67/0.92  --res_out_proof                         true
% 1.67/0.92  
% 1.67/0.92  ------ Superposition Options
% 1.67/0.92  
% 1.67/0.92  --superposition_flag                    true
% 1.67/0.92  --sup_passive_queue_type                priority_queues
% 1.67/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.67/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.67/0.92  --demod_completeness_check              fast
% 1.67/0.92  --demod_use_ground                      true
% 1.67/0.92  --sup_to_prop_solver                    passive
% 1.67/0.92  --sup_prop_simpl_new                    true
% 1.67/0.92  --sup_prop_simpl_given                  true
% 1.67/0.92  --sup_fun_splitting                     false
% 1.67/0.92  --sup_smt_interval                      50000
% 1.67/0.92  
% 1.67/0.92  ------ Superposition Simplification Setup
% 1.67/0.92  
% 1.67/0.92  --sup_indices_passive                   []
% 1.67/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.67/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.92  --sup_full_bw                           [BwDemod]
% 1.67/0.92  --sup_immed_triv                        [TrivRules]
% 1.67/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.67/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.92  --sup_immed_bw_main                     []
% 1.67/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.67/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/0.92  
% 1.67/0.92  ------ Combination Options
% 1.67/0.92  
% 1.67/0.92  --comb_res_mult                         3
% 1.67/0.92  --comb_sup_mult                         2
% 1.67/0.92  --comb_inst_mult                        10
% 1.67/0.92  
% 1.67/0.92  ------ Debug Options
% 1.67/0.92  
% 1.67/0.92  --dbg_backtrace                         false
% 1.67/0.92  --dbg_dump_prop_clauses                 false
% 1.67/0.92  --dbg_dump_prop_clauses_file            -
% 1.67/0.92  --dbg_out_stat                          false
% 1.67/0.92  ------ Parsing...
% 1.67/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.67/0.92  
% 1.67/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.67/0.92  
% 1.67/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.67/0.92  
% 1.67/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.67/0.92  ------ Proving...
% 1.67/0.92  ------ Problem Properties 
% 1.67/0.92  
% 1.67/0.92  
% 1.67/0.92  clauses                                 14
% 1.67/0.92  conjectures                             0
% 1.67/0.92  EPR                                     1
% 1.67/0.92  Horn                                    10
% 1.67/0.92  unary                                   6
% 1.67/0.92  binary                                  7
% 1.67/0.92  lits                                    23
% 1.67/0.92  lits eq                                 16
% 1.67/0.92  fd_pure                                 0
% 1.67/0.92  fd_pseudo                               0
% 1.67/0.92  fd_cond                                 0
% 1.67/0.92  fd_pseudo_cond                          1
% 1.67/0.92  AC symbols                              0
% 1.67/0.92  
% 1.67/0.92  ------ Schedule dynamic 5 is on 
% 1.67/0.92  
% 1.67/0.92  ------ no conjectures: strip conj schedule 
% 1.67/0.92  
% 1.67/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.67/0.92  
% 1.67/0.92  
% 1.67/0.92  ------ 
% 1.67/0.92  Current options:
% 1.67/0.92  ------ 
% 1.67/0.92  
% 1.67/0.92  ------ Input Options
% 1.67/0.92  
% 1.67/0.92  --out_options                           all
% 1.67/0.92  --tptp_safe_out                         true
% 1.67/0.92  --problem_path                          ""
% 1.67/0.92  --include_path                          ""
% 1.67/0.92  --clausifier                            res/vclausify_rel
% 1.67/0.92  --clausifier_options                    --mode clausify
% 1.67/0.92  --stdin                                 false
% 1.67/0.92  --stats_out                             all
% 1.67/0.92  
% 1.67/0.92  ------ General Options
% 1.67/0.92  
% 1.67/0.92  --fof                                   false
% 1.67/0.92  --time_out_real                         305.
% 1.67/0.92  --time_out_virtual                      -1.
% 1.67/0.92  --symbol_type_check                     false
% 1.67/0.92  --clausify_out                          false
% 1.67/0.92  --sig_cnt_out                           false
% 1.67/0.92  --trig_cnt_out                          false
% 1.67/0.92  --trig_cnt_out_tolerance                1.
% 1.67/0.92  --trig_cnt_out_sk_spl                   false
% 1.67/0.92  --abstr_cl_out                          false
% 1.67/0.92  
% 1.67/0.92  ------ Global Options
% 1.67/0.92  
% 1.67/0.92  --schedule                              default
% 1.67/0.92  --add_important_lit                     false
% 1.67/0.92  --prop_solver_per_cl                    1000
% 1.67/0.92  --min_unsat_core                        false
% 1.67/0.92  --soft_assumptions                      false
% 1.67/0.92  --soft_lemma_size                       3
% 1.67/0.92  --prop_impl_unit_size                   0
% 1.67/0.92  --prop_impl_unit                        []
% 1.67/0.92  --share_sel_clauses                     true
% 1.67/0.92  --reset_solvers                         false
% 1.67/0.92  --bc_imp_inh                            [conj_cone]
% 1.67/0.92  --conj_cone_tolerance                   3.
% 1.67/0.92  --extra_neg_conj                        none
% 1.67/0.92  --large_theory_mode                     true
% 1.67/0.92  --prolific_symb_bound                   200
% 1.67/0.92  --lt_threshold                          2000
% 1.67/0.92  --clause_weak_htbl                      true
% 1.67/0.92  --gc_record_bc_elim                     false
% 1.67/0.92  
% 1.67/0.92  ------ Preprocessing Options
% 1.67/0.92  
% 1.67/0.92  --preprocessing_flag                    true
% 1.67/0.92  --time_out_prep_mult                    0.1
% 1.67/0.92  --splitting_mode                        input
% 1.67/0.92  --splitting_grd                         true
% 1.67/0.92  --splitting_cvd                         false
% 1.67/0.92  --splitting_cvd_svl                     false
% 1.67/0.92  --splitting_nvd                         32
% 1.67/0.92  --sub_typing                            true
% 1.67/0.92  --prep_gs_sim                           true
% 1.67/0.92  --prep_unflatten                        true
% 1.67/0.92  --prep_res_sim                          true
% 1.67/0.92  --prep_upred                            true
% 1.67/0.92  --prep_sem_filter                       exhaustive
% 1.67/0.92  --prep_sem_filter_out                   false
% 1.67/0.92  --pred_elim                             true
% 1.67/0.92  --res_sim_input                         true
% 1.67/0.92  --eq_ax_congr_red                       true
% 1.67/0.92  --pure_diseq_elim                       true
% 1.67/0.92  --brand_transform                       false
% 1.67/0.92  --non_eq_to_eq                          false
% 1.67/0.92  --prep_def_merge                        true
% 1.67/0.92  --prep_def_merge_prop_impl              false
% 1.67/0.92  --prep_def_merge_mbd                    true
% 1.67/0.92  --prep_def_merge_tr_red                 false
% 1.67/0.92  --prep_def_merge_tr_cl                  false
% 1.67/0.92  --smt_preprocessing                     true
% 1.67/0.92  --smt_ac_axioms                         fast
% 1.67/0.92  --preprocessed_out                      false
% 1.67/0.92  --preprocessed_stats                    false
% 1.67/0.92  
% 1.67/0.92  ------ Abstraction refinement Options
% 1.67/0.92  
% 1.67/0.92  --abstr_ref                             []
% 1.67/0.92  --abstr_ref_prep                        false
% 1.67/0.92  --abstr_ref_until_sat                   false
% 1.67/0.92  --abstr_ref_sig_restrict                funpre
% 1.67/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.67/0.92  --abstr_ref_under                       []
% 1.67/0.92  
% 1.67/0.92  ------ SAT Options
% 1.67/0.92  
% 1.67/0.92  --sat_mode                              false
% 1.67/0.92  --sat_fm_restart_options                ""
% 1.67/0.92  --sat_gr_def                            false
% 1.67/0.92  --sat_epr_types                         true
% 1.67/0.92  --sat_non_cyclic_types                  false
% 1.67/0.92  --sat_finite_models                     false
% 1.67/0.92  --sat_fm_lemmas                         false
% 1.67/0.92  --sat_fm_prep                           false
% 1.67/0.92  --sat_fm_uc_incr                        true
% 1.67/0.92  --sat_out_model                         small
% 1.67/0.92  --sat_out_clauses                       false
% 1.67/0.92  
% 1.67/0.92  ------ QBF Options
% 1.67/0.92  
% 1.67/0.92  --qbf_mode                              false
% 1.67/0.92  --qbf_elim_univ                         false
% 1.67/0.92  --qbf_dom_inst                          none
% 1.67/0.92  --qbf_dom_pre_inst                      false
% 1.67/0.92  --qbf_sk_in                             false
% 1.67/0.92  --qbf_pred_elim                         true
% 1.67/0.92  --qbf_split                             512
% 1.67/0.92  
% 1.67/0.92  ------ BMC1 Options
% 1.67/0.92  
% 1.67/0.92  --bmc1_incremental                      false
% 1.67/0.92  --bmc1_axioms                           reachable_all
% 1.67/0.92  --bmc1_min_bound                        0
% 1.67/0.92  --bmc1_max_bound                        -1
% 1.67/0.92  --bmc1_max_bound_default                -1
% 1.67/0.92  --bmc1_symbol_reachability              true
% 1.67/0.92  --bmc1_property_lemmas                  false
% 1.67/0.92  --bmc1_k_induction                      false
% 1.67/0.92  --bmc1_non_equiv_states                 false
% 1.67/0.92  --bmc1_deadlock                         false
% 1.67/0.92  --bmc1_ucm                              false
% 1.67/0.92  --bmc1_add_unsat_core                   none
% 1.67/0.92  --bmc1_unsat_core_children              false
% 1.67/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.67/0.92  --bmc1_out_stat                         full
% 1.67/0.92  --bmc1_ground_init                      false
% 1.67/0.92  --bmc1_pre_inst_next_state              false
% 1.67/0.92  --bmc1_pre_inst_state                   false
% 1.67/0.92  --bmc1_pre_inst_reach_state             false
% 1.67/0.92  --bmc1_out_unsat_core                   false
% 1.67/0.92  --bmc1_aig_witness_out                  false
% 1.67/0.92  --bmc1_verbose                          false
% 1.67/0.92  --bmc1_dump_clauses_tptp                false
% 1.67/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.67/0.92  --bmc1_dump_file                        -
% 1.67/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.67/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.67/0.92  --bmc1_ucm_extend_mode                  1
% 1.67/0.92  --bmc1_ucm_init_mode                    2
% 1.67/0.92  --bmc1_ucm_cone_mode                    none
% 1.67/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.67/0.92  --bmc1_ucm_relax_model                  4
% 1.67/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.67/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.67/0.92  --bmc1_ucm_layered_model                none
% 1.67/0.92  --bmc1_ucm_max_lemma_size               10
% 1.67/0.92  
% 1.67/0.92  ------ AIG Options
% 1.67/0.92  
% 1.67/0.92  --aig_mode                              false
% 1.67/0.92  
% 1.67/0.92  ------ Instantiation Options
% 1.67/0.92  
% 1.67/0.92  --instantiation_flag                    true
% 1.67/0.92  --inst_sos_flag                         false
% 1.67/0.92  --inst_sos_phase                        true
% 1.67/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.67/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.67/0.92  --inst_lit_sel_side                     none
% 1.67/0.92  --inst_solver_per_active                1400
% 1.67/0.92  --inst_solver_calls_frac                1.
% 1.67/0.92  --inst_passive_queue_type               priority_queues
% 1.67/0.92  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.67/0.92  --inst_passive_queues_freq              [25;2]
% 1.67/0.92  --inst_dismatching                      true
% 1.67/0.92  --inst_eager_unprocessed_to_passive     true
% 1.67/0.92  --inst_prop_sim_given                   true
% 1.67/0.92  --inst_prop_sim_new                     false
% 1.67/0.92  --inst_subs_new                         false
% 1.67/0.92  --inst_eq_res_simp                      false
% 1.67/0.92  --inst_subs_given                       false
% 1.67/0.92  --inst_orphan_elimination               true
% 1.67/0.92  --inst_learning_loop_flag               true
% 1.67/0.92  --inst_learning_start                   3000
% 1.67/0.92  --inst_learning_factor                  2
% 1.67/0.92  --inst_start_prop_sim_after_learn       3
% 1.67/0.92  --inst_sel_renew                        solver
% 1.67/0.92  --inst_lit_activity_flag                true
% 1.67/0.92  --inst_restr_to_given                   false
% 1.67/0.92  --inst_activity_threshold               500
% 1.67/0.92  --inst_out_proof                        true
% 1.67/0.92  
% 1.67/0.92  ------ Resolution Options
% 1.67/0.92  
% 1.67/0.92  --resolution_flag                       false
% 1.67/0.92  --res_lit_sel                           adaptive
% 1.67/0.92  --res_lit_sel_side                      none
% 1.67/0.92  --res_ordering                          kbo
% 1.67/0.92  --res_to_prop_solver                    active
% 1.67/0.92  --res_prop_simpl_new                    false
% 1.67/0.92  --res_prop_simpl_given                  true
% 1.67/0.92  --res_passive_queue_type                priority_queues
% 1.67/0.92  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.67/0.92  --res_passive_queues_freq               [15;5]
% 1.67/0.92  --res_forward_subs                      full
% 1.67/0.92  --res_backward_subs                     full
% 1.67/0.92  --res_forward_subs_resolution           true
% 1.67/0.92  --res_backward_subs_resolution          true
% 1.67/0.92  --res_orphan_elimination                true
% 1.67/0.92  --res_time_limit                        2.
% 1.67/0.92  --res_out_proof                         true
% 1.67/0.92  
% 1.67/0.92  ------ Superposition Options
% 1.67/0.92  
% 1.67/0.92  --superposition_flag                    true
% 1.67/0.92  --sup_passive_queue_type                priority_queues
% 1.67/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.67/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.67/0.92  --demod_completeness_check              fast
% 1.67/0.92  --demod_use_ground                      true
% 1.67/0.92  --sup_to_prop_solver                    passive
% 1.67/0.92  --sup_prop_simpl_new                    true
% 1.67/0.92  --sup_prop_simpl_given                  true
% 1.67/0.92  --sup_fun_splitting                     false
% 1.67/0.92  --sup_smt_interval                      50000
% 1.67/0.92  
% 1.67/0.92  ------ Superposition Simplification Setup
% 1.67/0.92  
% 1.67/0.92  --sup_indices_passive                   []
% 1.67/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.67/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.67/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.92  --sup_full_bw                           [BwDemod]
% 1.67/0.92  --sup_immed_triv                        [TrivRules]
% 1.67/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.67/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.92  --sup_immed_bw_main                     []
% 1.67/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.67/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.67/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.67/0.92  
% 1.67/0.92  ------ Combination Options
% 1.67/0.92  
% 1.67/0.92  --comb_res_mult                         3
% 1.67/0.92  --comb_sup_mult                         2
% 1.67/0.92  --comb_inst_mult                        10
% 1.67/0.92  
% 1.67/0.92  ------ Debug Options
% 1.67/0.92  
% 1.67/0.92  --dbg_backtrace                         false
% 1.67/0.92  --dbg_dump_prop_clauses                 false
% 1.67/0.92  --dbg_dump_prop_clauses_file            -
% 1.67/0.92  --dbg_out_stat                          false
% 1.67/0.92  
% 1.67/0.92  
% 1.67/0.92  
% 1.67/0.92  
% 1.67/0.92  ------ Proving...
% 1.67/0.92  
% 1.67/0.92  
% 1.67/0.92  % SZS status Theorem for theBenchmark.p
% 1.67/0.92  
% 1.67/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 1.67/0.92  
% 1.67/0.92  fof(f19,axiom,(
% 1.67/0.92    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f26,plain,(
% 1.67/0.92    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 1.67/0.92    inference(ennf_transformation,[],[f19])).
% 1.67/0.92  
% 1.67/0.92  fof(f27,plain,(
% 1.67/0.92    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 1.67/0.92    inference(flattening,[],[f26])).
% 1.67/0.92  
% 1.67/0.92  fof(f57,plain,(
% 1.67/0.92    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f27])).
% 1.67/0.92  
% 1.67/0.92  fof(f20,conjecture,(
% 1.67/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f21,negated_conjecture,(
% 1.67/0.92    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 1.67/0.92    inference(negated_conjecture,[],[f20])).
% 1.67/0.92  
% 1.67/0.92  fof(f28,plain,(
% 1.67/0.92    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 1.67/0.92    inference(ennf_transformation,[],[f21])).
% 1.67/0.92  
% 1.67/0.92  fof(f32,plain,(
% 1.67/0.92    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 1.67/0.92    inference(nnf_transformation,[],[f28])).
% 1.67/0.92  
% 1.67/0.92  fof(f33,plain,(
% 1.67/0.92    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 1.67/0.92    inference(flattening,[],[f32])).
% 1.67/0.92  
% 1.67/0.92  fof(f34,plain,(
% 1.67/0.92    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.67/0.92    introduced(choice_axiom,[])).
% 1.67/0.92  
% 1.67/0.92  fof(f35,plain,(
% 1.67/0.92    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 1.67/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).
% 1.67/0.92  
% 1.67/0.92  fof(f58,plain,(
% 1.67/0.92    v1_relat_1(sK1)),
% 1.67/0.92    inference(cnf_transformation,[],[f35])).
% 1.67/0.92  
% 1.67/0.92  fof(f18,axiom,(
% 1.67/0.92    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f25,plain,(
% 1.67/0.92    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.67/0.92    inference(ennf_transformation,[],[f18])).
% 1.67/0.92  
% 1.67/0.92  fof(f31,plain,(
% 1.67/0.92    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.67/0.92    inference(nnf_transformation,[],[f25])).
% 1.67/0.92  
% 1.67/0.92  fof(f56,plain,(
% 1.67/0.92    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f31])).
% 1.67/0.92  
% 1.67/0.92  fof(f15,axiom,(
% 1.67/0.92    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f24,plain,(
% 1.67/0.92    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.67/0.92    inference(ennf_transformation,[],[f15])).
% 1.67/0.92  
% 1.67/0.92  fof(f51,plain,(
% 1.67/0.92    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f24])).
% 1.67/0.92  
% 1.67/0.92  fof(f7,axiom,(
% 1.67/0.92    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f42,plain,(
% 1.67/0.92    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f7])).
% 1.67/0.92  
% 1.67/0.92  fof(f8,axiom,(
% 1.67/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f43,plain,(
% 1.67/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f8])).
% 1.67/0.92  
% 1.67/0.92  fof(f9,axiom,(
% 1.67/0.92    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f44,plain,(
% 1.67/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f9])).
% 1.67/0.92  
% 1.67/0.92  fof(f10,axiom,(
% 1.67/0.92    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f45,plain,(
% 1.67/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f10])).
% 1.67/0.92  
% 1.67/0.92  fof(f11,axiom,(
% 1.67/0.92    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f46,plain,(
% 1.67/0.92    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f11])).
% 1.67/0.92  
% 1.67/0.92  fof(f12,axiom,(
% 1.67/0.92    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f47,plain,(
% 1.67/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f12])).
% 1.67/0.92  
% 1.67/0.92  fof(f13,axiom,(
% 1.67/0.92    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f48,plain,(
% 1.67/0.92    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f13])).
% 1.67/0.92  
% 1.67/0.92  fof(f61,plain,(
% 1.67/0.92    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f47,f48])).
% 1.67/0.92  
% 1.67/0.92  fof(f62,plain,(
% 1.67/0.92    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f46,f61])).
% 1.67/0.92  
% 1.67/0.92  fof(f63,plain,(
% 1.67/0.92    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f45,f62])).
% 1.67/0.92  
% 1.67/0.92  fof(f64,plain,(
% 1.67/0.92    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f44,f63])).
% 1.67/0.92  
% 1.67/0.92  fof(f65,plain,(
% 1.67/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f43,f64])).
% 1.67/0.92  
% 1.67/0.92  fof(f66,plain,(
% 1.67/0.92    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f42,f65])).
% 1.67/0.92  
% 1.67/0.92  fof(f72,plain,(
% 1.67/0.92    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f51,f66])).
% 1.67/0.92  
% 1.67/0.92  fof(f60,plain,(
% 1.67/0.92    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.67/0.92    inference(cnf_transformation,[],[f35])).
% 1.67/0.92  
% 1.67/0.92  fof(f76,plain,(
% 1.67/0.92    k1_xboole_0 = k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 1.67/0.92    inference(definition_unfolding,[],[f60,f66])).
% 1.67/0.92  
% 1.67/0.92  fof(f14,axiom,(
% 1.67/0.92    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f29,plain,(
% 1.67/0.92    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.67/0.92    inference(nnf_transformation,[],[f14])).
% 1.67/0.92  
% 1.67/0.92  fof(f50,plain,(
% 1.67/0.92    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f29])).
% 1.67/0.92  
% 1.67/0.92  fof(f70,plain,(
% 1.67/0.92    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f50,f66])).
% 1.67/0.92  
% 1.67/0.92  fof(f59,plain,(
% 1.67/0.92    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 1.67/0.92    inference(cnf_transformation,[],[f35])).
% 1.67/0.92  
% 1.67/0.92  fof(f77,plain,(
% 1.67/0.92    k1_xboole_0 != k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 1.67/0.92    inference(definition_unfolding,[],[f59,f66])).
% 1.67/0.92  
% 1.67/0.92  fof(f2,axiom,(
% 1.67/0.92    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f23,plain,(
% 1.67/0.92    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.67/0.92    inference(ennf_transformation,[],[f2])).
% 1.67/0.92  
% 1.67/0.92  fof(f37,plain,(
% 1.67/0.92    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f23])).
% 1.67/0.92  
% 1.67/0.92  fof(f55,plain,(
% 1.67/0.92    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f31])).
% 1.67/0.92  
% 1.67/0.92  fof(f1,axiom,(
% 1.67/0.92    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f22,plain,(
% 1.67/0.92    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.67/0.92    inference(rectify,[],[f1])).
% 1.67/0.92  
% 1.67/0.92  fof(f36,plain,(
% 1.67/0.92    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.67/0.92    inference(cnf_transformation,[],[f22])).
% 1.67/0.92  
% 1.67/0.92  fof(f5,axiom,(
% 1.67/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f40,plain,(
% 1.67/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.67/0.92    inference(cnf_transformation,[],[f5])).
% 1.67/0.92  
% 1.67/0.92  fof(f68,plain,(
% 1.67/0.92    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.67/0.92    inference(definition_unfolding,[],[f36,f40])).
% 1.67/0.92  
% 1.67/0.92  fof(f3,axiom,(
% 1.67/0.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f38,plain,(
% 1.67/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.67/0.92    inference(cnf_transformation,[],[f3])).
% 1.67/0.92  
% 1.67/0.92  fof(f67,plain,(
% 1.67/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.67/0.92    inference(definition_unfolding,[],[f38,f40])).
% 1.67/0.92  
% 1.67/0.92  fof(f4,axiom,(
% 1.67/0.92    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f39,plain,(
% 1.67/0.92    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.67/0.92    inference(cnf_transformation,[],[f4])).
% 1.67/0.92  
% 1.67/0.92  fof(f69,plain,(
% 1.67/0.92    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 1.67/0.92    inference(definition_unfolding,[],[f39,f40])).
% 1.67/0.92  
% 1.67/0.92  fof(f6,axiom,(
% 1.67/0.92    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f41,plain,(
% 1.67/0.92    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.67/0.92    inference(cnf_transformation,[],[f6])).
% 1.67/0.92  
% 1.67/0.92  fof(f16,axiom,(
% 1.67/0.92    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 1.67/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.67/0.92  
% 1.67/0.92  fof(f30,plain,(
% 1.67/0.92    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 1.67/0.92    inference(nnf_transformation,[],[f16])).
% 1.67/0.92  
% 1.67/0.92  fof(f52,plain,(
% 1.67/0.92    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 1.67/0.92    inference(cnf_transformation,[],[f30])).
% 1.67/0.92  
% 1.67/0.92  fof(f74,plain,(
% 1.67/0.92    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.67/0.92    inference(definition_unfolding,[],[f52,f66,f66,f66])).
% 1.67/0.92  
% 1.67/0.92  fof(f78,plain,(
% 1.67/0.92    ( ! [X1] : (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 1.67/0.92    inference(equality_resolution,[],[f74])).
% 1.67/0.92  
% 1.67/0.92  cnf(c_13,plain,
% 1.67/0.92      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 1.67/0.92      | ~ v1_relat_1(X1)
% 1.67/0.92      | k10_relat_1(X1,X0) != k1_xboole_0
% 1.67/0.92      | k1_xboole_0 = X0 ),
% 1.67/0.92      inference(cnf_transformation,[],[f57]) ).
% 1.67/0.92  
% 1.67/0.92  cnf(c_16,negated_conjecture,
% 1.67/0.92      ( v1_relat_1(sK1) ),
% 1.67/0.92      inference(cnf_transformation,[],[f58]) ).
% 1.67/0.92  
% 1.67/0.92  cnf(c_199,plain,
% 1.67/0.92      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 1.67/0.92      | k10_relat_1(X1,X0) != k1_xboole_0
% 1.67/0.92      | sK1 != X1
% 1.67/0.92      | k1_xboole_0 = X0 ),
% 1.67/0.92      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 1.67/0.92  
% 1.67/0.92  cnf(c_200,plain,
% 1.67/0.92      ( ~ r1_tarski(X0,k2_relat_1(sK1))
% 1.67/0.92      | k10_relat_1(sK1,X0) != k1_xboole_0
% 1.67/0.92      | k1_xboole_0 = X0 ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_199]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_11,plain,
% 1.67/0.93      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 1.67/0.93      | ~ v1_relat_1(X0)
% 1.67/0.93      | k10_relat_1(X0,X1) = k1_xboole_0 ),
% 1.67/0.93      inference(cnf_transformation,[],[f56]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_226,plain,
% 1.67/0.93      ( ~ r1_xboole_0(k2_relat_1(X0),X1)
% 1.67/0.93      | k10_relat_1(X0,X1) = k1_xboole_0
% 1.67/0.93      | sK1 != X0 ),
% 1.67/0.93      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_227,plain,
% 1.67/0.93      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
% 1.67/0.93      | k10_relat_1(sK1,X0) = k1_xboole_0 ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_226]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_400,plain,
% 1.67/0.93      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
% 1.67/0.93      | k10_relat_1(sK1,X0) = k1_xboole_0 ),
% 1.67/0.93      inference(prop_impl,[status(thm)],[c_227]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_429,plain,
% 1.67/0.93      ( ~ r1_tarski(X0,k2_relat_1(sK1))
% 1.67/0.93      | ~ r1_xboole_0(k2_relat_1(sK1),X0)
% 1.67/0.93      | k1_xboole_0 = X0 ),
% 1.67/0.93      inference(bin_hyper_res,[status(thm)],[c_200,c_400]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_7,plain,
% 1.67/0.93      ( r2_hidden(X0,X1)
% 1.67/0.93      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 1.67/0.93      inference(cnf_transformation,[],[f72]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_14,negated_conjecture,
% 1.67/0.93      ( ~ r2_hidden(sK0,k2_relat_1(sK1))
% 1.67/0.93      | k1_xboole_0 = k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 1.67/0.93      inference(cnf_transformation,[],[f76]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_98,plain,
% 1.67/0.93      ( ~ r2_hidden(sK0,k2_relat_1(sK1))
% 1.67/0.93      | k1_xboole_0 = k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 1.67/0.93      inference(prop_impl,[status(thm)],[c_14]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_280,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 1.67/0.93      | k2_relat_1(sK1) != X1
% 1.67/0.93      | sK0 != X0 ),
% 1.67/0.93      inference(resolution_lifted,[status(thm)],[c_7,c_98]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_281,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_280]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_5,plain,
% 1.67/0.93      ( ~ r2_hidden(X0,X1)
% 1.67/0.93      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 1.67/0.93      inference(cnf_transformation,[],[f70]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_94,plain,
% 1.67/0.93      ( ~ r2_hidden(X0,X1)
% 1.67/0.93      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 1.67/0.93      inference(prop_impl,[status(thm)],[c_5]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_15,negated_conjecture,
% 1.67/0.93      ( r2_hidden(sK0,k2_relat_1(sK1))
% 1.67/0.93      | k1_xboole_0 != k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 1.67/0.93      inference(cnf_transformation,[],[f77]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_96,plain,
% 1.67/0.93      ( r2_hidden(sK0,k2_relat_1(sK1))
% 1.67/0.93      | k1_xboole_0 != k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 1.67/0.93      inference(prop_impl,[status(thm)],[c_15]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_300,plain,
% 1.67/0.93      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 1.67/0.93      | k2_relat_1(sK1) != X1
% 1.67/0.93      | sK0 != X0 ),
% 1.67/0.93      inference(resolution_lifted,[status(thm)],[c_94,c_96]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_301,plain,
% 1.67/0.93      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_300]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_402,plain,
% 1.67/0.93      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
% 1.67/0.93      inference(prop_impl,[status(thm)],[c_301]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_432,plain,
% 1.67/0.93      ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) ),
% 1.67/0.93      inference(bin_hyper_res,[status(thm)],[c_281,c_402]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_500,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | ~ r1_xboole_0(k2_relat_1(sK1),X0)
% 1.67/0.93      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
% 1.67/0.93      | k2_relat_1(sK1) != k2_relat_1(sK1)
% 1.67/0.93      | k1_xboole_0 = X0 ),
% 1.67/0.93      inference(resolution_lifted,[status(thm)],[c_429,c_432]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_501,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | ~ r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 1.67/0.93      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_500]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_267,plain,
% 1.67/0.93      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 1.67/0.93      | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 1.67/0.93      inference(resolution,[status(thm)],[c_7,c_94]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_323,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 1.67/0.93      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X2
% 1.67/0.93      | k10_relat_1(sK1,X2) != k1_xboole_0
% 1.67/0.93      | k2_relat_1(sK1) != X1
% 1.67/0.93      | k1_xboole_0 = X2 ),
% 1.67/0.93      inference(resolution_lifted,[status(thm)],[c_267,c_200]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_324,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_relat_1(sK1))
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k1_xboole_0
% 1.67/0.93      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_323]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_326,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 1.67/0.93      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 1.67/0.93      inference(instantiation,[status(thm)],[c_324]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_503,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 1.67/0.93      inference(global_propositional_subsumption,
% 1.67/0.93                [status(thm)],
% 1.67/0.93                [c_501,c_281,c_326]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_833,plain,
% 1.67/0.93      ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 1.67/0.93      | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) = iProver_top ),
% 1.67/0.93      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_2,plain,
% 1.67/0.93      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 1.67/0.93      inference(cnf_transformation,[],[f37]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_838,plain,
% 1.67/0.93      ( r1_xboole_0(X0,X1) != iProver_top
% 1.67/0.93      | r1_xboole_0(X1,X0) = iProver_top ),
% 1.67/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1127,plain,
% 1.67/0.93      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 1.67/0.93      | r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 1.67/0.93      inference(superposition,[status(thm)],[c_833,c_838]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_282,plain,
% 1.67/0.93      ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0
% 1.67/0.93      | r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) = iProver_top ),
% 1.67/0.93      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_898,plain,
% 1.67/0.93      ( ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1))
% 1.67/0.93      | r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 1.67/0.93      inference(instantiation,[status(thm)],[c_2]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_899,plain,
% 1.67/0.93      ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_relat_1(sK1)) != iProver_top
% 1.67/0.93      | r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 1.67/0.93      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_12,plain,
% 1.67/0.93      ( r1_xboole_0(k2_relat_1(X0),X1)
% 1.67/0.93      | ~ v1_relat_1(X0)
% 1.67/0.93      | k10_relat_1(X0,X1) != k1_xboole_0 ),
% 1.67/0.93      inference(cnf_transformation,[],[f55]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_214,plain,
% 1.67/0.93      ( r1_xboole_0(k2_relat_1(X0),X1)
% 1.67/0.93      | k10_relat_1(X0,X1) != k1_xboole_0
% 1.67/0.93      | sK1 != X0 ),
% 1.67/0.93      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_215,plain,
% 1.67/0.93      ( r1_xboole_0(k2_relat_1(sK1),X0)
% 1.67/0.93      | k10_relat_1(sK1,X0) != k1_xboole_0 ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_214]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_560,plain,
% 1.67/0.93      ( r1_xboole_0(k2_relat_1(sK1),X0)
% 1.67/0.93      | k10_relat_1(sK1,X0) != k1_xboole_0 ),
% 1.67/0.93      inference(prop_impl,[status(thm)],[c_215]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1030,plain,
% 1.67/0.93      ( r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0 ),
% 1.67/0.93      inference(instantiation,[status(thm)],[c_560]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1031,plain,
% 1.67/0.93      ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 1.67/0.93      | r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 1.67/0.93      inference(predicate_to_equality,[status(thm)],[c_1030]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1130,plain,
% 1.67/0.93      ( r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 1.67/0.93      inference(global_propositional_subsumption,
% 1.67/0.93                [status(thm)],
% 1.67/0.93                [c_1127,c_282,c_899,c_1031]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_562,plain,
% 1.67/0.93      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
% 1.67/0.93      | k10_relat_1(sK1,X0) = k1_xboole_0 ),
% 1.67/0.93      inference(prop_impl,[status(thm)],[c_227]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_836,plain,
% 1.67/0.93      ( k10_relat_1(sK1,X0) = k1_xboole_0
% 1.67/0.93      | r1_xboole_0(k2_relat_1(sK1),X0) != iProver_top ),
% 1.67/0.93      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1238,plain,
% 1.67/0.93      ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 1.67/0.93      inference(superposition,[status(thm)],[c_1130,c_836]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_514,plain,
% 1.67/0.93      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
% 1.67/0.93      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 1.67/0.93      | k2_relat_1(sK1) != k2_relat_1(sK1)
% 1.67/0.93      | k1_xboole_0 = X0 ),
% 1.67/0.93      inference(resolution_lifted,[status(thm)],[c_429,c_402]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_515,plain,
% 1.67/0.93      ( ~ r1_xboole_0(k2_relat_1(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 1.67/0.93      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_514]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_351,plain,
% 1.67/0.93      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X0
% 1.67/0.93      | k10_relat_1(sK1,X0) != k1_xboole_0
% 1.67/0.93      | k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 1.67/0.93      | k2_relat_1(sK1) != k2_relat_1(sK1)
% 1.67/0.93      | k1_xboole_0 = X0 ),
% 1.67/0.93      inference(resolution_lifted,[status(thm)],[c_200,c_301]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_352,plain,
% 1.67/0.93      ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 1.67/0.93      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 1.67/0.93      inference(unflattening,[status(thm)],[c_351]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_517,plain,
% 1.67/0.93      ( k10_relat_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k1_xboole_0
% 1.67/0.93      | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 1.67/0.93      inference(global_propositional_subsumption,
% 1.67/0.93                [status(thm)],
% 1.67/0.93                [c_515,c_352]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1349,plain,
% 1.67/0.93      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 1.67/0.93      | k1_xboole_0 != k1_xboole_0 ),
% 1.67/0.93      inference(demodulation,[status(thm)],[c_1238,c_517]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1350,plain,
% 1.67/0.93      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 1.67/0.93      inference(equality_resolution_simp,[status(thm)],[c_1349]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1,plain,
% 1.67/0.93      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 1.67/0.93      inference(cnf_transformation,[],[f68]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_0,plain,
% 1.67/0.93      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 1.67/0.93      inference(cnf_transformation,[],[f67]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_941,plain,
% 1.67/0.93      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 1.67/0.93      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_3,plain,
% 1.67/0.93      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.67/0.93      inference(cnf_transformation,[],[f69]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_942,plain,
% 1.67/0.93      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 1.67/0.93      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_4,plain,
% 1.67/0.93      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.67/0.93      inference(cnf_transformation,[],[f41]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_952,plain,
% 1.67/0.93      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.67/0.93      inference(light_normalisation,[status(thm)],[c_942,c_4]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_944,plain,
% 1.67/0.93      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 1.67/0.93      inference(superposition,[status(thm)],[c_3,c_0]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_946,plain,
% 1.67/0.93      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.67/0.93      inference(light_normalisation,[status(thm)],[c_944,c_3]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_953,plain,
% 1.67/0.93      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.67/0.93      inference(demodulation,[status(thm)],[c_952,c_946]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_957,plain,
% 1.67/0.93      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.67/0.93      inference(light_normalisation,[status(thm)],[c_941,c_953]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_9,plain,
% 1.67/0.93      ( k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 1.67/0.93      inference(cnf_transformation,[],[f78]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1211,plain,
% 1.67/0.93      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 1.67/0.93      inference(demodulation,[status(thm)],[c_957,c_9]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(c_1214,plain,
% 1.67/0.93      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_xboole_0 ),
% 1.67/0.93      inference(instantiation,[status(thm)],[c_1211]) ).
% 1.67/0.93  
% 1.67/0.93  cnf(contradiction,plain,
% 1.67/0.93      ( $false ),
% 1.67/0.93      inference(minisat,[status(thm)],[c_1350,c_1214]) ).
% 1.67/0.93  
% 1.67/0.93  
% 1.67/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 1.67/0.93  
% 1.67/0.93  ------                               Statistics
% 1.67/0.93  
% 1.67/0.93  ------ General
% 1.67/0.93  
% 1.67/0.93  abstr_ref_over_cycles:                  0
% 1.67/0.93  abstr_ref_under_cycles:                 0
% 1.67/0.93  gc_basic_clause_elim:                   0
% 1.67/0.93  forced_gc_time:                         0
% 1.67/0.93  parsing_time:                           0.014
% 1.67/0.93  unif_index_cands_time:                  0.
% 1.67/0.93  unif_index_add_time:                    0.
% 1.67/0.93  orderings_time:                         0.
% 1.67/0.93  out_proof_time:                         0.01
% 1.67/0.93  total_time:                             0.077
% 1.67/0.93  num_of_symbols:                         44
% 1.67/0.93  num_of_terms:                           1026
% 1.67/0.93  
% 1.67/0.93  ------ Preprocessing
% 1.67/0.93  
% 1.67/0.93  num_of_splits:                          0
% 1.67/0.93  num_of_split_atoms:                     0
% 1.67/0.93  num_of_reused_defs:                     0
% 1.67/0.93  num_eq_ax_congr_red:                    5
% 1.67/0.93  num_of_sem_filtered_clauses:            1
% 1.67/0.93  num_of_subtypes:                        0
% 1.67/0.93  monotx_restored_types:                  0
% 1.67/0.93  sat_num_of_epr_types:                   0
% 1.67/0.93  sat_num_of_non_cyclic_types:            0
% 1.67/0.93  sat_guarded_non_collapsed_types:        0
% 1.67/0.93  num_pure_diseq_elim:                    0
% 1.67/0.93  simp_replaced_by:                       0
% 1.67/0.93  res_preprocessed:                       93
% 1.67/0.93  prep_upred:                             0
% 1.67/0.93  prep_unflattend:                        22
% 1.67/0.93  smt_new_axioms:                         0
% 1.67/0.93  pred_elim_cands:                        1
% 1.67/0.93  pred_elim:                              3
% 1.67/0.93  pred_elim_cl:                           3
% 1.67/0.93  pred_elim_cycles:                       8
% 1.67/0.93  merged_defs:                            14
% 1.67/0.93  merged_defs_ncl:                        0
% 1.67/0.93  bin_hyper_res:                          16
% 1.67/0.93  prep_cycles:                            5
% 1.67/0.93  pred_elim_time:                         0.008
% 1.67/0.93  splitting_time:                         0.
% 1.67/0.93  sem_filter_time:                        0.
% 1.67/0.93  monotx_time:                            0.
% 1.67/0.93  subtype_inf_time:                       0.
% 1.67/0.93  
% 1.67/0.93  ------ Problem properties
% 1.67/0.93  
% 1.67/0.93  clauses:                                14
% 1.67/0.93  conjectures:                            0
% 1.67/0.93  epr:                                    1
% 1.67/0.93  horn:                                   10
% 1.67/0.93  ground:                                 3
% 1.67/0.93  unary:                                  6
% 1.67/0.93  binary:                                 7
% 1.67/0.93  lits:                                   23
% 1.67/0.93  lits_eq:                                16
% 1.67/0.93  fd_pure:                                0
% 1.67/0.93  fd_pseudo:                              0
% 1.67/0.93  fd_cond:                                0
% 1.67/0.93  fd_pseudo_cond:                         1
% 1.67/0.93  ac_symbols:                             0
% 1.67/0.93  
% 1.67/0.93  ------ Propositional Solver
% 1.67/0.93  
% 1.67/0.93  prop_solver_calls:                      30
% 1.67/0.93  prop_fast_solver_calls:                 444
% 1.67/0.93  smt_solver_calls:                       0
% 1.67/0.93  smt_fast_solver_calls:                  0
% 1.67/0.93  prop_num_of_clauses:                    348
% 1.67/0.93  prop_preprocess_simplified:             2221
% 1.67/0.93  prop_fo_subsumed:                       3
% 1.67/0.93  prop_solver_time:                       0.
% 1.67/0.93  smt_solver_time:                        0.
% 1.67/0.93  smt_fast_solver_time:                   0.
% 1.67/0.93  prop_fast_solver_time:                  0.
% 1.67/0.93  prop_unsat_core_time:                   0.
% 1.67/0.93  
% 1.67/0.93  ------ QBF
% 1.67/0.93  
% 1.67/0.93  qbf_q_res:                              0
% 1.67/0.93  qbf_num_tautologies:                    0
% 1.67/0.93  qbf_prep_cycles:                        0
% 1.67/0.93  
% 1.67/0.93  ------ BMC1
% 1.67/0.93  
% 1.67/0.93  bmc1_current_bound:                     -1
% 1.67/0.93  bmc1_last_solved_bound:                 -1
% 1.67/0.93  bmc1_unsat_core_size:                   -1
% 1.67/0.93  bmc1_unsat_core_parents_size:           -1
% 1.67/0.93  bmc1_merge_next_fun:                    0
% 1.67/0.93  bmc1_unsat_core_clauses_time:           0.
% 1.67/0.93  
% 1.67/0.93  ------ Instantiation
% 1.67/0.93  
% 1.67/0.93  inst_num_of_clauses:                    123
% 1.67/0.93  inst_num_in_passive:                    48
% 1.67/0.93  inst_num_in_active:                     56
% 1.67/0.93  inst_num_in_unprocessed:                19
% 1.67/0.93  inst_num_of_loops:                      100
% 1.67/0.93  inst_num_of_learning_restarts:          0
% 1.67/0.93  inst_num_moves_active_passive:          41
% 1.67/0.93  inst_lit_activity:                      0
% 1.67/0.93  inst_lit_activity_moves:                0
% 1.67/0.93  inst_num_tautologies:                   0
% 1.67/0.93  inst_num_prop_implied:                  0
% 1.67/0.93  inst_num_existing_simplified:           0
% 1.67/0.93  inst_num_eq_res_simplified:             0
% 1.67/0.93  inst_num_child_elim:                    0
% 1.67/0.93  inst_num_of_dismatching_blockings:      14
% 1.67/0.93  inst_num_of_non_proper_insts:           86
% 1.67/0.93  inst_num_of_duplicates:                 0
% 1.67/0.93  inst_inst_num_from_inst_to_res:         0
% 1.67/0.93  inst_dismatching_checking_time:         0.
% 1.67/0.93  
% 1.67/0.93  ------ Resolution
% 1.67/0.93  
% 1.67/0.93  res_num_of_clauses:                     0
% 1.67/0.93  res_num_in_passive:                     0
% 1.67/0.93  res_num_in_active:                      0
% 1.67/0.93  res_num_of_loops:                       98
% 1.67/0.93  res_forward_subset_subsumed:            4
% 1.67/0.93  res_backward_subset_subsumed:           0
% 1.67/0.93  res_forward_subsumed:                   1
% 1.67/0.93  res_backward_subsumed:                  0
% 1.67/0.93  res_forward_subsumption_resolution:     0
% 1.67/0.93  res_backward_subsumption_resolution:    0
% 1.67/0.93  res_clause_to_clause_subsumption:       62
% 1.67/0.93  res_orphan_elimination:                 0
% 1.67/0.93  res_tautology_del:                      41
% 1.67/0.93  res_num_eq_res_simplified:              0
% 1.67/0.93  res_num_sel_changes:                    0
% 1.67/0.93  res_moves_from_active_to_pass:          0
% 1.67/0.93  
% 1.67/0.93  ------ Superposition
% 1.67/0.93  
% 1.67/0.93  sup_time_total:                         0.
% 1.67/0.93  sup_time_generating:                    0.
% 1.67/0.93  sup_time_sim_full:                      0.
% 1.67/0.93  sup_time_sim_immed:                     0.
% 1.67/0.93  
% 1.67/0.93  sup_num_of_clauses:                     17
% 1.67/0.93  sup_num_in_active:                      13
% 1.67/0.93  sup_num_in_passive:                     4
% 1.67/0.93  sup_num_of_loops:                       18
% 1.67/0.93  sup_fw_superposition:                   7
% 1.67/0.93  sup_bw_superposition:                   9
% 1.67/0.93  sup_immediate_simplified:               10
% 1.67/0.93  sup_given_eliminated:                   0
% 1.67/0.93  comparisons_done:                       0
% 1.67/0.93  comparisons_avoided:                    2
% 1.67/0.93  
% 1.67/0.93  ------ Simplifications
% 1.67/0.93  
% 1.67/0.93  
% 1.67/0.93  sim_fw_subset_subsumed:                 0
% 1.67/0.93  sim_bw_subset_subsumed:                 1
% 1.67/0.93  sim_fw_subsumed:                        1
% 1.67/0.93  sim_bw_subsumed:                        0
% 1.67/0.93  sim_fw_subsumption_res:                 0
% 1.67/0.93  sim_bw_subsumption_res:                 0
% 1.67/0.93  sim_tautology_del:                      0
% 1.67/0.93  sim_eq_tautology_del:                   6
% 1.67/0.93  sim_eq_res_simp:                        1
% 1.67/0.93  sim_fw_demodulated:                     0
% 1.67/0.93  sim_bw_demodulated:                     7
% 1.67/0.93  sim_light_normalised:                   7
% 1.67/0.93  sim_joinable_taut:                      0
% 1.67/0.93  sim_joinable_simp:                      0
% 1.67/0.93  sim_ac_normalised:                      0
% 1.67/0.93  sim_smt_subsumption:                    0
% 1.67/0.93  
%------------------------------------------------------------------------------
