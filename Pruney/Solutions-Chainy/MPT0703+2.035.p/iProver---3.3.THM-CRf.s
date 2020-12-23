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
% DateTime   : Thu Dec  3 11:52:19 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 177 expanded)
%              Number of clauses        :   44 (  48 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  210 ( 518 expanded)
%              Number of equality atoms :   75 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).

fof(f59,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f67])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

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
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_625,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,X0),sK1)
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8647,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))),sK1)
    | r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_540,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_223,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_538,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_223])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_545,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_938,plain,
    ( k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,X1)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_538,c_545])).

cnf(c_2798,plain,
    ( k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_540,c_938])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_188,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_189,plain,
    ( ~ v1_relat_1(sK2)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_193,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_189,c_16])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_217,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_218,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_588,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_193,c_218])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_541,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_544,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1771,plain,
    ( k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_relat_1(sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_541,c_544])).

cnf(c_2357,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_588,c_1771])).

cnf(c_2836,plain,
    ( k2_xboole_0(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))) = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_2798,c_2357])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_643,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_xboole_0(sK0,X2),sK1)
    | k2_xboole_0(sK0,X2) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_721,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_xboole_0(sK0,X1),sK1)
    | k2_xboole_0(sK0,X1) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_817,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | r1_tarski(k2_xboole_0(sK0,X0),sK1)
    | k2_xboole_0(sK0,X0) != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_999,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
    | r1_tarski(k2_xboole_0(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))),sK1)
    | k2_xboole_0(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_199,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_200,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_199])).

cnf(c_204,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_200,c_16])).

cnf(c_673,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_327,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_654,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8647,c_2836,c_999,c_673,c_654,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n002.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 15:17:21 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running in FOF mode
% 3.46/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/0.97  
% 3.46/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/0.97  
% 3.46/0.97  ------  iProver source info
% 3.46/0.97  
% 3.46/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.46/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/0.97  git: non_committed_changes: false
% 3.46/0.97  git: last_make_outside_of_git: false
% 3.46/0.97  
% 3.46/0.97  ------ 
% 3.46/0.97  
% 3.46/0.97  ------ Input Options
% 3.46/0.97  
% 3.46/0.97  --out_options                           all
% 3.46/0.97  --tptp_safe_out                         true
% 3.46/0.97  --problem_path                          ""
% 3.46/0.97  --include_path                          ""
% 3.46/0.97  --clausifier                            res/vclausify_rel
% 3.46/0.97  --clausifier_options                    --mode clausify
% 3.46/0.97  --stdin                                 false
% 3.46/0.97  --stats_out                             all
% 3.46/0.97  
% 3.46/0.97  ------ General Options
% 3.46/0.97  
% 3.46/0.97  --fof                                   false
% 3.46/0.97  --time_out_real                         305.
% 3.46/0.97  --time_out_virtual                      -1.
% 3.46/0.97  --symbol_type_check                     false
% 3.46/0.97  --clausify_out                          false
% 3.46/0.97  --sig_cnt_out                           false
% 3.46/0.97  --trig_cnt_out                          false
% 3.46/0.97  --trig_cnt_out_tolerance                1.
% 3.46/0.97  --trig_cnt_out_sk_spl                   false
% 3.46/0.97  --abstr_cl_out                          false
% 3.46/0.97  
% 3.46/0.97  ------ Global Options
% 3.46/0.97  
% 3.46/0.97  --schedule                              default
% 3.46/0.97  --add_important_lit                     false
% 3.46/0.97  --prop_solver_per_cl                    1000
% 3.46/0.97  --min_unsat_core                        false
% 3.46/0.97  --soft_assumptions                      false
% 3.46/0.97  --soft_lemma_size                       3
% 3.46/0.97  --prop_impl_unit_size                   0
% 3.46/0.97  --prop_impl_unit                        []
% 3.46/0.97  --share_sel_clauses                     true
% 3.46/0.97  --reset_solvers                         false
% 3.46/0.97  --bc_imp_inh                            [conj_cone]
% 3.46/0.97  --conj_cone_tolerance                   3.
% 3.46/0.97  --extra_neg_conj                        none
% 3.46/0.97  --large_theory_mode                     true
% 3.46/0.97  --prolific_symb_bound                   200
% 3.46/0.97  --lt_threshold                          2000
% 3.46/0.97  --clause_weak_htbl                      true
% 3.46/0.97  --gc_record_bc_elim                     false
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing Options
% 3.46/0.97  
% 3.46/0.97  --preprocessing_flag                    true
% 3.46/0.97  --time_out_prep_mult                    0.1
% 3.46/0.97  --splitting_mode                        input
% 3.46/0.97  --splitting_grd                         true
% 3.46/0.97  --splitting_cvd                         false
% 3.46/0.97  --splitting_cvd_svl                     false
% 3.46/0.97  --splitting_nvd                         32
% 3.46/0.97  --sub_typing                            true
% 3.46/0.97  --prep_gs_sim                           true
% 3.46/0.97  --prep_unflatten                        true
% 3.46/0.97  --prep_res_sim                          true
% 3.46/0.97  --prep_upred                            true
% 3.46/0.97  --prep_sem_filter                       exhaustive
% 3.46/0.97  --prep_sem_filter_out                   false
% 3.46/0.97  --pred_elim                             true
% 3.46/0.97  --res_sim_input                         true
% 3.46/0.97  --eq_ax_congr_red                       true
% 3.46/0.97  --pure_diseq_elim                       true
% 3.46/0.97  --brand_transform                       false
% 3.46/0.97  --non_eq_to_eq                          false
% 3.46/0.97  --prep_def_merge                        true
% 3.46/0.97  --prep_def_merge_prop_impl              false
% 3.46/0.97  --prep_def_merge_mbd                    true
% 3.46/0.97  --prep_def_merge_tr_red                 false
% 3.46/0.97  --prep_def_merge_tr_cl                  false
% 3.46/0.97  --smt_preprocessing                     true
% 3.46/0.97  --smt_ac_axioms                         fast
% 3.46/0.97  --preprocessed_out                      false
% 3.46/0.97  --preprocessed_stats                    false
% 3.46/0.97  
% 3.46/0.97  ------ Abstraction refinement Options
% 3.46/0.97  
% 3.46/0.97  --abstr_ref                             []
% 3.46/0.97  --abstr_ref_prep                        false
% 3.46/0.97  --abstr_ref_until_sat                   false
% 3.46/0.97  --abstr_ref_sig_restrict                funpre
% 3.46/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/0.97  --abstr_ref_under                       []
% 3.46/0.97  
% 3.46/0.97  ------ SAT Options
% 3.46/0.97  
% 3.46/0.97  --sat_mode                              false
% 3.46/0.97  --sat_fm_restart_options                ""
% 3.46/0.97  --sat_gr_def                            false
% 3.46/0.97  --sat_epr_types                         true
% 3.46/0.97  --sat_non_cyclic_types                  false
% 3.46/0.97  --sat_finite_models                     false
% 3.46/0.97  --sat_fm_lemmas                         false
% 3.46/0.97  --sat_fm_prep                           false
% 3.46/0.97  --sat_fm_uc_incr                        true
% 3.46/0.97  --sat_out_model                         small
% 3.46/0.97  --sat_out_clauses                       false
% 3.46/0.97  
% 3.46/0.97  ------ QBF Options
% 3.46/0.97  
% 3.46/0.97  --qbf_mode                              false
% 3.46/0.97  --qbf_elim_univ                         false
% 3.46/0.97  --qbf_dom_inst                          none
% 3.46/0.97  --qbf_dom_pre_inst                      false
% 3.46/0.97  --qbf_sk_in                             false
% 3.46/0.97  --qbf_pred_elim                         true
% 3.46/0.97  --qbf_split                             512
% 3.46/0.97  
% 3.46/0.97  ------ BMC1 Options
% 3.46/0.97  
% 3.46/0.97  --bmc1_incremental                      false
% 3.46/0.97  --bmc1_axioms                           reachable_all
% 3.46/0.97  --bmc1_min_bound                        0
% 3.46/0.97  --bmc1_max_bound                        -1
% 3.46/0.97  --bmc1_max_bound_default                -1
% 3.46/0.97  --bmc1_symbol_reachability              true
% 3.46/0.97  --bmc1_property_lemmas                  false
% 3.46/0.97  --bmc1_k_induction                      false
% 3.46/0.97  --bmc1_non_equiv_states                 false
% 3.46/0.97  --bmc1_deadlock                         false
% 3.46/0.97  --bmc1_ucm                              false
% 3.46/0.97  --bmc1_add_unsat_core                   none
% 3.46/0.97  --bmc1_unsat_core_children              false
% 3.46/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/0.97  --bmc1_out_stat                         full
% 3.46/0.97  --bmc1_ground_init                      false
% 3.46/0.97  --bmc1_pre_inst_next_state              false
% 3.46/0.97  --bmc1_pre_inst_state                   false
% 3.46/0.97  --bmc1_pre_inst_reach_state             false
% 3.46/0.97  --bmc1_out_unsat_core                   false
% 3.46/0.97  --bmc1_aig_witness_out                  false
% 3.46/0.97  --bmc1_verbose                          false
% 3.46/0.97  --bmc1_dump_clauses_tptp                false
% 3.46/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.46/0.97  --bmc1_dump_file                        -
% 3.46/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.46/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.46/0.97  --bmc1_ucm_extend_mode                  1
% 3.46/0.97  --bmc1_ucm_init_mode                    2
% 3.46/0.97  --bmc1_ucm_cone_mode                    none
% 3.46/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.46/0.97  --bmc1_ucm_relax_model                  4
% 3.46/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.46/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/0.97  --bmc1_ucm_layered_model                none
% 3.46/0.97  --bmc1_ucm_max_lemma_size               10
% 3.46/0.97  
% 3.46/0.97  ------ AIG Options
% 3.46/0.97  
% 3.46/0.97  --aig_mode                              false
% 3.46/0.97  
% 3.46/0.97  ------ Instantiation Options
% 3.46/0.97  
% 3.46/0.97  --instantiation_flag                    true
% 3.46/0.97  --inst_sos_flag                         false
% 3.46/0.97  --inst_sos_phase                        true
% 3.46/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/0.97  --inst_lit_sel_side                     num_symb
% 3.46/0.97  --inst_solver_per_active                1400
% 3.46/0.97  --inst_solver_calls_frac                1.
% 3.46/0.97  --inst_passive_queue_type               priority_queues
% 3.46/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/0.97  --inst_passive_queues_freq              [25;2]
% 3.46/0.97  --inst_dismatching                      true
% 3.46/0.97  --inst_eager_unprocessed_to_passive     true
% 3.46/0.97  --inst_prop_sim_given                   true
% 3.46/0.97  --inst_prop_sim_new                     false
% 3.46/0.97  --inst_subs_new                         false
% 3.46/0.97  --inst_eq_res_simp                      false
% 3.46/0.97  --inst_subs_given                       false
% 3.46/0.97  --inst_orphan_elimination               true
% 3.46/0.97  --inst_learning_loop_flag               true
% 3.46/0.97  --inst_learning_start                   3000
% 3.46/0.97  --inst_learning_factor                  2
% 3.46/0.97  --inst_start_prop_sim_after_learn       3
% 3.46/0.97  --inst_sel_renew                        solver
% 3.46/0.97  --inst_lit_activity_flag                true
% 3.46/0.97  --inst_restr_to_given                   false
% 3.46/0.97  --inst_activity_threshold               500
% 3.46/0.97  --inst_out_proof                        true
% 3.46/0.97  
% 3.46/0.97  ------ Resolution Options
% 3.46/0.97  
% 3.46/0.97  --resolution_flag                       true
% 3.46/0.97  --res_lit_sel                           adaptive
% 3.46/0.97  --res_lit_sel_side                      none
% 3.46/0.97  --res_ordering                          kbo
% 3.46/0.97  --res_to_prop_solver                    active
% 3.46/0.97  --res_prop_simpl_new                    false
% 3.46/0.97  --res_prop_simpl_given                  true
% 3.46/0.97  --res_passive_queue_type                priority_queues
% 3.46/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/0.97  --res_passive_queues_freq               [15;5]
% 3.46/0.97  --res_forward_subs                      full
% 3.46/0.97  --res_backward_subs                     full
% 3.46/0.97  --res_forward_subs_resolution           true
% 3.46/0.97  --res_backward_subs_resolution          true
% 3.46/0.97  --res_orphan_elimination                true
% 3.46/0.97  --res_time_limit                        2.
% 3.46/0.97  --res_out_proof                         true
% 3.46/0.97  
% 3.46/0.97  ------ Superposition Options
% 3.46/0.97  
% 3.46/0.97  --superposition_flag                    true
% 3.46/0.97  --sup_passive_queue_type                priority_queues
% 3.46/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.46/0.97  --demod_completeness_check              fast
% 3.46/0.97  --demod_use_ground                      true
% 3.46/0.97  --sup_to_prop_solver                    passive
% 3.46/0.97  --sup_prop_simpl_new                    true
% 3.46/0.97  --sup_prop_simpl_given                  true
% 3.46/0.97  --sup_fun_splitting                     false
% 3.46/0.97  --sup_smt_interval                      50000
% 3.46/0.97  
% 3.46/0.97  ------ Superposition Simplification Setup
% 3.46/0.97  
% 3.46/0.97  --sup_indices_passive                   []
% 3.46/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_full_bw                           [BwDemod]
% 3.46/0.97  --sup_immed_triv                        [TrivRules]
% 3.46/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_immed_bw_main                     []
% 3.46/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.97  
% 3.46/0.97  ------ Combination Options
% 3.46/0.97  
% 3.46/0.97  --comb_res_mult                         3
% 3.46/0.97  --comb_sup_mult                         2
% 3.46/0.97  --comb_inst_mult                        10
% 3.46/0.97  
% 3.46/0.97  ------ Debug Options
% 3.46/0.97  
% 3.46/0.97  --dbg_backtrace                         false
% 3.46/0.97  --dbg_dump_prop_clauses                 false
% 3.46/0.97  --dbg_dump_prop_clauses_file            -
% 3.46/0.97  --dbg_out_stat                          false
% 3.46/0.97  ------ Parsing...
% 3.46/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/0.97  ------ Proving...
% 3.46/0.97  ------ Problem Properties 
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  clauses                                 14
% 3.46/0.97  conjectures                             3
% 3.46/0.97  EPR                                     3
% 3.46/0.97  Horn                                    14
% 3.46/0.97  unary                                   7
% 3.46/0.97  binary                                  6
% 3.46/0.97  lits                                    22
% 3.46/0.97  lits eq                                 5
% 3.46/0.97  fd_pure                                 0
% 3.46/0.97  fd_pseudo                               0
% 3.46/0.97  fd_cond                                 0
% 3.46/0.97  fd_pseudo_cond                          1
% 3.46/0.97  AC symbols                              0
% 3.46/0.97  
% 3.46/0.97  ------ Schedule dynamic 5 is on 
% 3.46/0.97  
% 3.46/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  ------ 
% 3.46/0.97  Current options:
% 3.46/0.97  ------ 
% 3.46/0.97  
% 3.46/0.97  ------ Input Options
% 3.46/0.97  
% 3.46/0.97  --out_options                           all
% 3.46/0.97  --tptp_safe_out                         true
% 3.46/0.97  --problem_path                          ""
% 3.46/0.97  --include_path                          ""
% 3.46/0.97  --clausifier                            res/vclausify_rel
% 3.46/0.97  --clausifier_options                    --mode clausify
% 3.46/0.97  --stdin                                 false
% 3.46/0.97  --stats_out                             all
% 3.46/0.97  
% 3.46/0.97  ------ General Options
% 3.46/0.97  
% 3.46/0.97  --fof                                   false
% 3.46/0.97  --time_out_real                         305.
% 3.46/0.97  --time_out_virtual                      -1.
% 3.46/0.97  --symbol_type_check                     false
% 3.46/0.97  --clausify_out                          false
% 3.46/0.97  --sig_cnt_out                           false
% 3.46/0.97  --trig_cnt_out                          false
% 3.46/0.97  --trig_cnt_out_tolerance                1.
% 3.46/0.97  --trig_cnt_out_sk_spl                   false
% 3.46/0.97  --abstr_cl_out                          false
% 3.46/0.97  
% 3.46/0.97  ------ Global Options
% 3.46/0.97  
% 3.46/0.97  --schedule                              default
% 3.46/0.97  --add_important_lit                     false
% 3.46/0.97  --prop_solver_per_cl                    1000
% 3.46/0.97  --min_unsat_core                        false
% 3.46/0.97  --soft_assumptions                      false
% 3.46/0.97  --soft_lemma_size                       3
% 3.46/0.97  --prop_impl_unit_size                   0
% 3.46/0.97  --prop_impl_unit                        []
% 3.46/0.97  --share_sel_clauses                     true
% 3.46/0.97  --reset_solvers                         false
% 3.46/0.97  --bc_imp_inh                            [conj_cone]
% 3.46/0.97  --conj_cone_tolerance                   3.
% 3.46/0.97  --extra_neg_conj                        none
% 3.46/0.97  --large_theory_mode                     true
% 3.46/0.97  --prolific_symb_bound                   200
% 3.46/0.97  --lt_threshold                          2000
% 3.46/0.97  --clause_weak_htbl                      true
% 3.46/0.97  --gc_record_bc_elim                     false
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing Options
% 3.46/0.97  
% 3.46/0.97  --preprocessing_flag                    true
% 3.46/0.97  --time_out_prep_mult                    0.1
% 3.46/0.97  --splitting_mode                        input
% 3.46/0.97  --splitting_grd                         true
% 3.46/0.97  --splitting_cvd                         false
% 3.46/0.97  --splitting_cvd_svl                     false
% 3.46/0.97  --splitting_nvd                         32
% 3.46/0.97  --sub_typing                            true
% 3.46/0.97  --prep_gs_sim                           true
% 3.46/0.97  --prep_unflatten                        true
% 3.46/0.97  --prep_res_sim                          true
% 3.46/0.97  --prep_upred                            true
% 3.46/0.97  --prep_sem_filter                       exhaustive
% 3.46/0.97  --prep_sem_filter_out                   false
% 3.46/0.97  --pred_elim                             true
% 3.46/0.97  --res_sim_input                         true
% 3.46/0.97  --eq_ax_congr_red                       true
% 3.46/0.97  --pure_diseq_elim                       true
% 3.46/0.97  --brand_transform                       false
% 3.46/0.97  --non_eq_to_eq                          false
% 3.46/0.97  --prep_def_merge                        true
% 3.46/0.97  --prep_def_merge_prop_impl              false
% 3.46/0.97  --prep_def_merge_mbd                    true
% 3.46/0.97  --prep_def_merge_tr_red                 false
% 3.46/0.97  --prep_def_merge_tr_cl                  false
% 3.46/0.97  --smt_preprocessing                     true
% 3.46/0.97  --smt_ac_axioms                         fast
% 3.46/0.97  --preprocessed_out                      false
% 3.46/0.97  --preprocessed_stats                    false
% 3.46/0.97  
% 3.46/0.97  ------ Abstraction refinement Options
% 3.46/0.97  
% 3.46/0.97  --abstr_ref                             []
% 3.46/0.97  --abstr_ref_prep                        false
% 3.46/0.97  --abstr_ref_until_sat                   false
% 3.46/0.97  --abstr_ref_sig_restrict                funpre
% 3.46/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/0.97  --abstr_ref_under                       []
% 3.46/0.97  
% 3.46/0.97  ------ SAT Options
% 3.46/0.97  
% 3.46/0.97  --sat_mode                              false
% 3.46/0.97  --sat_fm_restart_options                ""
% 3.46/0.97  --sat_gr_def                            false
% 3.46/0.97  --sat_epr_types                         true
% 3.46/0.97  --sat_non_cyclic_types                  false
% 3.46/0.97  --sat_finite_models                     false
% 3.46/0.97  --sat_fm_lemmas                         false
% 3.46/0.97  --sat_fm_prep                           false
% 3.46/0.97  --sat_fm_uc_incr                        true
% 3.46/0.97  --sat_out_model                         small
% 3.46/0.97  --sat_out_clauses                       false
% 3.46/0.97  
% 3.46/0.97  ------ QBF Options
% 3.46/0.97  
% 3.46/0.97  --qbf_mode                              false
% 3.46/0.97  --qbf_elim_univ                         false
% 3.46/0.97  --qbf_dom_inst                          none
% 3.46/0.97  --qbf_dom_pre_inst                      false
% 3.46/0.97  --qbf_sk_in                             false
% 3.46/0.97  --qbf_pred_elim                         true
% 3.46/0.97  --qbf_split                             512
% 3.46/0.97  
% 3.46/0.97  ------ BMC1 Options
% 3.46/0.97  
% 3.46/0.97  --bmc1_incremental                      false
% 3.46/0.97  --bmc1_axioms                           reachable_all
% 3.46/0.97  --bmc1_min_bound                        0
% 3.46/0.97  --bmc1_max_bound                        -1
% 3.46/0.97  --bmc1_max_bound_default                -1
% 3.46/0.97  --bmc1_symbol_reachability              true
% 3.46/0.97  --bmc1_property_lemmas                  false
% 3.46/0.97  --bmc1_k_induction                      false
% 3.46/0.97  --bmc1_non_equiv_states                 false
% 3.46/0.97  --bmc1_deadlock                         false
% 3.46/0.97  --bmc1_ucm                              false
% 3.46/0.97  --bmc1_add_unsat_core                   none
% 3.46/0.97  --bmc1_unsat_core_children              false
% 3.46/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/0.97  --bmc1_out_stat                         full
% 3.46/0.97  --bmc1_ground_init                      false
% 3.46/0.97  --bmc1_pre_inst_next_state              false
% 3.46/0.97  --bmc1_pre_inst_state                   false
% 3.46/0.97  --bmc1_pre_inst_reach_state             false
% 3.46/0.97  --bmc1_out_unsat_core                   false
% 3.46/0.97  --bmc1_aig_witness_out                  false
% 3.46/0.97  --bmc1_verbose                          false
% 3.46/0.97  --bmc1_dump_clauses_tptp                false
% 3.46/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.46/0.97  --bmc1_dump_file                        -
% 3.46/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.46/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.46/0.97  --bmc1_ucm_extend_mode                  1
% 3.46/0.97  --bmc1_ucm_init_mode                    2
% 3.46/0.97  --bmc1_ucm_cone_mode                    none
% 3.46/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.46/0.97  --bmc1_ucm_relax_model                  4
% 3.46/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.46/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/0.97  --bmc1_ucm_layered_model                none
% 3.46/0.97  --bmc1_ucm_max_lemma_size               10
% 3.46/0.97  
% 3.46/0.97  ------ AIG Options
% 3.46/0.97  
% 3.46/0.97  --aig_mode                              false
% 3.46/0.97  
% 3.46/0.97  ------ Instantiation Options
% 3.46/0.97  
% 3.46/0.97  --instantiation_flag                    true
% 3.46/0.97  --inst_sos_flag                         false
% 3.46/0.97  --inst_sos_phase                        true
% 3.46/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/0.97  --inst_lit_sel_side                     none
% 3.46/0.97  --inst_solver_per_active                1400
% 3.46/0.97  --inst_solver_calls_frac                1.
% 3.46/0.97  --inst_passive_queue_type               priority_queues
% 3.46/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/0.97  --inst_passive_queues_freq              [25;2]
% 3.46/0.97  --inst_dismatching                      true
% 3.46/0.97  --inst_eager_unprocessed_to_passive     true
% 3.46/0.97  --inst_prop_sim_given                   true
% 3.46/0.97  --inst_prop_sim_new                     false
% 3.46/0.97  --inst_subs_new                         false
% 3.46/0.97  --inst_eq_res_simp                      false
% 3.46/0.97  --inst_subs_given                       false
% 3.46/0.97  --inst_orphan_elimination               true
% 3.46/0.97  --inst_learning_loop_flag               true
% 3.46/0.97  --inst_learning_start                   3000
% 3.46/0.97  --inst_learning_factor                  2
% 3.46/0.97  --inst_start_prop_sim_after_learn       3
% 3.46/0.97  --inst_sel_renew                        solver
% 3.46/0.97  --inst_lit_activity_flag                true
% 3.46/0.97  --inst_restr_to_given                   false
% 3.46/0.97  --inst_activity_threshold               500
% 3.46/0.97  --inst_out_proof                        true
% 3.46/0.97  
% 3.46/0.97  ------ Resolution Options
% 3.46/0.97  
% 3.46/0.97  --resolution_flag                       false
% 3.46/0.97  --res_lit_sel                           adaptive
% 3.46/0.97  --res_lit_sel_side                      none
% 3.46/0.97  --res_ordering                          kbo
% 3.46/0.97  --res_to_prop_solver                    active
% 3.46/0.97  --res_prop_simpl_new                    false
% 3.46/0.97  --res_prop_simpl_given                  true
% 3.46/0.97  --res_passive_queue_type                priority_queues
% 3.46/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/0.97  --res_passive_queues_freq               [15;5]
% 3.46/0.97  --res_forward_subs                      full
% 3.46/0.97  --res_backward_subs                     full
% 3.46/0.97  --res_forward_subs_resolution           true
% 3.46/0.97  --res_backward_subs_resolution          true
% 3.46/0.97  --res_orphan_elimination                true
% 3.46/0.97  --res_time_limit                        2.
% 3.46/0.97  --res_out_proof                         true
% 3.46/0.97  
% 3.46/0.97  ------ Superposition Options
% 3.46/0.97  
% 3.46/0.97  --superposition_flag                    true
% 3.46/0.97  --sup_passive_queue_type                priority_queues
% 3.46/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.46/0.97  --demod_completeness_check              fast
% 3.46/0.97  --demod_use_ground                      true
% 3.46/0.97  --sup_to_prop_solver                    passive
% 3.46/0.97  --sup_prop_simpl_new                    true
% 3.46/0.97  --sup_prop_simpl_given                  true
% 3.46/0.97  --sup_fun_splitting                     false
% 3.46/0.97  --sup_smt_interval                      50000
% 3.46/0.97  
% 3.46/0.97  ------ Superposition Simplification Setup
% 3.46/0.97  
% 3.46/0.97  --sup_indices_passive                   []
% 3.46/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.46/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_full_bw                           [BwDemod]
% 3.46/0.97  --sup_immed_triv                        [TrivRules]
% 3.46/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_immed_bw_main                     []
% 3.46/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.46/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.46/0.97  
% 3.46/0.97  ------ Combination Options
% 3.46/0.97  
% 3.46/0.97  --comb_res_mult                         3
% 3.46/0.97  --comb_sup_mult                         2
% 3.46/0.97  --comb_inst_mult                        10
% 3.46/0.97  
% 3.46/0.97  ------ Debug Options
% 3.46/0.97  
% 3.46/0.97  --dbg_backtrace                         false
% 3.46/0.97  --dbg_dump_prop_clauses                 false
% 3.46/0.97  --dbg_dump_prop_clauses_file            -
% 3.46/0.97  --dbg_out_stat                          false
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  ------ Proving...
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  % SZS status Theorem for theBenchmark.p
% 3.46/0.97  
% 3.46/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/0.97  
% 3.46/0.97  fof(f3,axiom,(
% 3.46/0.97    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f21,plain,(
% 3.46/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.46/0.97    inference(ennf_transformation,[],[f3])).
% 3.46/0.97  
% 3.46/0.97  fof(f42,plain,(
% 3.46/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f21])).
% 3.46/0.97  
% 3.46/0.97  fof(f18,conjecture,(
% 3.46/0.97    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f19,negated_conjecture,(
% 3.46/0.97    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.46/0.97    inference(negated_conjecture,[],[f18])).
% 3.46/0.97  
% 3.46/0.97  fof(f32,plain,(
% 3.46/0.97    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.46/0.97    inference(ennf_transformation,[],[f19])).
% 3.46/0.97  
% 3.46/0.97  fof(f33,plain,(
% 3.46/0.97    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.46/0.97    inference(flattening,[],[f32])).
% 3.46/0.97  
% 3.46/0.97  fof(f36,plain,(
% 3.46/0.97    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.46/0.97    introduced(choice_axiom,[])).
% 3.46/0.97  
% 3.46/0.97  fof(f37,plain,(
% 3.46/0.97    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.46/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36])).
% 3.46/0.97  
% 3.46/0.97  fof(f59,plain,(
% 3.46/0.97    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 3.46/0.97    inference(cnf_transformation,[],[f37])).
% 3.46/0.97  
% 3.46/0.97  fof(f15,axiom,(
% 3.46/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f26,plain,(
% 3.46/0.97    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.46/0.97    inference(ennf_transformation,[],[f15])).
% 3.46/0.97  
% 3.46/0.97  fof(f27,plain,(
% 3.46/0.97    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.46/0.97    inference(flattening,[],[f26])).
% 3.46/0.97  
% 3.46/0.97  fof(f54,plain,(
% 3.46/0.97    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f27])).
% 3.46/0.97  
% 3.46/0.97  fof(f57,plain,(
% 3.46/0.97    v1_relat_1(sK2)),
% 3.46/0.97    inference(cnf_transformation,[],[f37])).
% 3.46/0.97  
% 3.46/0.97  fof(f4,axiom,(
% 3.46/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f22,plain,(
% 3.46/0.97    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.46/0.97    inference(ennf_transformation,[],[f4])).
% 3.46/0.97  
% 3.46/0.97  fof(f43,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f22])).
% 3.46/0.97  
% 3.46/0.97  fof(f17,axiom,(
% 3.46/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f30,plain,(
% 3.46/0.97    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.46/0.97    inference(ennf_transformation,[],[f17])).
% 3.46/0.97  
% 3.46/0.97  fof(f31,plain,(
% 3.46/0.97    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.46/0.97    inference(flattening,[],[f30])).
% 3.46/0.97  
% 3.46/0.97  fof(f56,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f31])).
% 3.46/0.97  
% 3.46/0.97  fof(f13,axiom,(
% 3.46/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f52,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.46/0.97    inference(cnf_transformation,[],[f13])).
% 3.46/0.97  
% 3.46/0.97  fof(f7,axiom,(
% 3.46/0.97    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f46,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f7])).
% 3.46/0.97  
% 3.46/0.97  fof(f8,axiom,(
% 3.46/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f47,plain,(
% 3.46/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f8])).
% 3.46/0.97  
% 3.46/0.97  fof(f9,axiom,(
% 3.46/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f48,plain,(
% 3.46/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f9])).
% 3.46/0.97  
% 3.46/0.97  fof(f10,axiom,(
% 3.46/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f49,plain,(
% 3.46/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f10])).
% 3.46/0.97  
% 3.46/0.97  fof(f11,axiom,(
% 3.46/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f50,plain,(
% 3.46/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f11])).
% 3.46/0.97  
% 3.46/0.97  fof(f12,axiom,(
% 3.46/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f51,plain,(
% 3.46/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f12])).
% 3.46/0.97  
% 3.46/0.97  fof(f62,plain,(
% 3.46/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.46/0.97    inference(definition_unfolding,[],[f50,f51])).
% 3.46/0.97  
% 3.46/0.97  fof(f63,plain,(
% 3.46/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.46/0.97    inference(definition_unfolding,[],[f49,f62])).
% 3.46/0.97  
% 3.46/0.97  fof(f64,plain,(
% 3.46/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.46/0.97    inference(definition_unfolding,[],[f48,f63])).
% 3.46/0.97  
% 3.46/0.97  fof(f65,plain,(
% 3.46/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.46/0.97    inference(definition_unfolding,[],[f47,f64])).
% 3.46/0.97  
% 3.46/0.97  fof(f66,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.46/0.97    inference(definition_unfolding,[],[f46,f65])).
% 3.46/0.97  
% 3.46/0.97  fof(f67,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.46/0.97    inference(definition_unfolding,[],[f52,f66])).
% 3.46/0.97  
% 3.46/0.97  fof(f69,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.46/0.97    inference(definition_unfolding,[],[f56,f67])).
% 3.46/0.97  
% 3.46/0.97  fof(f58,plain,(
% 3.46/0.97    v1_funct_1(sK2)),
% 3.46/0.97    inference(cnf_transformation,[],[f37])).
% 3.46/0.97  
% 3.46/0.97  fof(f14,axiom,(
% 3.46/0.97    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f25,plain,(
% 3.46/0.97    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.46/0.97    inference(ennf_transformation,[],[f14])).
% 3.46/0.97  
% 3.46/0.97  fof(f53,plain,(
% 3.46/0.97    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f25])).
% 3.46/0.97  
% 3.46/0.97  fof(f60,plain,(
% 3.46/0.97    r1_tarski(sK0,k2_relat_1(sK2))),
% 3.46/0.97    inference(cnf_transformation,[],[f37])).
% 3.46/0.97  
% 3.46/0.97  fof(f5,axiom,(
% 3.46/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f23,plain,(
% 3.46/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.46/0.97    inference(ennf_transformation,[],[f5])).
% 3.46/0.97  
% 3.46/0.97  fof(f44,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f23])).
% 3.46/0.97  
% 3.46/0.97  fof(f68,plain,(
% 3.46/0.97    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.46/0.97    inference(definition_unfolding,[],[f44,f67])).
% 3.46/0.97  
% 3.46/0.97  fof(f16,axiom,(
% 3.46/0.97    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.46/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.46/0.97  
% 3.46/0.97  fof(f28,plain,(
% 3.46/0.97    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.46/0.97    inference(ennf_transformation,[],[f16])).
% 3.46/0.97  
% 3.46/0.97  fof(f29,plain,(
% 3.46/0.97    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.46/0.97    inference(flattening,[],[f28])).
% 3.46/0.97  
% 3.46/0.97  fof(f55,plain,(
% 3.46/0.97    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.46/0.97    inference(cnf_transformation,[],[f29])).
% 3.46/0.97  
% 3.46/0.97  fof(f61,plain,(
% 3.46/0.97    ~r1_tarski(sK0,sK1)),
% 3.46/0.97    inference(cnf_transformation,[],[f37])).
% 3.46/0.97  
% 3.46/0.97  cnf(c_4,plain,
% 3.46/0.97      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 3.46/0.97      inference(cnf_transformation,[],[f42]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_625,plain,
% 3.46/0.97      ( ~ r1_tarski(k2_xboole_0(sK0,X0),sK1) | r1_tarski(sK0,sK1) ),
% 3.46/0.97      inference(instantiation,[status(thm)],[c_4]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_8647,plain,
% 3.46/0.97      ( ~ r1_tarski(k2_xboole_0(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))),sK1)
% 3.46/0.97      | r1_tarski(sK0,sK1) ),
% 3.46/0.97      inference(instantiation,[status(thm)],[c_625]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_14,negated_conjecture,
% 3.46/0.97      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 3.46/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_540,plain,
% 3.46/0.97      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 3.46/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_9,plain,
% 3.46/0.97      ( ~ r1_tarski(X0,X1)
% 3.46/0.97      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.46/0.97      | ~ v1_relat_1(X2) ),
% 3.46/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_16,negated_conjecture,
% 3.46/0.97      ( v1_relat_1(sK2) ),
% 3.46/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_222,plain,
% 3.46/0.97      ( ~ r1_tarski(X0,X1)
% 3.46/0.97      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.46/0.97      | sK2 != X2 ),
% 3.46/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_223,plain,
% 3.46/0.97      ( ~ r1_tarski(X0,X1)
% 3.46/0.97      | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
% 3.46/0.97      inference(unflattening,[status(thm)],[c_222]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_538,plain,
% 3.46/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.46/0.97      | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = iProver_top ),
% 3.46/0.97      inference(predicate_to_equality,[status(thm)],[c_223]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_5,plain,
% 3.46/0.97      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.46/0.97      inference(cnf_transformation,[],[f43]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_545,plain,
% 3.46/0.97      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.46/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_938,plain,
% 3.46/0.97      ( k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,X1)
% 3.46/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.46/0.97      inference(superposition,[status(thm)],[c_538,c_545]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_2798,plain,
% 3.46/0.97      ( k2_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))) = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
% 3.46/0.97      inference(superposition,[status(thm)],[c_540,c_938]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_11,plain,
% 3.46/0.97      ( ~ v1_funct_1(X0)
% 3.46/0.97      | ~ v1_relat_1(X0)
% 3.46/0.97      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 3.46/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_15,negated_conjecture,
% 3.46/0.97      ( v1_funct_1(sK2) ),
% 3.46/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_188,plain,
% 3.46/0.97      ( ~ v1_relat_1(X0)
% 3.46/0.97      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 3.46/0.97      | sK2 != X0 ),
% 3.46/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_189,plain,
% 3.46/0.97      ( ~ v1_relat_1(sK2)
% 3.46/0.97      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 3.46/0.97      inference(unflattening,[status(thm)],[c_188]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_193,plain,
% 3.46/0.97      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 3.46/0.97      inference(global_propositional_subsumption,
% 3.46/0.97                [status(thm)],
% 3.46/0.97                [c_189,c_16]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_8,plain,
% 3.46/0.97      ( ~ v1_relat_1(X0)
% 3.46/0.97      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.46/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_217,plain,
% 3.46/0.97      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK2 != X0 ),
% 3.46/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_218,plain,
% 3.46/0.97      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.46/0.97      inference(unflattening,[status(thm)],[c_217]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_588,plain,
% 3.46/0.97      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_relat_1(sK2))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 3.46/0.97      inference(light_normalisation,[status(thm)],[c_193,c_218]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_13,negated_conjecture,
% 3.46/0.97      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 3.46/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_541,plain,
% 3.46/0.97      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 3.46/0.97      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_6,plain,
% 3.46/0.97      ( ~ r1_tarski(X0,X1)
% 3.46/0.97      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 3.46/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_544,plain,
% 3.46/0.97      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 3.46/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.46/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_1771,plain,
% 3.46/0.97      ( k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k2_relat_1(sK2))) = sK0 ),
% 3.46/0.97      inference(superposition,[status(thm)],[c_541,c_544]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_2357,plain,
% 3.46/0.97      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 3.46/0.97      inference(superposition,[status(thm)],[c_588,c_1771]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_2836,plain,
% 3.46/0.97      ( k2_xboole_0(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))) = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
% 3.46/0.97      inference(light_normalisation,[status(thm)],[c_2798,c_2357]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_329,plain,
% 3.46/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.46/0.97      theory(equality) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_643,plain,
% 3.46/0.97      ( ~ r1_tarski(X0,X1)
% 3.46/0.97      | r1_tarski(k2_xboole_0(sK0,X2),sK1)
% 3.46/0.97      | k2_xboole_0(sK0,X2) != X0
% 3.46/0.97      | sK1 != X1 ),
% 3.46/0.97      inference(instantiation,[status(thm)],[c_329]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_721,plain,
% 3.46/0.97      ( ~ r1_tarski(X0,sK1)
% 3.46/0.97      | r1_tarski(k2_xboole_0(sK0,X1),sK1)
% 3.46/0.97      | k2_xboole_0(sK0,X1) != X0
% 3.46/0.97      | sK1 != sK1 ),
% 3.46/0.97      inference(instantiation,[status(thm)],[c_643]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_817,plain,
% 3.46/0.97      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
% 3.46/0.97      | r1_tarski(k2_xboole_0(sK0,X0),sK1)
% 3.46/0.97      | k2_xboole_0(sK0,X0) != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
% 3.46/0.97      | sK1 != sK1 ),
% 3.46/0.97      inference(instantiation,[status(thm)],[c_721]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_999,plain,
% 3.46/0.97      ( ~ r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1)
% 3.46/0.97      | r1_tarski(k2_xboole_0(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))),sK1)
% 3.46/0.97      | k2_xboole_0(sK0,k9_relat_1(sK2,k10_relat_1(sK2,sK1))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
% 3.46/0.97      | sK1 != sK1 ),
% 3.46/0.97      inference(instantiation,[status(thm)],[c_817]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_10,plain,
% 3.46/0.97      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.46/0.97      | ~ v1_funct_1(X0)
% 3.46/0.97      | ~ v1_relat_1(X0) ),
% 3.46/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_199,plain,
% 3.46/0.97      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.46/0.97      | ~ v1_relat_1(X0)
% 3.46/0.97      | sK2 != X0 ),
% 3.46/0.97      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_200,plain,
% 3.46/0.97      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
% 3.46/0.97      | ~ v1_relat_1(sK2) ),
% 3.46/0.97      inference(unflattening,[status(thm)],[c_199]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_204,plain,
% 3.46/0.97      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
% 3.46/0.97      inference(global_propositional_subsumption,
% 3.46/0.97                [status(thm)],
% 3.46/0.97                [c_200,c_16]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_673,plain,
% 3.46/0.97      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),sK1) ),
% 3.46/0.97      inference(instantiation,[status(thm)],[c_204]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_327,plain,( X0 = X0 ),theory(equality) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_654,plain,
% 3.46/0.97      ( sK1 = sK1 ),
% 3.46/0.97      inference(instantiation,[status(thm)],[c_327]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(c_12,negated_conjecture,
% 3.46/0.97      ( ~ r1_tarski(sK0,sK1) ),
% 3.46/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.46/0.97  
% 3.46/0.97  cnf(contradiction,plain,
% 3.46/0.97      ( $false ),
% 3.46/0.97      inference(minisat,
% 3.46/0.97                [status(thm)],
% 3.46/0.97                [c_8647,c_2836,c_999,c_673,c_654,c_12]) ).
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/0.97  
% 3.46/0.97  ------                               Statistics
% 3.46/0.97  
% 3.46/0.97  ------ General
% 3.46/0.97  
% 3.46/0.97  abstr_ref_over_cycles:                  0
% 3.46/0.97  abstr_ref_under_cycles:                 0
% 3.46/0.97  gc_basic_clause_elim:                   0
% 3.46/0.97  forced_gc_time:                         0
% 3.46/0.97  parsing_time:                           0.009
% 3.46/0.97  unif_index_cands_time:                  0.
% 3.46/0.97  unif_index_add_time:                    0.
% 3.46/0.97  orderings_time:                         0.
% 3.46/0.97  out_proof_time:                         0.007
% 3.46/0.97  total_time:                             0.245
% 3.46/0.97  num_of_symbols:                         44
% 3.46/0.97  num_of_terms:                           8172
% 3.46/0.97  
% 3.46/0.97  ------ Preprocessing
% 3.46/0.97  
% 3.46/0.97  num_of_splits:                          0
% 3.46/0.97  num_of_split_atoms:                     0
% 3.46/0.97  num_of_reused_defs:                     0
% 3.46/0.97  num_eq_ax_congr_red:                    29
% 3.46/0.97  num_of_sem_filtered_clauses:            1
% 3.46/0.97  num_of_subtypes:                        0
% 3.46/0.97  monotx_restored_types:                  0
% 3.46/0.97  sat_num_of_epr_types:                   0
% 3.46/0.97  sat_num_of_non_cyclic_types:            0
% 3.46/0.97  sat_guarded_non_collapsed_types:        0
% 3.46/0.97  num_pure_diseq_elim:                    0
% 3.46/0.97  simp_replaced_by:                       0
% 3.46/0.97  res_preprocessed:                       77
% 3.46/0.97  prep_upred:                             0
% 3.46/0.97  prep_unflattend:                        4
% 3.46/0.97  smt_new_axioms:                         0
% 3.46/0.97  pred_elim_cands:                        1
% 3.46/0.97  pred_elim:                              2
% 3.46/0.97  pred_elim_cl:                           2
% 3.46/0.97  pred_elim_cycles:                       4
% 3.46/0.97  merged_defs:                            0
% 3.46/0.97  merged_defs_ncl:                        0
% 3.46/0.97  bin_hyper_res:                          0
% 3.46/0.97  prep_cycles:                            4
% 3.46/0.97  pred_elim_time:                         0.001
% 3.46/0.97  splitting_time:                         0.
% 3.46/0.97  sem_filter_time:                        0.
% 3.46/0.97  monotx_time:                            0.
% 3.46/0.97  subtype_inf_time:                       0.
% 3.46/0.97  
% 3.46/0.97  ------ Problem properties
% 3.46/0.97  
% 3.46/0.97  clauses:                                14
% 3.46/0.97  conjectures:                            3
% 3.46/0.97  epr:                                    3
% 3.46/0.97  horn:                                   14
% 3.46/0.97  ground:                                 4
% 3.46/0.97  unary:                                  7
% 3.46/0.97  binary:                                 6
% 3.46/0.97  lits:                                   22
% 3.46/0.97  lits_eq:                                5
% 3.46/0.97  fd_pure:                                0
% 3.46/0.97  fd_pseudo:                              0
% 3.46/0.97  fd_cond:                                0
% 3.46/0.97  fd_pseudo_cond:                         1
% 3.46/0.97  ac_symbols:                             0
% 3.46/0.97  
% 3.46/0.97  ------ Propositional Solver
% 3.46/0.97  
% 3.46/0.97  prop_solver_calls:                      31
% 3.46/0.97  prop_fast_solver_calls:                 410
% 3.46/0.97  smt_solver_calls:                       0
% 3.46/0.97  smt_fast_solver_calls:                  0
% 3.46/0.97  prop_num_of_clauses:                    3714
% 3.46/0.97  prop_preprocess_simplified:             6828
% 3.46/0.97  prop_fo_subsumed:                       2
% 3.46/0.97  prop_solver_time:                       0.
% 3.46/0.97  smt_solver_time:                        0.
% 3.46/0.97  smt_fast_solver_time:                   0.
% 3.46/0.97  prop_fast_solver_time:                  0.
% 3.46/0.97  prop_unsat_core_time:                   0.
% 3.46/0.97  
% 3.46/0.97  ------ QBF
% 3.46/0.97  
% 3.46/0.97  qbf_q_res:                              0
% 3.46/0.97  qbf_num_tautologies:                    0
% 3.46/0.97  qbf_prep_cycles:                        0
% 3.46/0.97  
% 3.46/0.97  ------ BMC1
% 3.46/0.97  
% 3.46/0.97  bmc1_current_bound:                     -1
% 3.46/0.97  bmc1_last_solved_bound:                 -1
% 3.46/0.97  bmc1_unsat_core_size:                   -1
% 3.46/0.97  bmc1_unsat_core_parents_size:           -1
% 3.46/0.97  bmc1_merge_next_fun:                    0
% 3.46/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.46/0.97  
% 3.46/0.97  ------ Instantiation
% 3.46/0.97  
% 3.46/0.97  inst_num_of_clauses:                    867
% 3.46/0.97  inst_num_in_passive:                    490
% 3.46/0.97  inst_num_in_active:                     372
% 3.46/0.97  inst_num_in_unprocessed:                4
% 3.46/0.97  inst_num_of_loops:                      384
% 3.46/0.97  inst_num_of_learning_restarts:          0
% 3.46/0.97  inst_num_moves_active_passive:          5
% 3.46/0.97  inst_lit_activity:                      0
% 3.46/0.97  inst_lit_activity_moves:                0
% 3.46/0.97  inst_num_tautologies:                   0
% 3.46/0.97  inst_num_prop_implied:                  0
% 3.46/0.97  inst_num_existing_simplified:           0
% 3.46/0.97  inst_num_eq_res_simplified:             0
% 3.46/0.97  inst_num_child_elim:                    0
% 3.46/0.97  inst_num_of_dismatching_blockings:      340
% 3.46/0.97  inst_num_of_non_proper_insts:           1010
% 3.46/0.97  inst_num_of_duplicates:                 0
% 3.46/0.97  inst_inst_num_from_inst_to_res:         0
% 3.46/0.97  inst_dismatching_checking_time:         0.
% 3.46/0.97  
% 3.46/0.97  ------ Resolution
% 3.46/0.97  
% 3.46/0.97  res_num_of_clauses:                     0
% 3.46/0.97  res_num_in_passive:                     0
% 3.46/0.97  res_num_in_active:                      0
% 3.46/0.97  res_num_of_loops:                       81
% 3.46/0.97  res_forward_subset_subsumed:            121
% 3.46/0.97  res_backward_subset_subsumed:           0
% 3.46/0.97  res_forward_subsumed:                   0
% 3.46/0.97  res_backward_subsumed:                  0
% 3.46/0.97  res_forward_subsumption_resolution:     0
% 3.46/0.97  res_backward_subsumption_resolution:    0
% 3.46/0.97  res_clause_to_clause_subsumption:       1946
% 3.46/0.97  res_orphan_elimination:                 0
% 3.46/0.97  res_tautology_del:                      59
% 3.46/0.97  res_num_eq_res_simplified:              0
% 3.46/0.97  res_num_sel_changes:                    0
% 3.46/0.97  res_moves_from_active_to_pass:          0
% 3.46/0.97  
% 3.46/0.97  ------ Superposition
% 3.46/0.97  
% 3.46/0.97  sup_time_total:                         0.
% 3.46/0.97  sup_time_generating:                    0.
% 3.46/0.97  sup_time_sim_full:                      0.
% 3.46/0.97  sup_time_sim_immed:                     0.
% 3.46/0.97  
% 3.46/0.97  sup_num_of_clauses:                     375
% 3.46/0.97  sup_num_in_active:                      76
% 3.46/0.97  sup_num_in_passive:                     299
% 3.46/0.97  sup_num_of_loops:                       76
% 3.46/0.97  sup_fw_superposition:                   342
% 3.46/0.97  sup_bw_superposition:                   266
% 3.46/0.97  sup_immediate_simplified:               140
% 3.46/0.97  sup_given_eliminated:                   0
% 3.46/0.97  comparisons_done:                       0
% 3.46/0.97  comparisons_avoided:                    0
% 3.46/0.97  
% 3.46/0.97  ------ Simplifications
% 3.46/0.97  
% 3.46/0.97  
% 3.46/0.97  sim_fw_subset_subsumed:                 15
% 3.46/0.97  sim_bw_subset_subsumed:                 2
% 3.46/0.97  sim_fw_subsumed:                        53
% 3.46/0.97  sim_bw_subsumed:                        0
% 3.46/0.97  sim_fw_subsumption_res:                 0
% 3.46/0.97  sim_bw_subsumption_res:                 0
% 3.46/0.97  sim_tautology_del:                      16
% 3.46/0.97  sim_eq_tautology_del:                   12
% 3.46/0.97  sim_eq_res_simp:                        0
% 3.46/0.97  sim_fw_demodulated:                     28
% 3.46/0.97  sim_bw_demodulated:                     0
% 3.46/0.97  sim_light_normalised:                   54
% 3.46/0.97  sim_joinable_taut:                      0
% 3.46/0.97  sim_joinable_simp:                      0
% 3.46/0.97  sim_ac_normalised:                      0
% 3.46/0.97  sim_smt_subsumption:                    0
% 3.46/0.97  
%------------------------------------------------------------------------------
