%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:23 EST 2020

% Result     : Theorem 8.04s
% Output     : CNFRefutation 8.04s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 452 expanded)
%              Number of clauses        :   93 ( 156 expanded)
%              Number of leaves         :   23 (  99 expanded)
%              Depth                    :   21
%              Number of atoms          :  305 ( 879 expanded)
%              Number of equality atoms :  175 ( 423 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f34])).

fof(f54,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f57])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f64,plain,(
    ! [X0] :
      ( k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f60,f60])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_157,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_437,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_164,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k2_wellord1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_431,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k2_wellord1(X0_41,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_168,plain,
    ( ~ v1_relat_1(X0_41)
    | k3_tarski(k5_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k2_relat_1(X0_41))) = k3_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_427,plain,
    ( k3_tarski(k5_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k2_relat_1(X0_41))) = k3_relat_1(X0_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_1106,plain,
    ( k3_tarski(k5_enumset1(k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k2_relat_1(k2_wellord1(X0_41,X0_42)))) = k3_relat_1(k2_wellord1(X0_41,X0_42))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_427])).

cnf(c_20208,plain,
    ( k3_tarski(k5_enumset1(k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k2_relat_1(k2_wellord1(sK2,X0_42)))) = k3_relat_1(k2_wellord1(sK2,X0_42)) ),
    inference(superposition,[status(thm)],[c_437,c_1106])).

cnf(c_2,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_169,plain,
    ( k5_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X1_42) = k5_enumset1(X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_170,plain,
    ( r1_tarski(X0_42,k3_tarski(k5_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X1_42))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_426,plain,
    ( r1_tarski(X0_42,k3_tarski(k5_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X1_42))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_672,plain,
    ( r1_tarski(X0_42,k3_tarski(k5_enumset1(X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_169,c_426])).

cnf(c_21147,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20208,c_672])).

cnf(c_9,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_162,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42)
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_433,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_171,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X2_42,X0_42)
    | r1_tarski(X2_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_425,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | r1_tarski(X2_42,X0_42) != iProver_top
    | r1_tarski(X2_42,X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_665,plain,
    ( r1_tarski(X0_42,X1_42) = iProver_top
    | r1_tarski(X0_42,k3_relat_1(k2_wellord1(X0_41,X1_42))) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_433,c_425])).

cnf(c_21378,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X0_42) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_21147,c_665])).

cnf(c_15,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_26063,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X0_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21378,c_15])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_158,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_436,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_664,plain,
    ( r1_tarski(X0_42,sK1) = iProver_top
    | r1_tarski(X0_42,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_425])).

cnf(c_26077,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_26063,c_664])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_165,plain,
    ( ~ r1_tarski(k2_relat_1(X0_41),X0_42)
    | ~ v1_relat_1(X0_41)
    | k8_relat_1(X0_42,X0_41) = X0_41 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_430,plain,
    ( k8_relat_1(X0_42,X0_41) = X0_41
    | r1_tarski(k2_relat_1(X0_41),X0_42) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_26187,plain,
    ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26077,c_430])).

cnf(c_16,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_212,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k2_wellord1(X0_41,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(c_214,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_212])).

cnf(c_218,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_220,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_218])).

cnf(c_992,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(X0_41,X2_42)),X0_42)
    | r1_tarski(k2_relat_1(k2_wellord1(X0_41,X2_42)),X1_42) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_1783,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(X0_41,X0_42)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(X0_41,X0_42)),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_1784,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(X0_41,X0_42)),sK1) = iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(X0_41,X0_42)),sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1783])).

cnf(c_1786,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_1793,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42)
    | r1_tarski(k2_relat_1(k2_wellord1(X1_41,X1_42)),X0_42)
    | ~ r1_tarski(k2_relat_1(k2_wellord1(X1_41,X1_42)),k3_relat_1(k2_wellord1(X0_41,X0_42))) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_1794,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(X1_41,X1_42)),X0_42) = iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(X1_41,X1_42)),k3_relat_1(k2_wellord1(X0_41,X0_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1793])).

cnf(c_1796,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_536,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),X0_42)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k8_relat_1(X0_42,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_4574,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_4577,plain,
    ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) != iProver_top
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4574])).

cnf(c_21161,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_21147])).

cnf(c_28907,plain,
    ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26187,c_15,c_16,c_214,c_220,c_1786,c_1796,c_4577,c_21161])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_163,plain,
    ( ~ v1_relat_1(X0_41)
    | k7_relat_1(k8_relat_1(X0_42,X0_41),X0_42) = k2_wellord1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_432,plain,
    ( k7_relat_1(k8_relat_1(X0_42,X0_41),X0_42) = k2_wellord1(X0_41,X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_611,plain,
    ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(X0_41,X1_42)),X0_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_431,c_432])).

cnf(c_2014,plain,
    ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(sK2,X1_42)),X0_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_437,c_611])).

cnf(c_28910,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_28907,c_2014])).

cnf(c_610,plain,
    ( k7_relat_1(k8_relat_1(X0_42,sK2),X0_42) = k2_wellord1(sK2,X0_42) ),
    inference(superposition,[status(thm)],[c_437,c_432])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_167,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k8_relat_1(X0_42,X0_41)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_428,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k8_relat_1(X0_42,X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_166,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ v1_relat_1(X0_41)
    | k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) = k7_relat_1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_429,plain,
    ( k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) = k7_relat_1(X0_41,X0_42)
    | r1_tarski(X0_42,X1_42) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(c_1211,plain,
    ( k7_relat_1(k7_relat_1(X0_41,sK0),sK1) = k7_relat_1(X0_41,sK0)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_436,c_429])).

cnf(c_1351,plain,
    ( k7_relat_1(k7_relat_1(k8_relat_1(X0_42,X0_41),sK0),sK1) = k7_relat_1(k8_relat_1(X0_42,X0_41),sK0)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_428,c_1211])).

cnf(c_1640,plain,
    ( k7_relat_1(k7_relat_1(k8_relat_1(X0_42,sK2),sK0),sK1) = k7_relat_1(k8_relat_1(X0_42,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_437,c_1351])).

cnf(c_1781,plain,
    ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k8_relat_1(sK0,sK2),sK0) ),
    inference(superposition,[status(thm)],[c_610,c_1640])).

cnf(c_1782,plain,
    ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_1781,c_610])).

cnf(c_28911,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
    inference(light_normalisation,[status(thm)],[c_28910,c_1782])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_160,plain,
    ( ~ v1_relat_1(X0_41)
    | k2_wellord1(k2_wellord1(X0_41,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_567,plain,
    ( ~ v1_relat_1(sK2)
    | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_176,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_459,plain,
    ( X0_41 != X1_41
    | k2_wellord1(sK2,sK0) != X1_41
    | k2_wellord1(sK2,sK0) = X0_41 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_468,plain,
    ( X0_41 != k2_wellord1(sK2,sK0)
    | k2_wellord1(sK2,sK0) = X0_41
    | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_489,plain,
    ( k2_wellord1(X0_41,X0_42) != k2_wellord1(sK2,sK0)
    | k2_wellord1(sK2,sK0) = k2_wellord1(X0_41,X0_42)
    | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_566,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0)
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_453,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X0_41
    | k2_wellord1(sK2,sK0) != X0_41
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_460,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(X0_41,X0_42)
    | k2_wellord1(sK2,sK0) != k2_wellord1(X0_41,X0_42)
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_472,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_12,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_159,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_174,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_195,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_173,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_194,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_185,plain,
    ( X0_42 != X1_42
    | X0_41 != X1_41
    | k2_wellord1(X0_41,X0_42) = k2_wellord1(X1_41,X1_42) ),
    theory(equality)).

cnf(c_192,plain,
    ( sK0 != sK0
    | k2_wellord1(sK2,sK0) = k2_wellord1(sK2,sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_185])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28911,c_567,c_566,c_472,c_159,c_195,c_194,c_192,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.04/1.55  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.04/1.55  
% 8.04/1.55  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.04/1.55  
% 8.04/1.55  ------  iProver source info
% 8.04/1.55  
% 8.04/1.55  git: date: 2020-06-30 10:37:57 +0100
% 8.04/1.55  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.04/1.55  git: non_committed_changes: false
% 8.04/1.55  git: last_make_outside_of_git: false
% 8.04/1.55  
% 8.04/1.55  ------ 
% 8.04/1.55  
% 8.04/1.55  ------ Input Options
% 8.04/1.55  
% 8.04/1.55  --out_options                           all
% 8.04/1.55  --tptp_safe_out                         true
% 8.04/1.55  --problem_path                          ""
% 8.04/1.55  --include_path                          ""
% 8.04/1.55  --clausifier                            res/vclausify_rel
% 8.04/1.55  --clausifier_options                    ""
% 8.04/1.55  --stdin                                 false
% 8.04/1.55  --stats_out                             all
% 8.04/1.55  
% 8.04/1.55  ------ General Options
% 8.04/1.55  
% 8.04/1.55  --fof                                   false
% 8.04/1.55  --time_out_real                         305.
% 8.04/1.55  --time_out_virtual                      -1.
% 8.04/1.55  --symbol_type_check                     false
% 8.04/1.55  --clausify_out                          false
% 8.04/1.55  --sig_cnt_out                           false
% 8.04/1.55  --trig_cnt_out                          false
% 8.04/1.55  --trig_cnt_out_tolerance                1.
% 8.04/1.55  --trig_cnt_out_sk_spl                   false
% 8.04/1.55  --abstr_cl_out                          false
% 8.04/1.55  
% 8.04/1.55  ------ Global Options
% 8.04/1.55  
% 8.04/1.55  --schedule                              default
% 8.04/1.55  --add_important_lit                     false
% 8.04/1.55  --prop_solver_per_cl                    1000
% 8.04/1.55  --min_unsat_core                        false
% 8.04/1.55  --soft_assumptions                      false
% 8.04/1.55  --soft_lemma_size                       3
% 8.04/1.55  --prop_impl_unit_size                   0
% 8.04/1.55  --prop_impl_unit                        []
% 8.04/1.55  --share_sel_clauses                     true
% 8.04/1.55  --reset_solvers                         false
% 8.04/1.55  --bc_imp_inh                            [conj_cone]
% 8.04/1.55  --conj_cone_tolerance                   3.
% 8.04/1.55  --extra_neg_conj                        none
% 8.04/1.55  --large_theory_mode                     true
% 8.04/1.55  --prolific_symb_bound                   200
% 8.04/1.55  --lt_threshold                          2000
% 8.04/1.55  --clause_weak_htbl                      true
% 8.04/1.55  --gc_record_bc_elim                     false
% 8.04/1.55  
% 8.04/1.55  ------ Preprocessing Options
% 8.04/1.55  
% 8.04/1.55  --preprocessing_flag                    true
% 8.04/1.55  --time_out_prep_mult                    0.1
% 8.04/1.55  --splitting_mode                        input
% 8.04/1.55  --splitting_grd                         true
% 8.04/1.55  --splitting_cvd                         false
% 8.04/1.55  --splitting_cvd_svl                     false
% 8.04/1.55  --splitting_nvd                         32
% 8.04/1.55  --sub_typing                            true
% 8.04/1.55  --prep_gs_sim                           true
% 8.04/1.55  --prep_unflatten                        true
% 8.04/1.55  --prep_res_sim                          true
% 8.04/1.55  --prep_upred                            true
% 8.04/1.55  --prep_sem_filter                       exhaustive
% 8.04/1.55  --prep_sem_filter_out                   false
% 8.04/1.55  --pred_elim                             true
% 8.04/1.55  --res_sim_input                         true
% 8.04/1.55  --eq_ax_congr_red                       true
% 8.04/1.55  --pure_diseq_elim                       true
% 8.04/1.55  --brand_transform                       false
% 8.04/1.55  --non_eq_to_eq                          false
% 8.04/1.55  --prep_def_merge                        true
% 8.04/1.55  --prep_def_merge_prop_impl              false
% 8.04/1.55  --prep_def_merge_mbd                    true
% 8.04/1.55  --prep_def_merge_tr_red                 false
% 8.04/1.55  --prep_def_merge_tr_cl                  false
% 8.04/1.55  --smt_preprocessing                     true
% 8.04/1.55  --smt_ac_axioms                         fast
% 8.04/1.55  --preprocessed_out                      false
% 8.04/1.55  --preprocessed_stats                    false
% 8.04/1.55  
% 8.04/1.55  ------ Abstraction refinement Options
% 8.04/1.55  
% 8.04/1.55  --abstr_ref                             []
% 8.04/1.55  --abstr_ref_prep                        false
% 8.04/1.55  --abstr_ref_until_sat                   false
% 8.04/1.55  --abstr_ref_sig_restrict                funpre
% 8.04/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.55  --abstr_ref_under                       []
% 8.04/1.55  
% 8.04/1.55  ------ SAT Options
% 8.04/1.55  
% 8.04/1.55  --sat_mode                              false
% 8.04/1.55  --sat_fm_restart_options                ""
% 8.04/1.55  --sat_gr_def                            false
% 8.04/1.55  --sat_epr_types                         true
% 8.04/1.55  --sat_non_cyclic_types                  false
% 8.04/1.55  --sat_finite_models                     false
% 8.04/1.55  --sat_fm_lemmas                         false
% 8.04/1.55  --sat_fm_prep                           false
% 8.04/1.55  --sat_fm_uc_incr                        true
% 8.04/1.55  --sat_out_model                         small
% 8.04/1.55  --sat_out_clauses                       false
% 8.04/1.55  
% 8.04/1.55  ------ QBF Options
% 8.04/1.55  
% 8.04/1.55  --qbf_mode                              false
% 8.04/1.55  --qbf_elim_univ                         false
% 8.04/1.55  --qbf_dom_inst                          none
% 8.04/1.55  --qbf_dom_pre_inst                      false
% 8.04/1.55  --qbf_sk_in                             false
% 8.04/1.55  --qbf_pred_elim                         true
% 8.04/1.55  --qbf_split                             512
% 8.04/1.55  
% 8.04/1.55  ------ BMC1 Options
% 8.04/1.55  
% 8.04/1.55  --bmc1_incremental                      false
% 8.04/1.55  --bmc1_axioms                           reachable_all
% 8.04/1.55  --bmc1_min_bound                        0
% 8.04/1.55  --bmc1_max_bound                        -1
% 8.04/1.55  --bmc1_max_bound_default                -1
% 8.04/1.55  --bmc1_symbol_reachability              true
% 8.04/1.55  --bmc1_property_lemmas                  false
% 8.04/1.55  --bmc1_k_induction                      false
% 8.04/1.55  --bmc1_non_equiv_states                 false
% 8.04/1.55  --bmc1_deadlock                         false
% 8.04/1.55  --bmc1_ucm                              false
% 8.04/1.55  --bmc1_add_unsat_core                   none
% 8.04/1.55  --bmc1_unsat_core_children              false
% 8.04/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.55  --bmc1_out_stat                         full
% 8.04/1.55  --bmc1_ground_init                      false
% 8.04/1.55  --bmc1_pre_inst_next_state              false
% 8.04/1.55  --bmc1_pre_inst_state                   false
% 8.04/1.55  --bmc1_pre_inst_reach_state             false
% 8.04/1.55  --bmc1_out_unsat_core                   false
% 8.04/1.55  --bmc1_aig_witness_out                  false
% 8.04/1.55  --bmc1_verbose                          false
% 8.04/1.55  --bmc1_dump_clauses_tptp                false
% 8.04/1.55  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.55  --bmc1_dump_file                        -
% 8.04/1.55  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.55  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.55  --bmc1_ucm_extend_mode                  1
% 8.04/1.55  --bmc1_ucm_init_mode                    2
% 8.04/1.55  --bmc1_ucm_cone_mode                    none
% 8.04/1.55  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.55  --bmc1_ucm_relax_model                  4
% 8.04/1.55  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.55  --bmc1_ucm_layered_model                none
% 8.04/1.55  --bmc1_ucm_max_lemma_size               10
% 8.04/1.55  
% 8.04/1.55  ------ AIG Options
% 8.04/1.55  
% 8.04/1.55  --aig_mode                              false
% 8.04/1.55  
% 8.04/1.55  ------ Instantiation Options
% 8.04/1.55  
% 8.04/1.55  --instantiation_flag                    true
% 8.04/1.55  --inst_sos_flag                         true
% 8.04/1.55  --inst_sos_phase                        true
% 8.04/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.55  --inst_lit_sel_side                     num_symb
% 8.04/1.55  --inst_solver_per_active                1400
% 8.04/1.55  --inst_solver_calls_frac                1.
% 8.04/1.55  --inst_passive_queue_type               priority_queues
% 8.04/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.55  --inst_passive_queues_freq              [25;2]
% 8.04/1.55  --inst_dismatching                      true
% 8.04/1.55  --inst_eager_unprocessed_to_passive     true
% 8.04/1.55  --inst_prop_sim_given                   true
% 8.04/1.55  --inst_prop_sim_new                     false
% 8.04/1.55  --inst_subs_new                         false
% 8.04/1.55  --inst_eq_res_simp                      false
% 8.04/1.55  --inst_subs_given                       false
% 8.04/1.55  --inst_orphan_elimination               true
% 8.04/1.55  --inst_learning_loop_flag               true
% 8.04/1.55  --inst_learning_start                   3000
% 8.04/1.55  --inst_learning_factor                  2
% 8.04/1.55  --inst_start_prop_sim_after_learn       3
% 8.04/1.55  --inst_sel_renew                        solver
% 8.04/1.55  --inst_lit_activity_flag                true
% 8.04/1.55  --inst_restr_to_given                   false
% 8.04/1.55  --inst_activity_threshold               500
% 8.04/1.55  --inst_out_proof                        true
% 8.04/1.55  
% 8.04/1.55  ------ Resolution Options
% 8.04/1.55  
% 8.04/1.55  --resolution_flag                       true
% 8.04/1.55  --res_lit_sel                           adaptive
% 8.04/1.55  --res_lit_sel_side                      none
% 8.04/1.55  --res_ordering                          kbo
% 8.04/1.55  --res_to_prop_solver                    active
% 8.04/1.55  --res_prop_simpl_new                    false
% 8.04/1.55  --res_prop_simpl_given                  true
% 8.04/1.55  --res_passive_queue_type                priority_queues
% 8.04/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.55  --res_passive_queues_freq               [15;5]
% 8.04/1.55  --res_forward_subs                      full
% 8.04/1.55  --res_backward_subs                     full
% 8.04/1.55  --res_forward_subs_resolution           true
% 8.04/1.55  --res_backward_subs_resolution          true
% 8.04/1.55  --res_orphan_elimination                true
% 8.04/1.55  --res_time_limit                        2.
% 8.04/1.55  --res_out_proof                         true
% 8.04/1.55  
% 8.04/1.55  ------ Superposition Options
% 8.04/1.55  
% 8.04/1.55  --superposition_flag                    true
% 8.04/1.55  --sup_passive_queue_type                priority_queues
% 8.04/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.55  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.55  --demod_completeness_check              fast
% 8.04/1.55  --demod_use_ground                      true
% 8.04/1.55  --sup_to_prop_solver                    passive
% 8.04/1.55  --sup_prop_simpl_new                    true
% 8.04/1.55  --sup_prop_simpl_given                  true
% 8.04/1.55  --sup_fun_splitting                     true
% 8.04/1.55  --sup_smt_interval                      50000
% 8.04/1.55  
% 8.04/1.55  ------ Superposition Simplification Setup
% 8.04/1.55  
% 8.04/1.55  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.04/1.55  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.04/1.55  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.04/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.04/1.55  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.04/1.55  --sup_immed_triv                        [TrivRules]
% 8.04/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.55  --sup_immed_bw_main                     []
% 8.04/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.04/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.55  --sup_input_bw                          []
% 8.04/1.55  
% 8.04/1.55  ------ Combination Options
% 8.04/1.55  
% 8.04/1.55  --comb_res_mult                         3
% 8.04/1.55  --comb_sup_mult                         2
% 8.04/1.55  --comb_inst_mult                        10
% 8.04/1.55  
% 8.04/1.55  ------ Debug Options
% 8.04/1.55  
% 8.04/1.55  --dbg_backtrace                         false
% 8.04/1.55  --dbg_dump_prop_clauses                 false
% 8.04/1.55  --dbg_dump_prop_clauses_file            -
% 8.04/1.55  --dbg_out_stat                          false
% 8.04/1.55  ------ Parsing...
% 8.04/1.55  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.04/1.55  
% 8.04/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 8.04/1.55  
% 8.04/1.55  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.04/1.55  
% 8.04/1.55  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.04/1.55  ------ Proving...
% 8.04/1.55  ------ Problem Properties 
% 8.04/1.55  
% 8.04/1.55  
% 8.04/1.55  clauses                                 15
% 8.04/1.55  conjectures                             3
% 8.04/1.55  EPR                                     3
% 8.04/1.55  Horn                                    15
% 8.04/1.55  unary                                   5
% 8.04/1.55  binary                                  7
% 8.04/1.55  lits                                    28
% 8.04/1.55  lits eq                                 7
% 8.04/1.55  fd_pure                                 0
% 8.04/1.55  fd_pseudo                               0
% 8.04/1.55  fd_cond                                 0
% 8.04/1.55  fd_pseudo_cond                          0
% 8.04/1.55  AC symbols                              0
% 8.04/1.55  
% 8.04/1.55  ------ Schedule dynamic 5 is on 
% 8.04/1.55  
% 8.04/1.55  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.04/1.55  
% 8.04/1.55  
% 8.04/1.55  ------ 
% 8.04/1.55  Current options:
% 8.04/1.55  ------ 
% 8.04/1.55  
% 8.04/1.55  ------ Input Options
% 8.04/1.55  
% 8.04/1.55  --out_options                           all
% 8.04/1.55  --tptp_safe_out                         true
% 8.04/1.55  --problem_path                          ""
% 8.04/1.55  --include_path                          ""
% 8.04/1.55  --clausifier                            res/vclausify_rel
% 8.04/1.55  --clausifier_options                    ""
% 8.04/1.55  --stdin                                 false
% 8.04/1.55  --stats_out                             all
% 8.04/1.55  
% 8.04/1.55  ------ General Options
% 8.04/1.55  
% 8.04/1.55  --fof                                   false
% 8.04/1.55  --time_out_real                         305.
% 8.04/1.55  --time_out_virtual                      -1.
% 8.04/1.55  --symbol_type_check                     false
% 8.04/1.55  --clausify_out                          false
% 8.04/1.55  --sig_cnt_out                           false
% 8.04/1.55  --trig_cnt_out                          false
% 8.04/1.55  --trig_cnt_out_tolerance                1.
% 8.04/1.55  --trig_cnt_out_sk_spl                   false
% 8.04/1.55  --abstr_cl_out                          false
% 8.04/1.55  
% 8.04/1.55  ------ Global Options
% 8.04/1.55  
% 8.04/1.55  --schedule                              default
% 8.04/1.55  --add_important_lit                     false
% 8.04/1.55  --prop_solver_per_cl                    1000
% 8.04/1.55  --min_unsat_core                        false
% 8.04/1.55  --soft_assumptions                      false
% 8.04/1.55  --soft_lemma_size                       3
% 8.04/1.55  --prop_impl_unit_size                   0
% 8.04/1.55  --prop_impl_unit                        []
% 8.04/1.55  --share_sel_clauses                     true
% 8.04/1.55  --reset_solvers                         false
% 8.04/1.55  --bc_imp_inh                            [conj_cone]
% 8.04/1.55  --conj_cone_tolerance                   3.
% 8.04/1.55  --extra_neg_conj                        none
% 8.04/1.55  --large_theory_mode                     true
% 8.04/1.55  --prolific_symb_bound                   200
% 8.04/1.55  --lt_threshold                          2000
% 8.04/1.55  --clause_weak_htbl                      true
% 8.04/1.55  --gc_record_bc_elim                     false
% 8.04/1.55  
% 8.04/1.55  ------ Preprocessing Options
% 8.04/1.55  
% 8.04/1.55  --preprocessing_flag                    true
% 8.04/1.55  --time_out_prep_mult                    0.1
% 8.04/1.55  --splitting_mode                        input
% 8.04/1.55  --splitting_grd                         true
% 8.04/1.55  --splitting_cvd                         false
% 8.04/1.55  --splitting_cvd_svl                     false
% 8.04/1.55  --splitting_nvd                         32
% 8.04/1.55  --sub_typing                            true
% 8.04/1.55  --prep_gs_sim                           true
% 8.04/1.55  --prep_unflatten                        true
% 8.04/1.55  --prep_res_sim                          true
% 8.04/1.55  --prep_upred                            true
% 8.04/1.55  --prep_sem_filter                       exhaustive
% 8.04/1.55  --prep_sem_filter_out                   false
% 8.04/1.55  --pred_elim                             true
% 8.04/1.55  --res_sim_input                         true
% 8.04/1.55  --eq_ax_congr_red                       true
% 8.04/1.55  --pure_diseq_elim                       true
% 8.04/1.55  --brand_transform                       false
% 8.04/1.55  --non_eq_to_eq                          false
% 8.04/1.55  --prep_def_merge                        true
% 8.04/1.55  --prep_def_merge_prop_impl              false
% 8.04/1.55  --prep_def_merge_mbd                    true
% 8.04/1.55  --prep_def_merge_tr_red                 false
% 8.04/1.55  --prep_def_merge_tr_cl                  false
% 8.04/1.55  --smt_preprocessing                     true
% 8.04/1.55  --smt_ac_axioms                         fast
% 8.04/1.55  --preprocessed_out                      false
% 8.04/1.55  --preprocessed_stats                    false
% 8.04/1.55  
% 8.04/1.55  ------ Abstraction refinement Options
% 8.04/1.55  
% 8.04/1.55  --abstr_ref                             []
% 8.04/1.55  --abstr_ref_prep                        false
% 8.04/1.55  --abstr_ref_until_sat                   false
% 8.04/1.55  --abstr_ref_sig_restrict                funpre
% 8.04/1.55  --abstr_ref_af_restrict_to_split_sk     false
% 8.04/1.55  --abstr_ref_under                       []
% 8.04/1.55  
% 8.04/1.55  ------ SAT Options
% 8.04/1.55  
% 8.04/1.55  --sat_mode                              false
% 8.04/1.55  --sat_fm_restart_options                ""
% 8.04/1.55  --sat_gr_def                            false
% 8.04/1.55  --sat_epr_types                         true
% 8.04/1.55  --sat_non_cyclic_types                  false
% 8.04/1.55  --sat_finite_models                     false
% 8.04/1.55  --sat_fm_lemmas                         false
% 8.04/1.55  --sat_fm_prep                           false
% 8.04/1.55  --sat_fm_uc_incr                        true
% 8.04/1.55  --sat_out_model                         small
% 8.04/1.55  --sat_out_clauses                       false
% 8.04/1.55  
% 8.04/1.55  ------ QBF Options
% 8.04/1.55  
% 8.04/1.55  --qbf_mode                              false
% 8.04/1.55  --qbf_elim_univ                         false
% 8.04/1.55  --qbf_dom_inst                          none
% 8.04/1.55  --qbf_dom_pre_inst                      false
% 8.04/1.55  --qbf_sk_in                             false
% 8.04/1.55  --qbf_pred_elim                         true
% 8.04/1.55  --qbf_split                             512
% 8.04/1.55  
% 8.04/1.55  ------ BMC1 Options
% 8.04/1.55  
% 8.04/1.55  --bmc1_incremental                      false
% 8.04/1.55  --bmc1_axioms                           reachable_all
% 8.04/1.55  --bmc1_min_bound                        0
% 8.04/1.55  --bmc1_max_bound                        -1
% 8.04/1.55  --bmc1_max_bound_default                -1
% 8.04/1.55  --bmc1_symbol_reachability              true
% 8.04/1.55  --bmc1_property_lemmas                  false
% 8.04/1.55  --bmc1_k_induction                      false
% 8.04/1.55  --bmc1_non_equiv_states                 false
% 8.04/1.55  --bmc1_deadlock                         false
% 8.04/1.55  --bmc1_ucm                              false
% 8.04/1.55  --bmc1_add_unsat_core                   none
% 8.04/1.55  --bmc1_unsat_core_children              false
% 8.04/1.55  --bmc1_unsat_core_extrapolate_axioms    false
% 8.04/1.55  --bmc1_out_stat                         full
% 8.04/1.55  --bmc1_ground_init                      false
% 8.04/1.55  --bmc1_pre_inst_next_state              false
% 8.04/1.55  --bmc1_pre_inst_state                   false
% 8.04/1.55  --bmc1_pre_inst_reach_state             false
% 8.04/1.55  --bmc1_out_unsat_core                   false
% 8.04/1.55  --bmc1_aig_witness_out                  false
% 8.04/1.55  --bmc1_verbose                          false
% 8.04/1.55  --bmc1_dump_clauses_tptp                false
% 8.04/1.55  --bmc1_dump_unsat_core_tptp             false
% 8.04/1.55  --bmc1_dump_file                        -
% 8.04/1.55  --bmc1_ucm_expand_uc_limit              128
% 8.04/1.55  --bmc1_ucm_n_expand_iterations          6
% 8.04/1.55  --bmc1_ucm_extend_mode                  1
% 8.04/1.55  --bmc1_ucm_init_mode                    2
% 8.04/1.55  --bmc1_ucm_cone_mode                    none
% 8.04/1.55  --bmc1_ucm_reduced_relation_type        0
% 8.04/1.55  --bmc1_ucm_relax_model                  4
% 8.04/1.55  --bmc1_ucm_full_tr_after_sat            true
% 8.04/1.55  --bmc1_ucm_expand_neg_assumptions       false
% 8.04/1.55  --bmc1_ucm_layered_model                none
% 8.04/1.55  --bmc1_ucm_max_lemma_size               10
% 8.04/1.55  
% 8.04/1.55  ------ AIG Options
% 8.04/1.55  
% 8.04/1.55  --aig_mode                              false
% 8.04/1.55  
% 8.04/1.55  ------ Instantiation Options
% 8.04/1.55  
% 8.04/1.55  --instantiation_flag                    true
% 8.04/1.55  --inst_sos_flag                         true
% 8.04/1.55  --inst_sos_phase                        true
% 8.04/1.55  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.04/1.55  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.04/1.55  --inst_lit_sel_side                     none
% 8.04/1.55  --inst_solver_per_active                1400
% 8.04/1.55  --inst_solver_calls_frac                1.
% 8.04/1.55  --inst_passive_queue_type               priority_queues
% 8.04/1.55  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.04/1.55  --inst_passive_queues_freq              [25;2]
% 8.04/1.55  --inst_dismatching                      true
% 8.04/1.55  --inst_eager_unprocessed_to_passive     true
% 8.04/1.55  --inst_prop_sim_given                   true
% 8.04/1.55  --inst_prop_sim_new                     false
% 8.04/1.55  --inst_subs_new                         false
% 8.04/1.55  --inst_eq_res_simp                      false
% 8.04/1.55  --inst_subs_given                       false
% 8.04/1.55  --inst_orphan_elimination               true
% 8.04/1.55  --inst_learning_loop_flag               true
% 8.04/1.55  --inst_learning_start                   3000
% 8.04/1.55  --inst_learning_factor                  2
% 8.04/1.55  --inst_start_prop_sim_after_learn       3
% 8.04/1.55  --inst_sel_renew                        solver
% 8.04/1.55  --inst_lit_activity_flag                true
% 8.04/1.55  --inst_restr_to_given                   false
% 8.04/1.55  --inst_activity_threshold               500
% 8.04/1.55  --inst_out_proof                        true
% 8.04/1.55  
% 8.04/1.55  ------ Resolution Options
% 8.04/1.55  
% 8.04/1.55  --resolution_flag                       false
% 8.04/1.55  --res_lit_sel                           adaptive
% 8.04/1.55  --res_lit_sel_side                      none
% 8.04/1.55  --res_ordering                          kbo
% 8.04/1.55  --res_to_prop_solver                    active
% 8.04/1.55  --res_prop_simpl_new                    false
% 8.04/1.55  --res_prop_simpl_given                  true
% 8.04/1.55  --res_passive_queue_type                priority_queues
% 8.04/1.55  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.04/1.55  --res_passive_queues_freq               [15;5]
% 8.04/1.55  --res_forward_subs                      full
% 8.04/1.55  --res_backward_subs                     full
% 8.04/1.55  --res_forward_subs_resolution           true
% 8.04/1.55  --res_backward_subs_resolution          true
% 8.04/1.55  --res_orphan_elimination                true
% 8.04/1.55  --res_time_limit                        2.
% 8.04/1.55  --res_out_proof                         true
% 8.04/1.55  
% 8.04/1.55  ------ Superposition Options
% 8.04/1.55  
% 8.04/1.55  --superposition_flag                    true
% 8.04/1.55  --sup_passive_queue_type                priority_queues
% 8.04/1.55  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.04/1.55  --sup_passive_queues_freq               [8;1;4]
% 8.04/1.55  --demod_completeness_check              fast
% 8.04/1.55  --demod_use_ground                      true
% 8.04/1.55  --sup_to_prop_solver                    passive
% 8.04/1.55  --sup_prop_simpl_new                    true
% 8.04/1.55  --sup_prop_simpl_given                  true
% 8.04/1.55  --sup_fun_splitting                     true
% 8.04/1.55  --sup_smt_interval                      50000
% 8.04/1.55  
% 8.04/1.55  ------ Superposition Simplification Setup
% 8.04/1.55  
% 8.04/1.55  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.04/1.55  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.04/1.55  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.04/1.55  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.04/1.55  --sup_full_triv                         [TrivRules;PropSubs]
% 8.04/1.55  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.04/1.55  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.04/1.55  --sup_immed_triv                        [TrivRules]
% 8.04/1.55  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.55  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.55  --sup_immed_bw_main                     []
% 8.04/1.55  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.04/1.55  --sup_input_triv                        [Unflattening;TrivRules]
% 8.04/1.55  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.04/1.55  --sup_input_bw                          []
% 8.04/1.55  
% 8.04/1.55  ------ Combination Options
% 8.04/1.55  
% 8.04/1.55  --comb_res_mult                         3
% 8.04/1.55  --comb_sup_mult                         2
% 8.04/1.55  --comb_inst_mult                        10
% 8.04/1.55  
% 8.04/1.55  ------ Debug Options
% 8.04/1.55  
% 8.04/1.55  --dbg_backtrace                         false
% 8.04/1.55  --dbg_dump_prop_clauses                 false
% 8.04/1.55  --dbg_dump_prop_clauses_file            -
% 8.04/1.55  --dbg_out_stat                          false
% 8.04/1.55  
% 8.04/1.55  
% 8.04/1.55  
% 8.04/1.55  
% 8.04/1.55  ------ Proving...
% 8.04/1.55  
% 8.04/1.55  
% 8.04/1.55  % SZS status Theorem for theBenchmark.p
% 8.04/1.55  
% 8.04/1.55  % SZS output start CNFRefutation for theBenchmark.p
% 8.04/1.55  
% 8.04/1.55  fof(f18,conjecture,(
% 8.04/1.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f19,negated_conjecture,(
% 8.04/1.55    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 8.04/1.55    inference(negated_conjecture,[],[f18])).
% 8.04/1.55  
% 8.04/1.55  fof(f32,plain,(
% 8.04/1.55    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 8.04/1.55    inference(ennf_transformation,[],[f19])).
% 8.04/1.55  
% 8.04/1.55  fof(f33,plain,(
% 8.04/1.55    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 8.04/1.55    inference(flattening,[],[f32])).
% 8.04/1.55  
% 8.04/1.55  fof(f34,plain,(
% 8.04/1.55    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 8.04/1.55    introduced(choice_axiom,[])).
% 8.04/1.55  
% 8.04/1.55  fof(f35,plain,(
% 8.04/1.55    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 8.04/1.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f34])).
% 8.04/1.55  
% 8.04/1.55  fof(f54,plain,(
% 8.04/1.55    v1_relat_1(sK2)),
% 8.04/1.55    inference(cnf_transformation,[],[f35])).
% 8.04/1.55  
% 8.04/1.55  fof(f14,axiom,(
% 8.04/1.55    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f28,plain,(
% 8.04/1.55    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 8.04/1.55    inference(ennf_transformation,[],[f14])).
% 8.04/1.55  
% 8.04/1.55  fof(f49,plain,(
% 8.04/1.55    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f28])).
% 8.04/1.55  
% 8.04/1.55  fof(f10,axiom,(
% 8.04/1.55    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f22,plain,(
% 8.04/1.55    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 8.04/1.55    inference(ennf_transformation,[],[f10])).
% 8.04/1.55  
% 8.04/1.55  fof(f45,plain,(
% 8.04/1.55    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f22])).
% 8.04/1.55  
% 8.04/1.55  fof(f9,axiom,(
% 8.04/1.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f44,plain,(
% 8.04/1.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 8.04/1.55    inference(cnf_transformation,[],[f9])).
% 8.04/1.55  
% 8.04/1.55  fof(f4,axiom,(
% 8.04/1.55    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f39,plain,(
% 8.04/1.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f4])).
% 8.04/1.55  
% 8.04/1.55  fof(f5,axiom,(
% 8.04/1.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f40,plain,(
% 8.04/1.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f5])).
% 8.04/1.55  
% 8.04/1.55  fof(f6,axiom,(
% 8.04/1.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f41,plain,(
% 8.04/1.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f6])).
% 8.04/1.55  
% 8.04/1.55  fof(f7,axiom,(
% 8.04/1.55    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f42,plain,(
% 8.04/1.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f7])).
% 8.04/1.55  
% 8.04/1.55  fof(f8,axiom,(
% 8.04/1.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f43,plain,(
% 8.04/1.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f8])).
% 8.04/1.55  
% 8.04/1.55  fof(f57,plain,(
% 8.04/1.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 8.04/1.55    inference(definition_unfolding,[],[f42,f43])).
% 8.04/1.55  
% 8.04/1.55  fof(f58,plain,(
% 8.04/1.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 8.04/1.55    inference(definition_unfolding,[],[f41,f57])).
% 8.04/1.55  
% 8.04/1.55  fof(f59,plain,(
% 8.04/1.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 8.04/1.55    inference(definition_unfolding,[],[f40,f58])).
% 8.04/1.55  
% 8.04/1.55  fof(f60,plain,(
% 8.04/1.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 8.04/1.55    inference(definition_unfolding,[],[f39,f59])).
% 8.04/1.55  
% 8.04/1.55  fof(f61,plain,(
% 8.04/1.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 8.04/1.55    inference(definition_unfolding,[],[f44,f60])).
% 8.04/1.55  
% 8.04/1.55  fof(f64,plain,(
% 8.04/1.55    ( ! [X0] : (k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.04/1.55    inference(definition_unfolding,[],[f45,f61])).
% 8.04/1.55  
% 8.04/1.55  fof(f3,axiom,(
% 8.04/1.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f38,plain,(
% 8.04/1.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f3])).
% 8.04/1.55  
% 8.04/1.55  fof(f63,plain,(
% 8.04/1.55    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) )),
% 8.04/1.55    inference(definition_unfolding,[],[f38,f60,f60])).
% 8.04/1.55  
% 8.04/1.55  fof(f2,axiom,(
% 8.04/1.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f37,plain,(
% 8.04/1.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.04/1.55    inference(cnf_transformation,[],[f2])).
% 8.04/1.55  
% 8.04/1.55  fof(f62,plain,(
% 8.04/1.55    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 8.04/1.55    inference(definition_unfolding,[],[f37,f61])).
% 8.04/1.55  
% 8.04/1.55  fof(f16,axiom,(
% 8.04/1.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f30,plain,(
% 8.04/1.55    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 8.04/1.55    inference(ennf_transformation,[],[f16])).
% 8.04/1.55  
% 8.04/1.55  fof(f52,plain,(
% 8.04/1.55    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f30])).
% 8.04/1.55  
% 8.04/1.55  fof(f1,axiom,(
% 8.04/1.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f20,plain,(
% 8.04/1.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 8.04/1.55    inference(ennf_transformation,[],[f1])).
% 8.04/1.55  
% 8.04/1.55  fof(f21,plain,(
% 8.04/1.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 8.04/1.55    inference(flattening,[],[f20])).
% 8.04/1.55  
% 8.04/1.55  fof(f36,plain,(
% 8.04/1.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f21])).
% 8.04/1.55  
% 8.04/1.55  fof(f55,plain,(
% 8.04/1.55    r1_tarski(sK0,sK1)),
% 8.04/1.55    inference(cnf_transformation,[],[f35])).
% 8.04/1.55  
% 8.04/1.55  fof(f13,axiom,(
% 8.04/1.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f26,plain,(
% 8.04/1.55    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 8.04/1.55    inference(ennf_transformation,[],[f13])).
% 8.04/1.55  
% 8.04/1.55  fof(f27,plain,(
% 8.04/1.55    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 8.04/1.55    inference(flattening,[],[f26])).
% 8.04/1.55  
% 8.04/1.55  fof(f48,plain,(
% 8.04/1.55    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f27])).
% 8.04/1.55  
% 8.04/1.55  fof(f15,axiom,(
% 8.04/1.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f29,plain,(
% 8.04/1.55    ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 8.04/1.55    inference(ennf_transformation,[],[f15])).
% 8.04/1.55  
% 8.04/1.55  fof(f50,plain,(
% 8.04/1.55    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f29])).
% 8.04/1.55  
% 8.04/1.55  fof(f11,axiom,(
% 8.04/1.55    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f23,plain,(
% 8.04/1.55    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 8.04/1.55    inference(ennf_transformation,[],[f11])).
% 8.04/1.55  
% 8.04/1.55  fof(f46,plain,(
% 8.04/1.55    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f23])).
% 8.04/1.55  
% 8.04/1.55  fof(f12,axiom,(
% 8.04/1.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f24,plain,(
% 8.04/1.55    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 8.04/1.55    inference(ennf_transformation,[],[f12])).
% 8.04/1.55  
% 8.04/1.55  fof(f25,plain,(
% 8.04/1.55    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 8.04/1.55    inference(flattening,[],[f24])).
% 8.04/1.55  
% 8.04/1.55  fof(f47,plain,(
% 8.04/1.55    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f25])).
% 8.04/1.55  
% 8.04/1.55  fof(f17,axiom,(
% 8.04/1.55    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 8.04/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.04/1.55  
% 8.04/1.55  fof(f31,plain,(
% 8.04/1.55    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 8.04/1.55    inference(ennf_transformation,[],[f17])).
% 8.04/1.55  
% 8.04/1.55  fof(f53,plain,(
% 8.04/1.55    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 8.04/1.55    inference(cnf_transformation,[],[f31])).
% 8.04/1.55  
% 8.04/1.55  fof(f56,plain,(
% 8.04/1.55    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 8.04/1.55    inference(cnf_transformation,[],[f35])).
% 8.04/1.55  
% 8.04/1.55  cnf(c_14,negated_conjecture,
% 8.04/1.55      ( v1_relat_1(sK2) ),
% 8.04/1.55      inference(cnf_transformation,[],[f54]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_157,negated_conjecture,
% 8.04/1.55      ( v1_relat_1(sK2) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_14]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_437,plain,
% 8.04/1.55      ( v1_relat_1(sK2) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_7,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 8.04/1.55      inference(cnf_transformation,[],[f49]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_164,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0_41) | v1_relat_1(k2_wellord1(X0_41,X0_42)) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_7]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_431,plain,
% 8.04/1.55      ( v1_relat_1(X0_41) != iProver_top
% 8.04/1.55      | v1_relat_1(k2_wellord1(X0_41,X0_42)) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_164]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_3,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0)
% 8.04/1.55      | k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 8.04/1.55      inference(cnf_transformation,[],[f64]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_168,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0_41)
% 8.04/1.55      | k3_tarski(k5_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k2_relat_1(X0_41))) = k3_relat_1(X0_41) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_3]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_427,plain,
% 8.04/1.55      ( k3_tarski(k5_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k1_relat_1(X0_41),k2_relat_1(X0_41))) = k3_relat_1(X0_41)
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1106,plain,
% 8.04/1.55      ( k3_tarski(k5_enumset1(k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k2_relat_1(k2_wellord1(X0_41,X0_42)))) = k3_relat_1(k2_wellord1(X0_41,X0_42))
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_431,c_427]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_20208,plain,
% 8.04/1.55      ( k3_tarski(k5_enumset1(k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k2_relat_1(k2_wellord1(sK2,X0_42)))) = k3_relat_1(k2_wellord1(sK2,X0_42)) ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_437,c_1106]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_2,plain,
% 8.04/1.55      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
% 8.04/1.55      inference(cnf_transformation,[],[f63]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_169,plain,
% 8.04/1.55      ( k5_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X1_42) = k5_enumset1(X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X0_42) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_2]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1,plain,
% 8.04/1.55      ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
% 8.04/1.55      inference(cnf_transformation,[],[f62]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_170,plain,
% 8.04/1.55      ( r1_tarski(X0_42,k3_tarski(k5_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X1_42))) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_1]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_426,plain,
% 8.04/1.55      ( r1_tarski(X0_42,k3_tarski(k5_enumset1(X0_42,X0_42,X0_42,X0_42,X0_42,X0_42,X1_42))) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_672,plain,
% 8.04/1.55      ( r1_tarski(X0_42,k3_tarski(k5_enumset1(X1_42,X1_42,X1_42,X1_42,X1_42,X1_42,X0_42))) = iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_169,c_426]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_21147,plain,
% 8.04/1.55      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_20208,c_672]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_9,plain,
% 8.04/1.55      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 8.04/1.55      inference(cnf_transformation,[],[f52]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_162,plain,
% 8.04/1.55      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42)
% 8.04/1.55      | ~ v1_relat_1(X0_41) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_9]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_433,plain,
% 8.04/1.55      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42) = iProver_top
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_0,plain,
% 8.04/1.55      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 8.04/1.55      inference(cnf_transformation,[],[f36]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_171,plain,
% 8.04/1.55      ( ~ r1_tarski(X0_42,X1_42)
% 8.04/1.55      | ~ r1_tarski(X2_42,X0_42)
% 8.04/1.55      | r1_tarski(X2_42,X1_42) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_0]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_425,plain,
% 8.04/1.55      ( r1_tarski(X0_42,X1_42) != iProver_top
% 8.04/1.55      | r1_tarski(X2_42,X0_42) != iProver_top
% 8.04/1.55      | r1_tarski(X2_42,X1_42) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_665,plain,
% 8.04/1.55      ( r1_tarski(X0_42,X1_42) = iProver_top
% 8.04/1.55      | r1_tarski(X0_42,k3_relat_1(k2_wellord1(X0_41,X1_42))) != iProver_top
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_433,c_425]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_21378,plain,
% 8.04/1.55      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X0_42) = iProver_top
% 8.04/1.55      | v1_relat_1(sK2) != iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_21147,c_665]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_15,plain,
% 8.04/1.55      ( v1_relat_1(sK2) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_26063,plain,
% 8.04/1.55      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X0_42) = iProver_top ),
% 8.04/1.55      inference(global_propositional_subsumption,
% 8.04/1.55                [status(thm)],
% 8.04/1.55                [c_21378,c_15]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_13,negated_conjecture,
% 8.04/1.55      ( r1_tarski(sK0,sK1) ),
% 8.04/1.55      inference(cnf_transformation,[],[f55]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_158,negated_conjecture,
% 8.04/1.55      ( r1_tarski(sK0,sK1) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_13]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_436,plain,
% 8.04/1.55      ( r1_tarski(sK0,sK1) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_664,plain,
% 8.04/1.55      ( r1_tarski(X0_42,sK1) = iProver_top
% 8.04/1.55      | r1_tarski(X0_42,sK0) != iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_436,c_425]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_26077,plain,
% 8.04/1.55      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_26063,c_664]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_6,plain,
% 8.04/1.55      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 8.04/1.55      | ~ v1_relat_1(X0)
% 8.04/1.55      | k8_relat_1(X1,X0) = X0 ),
% 8.04/1.55      inference(cnf_transformation,[],[f48]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_165,plain,
% 8.04/1.55      ( ~ r1_tarski(k2_relat_1(X0_41),X0_42)
% 8.04/1.55      | ~ v1_relat_1(X0_41)
% 8.04/1.55      | k8_relat_1(X0_42,X0_41) = X0_41 ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_6]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_430,plain,
% 8.04/1.55      ( k8_relat_1(X0_42,X0_41) = X0_41
% 8.04/1.55      | r1_tarski(k2_relat_1(X0_41),X0_42) != iProver_top
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_26187,plain,
% 8.04/1.55      ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
% 8.04/1.55      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_26077,c_430]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_16,plain,
% 8.04/1.55      ( r1_tarski(sK0,sK1) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_212,plain,
% 8.04/1.55      ( v1_relat_1(X0_41) != iProver_top
% 8.04/1.55      | v1_relat_1(k2_wellord1(X0_41,X0_42)) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_164]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_214,plain,
% 8.04/1.55      ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
% 8.04/1.55      | v1_relat_1(sK2) != iProver_top ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_212]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_218,plain,
% 8.04/1.55      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42) = iProver_top
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_220,plain,
% 8.04/1.55      ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top
% 8.04/1.55      | v1_relat_1(sK2) != iProver_top ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_218]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_992,plain,
% 8.04/1.55      ( ~ r1_tarski(X0_42,X1_42)
% 8.04/1.55      | ~ r1_tarski(k2_relat_1(k2_wellord1(X0_41,X2_42)),X0_42)
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(X0_41,X2_42)),X1_42) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_171]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1783,plain,
% 8.04/1.55      ( r1_tarski(k2_relat_1(k2_wellord1(X0_41,X0_42)),sK1)
% 8.04/1.55      | ~ r1_tarski(k2_relat_1(k2_wellord1(X0_41,X0_42)),sK0)
% 8.04/1.55      | ~ r1_tarski(sK0,sK1) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_992]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1784,plain,
% 8.04/1.55      ( r1_tarski(k2_relat_1(k2_wellord1(X0_41,X0_42)),sK1) = iProver_top
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(X0_41,X0_42)),sK0) != iProver_top
% 8.04/1.55      | r1_tarski(sK0,sK1) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_1783]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1786,plain,
% 8.04/1.55      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
% 8.04/1.55      | r1_tarski(sK0,sK1) != iProver_top ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_1784]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1793,plain,
% 8.04/1.55      ( ~ r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42)
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(X1_41,X1_42)),X0_42)
% 8.04/1.55      | ~ r1_tarski(k2_relat_1(k2_wellord1(X1_41,X1_42)),k3_relat_1(k2_wellord1(X0_41,X0_42))) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_992]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1794,plain,
% 8.04/1.55      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42) != iProver_top
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(X1_41,X1_42)),X0_42) = iProver_top
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(X1_41,X1_42)),k3_relat_1(k2_wellord1(X0_41,X0_42))) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_1793]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1796,plain,
% 8.04/1.55      ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0) != iProver_top
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) != iProver_top
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK0) = iProver_top ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_1794]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_536,plain,
% 8.04/1.55      ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),X0_42)
% 8.04/1.55      | ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 8.04/1.55      | k8_relat_1(X0_42,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_165]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_4574,plain,
% 8.04/1.55      ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
% 8.04/1.55      | ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 8.04/1.55      | k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_536]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_4577,plain,
% 8.04/1.55      ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
% 8.04/1.55      | r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) != iProver_top
% 8.04/1.55      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_4574]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_21161,plain,
% 8.04/1.55      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),k3_relat_1(k2_wellord1(sK2,sK0))) = iProver_top ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_21147]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_28907,plain,
% 8.04/1.55      ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
% 8.04/1.55      inference(global_propositional_subsumption,
% 8.04/1.55                [status(thm)],
% 8.04/1.55                [c_26187,c_15,c_16,c_214,c_220,c_1786,c_1796,c_4577,
% 8.04/1.55                 c_21161]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_8,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0)
% 8.04/1.55      | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
% 8.04/1.55      inference(cnf_transformation,[],[f50]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_163,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0_41)
% 8.04/1.55      | k7_relat_1(k8_relat_1(X0_42,X0_41),X0_42) = k2_wellord1(X0_41,X0_42) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_8]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_432,plain,
% 8.04/1.55      ( k7_relat_1(k8_relat_1(X0_42,X0_41),X0_42) = k2_wellord1(X0_41,X0_42)
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_163]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_611,plain,
% 8.04/1.55      ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(X0_41,X1_42)),X0_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42)
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_431,c_432]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_2014,plain,
% 8.04/1.55      ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(sK2,X1_42)),X0_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_437,c_611]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_28910,plain,
% 8.04/1.55      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_28907,c_2014]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_610,plain,
% 8.04/1.55      ( k7_relat_1(k8_relat_1(X0_42,sK2),X0_42) = k2_wellord1(sK2,X0_42) ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_437,c_432]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_4,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 8.04/1.55      inference(cnf_transformation,[],[f46]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_167,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0_41) | v1_relat_1(k8_relat_1(X0_42,X0_41)) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_4]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_428,plain,
% 8.04/1.55      ( v1_relat_1(X0_41) != iProver_top
% 8.04/1.55      | v1_relat_1(k8_relat_1(X0_42,X0_41)) = iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_5,plain,
% 8.04/1.55      ( ~ r1_tarski(X0,X1)
% 8.04/1.55      | ~ v1_relat_1(X2)
% 8.04/1.55      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
% 8.04/1.55      inference(cnf_transformation,[],[f47]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_166,plain,
% 8.04/1.55      ( ~ r1_tarski(X0_42,X1_42)
% 8.04/1.55      | ~ v1_relat_1(X0_41)
% 8.04/1.55      | k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) = k7_relat_1(X0_41,X0_42) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_5]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_429,plain,
% 8.04/1.55      ( k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) = k7_relat_1(X0_41,X0_42)
% 8.04/1.55      | r1_tarski(X0_42,X1_42) != iProver_top
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(predicate_to_equality,[status(thm)],[c_166]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1211,plain,
% 8.04/1.55      ( k7_relat_1(k7_relat_1(X0_41,sK0),sK1) = k7_relat_1(X0_41,sK0)
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_436,c_429]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1351,plain,
% 8.04/1.55      ( k7_relat_1(k7_relat_1(k8_relat_1(X0_42,X0_41),sK0),sK1) = k7_relat_1(k8_relat_1(X0_42,X0_41),sK0)
% 8.04/1.55      | v1_relat_1(X0_41) != iProver_top ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_428,c_1211]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1640,plain,
% 8.04/1.55      ( k7_relat_1(k7_relat_1(k8_relat_1(X0_42,sK2),sK0),sK1) = k7_relat_1(k8_relat_1(X0_42,sK2),sK0) ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_437,c_1351]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1781,plain,
% 8.04/1.55      ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k8_relat_1(sK0,sK2),sK0) ),
% 8.04/1.55      inference(superposition,[status(thm)],[c_610,c_1640]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_1782,plain,
% 8.04/1.55      ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
% 8.04/1.55      inference(demodulation,[status(thm)],[c_1781,c_610]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_28911,plain,
% 8.04/1.55      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
% 8.04/1.55      inference(light_normalisation,[status(thm)],[c_28910,c_1782]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_11,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0)
% 8.04/1.55      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 8.04/1.55      inference(cnf_transformation,[],[f53]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_160,plain,
% 8.04/1.55      ( ~ v1_relat_1(X0_41)
% 8.04/1.55      | k2_wellord1(k2_wellord1(X0_41,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_11]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_567,plain,
% 8.04/1.55      ( ~ v1_relat_1(sK2)
% 8.04/1.55      | k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_160]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_176,plain,
% 8.04/1.55      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 8.04/1.55      theory(equality) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_459,plain,
% 8.04/1.55      ( X0_41 != X1_41
% 8.04/1.55      | k2_wellord1(sK2,sK0) != X1_41
% 8.04/1.55      | k2_wellord1(sK2,sK0) = X0_41 ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_176]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_468,plain,
% 8.04/1.55      ( X0_41 != k2_wellord1(sK2,sK0)
% 8.04/1.55      | k2_wellord1(sK2,sK0) = X0_41
% 8.04/1.55      | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_459]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_489,plain,
% 8.04/1.55      ( k2_wellord1(X0_41,X0_42) != k2_wellord1(sK2,sK0)
% 8.04/1.55      | k2_wellord1(sK2,sK0) = k2_wellord1(X0_41,X0_42)
% 8.04/1.55      | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_468]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_566,plain,
% 8.04/1.55      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0)
% 8.04/1.55      | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)
% 8.04/1.55      | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_489]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_453,plain,
% 8.04/1.55      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X0_41
% 8.04/1.55      | k2_wellord1(sK2,sK0) != X0_41
% 8.04/1.55      | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_176]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_460,plain,
% 8.04/1.55      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(X0_41,X0_42)
% 8.04/1.55      | k2_wellord1(sK2,sK0) != k2_wellord1(X0_41,X0_42)
% 8.04/1.55      | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_453]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_472,plain,
% 8.04/1.55      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
% 8.04/1.55      | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)
% 8.04/1.55      | k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_460]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_12,negated_conjecture,
% 8.04/1.55      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 8.04/1.55      inference(cnf_transformation,[],[f56]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_159,negated_conjecture,
% 8.04/1.55      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 8.04/1.55      inference(subtyping,[status(esa)],[c_12]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_174,plain,( X0_42 = X0_42 ),theory(equality) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_195,plain,
% 8.04/1.55      ( sK0 = sK0 ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_174]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_173,plain,( X0_41 = X0_41 ),theory(equality) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_194,plain,
% 8.04/1.55      ( sK2 = sK2 ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_173]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_185,plain,
% 8.04/1.55      ( X0_42 != X1_42
% 8.04/1.55      | X0_41 != X1_41
% 8.04/1.55      | k2_wellord1(X0_41,X0_42) = k2_wellord1(X1_41,X1_42) ),
% 8.04/1.55      theory(equality) ).
% 8.04/1.55  
% 8.04/1.55  cnf(c_192,plain,
% 8.04/1.55      ( sK0 != sK0
% 8.04/1.55      | k2_wellord1(sK2,sK0) = k2_wellord1(sK2,sK0)
% 8.04/1.55      | sK2 != sK2 ),
% 8.04/1.55      inference(instantiation,[status(thm)],[c_185]) ).
% 8.04/1.55  
% 8.04/1.55  cnf(contradiction,plain,
% 8.04/1.55      ( $false ),
% 8.04/1.55      inference(minisat,
% 8.04/1.55                [status(thm)],
% 8.04/1.55                [c_28911,c_567,c_566,c_472,c_159,c_195,c_194,c_192,c_14]) ).
% 8.04/1.55  
% 8.04/1.55  
% 8.04/1.55  % SZS output end CNFRefutation for theBenchmark.p
% 8.04/1.55  
% 8.04/1.55  ------                               Statistics
% 8.04/1.55  
% 8.04/1.55  ------ General
% 8.04/1.55  
% 8.04/1.55  abstr_ref_over_cycles:                  0
% 8.04/1.55  abstr_ref_under_cycles:                 0
% 8.04/1.55  gc_basic_clause_elim:                   0
% 8.04/1.55  forced_gc_time:                         0
% 8.04/1.55  parsing_time:                           0.007
% 8.04/1.55  unif_index_cands_time:                  0.
% 8.04/1.55  unif_index_add_time:                    0.
% 8.04/1.55  orderings_time:                         0.
% 8.04/1.55  out_proof_time:                         0.012
% 8.04/1.55  total_time:                             0.969
% 8.04/1.55  num_of_symbols:                         44
% 8.04/1.55  num_of_terms:                           27037
% 8.04/1.55  
% 8.04/1.55  ------ Preprocessing
% 8.04/1.55  
% 8.04/1.55  num_of_splits:                          0
% 8.04/1.55  num_of_split_atoms:                     0
% 8.04/1.55  num_of_reused_defs:                     0
% 8.04/1.55  num_eq_ax_congr_red:                    10
% 8.04/1.55  num_of_sem_filtered_clauses:            1
% 8.04/1.55  num_of_subtypes:                        3
% 8.04/1.55  monotx_restored_types:                  0
% 8.04/1.55  sat_num_of_epr_types:                   0
% 8.04/1.55  sat_num_of_non_cyclic_types:            0
% 8.04/1.55  sat_guarded_non_collapsed_types:        1
% 8.04/1.55  num_pure_diseq_elim:                    0
% 8.04/1.55  simp_replaced_by:                       0
% 8.04/1.55  res_preprocessed:                       72
% 8.04/1.55  prep_upred:                             0
% 8.04/1.55  prep_unflattend:                        0
% 8.04/1.55  smt_new_axioms:                         0
% 8.04/1.55  pred_elim_cands:                        2
% 8.04/1.55  pred_elim:                              0
% 8.04/1.55  pred_elim_cl:                           0
% 8.04/1.55  pred_elim_cycles:                       1
% 8.04/1.55  merged_defs:                            0
% 8.04/1.55  merged_defs_ncl:                        0
% 8.04/1.55  bin_hyper_res:                          0
% 8.04/1.55  prep_cycles:                            3
% 8.04/1.55  pred_elim_time:                         0.
% 8.04/1.55  splitting_time:                         0.
% 8.04/1.55  sem_filter_time:                        0.
% 8.04/1.55  monotx_time:                            0.
% 8.04/1.55  subtype_inf_time:                       0.
% 8.04/1.55  
% 8.04/1.55  ------ Problem properties
% 8.04/1.55  
% 8.04/1.55  clauses:                                15
% 8.04/1.55  conjectures:                            3
% 8.04/1.55  epr:                                    3
% 8.04/1.55  horn:                                   15
% 8.04/1.55  ground:                                 3
% 8.04/1.55  unary:                                  5
% 8.04/1.55  binary:                                 7
% 8.04/1.55  lits:                                   28
% 8.04/1.55  lits_eq:                                7
% 8.04/1.55  fd_pure:                                0
% 8.04/1.55  fd_pseudo:                              0
% 8.04/1.55  fd_cond:                                0
% 8.04/1.55  fd_pseudo_cond:                         0
% 8.04/1.55  ac_symbols:                             0
% 8.04/1.55  
% 8.04/1.55  ------ Propositional Solver
% 8.04/1.55  
% 8.04/1.55  prop_solver_calls:                      30
% 8.04/1.55  prop_fast_solver_calls:                 696
% 8.04/1.55  smt_solver_calls:                       0
% 8.04/1.55  smt_fast_solver_calls:                  0
% 8.04/1.55  prop_num_of_clauses:                    10320
% 8.04/1.55  prop_preprocess_simplified:             12931
% 8.04/1.55  prop_fo_subsumed:                       14
% 8.04/1.55  prop_solver_time:                       0.
% 8.04/1.55  smt_solver_time:                        0.
% 8.04/1.55  smt_fast_solver_time:                   0.
% 8.04/1.55  prop_fast_solver_time:                  0.
% 8.04/1.55  prop_unsat_core_time:                   0.001
% 8.04/1.55  
% 8.04/1.55  ------ QBF
% 8.04/1.55  
% 8.04/1.55  qbf_q_res:                              0
% 8.04/1.55  qbf_num_tautologies:                    0
% 8.04/1.55  qbf_prep_cycles:                        0
% 8.04/1.55  
% 8.04/1.55  ------ BMC1
% 8.04/1.55  
% 8.04/1.55  bmc1_current_bound:                     -1
% 8.04/1.55  bmc1_last_solved_bound:                 -1
% 8.04/1.55  bmc1_unsat_core_size:                   -1
% 8.04/1.55  bmc1_unsat_core_parents_size:           -1
% 8.04/1.55  bmc1_merge_next_fun:                    0
% 8.04/1.55  bmc1_unsat_core_clauses_time:           0.
% 8.04/1.55  
% 8.04/1.55  ------ Instantiation
% 8.04/1.55  
% 8.04/1.55  inst_num_of_clauses:                    2626
% 8.04/1.55  inst_num_in_passive:                    394
% 8.04/1.55  inst_num_in_active:                     1107
% 8.04/1.55  inst_num_in_unprocessed:                1126
% 8.04/1.55  inst_num_of_loops:                      1130
% 8.04/1.55  inst_num_of_learning_restarts:          0
% 8.04/1.55  inst_num_moves_active_passive:          18
% 8.04/1.55  inst_lit_activity:                      0
% 8.04/1.55  inst_lit_activity_moves:                0
% 8.04/1.55  inst_num_tautologies:                   0
% 8.04/1.55  inst_num_prop_implied:                  0
% 8.04/1.55  inst_num_existing_simplified:           0
% 8.04/1.55  inst_num_eq_res_simplified:             0
% 8.04/1.55  inst_num_child_elim:                    0
% 8.04/1.55  inst_num_of_dismatching_blockings:      4487
% 8.04/1.55  inst_num_of_non_proper_insts:           5899
% 8.04/1.55  inst_num_of_duplicates:                 0
% 8.04/1.55  inst_inst_num_from_inst_to_res:         0
% 8.04/1.55  inst_dismatching_checking_time:         0.
% 8.04/1.55  
% 8.04/1.55  ------ Resolution
% 8.04/1.55  
% 8.04/1.55  res_num_of_clauses:                     0
% 8.04/1.55  res_num_in_passive:                     0
% 8.04/1.55  res_num_in_active:                      0
% 8.04/1.55  res_num_of_loops:                       75
% 8.04/1.55  res_forward_subset_subsumed:            469
% 8.04/1.55  res_backward_subset_subsumed:           2
% 8.04/1.55  res_forward_subsumed:                   0
% 8.04/1.55  res_backward_subsumed:                  0
% 8.04/1.55  res_forward_subsumption_resolution:     0
% 8.04/1.55  res_backward_subsumption_resolution:    0
% 8.04/1.55  res_clause_to_clause_subsumption:       7597
% 8.04/1.55  res_orphan_elimination:                 0
% 8.04/1.55  res_tautology_del:                      877
% 8.04/1.55  res_num_eq_res_simplified:              0
% 8.04/1.55  res_num_sel_changes:                    0
% 8.04/1.55  res_moves_from_active_to_pass:          0
% 8.04/1.55  
% 8.04/1.55  ------ Superposition
% 8.04/1.55  
% 8.04/1.55  sup_time_total:                         0.
% 8.04/1.55  sup_time_generating:                    0.
% 8.04/1.55  sup_time_sim_full:                      0.
% 8.04/1.55  sup_time_sim_immed:                     0.
% 8.04/1.55  
% 8.04/1.55  sup_num_of_clauses:                     2057
% 8.04/1.55  sup_num_in_active:                      220
% 8.04/1.55  sup_num_in_passive:                     1837
% 8.04/1.55  sup_num_of_loops:                       225
% 8.04/1.55  sup_fw_superposition:                   2803
% 8.04/1.55  sup_bw_superposition:                   1879
% 8.04/1.55  sup_immediate_simplified:               660
% 8.04/1.55  sup_given_eliminated:                   0
% 8.04/1.55  comparisons_done:                       0
% 8.04/1.55  comparisons_avoided:                    0
% 8.04/1.55  
% 8.04/1.55  ------ Simplifications
% 8.04/1.55  
% 8.04/1.55  
% 8.04/1.55  sim_fw_subset_subsumed:                 30
% 8.04/1.55  sim_bw_subset_subsumed:                 47
% 8.04/1.55  sim_fw_subsumed:                        143
% 8.04/1.55  sim_bw_subsumed:                        7
% 8.04/1.55  sim_fw_subsumption_res:                 0
% 8.04/1.55  sim_bw_subsumption_res:                 0
% 8.04/1.55  sim_tautology_del:                      7
% 8.04/1.55  sim_eq_tautology_del:                   46
% 8.04/1.55  sim_eq_res_simp:                        0
% 8.04/1.55  sim_fw_demodulated:                     150
% 8.04/1.55  sim_bw_demodulated:                     25
% 8.04/1.55  sim_light_normalised:                   391
% 8.04/1.55  sim_joinable_taut:                      0
% 8.04/1.55  sim_joinable_simp:                      0
% 8.04/1.55  sim_ac_normalised:                      0
% 8.04/1.55  sim_smt_subsumption:                    0
% 8.04/1.55  
%------------------------------------------------------------------------------
