%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:22 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 255 expanded)
%              Number of clauses        :   79 ( 105 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  284 ( 574 expanded)
%              Number of equality atoms :  112 ( 198 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f32])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f55,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f37,f37])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f50,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_10,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_282,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_546,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_277,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_550,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_284,plain,
    ( ~ v1_relat_1(X0_43)
    | v1_relat_1(k2_wellord1(X0_43,X0_42)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_544,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_wellord1(X0_43,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_286,plain,
    ( ~ v1_relat_1(X0_43)
    | k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_542,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_993,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))) = k3_relat_1(k2_wellord1(X0_43,X0_42))
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_544,c_542])).

cnf(c_3752,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k2_relat_1(k2_wellord1(sK2,X0_42)))) = k3_relat_1(k2_wellord1(sK2,X0_42)) ),
    inference(superposition,[status(thm)],[c_550,c_993])).

cnf(c_2,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_287,plain,
    ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_289,plain,
    ( r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X2_42)),X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_540,plain,
    ( r1_tarski(X0_42,X1_42) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X2_42)),X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_863,plain,
    ( r1_tarski(X0_42,X1_42) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X2_42,X2_42,X0_42)),X1_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_287,c_540])).

cnf(c_4123,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,X0_42)),X1_42) != iProver_top
    | r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X1_42) = iProver_top ),
    inference(superposition,[status(thm)],[c_3752,c_863])).

cnf(c_4464,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X0_42) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_4123])).

cnf(c_16,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4586,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X0_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4464,c_16])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_278,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_549,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_288,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X2_42,X0_42)
    | r1_tarski(X2_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_541,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | r1_tarski(X2_42,X0_42) != iProver_top
    | r1_tarski(X2_42,X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_1620,plain,
    ( r1_tarski(X0_42,sK1) = iProver_top
    | r1_tarski(X0_42,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_541])).

cnf(c_4595,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4586,c_1620])).

cnf(c_6,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_285,plain,
    ( ~ r1_tarski(k2_relat_1(X0_43),X0_42)
    | ~ v1_relat_1(X0_43)
    | k8_relat_1(X0_42,X0_43) = X0_43 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_543,plain,
    ( k8_relat_1(X0_42,X0_43) = X0_43
    | r1_tarski(k2_relat_1(X0_43),X0_42) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_4647,plain,
    ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4595,c_543])).

cnf(c_324,plain,
    ( v1_relat_1(X0_43) != iProver_top
    | v1_relat_1(k2_wellord1(X0_43,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_326,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_10015,plain,
    ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4647,c_16,c_326])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_283,plain,
    ( ~ v1_relat_1(X0_43)
    | k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k2_wellord1(X0_43,X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_545,plain,
    ( k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k2_wellord1(X0_43,X0_42)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_778,plain,
    ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(X0_43,X1_42)),X0_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_544,c_545])).

cnf(c_2493,plain,
    ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(sK2,X1_42)),X0_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_550,c_778])).

cnf(c_10018,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_10015,c_2493])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_280,plain,
    ( ~ v1_relat_1(X0_43)
    | k2_wellord1(k2_wellord1(X0_43,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_548,plain,
    ( k2_wellord1(k2_wellord1(X0_43,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_1039,plain,
    ( k2_wellord1(k2_wellord1(sK2,X0_42),X1_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_550,c_548])).

cnf(c_13,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_279,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1165,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_1039,c_279])).

cnf(c_10614,plain,
    ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_10018,c_1165])).

cnf(c_3,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_168,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_276,plain,
    ( ~ r1_tarski(k1_relat_1(X0_43),X0_42)
    | ~ v1_relat_1(X0_43)
    | k7_relat_1(X0_43,X0_42) = X0_43 ),
    inference(subtyping,[status(esa)],[c_168])).

cnf(c_672,plain,
    ( ~ r1_tarski(k1_relat_1(X0_43),sK1)
    | ~ v1_relat_1(X0_43)
    | k7_relat_1(X0_43,sK1) = X0_43 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_2289,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK1)
    | ~ v1_relat_1(k2_wellord1(X0_43,X0_42))
    | k7_relat_1(k2_wellord1(X0_43,X0_42),sK1) = k2_wellord1(X0_43,X0_42) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_2291,plain,
    ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_2289])).

cnf(c_698,plain,
    ( r1_tarski(X0_42,sK1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X1_42)),sK1) ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_824,plain,
    ( r1_tarski(k1_relat_1(X0_43),sK1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),X0_42)),sK1) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1597,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))),sK1) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_1603,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))),sK1) ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_635,plain,
    ( r1_tarski(X0_42,sK1)
    | ~ r1_tarski(X0_42,sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_697,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X1_42)),sK1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X1_42)),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_1589,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))),sK1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_1593,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))),sK1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))),sK0)
    | ~ r1_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_890,plain,
    ( ~ v1_relat_1(k2_wellord1(X0_43,X0_42))
    | k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))) = k3_relat_1(k2_wellord1(X0_43,X0_42)) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_896,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))) = k3_relat_1(k2_wellord1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_297,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | r1_tarski(X2_42,X3_42)
    | X2_42 != X0_42
    | X3_42 != X1_42 ),
    theory(equality)).

cnf(c_663,plain,
    ( r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(k3_relat_1(k2_wellord1(X0_43,X2_42)),X2_42)
    | X1_42 != X2_42
    | X0_42 != k3_relat_1(k2_wellord1(X0_43,X2_42)) ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_889,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
    | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))),X1_42)
    | X1_42 != X0_42
    | k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))) != k3_relat_1(k2_wellord1(X0_43,X0_42)) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_892,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0)
    | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))),sK0)
    | k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))) != k3_relat_1(k2_wellord1(sK2,sK0))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_331,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_325,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_291,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_312,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10614,c_2291,c_1603,c_1593,c_896,c_892,c_331,c_325,c_312,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:17:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.37/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/0.98  
% 3.37/0.98  ------  iProver source info
% 3.37/0.98  
% 3.37/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.37/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/0.98  git: non_committed_changes: false
% 3.37/0.98  git: last_make_outside_of_git: false
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.98  --extra_neg_conj                        none
% 3.37/0.98  --large_theory_mode                     true
% 3.37/0.98  --prolific_symb_bound                   200
% 3.37/0.98  --lt_threshold                          2000
% 3.37/0.98  --clause_weak_htbl                      true
% 3.37/0.98  --gc_record_bc_elim                     false
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing Options
% 3.37/0.98  
% 3.37/0.98  --preprocessing_flag                    true
% 3.37/0.98  --time_out_prep_mult                    0.1
% 3.37/0.98  --splitting_mode                        input
% 3.37/0.98  --splitting_grd                         true
% 3.37/0.98  --splitting_cvd                         false
% 3.37/0.98  --splitting_cvd_svl                     false
% 3.37/0.98  --splitting_nvd                         32
% 3.37/0.98  --sub_typing                            true
% 3.37/0.98  --prep_gs_sim                           true
% 3.37/0.98  --prep_unflatten                        true
% 3.37/0.98  --prep_res_sim                          true
% 3.37/0.98  --prep_upred                            true
% 3.37/0.98  --prep_sem_filter                       exhaustive
% 3.37/0.98  --prep_sem_filter_out                   false
% 3.37/0.98  --pred_elim                             true
% 3.37/0.98  --res_sim_input                         true
% 3.37/0.98  --eq_ax_congr_red                       true
% 3.37/0.98  --pure_diseq_elim                       true
% 3.37/0.98  --brand_transform                       false
% 3.37/0.98  --non_eq_to_eq                          false
% 3.37/0.98  --prep_def_merge                        true
% 3.37/0.98  --prep_def_merge_prop_impl              false
% 3.37/0.98  --prep_def_merge_mbd                    true
% 3.37/0.98  --prep_def_merge_tr_red                 false
% 3.37/0.98  --prep_def_merge_tr_cl                  false
% 3.37/0.98  --smt_preprocessing                     true
% 3.37/0.98  --smt_ac_axioms                         fast
% 3.37/0.98  --preprocessed_out                      false
% 3.37/0.98  --preprocessed_stats                    false
% 3.37/0.98  
% 3.37/0.98  ------ Abstraction refinement Options
% 3.37/0.98  
% 3.37/0.98  --abstr_ref                             []
% 3.37/0.98  --abstr_ref_prep                        false
% 3.37/0.98  --abstr_ref_until_sat                   false
% 3.37/0.98  --abstr_ref_sig_restrict                funpre
% 3.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.98  --abstr_ref_under                       []
% 3.37/0.98  
% 3.37/0.98  ------ SAT Options
% 3.37/0.98  
% 3.37/0.98  --sat_mode                              false
% 3.37/0.98  --sat_fm_restart_options                ""
% 3.37/0.98  --sat_gr_def                            false
% 3.37/0.98  --sat_epr_types                         true
% 3.37/0.98  --sat_non_cyclic_types                  false
% 3.37/0.98  --sat_finite_models                     false
% 3.37/0.98  --sat_fm_lemmas                         false
% 3.37/0.98  --sat_fm_prep                           false
% 3.37/0.98  --sat_fm_uc_incr                        true
% 3.37/0.98  --sat_out_model                         small
% 3.37/0.98  --sat_out_clauses                       false
% 3.37/0.98  
% 3.37/0.98  ------ QBF Options
% 3.37/0.98  
% 3.37/0.98  --qbf_mode                              false
% 3.37/0.98  --qbf_elim_univ                         false
% 3.37/0.98  --qbf_dom_inst                          none
% 3.37/0.98  --qbf_dom_pre_inst                      false
% 3.37/0.98  --qbf_sk_in                             false
% 3.37/0.98  --qbf_pred_elim                         true
% 3.37/0.98  --qbf_split                             512
% 3.37/0.98  
% 3.37/0.98  ------ BMC1 Options
% 3.37/0.98  
% 3.37/0.98  --bmc1_incremental                      false
% 3.37/0.98  --bmc1_axioms                           reachable_all
% 3.37/0.98  --bmc1_min_bound                        0
% 3.37/0.98  --bmc1_max_bound                        -1
% 3.37/0.98  --bmc1_max_bound_default                -1
% 3.37/0.98  --bmc1_symbol_reachability              true
% 3.37/0.98  --bmc1_property_lemmas                  false
% 3.37/0.98  --bmc1_k_induction                      false
% 3.37/0.98  --bmc1_non_equiv_states                 false
% 3.37/0.98  --bmc1_deadlock                         false
% 3.37/0.98  --bmc1_ucm                              false
% 3.37/0.98  --bmc1_add_unsat_core                   none
% 3.37/0.98  --bmc1_unsat_core_children              false
% 3.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.98  --bmc1_out_stat                         full
% 3.37/0.98  --bmc1_ground_init                      false
% 3.37/0.98  --bmc1_pre_inst_next_state              false
% 3.37/0.98  --bmc1_pre_inst_state                   false
% 3.37/0.98  --bmc1_pre_inst_reach_state             false
% 3.37/0.98  --bmc1_out_unsat_core                   false
% 3.37/0.98  --bmc1_aig_witness_out                  false
% 3.37/0.98  --bmc1_verbose                          false
% 3.37/0.98  --bmc1_dump_clauses_tptp                false
% 3.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.98  --bmc1_dump_file                        -
% 3.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.98  --bmc1_ucm_extend_mode                  1
% 3.37/0.98  --bmc1_ucm_init_mode                    2
% 3.37/0.98  --bmc1_ucm_cone_mode                    none
% 3.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.98  --bmc1_ucm_relax_model                  4
% 3.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.98  --bmc1_ucm_layered_model                none
% 3.37/0.98  --bmc1_ucm_max_lemma_size               10
% 3.37/0.98  
% 3.37/0.98  ------ AIG Options
% 3.37/0.98  
% 3.37/0.98  --aig_mode                              false
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation Options
% 3.37/0.98  
% 3.37/0.98  --instantiation_flag                    true
% 3.37/0.98  --inst_sos_flag                         false
% 3.37/0.98  --inst_sos_phase                        true
% 3.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel_side                     num_symb
% 3.37/0.98  --inst_solver_per_active                1400
% 3.37/0.98  --inst_solver_calls_frac                1.
% 3.37/0.98  --inst_passive_queue_type               priority_queues
% 3.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.98  --inst_passive_queues_freq              [25;2]
% 3.37/0.98  --inst_dismatching                      true
% 3.37/0.98  --inst_eager_unprocessed_to_passive     true
% 3.37/0.98  --inst_prop_sim_given                   true
% 3.37/0.98  --inst_prop_sim_new                     false
% 3.37/0.98  --inst_subs_new                         false
% 3.37/0.98  --inst_eq_res_simp                      false
% 3.37/0.98  --inst_subs_given                       false
% 3.37/0.98  --inst_orphan_elimination               true
% 3.37/0.98  --inst_learning_loop_flag               true
% 3.37/0.98  --inst_learning_start                   3000
% 3.37/0.98  --inst_learning_factor                  2
% 3.37/0.98  --inst_start_prop_sim_after_learn       3
% 3.37/0.98  --inst_sel_renew                        solver
% 3.37/0.98  --inst_lit_activity_flag                true
% 3.37/0.98  --inst_restr_to_given                   false
% 3.37/0.98  --inst_activity_threshold               500
% 3.37/0.98  --inst_out_proof                        true
% 3.37/0.98  
% 3.37/0.98  ------ Resolution Options
% 3.37/0.98  
% 3.37/0.98  --resolution_flag                       true
% 3.37/0.98  --res_lit_sel                           adaptive
% 3.37/0.98  --res_lit_sel_side                      none
% 3.37/0.98  --res_ordering                          kbo
% 3.37/0.98  --res_to_prop_solver                    active
% 3.37/0.98  --res_prop_simpl_new                    false
% 3.37/0.98  --res_prop_simpl_given                  true
% 3.37/0.98  --res_passive_queue_type                priority_queues
% 3.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.98  --res_passive_queues_freq               [15;5]
% 3.37/0.98  --res_forward_subs                      full
% 3.37/0.98  --res_backward_subs                     full
% 3.37/0.98  --res_forward_subs_resolution           true
% 3.37/0.98  --res_backward_subs_resolution          true
% 3.37/0.98  --res_orphan_elimination                true
% 3.37/0.98  --res_time_limit                        2.
% 3.37/0.98  --res_out_proof                         true
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Options
% 3.37/0.98  
% 3.37/0.98  --superposition_flag                    true
% 3.37/0.98  --sup_passive_queue_type                priority_queues
% 3.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.98  --demod_completeness_check              fast
% 3.37/0.98  --demod_use_ground                      true
% 3.37/0.98  --sup_to_prop_solver                    passive
% 3.37/0.98  --sup_prop_simpl_new                    true
% 3.37/0.98  --sup_prop_simpl_given                  true
% 3.37/0.98  --sup_fun_splitting                     false
% 3.37/0.98  --sup_smt_interval                      50000
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Simplification Setup
% 3.37/0.98  
% 3.37/0.98  --sup_indices_passive                   []
% 3.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_full_bw                           [BwDemod]
% 3.37/0.98  --sup_immed_triv                        [TrivRules]
% 3.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_immed_bw_main                     []
% 3.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  
% 3.37/0.98  ------ Combination Options
% 3.37/0.98  
% 3.37/0.98  --comb_res_mult                         3
% 3.37/0.98  --comb_sup_mult                         2
% 3.37/0.98  --comb_inst_mult                        10
% 3.37/0.98  
% 3.37/0.98  ------ Debug Options
% 3.37/0.98  
% 3.37/0.98  --dbg_backtrace                         false
% 3.37/0.98  --dbg_dump_prop_clauses                 false
% 3.37/0.98  --dbg_dump_prop_clauses_file            -
% 3.37/0.98  --dbg_out_stat                          false
% 3.37/0.98  ------ Parsing...
% 3.37/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/0.98  ------ Proving...
% 3.37/0.98  ------ Problem Properties 
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  clauses                                 14
% 3.37/0.98  conjectures                             3
% 3.37/0.98  EPR                                     3
% 3.37/0.98  Horn                                    14
% 3.37/0.98  unary                                   4
% 3.37/0.98  binary                                  7
% 3.37/0.98  lits                                    27
% 3.37/0.98  lits eq                                 7
% 3.37/0.98  fd_pure                                 0
% 3.37/0.98  fd_pseudo                               0
% 3.37/0.98  fd_cond                                 0
% 3.37/0.98  fd_pseudo_cond                          0
% 3.37/0.98  AC symbols                              0
% 3.37/0.98  
% 3.37/0.98  ------ Schedule dynamic 5 is on 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  ------ 
% 3.37/0.98  Current options:
% 3.37/0.98  ------ 
% 3.37/0.98  
% 3.37/0.98  ------ Input Options
% 3.37/0.98  
% 3.37/0.98  --out_options                           all
% 3.37/0.98  --tptp_safe_out                         true
% 3.37/0.98  --problem_path                          ""
% 3.37/0.98  --include_path                          ""
% 3.37/0.98  --clausifier                            res/vclausify_rel
% 3.37/0.98  --clausifier_options                    --mode clausify
% 3.37/0.98  --stdin                                 false
% 3.37/0.98  --stats_out                             all
% 3.37/0.98  
% 3.37/0.98  ------ General Options
% 3.37/0.98  
% 3.37/0.98  --fof                                   false
% 3.37/0.98  --time_out_real                         305.
% 3.37/0.98  --time_out_virtual                      -1.
% 3.37/0.98  --symbol_type_check                     false
% 3.37/0.98  --clausify_out                          false
% 3.37/0.98  --sig_cnt_out                           false
% 3.37/0.98  --trig_cnt_out                          false
% 3.37/0.98  --trig_cnt_out_tolerance                1.
% 3.37/0.98  --trig_cnt_out_sk_spl                   false
% 3.37/0.98  --abstr_cl_out                          false
% 3.37/0.98  
% 3.37/0.98  ------ Global Options
% 3.37/0.98  
% 3.37/0.98  --schedule                              default
% 3.37/0.98  --add_important_lit                     false
% 3.37/0.98  --prop_solver_per_cl                    1000
% 3.37/0.98  --min_unsat_core                        false
% 3.37/0.98  --soft_assumptions                      false
% 3.37/0.98  --soft_lemma_size                       3
% 3.37/0.98  --prop_impl_unit_size                   0
% 3.37/0.98  --prop_impl_unit                        []
% 3.37/0.98  --share_sel_clauses                     true
% 3.37/0.98  --reset_solvers                         false
% 3.37/0.98  --bc_imp_inh                            [conj_cone]
% 3.37/0.98  --conj_cone_tolerance                   3.
% 3.37/0.98  --extra_neg_conj                        none
% 3.37/0.98  --large_theory_mode                     true
% 3.37/0.98  --prolific_symb_bound                   200
% 3.37/0.98  --lt_threshold                          2000
% 3.37/0.98  --clause_weak_htbl                      true
% 3.37/0.98  --gc_record_bc_elim                     false
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing Options
% 3.37/0.98  
% 3.37/0.98  --preprocessing_flag                    true
% 3.37/0.98  --time_out_prep_mult                    0.1
% 3.37/0.98  --splitting_mode                        input
% 3.37/0.98  --splitting_grd                         true
% 3.37/0.98  --splitting_cvd                         false
% 3.37/0.98  --splitting_cvd_svl                     false
% 3.37/0.98  --splitting_nvd                         32
% 3.37/0.98  --sub_typing                            true
% 3.37/0.98  --prep_gs_sim                           true
% 3.37/0.98  --prep_unflatten                        true
% 3.37/0.98  --prep_res_sim                          true
% 3.37/0.98  --prep_upred                            true
% 3.37/0.98  --prep_sem_filter                       exhaustive
% 3.37/0.98  --prep_sem_filter_out                   false
% 3.37/0.98  --pred_elim                             true
% 3.37/0.98  --res_sim_input                         true
% 3.37/0.98  --eq_ax_congr_red                       true
% 3.37/0.98  --pure_diseq_elim                       true
% 3.37/0.98  --brand_transform                       false
% 3.37/0.98  --non_eq_to_eq                          false
% 3.37/0.98  --prep_def_merge                        true
% 3.37/0.98  --prep_def_merge_prop_impl              false
% 3.37/0.98  --prep_def_merge_mbd                    true
% 3.37/0.98  --prep_def_merge_tr_red                 false
% 3.37/0.98  --prep_def_merge_tr_cl                  false
% 3.37/0.98  --smt_preprocessing                     true
% 3.37/0.98  --smt_ac_axioms                         fast
% 3.37/0.98  --preprocessed_out                      false
% 3.37/0.98  --preprocessed_stats                    false
% 3.37/0.98  
% 3.37/0.98  ------ Abstraction refinement Options
% 3.37/0.98  
% 3.37/0.98  --abstr_ref                             []
% 3.37/0.98  --abstr_ref_prep                        false
% 3.37/0.98  --abstr_ref_until_sat                   false
% 3.37/0.98  --abstr_ref_sig_restrict                funpre
% 3.37/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/0.98  --abstr_ref_under                       []
% 3.37/0.98  
% 3.37/0.98  ------ SAT Options
% 3.37/0.98  
% 3.37/0.98  --sat_mode                              false
% 3.37/0.98  --sat_fm_restart_options                ""
% 3.37/0.98  --sat_gr_def                            false
% 3.37/0.98  --sat_epr_types                         true
% 3.37/0.98  --sat_non_cyclic_types                  false
% 3.37/0.98  --sat_finite_models                     false
% 3.37/0.98  --sat_fm_lemmas                         false
% 3.37/0.98  --sat_fm_prep                           false
% 3.37/0.98  --sat_fm_uc_incr                        true
% 3.37/0.98  --sat_out_model                         small
% 3.37/0.98  --sat_out_clauses                       false
% 3.37/0.98  
% 3.37/0.98  ------ QBF Options
% 3.37/0.98  
% 3.37/0.98  --qbf_mode                              false
% 3.37/0.98  --qbf_elim_univ                         false
% 3.37/0.98  --qbf_dom_inst                          none
% 3.37/0.98  --qbf_dom_pre_inst                      false
% 3.37/0.98  --qbf_sk_in                             false
% 3.37/0.98  --qbf_pred_elim                         true
% 3.37/0.98  --qbf_split                             512
% 3.37/0.98  
% 3.37/0.98  ------ BMC1 Options
% 3.37/0.98  
% 3.37/0.98  --bmc1_incremental                      false
% 3.37/0.98  --bmc1_axioms                           reachable_all
% 3.37/0.98  --bmc1_min_bound                        0
% 3.37/0.98  --bmc1_max_bound                        -1
% 3.37/0.98  --bmc1_max_bound_default                -1
% 3.37/0.98  --bmc1_symbol_reachability              true
% 3.37/0.98  --bmc1_property_lemmas                  false
% 3.37/0.98  --bmc1_k_induction                      false
% 3.37/0.98  --bmc1_non_equiv_states                 false
% 3.37/0.98  --bmc1_deadlock                         false
% 3.37/0.98  --bmc1_ucm                              false
% 3.37/0.98  --bmc1_add_unsat_core                   none
% 3.37/0.98  --bmc1_unsat_core_children              false
% 3.37/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/0.98  --bmc1_out_stat                         full
% 3.37/0.98  --bmc1_ground_init                      false
% 3.37/0.98  --bmc1_pre_inst_next_state              false
% 3.37/0.98  --bmc1_pre_inst_state                   false
% 3.37/0.98  --bmc1_pre_inst_reach_state             false
% 3.37/0.98  --bmc1_out_unsat_core                   false
% 3.37/0.98  --bmc1_aig_witness_out                  false
% 3.37/0.98  --bmc1_verbose                          false
% 3.37/0.98  --bmc1_dump_clauses_tptp                false
% 3.37/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.37/0.98  --bmc1_dump_file                        -
% 3.37/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.37/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.37/0.98  --bmc1_ucm_extend_mode                  1
% 3.37/0.98  --bmc1_ucm_init_mode                    2
% 3.37/0.98  --bmc1_ucm_cone_mode                    none
% 3.37/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.37/0.98  --bmc1_ucm_relax_model                  4
% 3.37/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.37/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/0.98  --bmc1_ucm_layered_model                none
% 3.37/0.98  --bmc1_ucm_max_lemma_size               10
% 3.37/0.98  
% 3.37/0.98  ------ AIG Options
% 3.37/0.98  
% 3.37/0.98  --aig_mode                              false
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation Options
% 3.37/0.98  
% 3.37/0.98  --instantiation_flag                    true
% 3.37/0.98  --inst_sos_flag                         false
% 3.37/0.98  --inst_sos_phase                        true
% 3.37/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/0.98  --inst_lit_sel_side                     none
% 3.37/0.98  --inst_solver_per_active                1400
% 3.37/0.98  --inst_solver_calls_frac                1.
% 3.37/0.98  --inst_passive_queue_type               priority_queues
% 3.37/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/0.98  --inst_passive_queues_freq              [25;2]
% 3.37/0.98  --inst_dismatching                      true
% 3.37/0.98  --inst_eager_unprocessed_to_passive     true
% 3.37/0.98  --inst_prop_sim_given                   true
% 3.37/0.98  --inst_prop_sim_new                     false
% 3.37/0.98  --inst_subs_new                         false
% 3.37/0.98  --inst_eq_res_simp                      false
% 3.37/0.98  --inst_subs_given                       false
% 3.37/0.98  --inst_orphan_elimination               true
% 3.37/0.98  --inst_learning_loop_flag               true
% 3.37/0.98  --inst_learning_start                   3000
% 3.37/0.98  --inst_learning_factor                  2
% 3.37/0.98  --inst_start_prop_sim_after_learn       3
% 3.37/0.98  --inst_sel_renew                        solver
% 3.37/0.98  --inst_lit_activity_flag                true
% 3.37/0.98  --inst_restr_to_given                   false
% 3.37/0.98  --inst_activity_threshold               500
% 3.37/0.98  --inst_out_proof                        true
% 3.37/0.98  
% 3.37/0.98  ------ Resolution Options
% 3.37/0.98  
% 3.37/0.98  --resolution_flag                       false
% 3.37/0.98  --res_lit_sel                           adaptive
% 3.37/0.98  --res_lit_sel_side                      none
% 3.37/0.98  --res_ordering                          kbo
% 3.37/0.98  --res_to_prop_solver                    active
% 3.37/0.98  --res_prop_simpl_new                    false
% 3.37/0.98  --res_prop_simpl_given                  true
% 3.37/0.98  --res_passive_queue_type                priority_queues
% 3.37/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/0.98  --res_passive_queues_freq               [15;5]
% 3.37/0.98  --res_forward_subs                      full
% 3.37/0.98  --res_backward_subs                     full
% 3.37/0.98  --res_forward_subs_resolution           true
% 3.37/0.98  --res_backward_subs_resolution          true
% 3.37/0.98  --res_orphan_elimination                true
% 3.37/0.98  --res_time_limit                        2.
% 3.37/0.98  --res_out_proof                         true
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Options
% 3.37/0.98  
% 3.37/0.98  --superposition_flag                    true
% 3.37/0.98  --sup_passive_queue_type                priority_queues
% 3.37/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.37/0.98  --demod_completeness_check              fast
% 3.37/0.98  --demod_use_ground                      true
% 3.37/0.98  --sup_to_prop_solver                    passive
% 3.37/0.98  --sup_prop_simpl_new                    true
% 3.37/0.98  --sup_prop_simpl_given                  true
% 3.37/0.98  --sup_fun_splitting                     false
% 3.37/0.98  --sup_smt_interval                      50000
% 3.37/0.98  
% 3.37/0.98  ------ Superposition Simplification Setup
% 3.37/0.98  
% 3.37/0.98  --sup_indices_passive                   []
% 3.37/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.37/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_full_bw                           [BwDemod]
% 3.37/0.98  --sup_immed_triv                        [TrivRules]
% 3.37/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_immed_bw_main                     []
% 3.37/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.37/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.37/0.98  
% 3.37/0.98  ------ Combination Options
% 3.37/0.98  
% 3.37/0.98  --comb_res_mult                         3
% 3.37/0.98  --comb_sup_mult                         2
% 3.37/0.98  --comb_inst_mult                        10
% 3.37/0.98  
% 3.37/0.98  ------ Debug Options
% 3.37/0.98  
% 3.37/0.98  --dbg_backtrace                         false
% 3.37/0.98  --dbg_dump_prop_clauses                 false
% 3.37/0.98  --dbg_dump_prop_clauses_file            -
% 3.37/0.98  --dbg_out_stat                          false
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  ------ Proving...
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  % SZS status Theorem for theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  fof(f12,axiom,(
% 3.37/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f27,plain,(
% 3.37/0.98    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.37/0.98    inference(ennf_transformation,[],[f12])).
% 3.37/0.98  
% 3.37/0.98  fof(f47,plain,(
% 3.37/0.98    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f27])).
% 3.37/0.98  
% 3.37/0.98  fof(f14,conjecture,(
% 3.37/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f15,negated_conjecture,(
% 3.37/0.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 3.37/0.98    inference(negated_conjecture,[],[f14])).
% 3.37/0.98  
% 3.37/0.98  fof(f29,plain,(
% 3.37/0.98    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.37/0.98    inference(ennf_transformation,[],[f15])).
% 3.37/0.98  
% 3.37/0.98  fof(f30,plain,(
% 3.37/0.98    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.37/0.98    inference(flattening,[],[f29])).
% 3.37/0.98  
% 3.37/0.98  fof(f32,plain,(
% 3.37/0.98    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 3.37/0.98    introduced(choice_axiom,[])).
% 3.37/0.98  
% 3.37/0.98  fof(f33,plain,(
% 3.37/0.98    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 3.37/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f32])).
% 3.37/0.98  
% 3.37/0.98  fof(f49,plain,(
% 3.37/0.98    v1_relat_1(sK2)),
% 3.37/0.98    inference(cnf_transformation,[],[f33])).
% 3.37/0.98  
% 3.37/0.98  fof(f10,axiom,(
% 3.37/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f25,plain,(
% 3.37/0.98    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 3.37/0.98    inference(ennf_transformation,[],[f10])).
% 3.37/0.98  
% 3.37/0.98  fof(f44,plain,(
% 3.37/0.98    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f25])).
% 3.37/0.98  
% 3.37/0.98  fof(f7,axiom,(
% 3.37/0.98    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f20,plain,(
% 3.37/0.98    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.37/0.98    inference(ennf_transformation,[],[f7])).
% 3.37/0.98  
% 3.37/0.98  fof(f41,plain,(
% 3.37/0.98    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f20])).
% 3.37/0.98  
% 3.37/0.98  fof(f5,axiom,(
% 3.37/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f38,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.37/0.98    inference(cnf_transformation,[],[f5])).
% 3.37/0.98  
% 3.37/0.98  fof(f4,axiom,(
% 3.37/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f37,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f4])).
% 3.37/0.98  
% 3.37/0.98  fof(f52,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.37/0.98    inference(definition_unfolding,[],[f38,f37])).
% 3.37/0.98  
% 3.37/0.98  fof(f55,plain,(
% 3.37/0.98    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f41,f52])).
% 3.37/0.98  
% 3.37/0.98  fof(f3,axiom,(
% 3.37/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f36,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f3])).
% 3.37/0.98  
% 3.37/0.98  fof(f54,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f36,f37,f37])).
% 3.37/0.98  
% 3.37/0.98  fof(f1,axiom,(
% 3.37/0.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f16,plain,(
% 3.37/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.37/0.98    inference(ennf_transformation,[],[f1])).
% 3.37/0.98  
% 3.37/0.98  fof(f34,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f16])).
% 3.37/0.98  
% 3.37/0.98  fof(f53,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2)) )),
% 3.37/0.98    inference(definition_unfolding,[],[f34,f52])).
% 3.37/0.98  
% 3.37/0.98  fof(f50,plain,(
% 3.37/0.98    r1_tarski(sK0,sK1)),
% 3.37/0.98    inference(cnf_transformation,[],[f33])).
% 3.37/0.98  
% 3.37/0.98  fof(f2,axiom,(
% 3.37/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f17,plain,(
% 3.37/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.37/0.98    inference(ennf_transformation,[],[f2])).
% 3.37/0.98  
% 3.37/0.98  fof(f18,plain,(
% 3.37/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.37/0.98    inference(flattening,[],[f17])).
% 3.37/0.98  
% 3.37/0.98  fof(f35,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f18])).
% 3.37/0.98  
% 3.37/0.98  fof(f8,axiom,(
% 3.37/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f21,plain,(
% 3.37/0.98    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.37/0.98    inference(ennf_transformation,[],[f8])).
% 3.37/0.98  
% 3.37/0.98  fof(f22,plain,(
% 3.37/0.98    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.37/0.98    inference(flattening,[],[f21])).
% 3.37/0.98  
% 3.37/0.98  fof(f42,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f22])).
% 3.37/0.98  
% 3.37/0.98  fof(f11,axiom,(
% 3.37/0.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f26,plain,(
% 3.37/0.98    ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 3.37/0.98    inference(ennf_transformation,[],[f11])).
% 3.37/0.98  
% 3.37/0.98  fof(f45,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f26])).
% 3.37/0.98  
% 3.37/0.98  fof(f13,axiom,(
% 3.37/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f28,plain,(
% 3.37/0.98    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 3.37/0.98    inference(ennf_transformation,[],[f13])).
% 3.37/0.98  
% 3.37/0.98  fof(f48,plain,(
% 3.37/0.98    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f28])).
% 3.37/0.98  
% 3.37/0.98  fof(f51,plain,(
% 3.37/0.98    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 3.37/0.98    inference(cnf_transformation,[],[f33])).
% 3.37/0.98  
% 3.37/0.98  fof(f6,axiom,(
% 3.37/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f19,plain,(
% 3.37/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.37/0.98    inference(ennf_transformation,[],[f6])).
% 3.37/0.98  
% 3.37/0.98  fof(f31,plain,(
% 3.37/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.37/0.98    inference(nnf_transformation,[],[f19])).
% 3.37/0.98  
% 3.37/0.98  fof(f40,plain,(
% 3.37/0.98    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f31])).
% 3.37/0.98  
% 3.37/0.98  fof(f9,axiom,(
% 3.37/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.37/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.37/0.98  
% 3.37/0.98  fof(f23,plain,(
% 3.37/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.37/0.98    inference(ennf_transformation,[],[f9])).
% 3.37/0.98  
% 3.37/0.98  fof(f24,plain,(
% 3.37/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.37/0.98    inference(flattening,[],[f23])).
% 3.37/0.98  
% 3.37/0.98  fof(f43,plain,(
% 3.37/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.37/0.98    inference(cnf_transformation,[],[f24])).
% 3.37/0.98  
% 3.37/0.98  cnf(c_10,plain,
% 3.37/0.98      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.37/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_282,plain,
% 3.37/0.98      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
% 3.37/0.98      | ~ v1_relat_1(X0_43) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_546,plain,
% 3.37/0.98      ( r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42) = iProver_top
% 3.37/0.98      | v1_relat_1(X0_43) != iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_15,negated_conjecture,
% 3.37/0.98      ( v1_relat_1(sK2) ),
% 3.37/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_277,negated_conjecture,
% 3.37/0.98      ( v1_relat_1(sK2) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_550,plain,
% 3.37/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_8,plain,
% 3.37/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 3.37/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_284,plain,
% 3.37/0.98      ( ~ v1_relat_1(X0_43) | v1_relat_1(k2_wellord1(X0_43,X0_42)) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_544,plain,
% 3.37/0.98      ( v1_relat_1(X0_43) != iProver_top
% 3.37/0.98      | v1_relat_1(k2_wellord1(X0_43,X0_42)) = iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_5,plain,
% 3.37/0.98      ( ~ v1_relat_1(X0)
% 3.37/0.98      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 3.37/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_286,plain,
% 3.37/0.98      ( ~ v1_relat_1(X0_43)
% 3.37/0.98      | k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_542,plain,
% 3.37/0.98      ( k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
% 3.37/0.98      | v1_relat_1(X0_43) != iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_993,plain,
% 3.37/0.98      ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))) = k3_relat_1(k2_wellord1(X0_43,X0_42))
% 3.37/0.98      | v1_relat_1(X0_43) != iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_544,c_542]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_3752,plain,
% 3.37/0.98      ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k2_relat_1(k2_wellord1(sK2,X0_42)))) = k3_relat_1(k2_wellord1(sK2,X0_42)) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_550,c_993]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_2,plain,
% 3.37/0.98      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.37/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_287,plain,
% 3.37/0.98      ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_0,plain,
% 3.37/0.98      ( r1_tarski(X0,X1)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 3.37/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_289,plain,
% 3.37/0.98      ( r1_tarski(X0_42,X1_42)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X2_42)),X1_42) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_540,plain,
% 3.37/0.98      ( r1_tarski(X0_42,X1_42) = iProver_top
% 3.37/0.98      | r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X2_42)),X1_42) != iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_863,plain,
% 3.37/0.98      ( r1_tarski(X0_42,X1_42) = iProver_top
% 3.37/0.98      | r1_tarski(k3_tarski(k1_enumset1(X2_42,X2_42,X0_42)),X1_42) != iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_287,c_540]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_4123,plain,
% 3.37/0.98      ( r1_tarski(k3_relat_1(k2_wellord1(sK2,X0_42)),X1_42) != iProver_top
% 3.37/0.98      | r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X1_42) = iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_3752,c_863]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_4464,plain,
% 3.37/0.98      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X0_42) = iProver_top
% 3.37/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_546,c_4123]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_16,plain,
% 3.37/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_4586,plain,
% 3.37/0.98      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),X0_42) = iProver_top ),
% 3.37/0.98      inference(global_propositional_subsumption,
% 3.37/0.98                [status(thm)],
% 3.37/0.98                [c_4464,c_16]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_14,negated_conjecture,
% 3.37/0.98      ( r1_tarski(sK0,sK1) ),
% 3.37/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_278,negated_conjecture,
% 3.37/0.98      ( r1_tarski(sK0,sK1) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_549,plain,
% 3.37/0.98      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1,plain,
% 3.37/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.37/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_288,plain,
% 3.37/0.98      ( ~ r1_tarski(X0_42,X1_42)
% 3.37/0.98      | ~ r1_tarski(X2_42,X0_42)
% 3.37/0.98      | r1_tarski(X2_42,X1_42) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_541,plain,
% 3.37/0.98      ( r1_tarski(X0_42,X1_42) != iProver_top
% 3.37/0.98      | r1_tarski(X2_42,X0_42) != iProver_top
% 3.37/0.98      | r1_tarski(X2_42,X1_42) = iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1620,plain,
% 3.37/0.98      ( r1_tarski(X0_42,sK1) = iProver_top
% 3.37/0.98      | r1_tarski(X0_42,sK0) != iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_549,c_541]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_4595,plain,
% 3.37/0.98      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_4586,c_1620]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_6,plain,
% 3.37/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.37/0.98      | ~ v1_relat_1(X0)
% 3.37/0.98      | k8_relat_1(X1,X0) = X0 ),
% 3.37/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_285,plain,
% 3.37/0.98      ( ~ r1_tarski(k2_relat_1(X0_43),X0_42)
% 3.37/0.98      | ~ v1_relat_1(X0_43)
% 3.37/0.98      | k8_relat_1(X0_42,X0_43) = X0_43 ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_543,plain,
% 3.37/0.98      ( k8_relat_1(X0_42,X0_43) = X0_43
% 3.37/0.98      | r1_tarski(k2_relat_1(X0_43),X0_42) != iProver_top
% 3.37/0.98      | v1_relat_1(X0_43) != iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_4647,plain,
% 3.37/0.98      ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
% 3.37/0.98      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_4595,c_543]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_324,plain,
% 3.37/0.98      ( v1_relat_1(X0_43) != iProver_top
% 3.37/0.98      | v1_relat_1(k2_wellord1(X0_43,X0_42)) = iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_326,plain,
% 3.37/0.98      ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
% 3.37/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_324]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_10015,plain,
% 3.37/0.98      ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
% 3.37/0.98      inference(global_propositional_subsumption,
% 3.37/0.98                [status(thm)],
% 3.37/0.98                [c_4647,c_16,c_326]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_9,plain,
% 3.37/0.98      ( ~ v1_relat_1(X0)
% 3.37/0.98      | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
% 3.37/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_283,plain,
% 3.37/0.98      ( ~ v1_relat_1(X0_43)
% 3.37/0.98      | k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k2_wellord1(X0_43,X0_42) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_545,plain,
% 3.37/0.98      ( k7_relat_1(k8_relat_1(X0_42,X0_43),X0_42) = k2_wellord1(X0_43,X0_42)
% 3.37/0.98      | v1_relat_1(X0_43) != iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_778,plain,
% 3.37/0.98      ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(X0_43,X1_42)),X0_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42)
% 3.37/0.98      | v1_relat_1(X0_43) != iProver_top ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_544,c_545]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_2493,plain,
% 3.37/0.98      ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(sK2,X1_42)),X0_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_550,c_778]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_10018,plain,
% 3.37/0.98      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_10015,c_2493]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_12,plain,
% 3.37/0.98      ( ~ v1_relat_1(X0)
% 3.37/0.98      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 3.37/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_280,plain,
% 3.37/0.98      ( ~ v1_relat_1(X0_43)
% 3.37/0.98      | k2_wellord1(k2_wellord1(X0_43,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_548,plain,
% 3.37/0.98      ( k2_wellord1(k2_wellord1(X0_43,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_43,X1_42),X0_42)
% 3.37/0.98      | v1_relat_1(X0_43) != iProver_top ),
% 3.37/0.98      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1039,plain,
% 3.37/0.98      ( k2_wellord1(k2_wellord1(sK2,X0_42),X1_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
% 3.37/0.98      inference(superposition,[status(thm)],[c_550,c_548]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_13,negated_conjecture,
% 3.37/0.98      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 3.37/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_279,negated_conjecture,
% 3.37/0.98      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1165,plain,
% 3.37/0.98      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
% 3.37/0.98      inference(demodulation,[status(thm)],[c_1039,c_279]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_10614,plain,
% 3.37/0.98      ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
% 3.37/0.98      inference(demodulation,[status(thm)],[c_10018,c_1165]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_3,plain,
% 3.37/0.98      ( v4_relat_1(X0,X1)
% 3.37/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.37/0.98      | ~ v1_relat_1(X0) ),
% 3.37/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_7,plain,
% 3.37/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.37/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_168,plain,
% 3.37/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.37/0.98      | ~ v1_relat_1(X0)
% 3.37/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.37/0.98      inference(resolution,[status(thm)],[c_3,c_7]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_276,plain,
% 3.37/0.98      ( ~ r1_tarski(k1_relat_1(X0_43),X0_42)
% 3.37/0.98      | ~ v1_relat_1(X0_43)
% 3.37/0.98      | k7_relat_1(X0_43,X0_42) = X0_43 ),
% 3.37/0.98      inference(subtyping,[status(esa)],[c_168]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_672,plain,
% 3.37/0.98      ( ~ r1_tarski(k1_relat_1(X0_43),sK1)
% 3.37/0.98      | ~ v1_relat_1(X0_43)
% 3.37/0.98      | k7_relat_1(X0_43,sK1) = X0_43 ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_276]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_2289,plain,
% 3.37/0.98      ( ~ r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK1)
% 3.37/0.98      | ~ v1_relat_1(k2_wellord1(X0_43,X0_42))
% 3.37/0.98      | k7_relat_1(k2_wellord1(X0_43,X0_42),sK1) = k2_wellord1(X0_43,X0_42) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_672]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_2291,plain,
% 3.37/0.98      ( ~ r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
% 3.37/0.98      | ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 3.37/0.98      | k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_2289]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_698,plain,
% 3.37/0.98      ( r1_tarski(X0_42,sK1)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X1_42)),sK1) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_289]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_824,plain,
% 3.37/0.98      ( r1_tarski(k1_relat_1(X0_43),sK1)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),X0_42)),sK1) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_698]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1597,plain,
% 3.37/0.98      ( r1_tarski(k1_relat_1(k2_wellord1(X0_43,X0_42)),sK1)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))),sK1) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_824]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1603,plain,
% 3.37/0.98      ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))),sK1) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_1597]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_635,plain,
% 3.37/0.98      ( r1_tarski(X0_42,sK1)
% 3.37/0.98      | ~ r1_tarski(X0_42,sK0)
% 3.37/0.98      | ~ r1_tarski(sK0,sK1) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_288]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_697,plain,
% 3.37/0.98      ( r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X1_42)),sK1)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(X0_42,X0_42,X1_42)),sK0)
% 3.37/0.98      | ~ r1_tarski(sK0,sK1) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_635]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1589,plain,
% 3.37/0.98      ( r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))),sK1)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))),sK0)
% 3.37/0.98      | ~ r1_tarski(sK0,sK1) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_697]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_1593,plain,
% 3.37/0.98      ( r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))),sK1)
% 3.37/0.98      | ~ r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))),sK0)
% 3.37/0.98      | ~ r1_tarski(sK0,sK1) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_1589]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_890,plain,
% 3.37/0.98      ( ~ v1_relat_1(k2_wellord1(X0_43,X0_42))
% 3.37/0.98      | k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))) = k3_relat_1(k2_wellord1(X0_43,X0_42)) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_286]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_896,plain,
% 3.37/0.98      ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
% 3.37/0.98      | k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))) = k3_relat_1(k2_wellord1(sK2,sK0)) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_890]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_297,plain,
% 3.37/0.98      ( ~ r1_tarski(X0_42,X1_42)
% 3.37/0.98      | r1_tarski(X2_42,X3_42)
% 3.37/0.98      | X2_42 != X0_42
% 3.37/0.98      | X3_42 != X1_42 ),
% 3.37/0.98      theory(equality) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_663,plain,
% 3.37/0.98      ( r1_tarski(X0_42,X1_42)
% 3.37/0.98      | ~ r1_tarski(k3_relat_1(k2_wellord1(X0_43,X2_42)),X2_42)
% 3.37/0.98      | X1_42 != X2_42
% 3.37/0.98      | X0_42 != k3_relat_1(k2_wellord1(X0_43,X2_42)) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_297]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_889,plain,
% 3.37/0.98      ( ~ r1_tarski(k3_relat_1(k2_wellord1(X0_43,X0_42)),X0_42)
% 3.37/0.98      | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))),X1_42)
% 3.37/0.98      | X1_42 != X0_42
% 3.37/0.98      | k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_43,X0_42)),k1_relat_1(k2_wellord1(X0_43,X0_42)),k2_relat_1(k2_wellord1(X0_43,X0_42)))) != k3_relat_1(k2_wellord1(X0_43,X0_42)) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_663]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_892,plain,
% 3.37/0.98      ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0)
% 3.37/0.98      | r1_tarski(k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))),sK0)
% 3.37/0.98      | k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,sK0)),k1_relat_1(k2_wellord1(sK2,sK0)),k2_relat_1(k2_wellord1(sK2,sK0)))) != k3_relat_1(k2_wellord1(sK2,sK0))
% 3.37/0.98      | sK0 != sK0 ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_889]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_331,plain,
% 3.37/0.98      ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK0)
% 3.37/0.98      | ~ v1_relat_1(sK2) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_282]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_325,plain,
% 3.37/0.98      ( v1_relat_1(k2_wellord1(sK2,sK0)) | ~ v1_relat_1(sK2) ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_284]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_291,plain,( X0_42 = X0_42 ),theory(equality) ).
% 3.37/0.98  
% 3.37/0.98  cnf(c_312,plain,
% 3.37/0.98      ( sK0 = sK0 ),
% 3.37/0.98      inference(instantiation,[status(thm)],[c_291]) ).
% 3.37/0.98  
% 3.37/0.98  cnf(contradiction,plain,
% 3.37/0.98      ( $false ),
% 3.37/0.98      inference(minisat,
% 3.37/0.98                [status(thm)],
% 3.37/0.98                [c_10614,c_2291,c_1603,c_1593,c_896,c_892,c_331,c_325,
% 3.37/0.98                 c_312,c_14,c_15]) ).
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/0.98  
% 3.37/0.98  ------                               Statistics
% 3.37/0.98  
% 3.37/0.98  ------ General
% 3.37/0.98  
% 3.37/0.98  abstr_ref_over_cycles:                  0
% 3.37/0.98  abstr_ref_under_cycles:                 0
% 3.37/0.98  gc_basic_clause_elim:                   0
% 3.37/0.98  forced_gc_time:                         0
% 3.37/0.98  parsing_time:                           0.008
% 3.37/0.98  unif_index_cands_time:                  0.
% 3.37/0.98  unif_index_add_time:                    0.
% 3.37/0.98  orderings_time:                         0.
% 3.37/0.98  out_proof_time:                         0.01
% 3.37/0.98  total_time:                             0.34
% 3.37/0.98  num_of_symbols:                         45
% 3.37/0.98  num_of_terms:                           14387
% 3.37/0.98  
% 3.37/0.98  ------ Preprocessing
% 3.37/0.98  
% 3.37/0.98  num_of_splits:                          0
% 3.37/0.98  num_of_split_atoms:                     0
% 3.37/0.98  num_of_reused_defs:                     0
% 3.37/0.98  num_eq_ax_congr_red:                    17
% 3.37/0.98  num_of_sem_filtered_clauses:            1
% 3.37/0.98  num_of_subtypes:                        3
% 3.37/0.98  monotx_restored_types:                  0
% 3.37/0.98  sat_num_of_epr_types:                   0
% 3.37/0.98  sat_num_of_non_cyclic_types:            0
% 3.37/0.98  sat_guarded_non_collapsed_types:        1
% 3.37/0.98  num_pure_diseq_elim:                    0
% 3.37/0.98  simp_replaced_by:                       0
% 3.37/0.98  res_preprocessed:                       85
% 3.37/0.98  prep_upred:                             0
% 3.37/0.98  prep_unflattend:                        0
% 3.37/0.98  smt_new_axioms:                         0
% 3.37/0.98  pred_elim_cands:                        2
% 3.37/0.98  pred_elim:                              1
% 3.37/0.98  pred_elim_cl:                           2
% 3.37/0.98  pred_elim_cycles:                       3
% 3.37/0.98  merged_defs:                            0
% 3.37/0.98  merged_defs_ncl:                        0
% 3.37/0.98  bin_hyper_res:                          0
% 3.37/0.98  prep_cycles:                            4
% 3.37/0.98  pred_elim_time:                         0.
% 3.37/0.98  splitting_time:                         0.
% 3.37/0.98  sem_filter_time:                        0.
% 3.37/0.98  monotx_time:                            0.
% 3.37/0.98  subtype_inf_time:                       0.
% 3.37/0.98  
% 3.37/0.98  ------ Problem properties
% 3.37/0.98  
% 3.37/0.98  clauses:                                14
% 3.37/0.98  conjectures:                            3
% 3.37/0.98  epr:                                    3
% 3.37/0.98  horn:                                   14
% 3.37/0.98  ground:                                 3
% 3.37/0.98  unary:                                  4
% 3.37/0.98  binary:                                 7
% 3.37/0.98  lits:                                   27
% 3.37/0.98  lits_eq:                                7
% 3.37/0.98  fd_pure:                                0
% 3.37/0.98  fd_pseudo:                              0
% 3.37/0.98  fd_cond:                                0
% 3.37/0.98  fd_pseudo_cond:                         0
% 3.37/0.98  ac_symbols:                             0
% 3.37/0.98  
% 3.37/0.98  ------ Propositional Solver
% 3.37/0.98  
% 3.37/0.98  prop_solver_calls:                      30
% 3.37/0.98  prop_fast_solver_calls:                 536
% 3.37/0.98  smt_solver_calls:                       0
% 3.37/0.98  smt_fast_solver_calls:                  0
% 3.37/0.98  prop_num_of_clauses:                    3797
% 3.37/0.98  prop_preprocess_simplified:             8485
% 3.37/0.98  prop_fo_subsumed:                       8
% 3.37/0.98  prop_solver_time:                       0.
% 3.37/0.98  smt_solver_time:                        0.
% 3.37/0.98  smt_fast_solver_time:                   0.
% 3.37/0.98  prop_fast_solver_time:                  0.
% 3.37/0.98  prop_unsat_core_time:                   0.
% 3.37/0.98  
% 3.37/0.98  ------ QBF
% 3.37/0.98  
% 3.37/0.98  qbf_q_res:                              0
% 3.37/0.98  qbf_num_tautologies:                    0
% 3.37/0.98  qbf_prep_cycles:                        0
% 3.37/0.98  
% 3.37/0.98  ------ BMC1
% 3.37/0.98  
% 3.37/0.98  bmc1_current_bound:                     -1
% 3.37/0.98  bmc1_last_solved_bound:                 -1
% 3.37/0.98  bmc1_unsat_core_size:                   -1
% 3.37/0.98  bmc1_unsat_core_parents_size:           -1
% 3.37/0.98  bmc1_merge_next_fun:                    0
% 3.37/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.37/0.98  
% 3.37/0.98  ------ Instantiation
% 3.37/0.98  
% 3.37/0.98  inst_num_of_clauses:                    1003
% 3.37/0.98  inst_num_in_passive:                    513
% 3.37/0.98  inst_num_in_active:                     426
% 3.37/0.98  inst_num_in_unprocessed:                64
% 3.37/0.98  inst_num_of_loops:                      440
% 3.37/0.98  inst_num_of_learning_restarts:          0
% 3.37/0.98  inst_num_moves_active_passive:          11
% 3.37/0.98  inst_lit_activity:                      0
% 3.37/0.98  inst_lit_activity_moves:                0
% 3.37/0.98  inst_num_tautologies:                   0
% 3.37/0.98  inst_num_prop_implied:                  0
% 3.37/0.98  inst_num_existing_simplified:           0
% 3.37/0.98  inst_num_eq_res_simplified:             0
% 3.37/0.98  inst_num_child_elim:                    0
% 3.37/0.98  inst_num_of_dismatching_blockings:      1198
% 3.37/0.98  inst_num_of_non_proper_insts:           991
% 3.37/0.98  inst_num_of_duplicates:                 0
% 3.37/0.98  inst_inst_num_from_inst_to_res:         0
% 3.37/0.98  inst_dismatching_checking_time:         0.
% 3.37/0.98  
% 3.37/0.98  ------ Resolution
% 3.37/0.98  
% 3.37/0.98  res_num_of_clauses:                     0
% 3.37/0.98  res_num_in_passive:                     0
% 3.37/0.98  res_num_in_active:                      0
% 3.37/0.98  res_num_of_loops:                       89
% 3.37/0.98  res_forward_subset_subsumed:            101
% 3.37/0.98  res_backward_subset_subsumed:           2
% 3.37/0.98  res_forward_subsumed:                   0
% 3.37/0.98  res_backward_subsumed:                  0
% 3.37/0.98  res_forward_subsumption_resolution:     0
% 3.37/0.98  res_backward_subsumption_resolution:    0
% 3.37/0.98  res_clause_to_clause_subsumption:       1326
% 3.37/0.98  res_orphan_elimination:                 0
% 3.37/0.98  res_tautology_del:                      166
% 3.37/0.98  res_num_eq_res_simplified:              0
% 3.37/0.98  res_num_sel_changes:                    0
% 3.37/0.98  res_moves_from_active_to_pass:          0
% 3.37/0.98  
% 3.37/0.98  ------ Superposition
% 3.37/0.98  
% 3.37/0.98  sup_time_total:                         0.
% 3.37/0.98  sup_time_generating:                    0.
% 3.37/0.98  sup_time_sim_full:                      0.
% 3.37/0.98  sup_time_sim_immed:                     0.
% 3.37/0.98  
% 3.37/0.98  sup_num_of_clauses:                     349
% 3.37/0.98  sup_num_in_active:                      83
% 3.37/0.98  sup_num_in_passive:                     266
% 3.37/0.98  sup_num_of_loops:                       87
% 3.37/0.98  sup_fw_superposition:                   397
% 3.37/0.98  sup_bw_superposition:                   329
% 3.37/0.98  sup_immediate_simplified:               44
% 3.37/0.98  sup_given_eliminated:                   0
% 3.37/0.98  comparisons_done:                       0
% 3.37/0.98  comparisons_avoided:                    0
% 3.37/0.98  
% 3.37/0.98  ------ Simplifications
% 3.37/0.98  
% 3.37/0.98  
% 3.37/0.98  sim_fw_subset_subsumed:                 14
% 3.37/0.98  sim_bw_subset_subsumed:                 9
% 3.37/0.98  sim_fw_subsumed:                        27
% 3.37/0.98  sim_bw_subsumed:                        1
% 3.37/0.98  sim_fw_subsumption_res:                 0
% 3.37/0.98  sim_bw_subsumption_res:                 0
% 3.37/0.98  sim_tautology_del:                      0
% 3.37/0.98  sim_eq_tautology_del:                   1
% 3.37/0.98  sim_eq_res_simp:                        0
% 3.37/0.98  sim_fw_demodulated:                     2
% 3.37/0.98  sim_bw_demodulated:                     2
% 3.37/0.98  sim_light_normalised:                   9
% 3.37/0.98  sim_joinable_taut:                      0
% 3.37/0.98  sim_joinable_simp:                      0
% 3.37/0.98  sim_ac_normalised:                      0
% 3.37/0.98  sim_smt_subsumption:                    0
% 3.37/0.98  
%------------------------------------------------------------------------------
