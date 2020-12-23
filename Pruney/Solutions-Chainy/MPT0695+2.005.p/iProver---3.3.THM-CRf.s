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
% DateTime   : Thu Dec  3 11:52:01 EST 2020

% Result     : Theorem 47.24s
% Output     : CNFRefutation 47.24s
% Verified   : 
% Statistics : Number of formulae       :  162 (1986 expanded)
%              Number of clauses        :  111 ( 735 expanded)
%              Number of leaves         :   16 ( 404 expanded)
%              Depth                    :   32
%              Number of atoms          :  285 (3854 expanded)
%              Number of equality atoms :  175 (1870 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f31,f32,f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f46,f47,f47])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_277,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_555,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_284,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),X0_42)
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_549,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),X0_42) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_284])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_283,plain,
    ( ~ r1_tarski(k1_relat_1(X0_41),X0_42)
    | ~ v1_relat_1(X0_41)
    | k7_relat_1(X0_41,X0_42) = X0_41 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_550,plain,
    ( k7_relat_1(X0_41,X0_42) = X0_41
    | r1_tarski(k1_relat_1(X0_41),X0_42) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_935,plain,
    ( k7_relat_1(k7_relat_1(X0_41,X0_42),X0_42) = k7_relat_1(X0_41,X0_42)
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_550])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_288,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_322,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_7528,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | k7_relat_1(k7_relat_1(X0_41,X0_42),X0_42) = k7_relat_1(X0_41,X0_42) ),
    inference(global_propositional_subsumption,[status(thm)],[c_935,c_322])).

cnf(c_7529,plain,
    ( k7_relat_1(k7_relat_1(X0_41,X0_42),X0_42) = k7_relat_1(X0_41,X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(renaming,[status(thm)],[c_7528])).

cnf(c_7536,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),X0_42) = k7_relat_1(sK2,X0_42) ),
    inference(superposition,[status(thm)],[c_555,c_7529])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_287,plain,
    ( ~ v1_relat_1(X0_41)
    | k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_546,plain,
    ( k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_778,plain,
    ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_555,c_546])).

cnf(c_0,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_289,plain,
    ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1012,plain,
    ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_289,c_778])).

cnf(c_1053,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),X1_42) = k7_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_1012,c_778])).

cnf(c_1116,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X2_42),X0_42) ),
    inference(superposition,[status(thm)],[c_778,c_1053])).

cnf(c_1862,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X3_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) ),
    inference(superposition,[status(thm)],[c_778,c_1116])).

cnf(c_2756,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42)),k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42)),X4_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X3_42),X4_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) ),
    inference(superposition,[status(thm)],[c_778,c_1862])).

cnf(c_9084,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X2_42),X3_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42))) ),
    inference(superposition,[status(thm)],[c_7536,c_2756])).

cnf(c_124047,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X2_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42))) ),
    inference(superposition,[status(thm)],[c_7536,c_9084])).

cnf(c_545,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_779,plain,
    ( k7_relat_1(k7_relat_1(X0_41,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42),X2_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_546])).

cnf(c_3517,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42) ),
    inference(superposition,[status(thm)],[c_555,c_779])).

cnf(c_4343,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_3517,c_1116])).

cnf(c_130157,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42))),X1_42) ),
    inference(superposition,[status(thm)],[c_124047,c_4343])).

cnf(c_1115,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_1012,c_1053])).

cnf(c_2763,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X3_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X0_42))) ),
    inference(superposition,[status(thm)],[c_289,c_1862])).

cnf(c_4311,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X2_42),X0_42) ),
    inference(superposition,[status(thm)],[c_1116,c_3517])).

cnf(c_4429,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))),X3_42) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X1_42),k1_setfam_1(k1_enumset1(X3_42,X3_42,X0_42))) ),
    inference(superposition,[status(thm)],[c_2763,c_4311])).

cnf(c_4438,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X3_42),X2_42),X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_1012,c_4311])).

cnf(c_4589,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))),X3_42) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X3_42),X2_42),X1_42) ),
    inference(demodulation,[status(thm)],[c_4429,c_4438])).

cnf(c_4591,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42),X3_42) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X3_42),X2_42),X1_42) ),
    inference(light_normalisation,[status(thm)],[c_4589,c_3517])).

cnf(c_124464,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42))),X3_42),X2_42) ),
    inference(superposition,[status(thm)],[c_9084,c_4591])).

cnf(c_124517,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42),X3_42),X2_42) ),
    inference(demodulation,[status(thm)],[c_124464,c_1115])).

cnf(c_124518,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X3_42),X2_42) ),
    inference(light_normalisation,[status(thm)],[c_124517,c_7536])).

cnf(c_130251,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X2_42),X1_42) ),
    inference(demodulation,[status(thm)],[c_130157,c_1115,c_124518])).

cnf(c_130252,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X2_42),X1_42) ),
    inference(light_normalisation,[status(thm)],[c_130251,c_7536])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_281,plain,
    ( ~ v1_relat_1(X0_41)
    | k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(X0_41,X1_42))) = k10_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_552,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(X0_41,X1_42))) = k10_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_1330,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(sK2,X1_42))) = k10_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_555,c_552])).

cnf(c_1553,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k7_relat_1(k7_relat_1(sK2,k10_relat_1(sK2,X1_42)),X0_42) ),
    inference(superposition,[status(thm)],[c_1330,c_1012])).

cnf(c_130729,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42)),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42)),X1_42))),X2_42)) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,k10_relat_1(sK2,X2_42)),X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_130252,c_1553])).

cnf(c_131020,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42))),X2_42)) = k7_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X2_42)),X1_42) ),
    inference(demodulation,[status(thm)],[c_130729,c_1012,c_1553])).

cnf(c_131021,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42),X2_42)) = k7_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_42),X2_42)),X0_42) ),
    inference(demodulation,[status(thm)],[c_131020,c_1115])).

cnf(c_131022,plain,
    ( k7_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)),X2_42) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X0_42),X1_42)) ),
    inference(light_normalisation,[status(thm)],[c_131021,c_7536])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_285,plain,
    ( ~ v1_relat_1(X0_41)
    | k2_relat_1(k7_relat_1(X0_41,X0_42)) = k9_relat_1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_548,plain,
    ( k2_relat_1(k7_relat_1(X0_41,X0_42)) = k9_relat_1(X0_41,X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_794,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)) = k9_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_548])).

cnf(c_5779,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k9_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
    inference(superposition,[status(thm)],[c_555,c_794])).

cnf(c_6703,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k9_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_1053,c_5779])).

cnf(c_141046,plain,
    ( k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42))) = k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X1_42),X2_42)) ),
    inference(superposition,[status(thm)],[c_131022,c_6703])).

cnf(c_793,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_42)) = k9_relat_1(sK2,X0_42) ),
    inference(superposition,[status(thm)],[c_555,c_548])).

cnf(c_141442,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X1_42),X2_42)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42)) ),
    inference(demodulation,[status(thm)],[c_141046,c_793])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_278,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_554,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_282,plain,
    ( ~ v1_funct_1(X0_41)
    | v1_funct_1(k7_relat_1(X0_41,X0_42))
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_551,plain,
    ( v1_funct_1(X0_41) != iProver_top
    | v1_funct_1(k7_relat_1(X0_41,X0_42)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_280,plain,
    ( ~ v1_funct_1(X0_41)
    | ~ v1_relat_1(X0_41)
    | k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(X0_41,k1_relat_1(X0_41)))) = k9_relat_1(X0_41,k10_relat_1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_553,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(X0_41,k1_relat_1(X0_41)))) = k9_relat_1(X0_41,k10_relat_1(X0_41,X0_42))
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_1421,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(X0_41,X1_42),k1_relat_1(k7_relat_1(X0_41,X1_42))))) = k9_relat_1(k7_relat_1(X0_41,X1_42),k10_relat_1(k7_relat_1(X0_41,X1_42),X0_42))
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X1_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_551,c_553])).

cnf(c_56654,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(X0_41,X1_42),k1_relat_1(k7_relat_1(X0_41,X1_42))))) = k9_relat_1(k7_relat_1(X0_41,X1_42),k10_relat_1(k7_relat_1(X0_41,X1_42),X0_42))
    | v1_funct_1(X0_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1421,c_545])).

cnf(c_56658,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(sK2,X1_42),k1_relat_1(k7_relat_1(sK2,X1_42))))) = k9_relat_1(k7_relat_1(sK2,X1_42),k10_relat_1(k7_relat_1(sK2,X1_42),X0_42))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_56654])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_286,plain,
    ( ~ v1_relat_1(X0_41)
    | k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_547,plain,
    ( k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_714,plain,
    ( k9_relat_1(k7_relat_1(X0_41,X0_42),k1_relat_1(k7_relat_1(X0_41,X0_42))) = k2_relat_1(k7_relat_1(X0_41,X0_42))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_547])).

cnf(c_2112,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k2_relat_1(k7_relat_1(sK2,X0_42)) ),
    inference(superposition,[status(thm)],[c_555,c_714])).

cnf(c_2124,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k9_relat_1(sK2,X0_42) ),
    inference(light_normalisation,[status(thm)],[c_2112,c_793])).

cnf(c_56701,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k1_setfam_1(k1_enumset1(X1_42,X1_42,k9_relat_1(sK2,X0_42)))
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_56658,c_2124])).

cnf(c_1016,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_545])).

cnf(c_14,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1152,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1016,c_14])).

cnf(c_9092,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0_42)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7536,c_1152])).

cnf(c_1014,plain,
    ( v1_funct_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_551])).

cnf(c_15,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2506,plain,
    ( v1_funct_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1014,c_14,c_15])).

cnf(c_9088,plain,
    ( v1_funct_1(k7_relat_1(sK2,X0_42)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7536,c_2506])).

cnf(c_9238,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(sK2,X1_42),k1_relat_1(k7_relat_1(sK2,X1_42))))) = k9_relat_1(k7_relat_1(sK2,X1_42),k10_relat_1(k7_relat_1(sK2,X1_42),X0_42))
    | v1_relat_1(k7_relat_1(sK2,X1_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9088,c_553])).

cnf(c_9241,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k1_setfam_1(k1_enumset1(X1_42,X1_42,k9_relat_1(sK2,X0_42)))
    | v1_relat_1(k7_relat_1(sK2,X0_42)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9238,c_2124])).

cnf(c_58177,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k1_setfam_1(k1_enumset1(X1_42,X1_42,k9_relat_1(sK2,X0_42))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56701,c_9092,c_9241])).

cnf(c_147027,plain,
    ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42)) = k1_setfam_1(k1_enumset1(X1_42,X1_42,k9_relat_1(sK2,X0_42))) ),
    inference(superposition,[status(thm)],[c_141442,c_58177])).

cnf(c_147044,plain,
    ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(sK2,X1_42))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_42),X0_42)) ),
    inference(light_normalisation,[status(thm)],[c_147027,c_7536])).

cnf(c_1554,plain,
    ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k7_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(sK2,X1_42)) ),
    inference(superposition,[status(thm)],[c_1330,c_778])).

cnf(c_1017,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) ),
    inference(superposition,[status(thm)],[c_778,c_793])).

cnf(c_11,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_279,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_644,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_289,c_279])).

cnf(c_1242,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_1017,c_644])).

cnf(c_1742,plain,
    ( k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_1554,c_1242])).

cnf(c_1743,plain,
    ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_1742,c_793])).

cnf(c_147379,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(demodulation,[status(thm)],[c_147044,c_1743])).

cnf(c_293,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_9487,plain,
    ( k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) = k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_293])).

cnf(c_300,plain,
    ( X0_43 != X1_43
    | k1_setfam_1(X0_43) = k1_setfam_1(X1_43) ),
    theory(equality)).

cnf(c_4905,plain,
    ( X0_43 != k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))
    | k1_setfam_1(X0_43) = k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_9486,plain,
    ( k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) != k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))
    | k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) = k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
    inference(instantiation,[status(thm)],[c_4905])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_147379,c_9487,c_9486])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 47.24/6.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.24/6.51  
% 47.24/6.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.24/6.51  
% 47.24/6.51  ------  iProver source info
% 47.24/6.51  
% 47.24/6.51  git: date: 2020-06-30 10:37:57 +0100
% 47.24/6.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.24/6.51  git: non_committed_changes: false
% 47.24/6.51  git: last_make_outside_of_git: false
% 47.24/6.51  
% 47.24/6.51  ------ 
% 47.24/6.51  
% 47.24/6.51  ------ Input Options
% 47.24/6.51  
% 47.24/6.51  --out_options                           all
% 47.24/6.51  --tptp_safe_out                         true
% 47.24/6.51  --problem_path                          ""
% 47.24/6.51  --include_path                          ""
% 47.24/6.51  --clausifier                            res/vclausify_rel
% 47.24/6.51  --clausifier_options                    --mode clausify
% 47.24/6.51  --stdin                                 false
% 47.24/6.51  --stats_out                             all
% 47.24/6.51  
% 47.24/6.51  ------ General Options
% 47.24/6.51  
% 47.24/6.51  --fof                                   false
% 47.24/6.51  --time_out_real                         305.
% 47.24/6.51  --time_out_virtual                      -1.
% 47.24/6.51  --symbol_type_check                     false
% 47.24/6.51  --clausify_out                          false
% 47.24/6.51  --sig_cnt_out                           false
% 47.24/6.51  --trig_cnt_out                          false
% 47.24/6.51  --trig_cnt_out_tolerance                1.
% 47.24/6.51  --trig_cnt_out_sk_spl                   false
% 47.24/6.51  --abstr_cl_out                          false
% 47.24/6.51  
% 47.24/6.51  ------ Global Options
% 47.24/6.51  
% 47.24/6.51  --schedule                              default
% 47.24/6.51  --add_important_lit                     false
% 47.24/6.51  --prop_solver_per_cl                    1000
% 47.24/6.51  --min_unsat_core                        false
% 47.24/6.51  --soft_assumptions                      false
% 47.24/6.51  --soft_lemma_size                       3
% 47.24/6.51  --prop_impl_unit_size                   0
% 47.24/6.51  --prop_impl_unit                        []
% 47.24/6.51  --share_sel_clauses                     true
% 47.24/6.51  --reset_solvers                         false
% 47.24/6.51  --bc_imp_inh                            [conj_cone]
% 47.24/6.51  --conj_cone_tolerance                   3.
% 47.24/6.51  --extra_neg_conj                        none
% 47.24/6.51  --large_theory_mode                     true
% 47.24/6.51  --prolific_symb_bound                   200
% 47.24/6.51  --lt_threshold                          2000
% 47.24/6.51  --clause_weak_htbl                      true
% 47.24/6.51  --gc_record_bc_elim                     false
% 47.24/6.51  
% 47.24/6.51  ------ Preprocessing Options
% 47.24/6.51  
% 47.24/6.51  --preprocessing_flag                    true
% 47.24/6.51  --time_out_prep_mult                    0.1
% 47.24/6.51  --splitting_mode                        input
% 47.24/6.51  --splitting_grd                         true
% 47.24/6.51  --splitting_cvd                         false
% 47.24/6.51  --splitting_cvd_svl                     false
% 47.24/6.51  --splitting_nvd                         32
% 47.24/6.51  --sub_typing                            true
% 47.24/6.51  --prep_gs_sim                           true
% 47.24/6.51  --prep_unflatten                        true
% 47.24/6.51  --prep_res_sim                          true
% 47.24/6.51  --prep_upred                            true
% 47.24/6.51  --prep_sem_filter                       exhaustive
% 47.24/6.51  --prep_sem_filter_out                   false
% 47.24/6.51  --pred_elim                             true
% 47.24/6.51  --res_sim_input                         true
% 47.24/6.51  --eq_ax_congr_red                       true
% 47.24/6.51  --pure_diseq_elim                       true
% 47.24/6.51  --brand_transform                       false
% 47.24/6.51  --non_eq_to_eq                          false
% 47.24/6.51  --prep_def_merge                        true
% 47.24/6.51  --prep_def_merge_prop_impl              false
% 47.24/6.51  --prep_def_merge_mbd                    true
% 47.24/6.51  --prep_def_merge_tr_red                 false
% 47.24/6.51  --prep_def_merge_tr_cl                  false
% 47.24/6.51  --smt_preprocessing                     true
% 47.24/6.51  --smt_ac_axioms                         fast
% 47.24/6.51  --preprocessed_out                      false
% 47.24/6.51  --preprocessed_stats                    false
% 47.24/6.51  
% 47.24/6.51  ------ Abstraction refinement Options
% 47.24/6.51  
% 47.24/6.51  --abstr_ref                             []
% 47.24/6.51  --abstr_ref_prep                        false
% 47.24/6.51  --abstr_ref_until_sat                   false
% 47.24/6.51  --abstr_ref_sig_restrict                funpre
% 47.24/6.51  --abstr_ref_af_restrict_to_split_sk     false
% 47.24/6.51  --abstr_ref_under                       []
% 47.24/6.51  
% 47.24/6.51  ------ SAT Options
% 47.24/6.51  
% 47.24/6.51  --sat_mode                              false
% 47.24/6.51  --sat_fm_restart_options                ""
% 47.24/6.51  --sat_gr_def                            false
% 47.24/6.51  --sat_epr_types                         true
% 47.24/6.51  --sat_non_cyclic_types                  false
% 47.24/6.51  --sat_finite_models                     false
% 47.24/6.51  --sat_fm_lemmas                         false
% 47.24/6.51  --sat_fm_prep                           false
% 47.24/6.51  --sat_fm_uc_incr                        true
% 47.24/6.51  --sat_out_model                         small
% 47.24/6.51  --sat_out_clauses                       false
% 47.24/6.51  
% 47.24/6.51  ------ QBF Options
% 47.24/6.51  
% 47.24/6.51  --qbf_mode                              false
% 47.24/6.51  --qbf_elim_univ                         false
% 47.24/6.51  --qbf_dom_inst                          none
% 47.24/6.51  --qbf_dom_pre_inst                      false
% 47.24/6.51  --qbf_sk_in                             false
% 47.24/6.51  --qbf_pred_elim                         true
% 47.24/6.51  --qbf_split                             512
% 47.24/6.51  
% 47.24/6.51  ------ BMC1 Options
% 47.24/6.51  
% 47.24/6.51  --bmc1_incremental                      false
% 47.24/6.51  --bmc1_axioms                           reachable_all
% 47.24/6.51  --bmc1_min_bound                        0
% 47.24/6.51  --bmc1_max_bound                        -1
% 47.24/6.51  --bmc1_max_bound_default                -1
% 47.24/6.51  --bmc1_symbol_reachability              true
% 47.24/6.51  --bmc1_property_lemmas                  false
% 47.24/6.51  --bmc1_k_induction                      false
% 47.24/6.51  --bmc1_non_equiv_states                 false
% 47.24/6.51  --bmc1_deadlock                         false
% 47.24/6.51  --bmc1_ucm                              false
% 47.24/6.51  --bmc1_add_unsat_core                   none
% 47.24/6.51  --bmc1_unsat_core_children              false
% 47.24/6.51  --bmc1_unsat_core_extrapolate_axioms    false
% 47.24/6.51  --bmc1_out_stat                         full
% 47.24/6.51  --bmc1_ground_init                      false
% 47.24/6.51  --bmc1_pre_inst_next_state              false
% 47.24/6.51  --bmc1_pre_inst_state                   false
% 47.24/6.51  --bmc1_pre_inst_reach_state             false
% 47.24/6.51  --bmc1_out_unsat_core                   false
% 47.24/6.51  --bmc1_aig_witness_out                  false
% 47.24/6.51  --bmc1_verbose                          false
% 47.24/6.51  --bmc1_dump_clauses_tptp                false
% 47.24/6.51  --bmc1_dump_unsat_core_tptp             false
% 47.24/6.51  --bmc1_dump_file                        -
% 47.24/6.51  --bmc1_ucm_expand_uc_limit              128
% 47.24/6.51  --bmc1_ucm_n_expand_iterations          6
% 47.24/6.51  --bmc1_ucm_extend_mode                  1
% 47.24/6.51  --bmc1_ucm_init_mode                    2
% 47.24/6.51  --bmc1_ucm_cone_mode                    none
% 47.24/6.51  --bmc1_ucm_reduced_relation_type        0
% 47.24/6.51  --bmc1_ucm_relax_model                  4
% 47.24/6.51  --bmc1_ucm_full_tr_after_sat            true
% 47.24/6.51  --bmc1_ucm_expand_neg_assumptions       false
% 47.24/6.51  --bmc1_ucm_layered_model                none
% 47.24/6.51  --bmc1_ucm_max_lemma_size               10
% 47.24/6.51  
% 47.24/6.51  ------ AIG Options
% 47.24/6.51  
% 47.24/6.51  --aig_mode                              false
% 47.24/6.51  
% 47.24/6.51  ------ Instantiation Options
% 47.24/6.51  
% 47.24/6.51  --instantiation_flag                    true
% 47.24/6.51  --inst_sos_flag                         false
% 47.24/6.51  --inst_sos_phase                        true
% 47.24/6.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.24/6.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.24/6.51  --inst_lit_sel_side                     num_symb
% 47.24/6.51  --inst_solver_per_active                1400
% 47.24/6.51  --inst_solver_calls_frac                1.
% 47.24/6.51  --inst_passive_queue_type               priority_queues
% 47.24/6.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.24/6.51  --inst_passive_queues_freq              [25;2]
% 47.24/6.51  --inst_dismatching                      true
% 47.24/6.51  --inst_eager_unprocessed_to_passive     true
% 47.24/6.51  --inst_prop_sim_given                   true
% 47.24/6.51  --inst_prop_sim_new                     false
% 47.24/6.51  --inst_subs_new                         false
% 47.24/6.51  --inst_eq_res_simp                      false
% 47.24/6.51  --inst_subs_given                       false
% 47.24/6.51  --inst_orphan_elimination               true
% 47.24/6.51  --inst_learning_loop_flag               true
% 47.24/6.51  --inst_learning_start                   3000
% 47.24/6.51  --inst_learning_factor                  2
% 47.24/6.51  --inst_start_prop_sim_after_learn       3
% 47.24/6.51  --inst_sel_renew                        solver
% 47.24/6.51  --inst_lit_activity_flag                true
% 47.24/6.51  --inst_restr_to_given                   false
% 47.24/6.51  --inst_activity_threshold               500
% 47.24/6.51  --inst_out_proof                        true
% 47.24/6.51  
% 47.24/6.51  ------ Resolution Options
% 47.24/6.51  
% 47.24/6.51  --resolution_flag                       true
% 47.24/6.51  --res_lit_sel                           adaptive
% 47.24/6.51  --res_lit_sel_side                      none
% 47.24/6.51  --res_ordering                          kbo
% 47.24/6.51  --res_to_prop_solver                    active
% 47.24/6.51  --res_prop_simpl_new                    false
% 47.24/6.51  --res_prop_simpl_given                  true
% 47.24/6.51  --res_passive_queue_type                priority_queues
% 47.24/6.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.24/6.51  --res_passive_queues_freq               [15;5]
% 47.24/6.51  --res_forward_subs                      full
% 47.24/6.51  --res_backward_subs                     full
% 47.24/6.51  --res_forward_subs_resolution           true
% 47.24/6.51  --res_backward_subs_resolution          true
% 47.24/6.51  --res_orphan_elimination                true
% 47.24/6.51  --res_time_limit                        2.
% 47.24/6.51  --res_out_proof                         true
% 47.24/6.51  
% 47.24/6.51  ------ Superposition Options
% 47.24/6.51  
% 47.24/6.51  --superposition_flag                    true
% 47.24/6.51  --sup_passive_queue_type                priority_queues
% 47.24/6.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.24/6.51  --sup_passive_queues_freq               [8;1;4]
% 47.24/6.51  --demod_completeness_check              fast
% 47.24/6.51  --demod_use_ground                      true
% 47.24/6.51  --sup_to_prop_solver                    passive
% 47.24/6.51  --sup_prop_simpl_new                    true
% 47.24/6.51  --sup_prop_simpl_given                  true
% 47.24/6.51  --sup_fun_splitting                     false
% 47.24/6.51  --sup_smt_interval                      50000
% 47.24/6.51  
% 47.24/6.51  ------ Superposition Simplification Setup
% 47.24/6.51  
% 47.24/6.51  --sup_indices_passive                   []
% 47.24/6.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.24/6.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.24/6.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.24/6.51  --sup_full_triv                         [TrivRules;PropSubs]
% 47.24/6.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.24/6.51  --sup_full_bw                           [BwDemod]
% 47.24/6.51  --sup_immed_triv                        [TrivRules]
% 47.24/6.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.24/6.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.24/6.51  --sup_immed_bw_main                     []
% 47.24/6.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.24/6.51  --sup_input_triv                        [Unflattening;TrivRules]
% 47.24/6.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.24/6.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.24/6.51  
% 47.24/6.51  ------ Combination Options
% 47.24/6.51  
% 47.24/6.51  --comb_res_mult                         3
% 47.24/6.51  --comb_sup_mult                         2
% 47.24/6.51  --comb_inst_mult                        10
% 47.24/6.51  
% 47.24/6.51  ------ Debug Options
% 47.24/6.51  
% 47.24/6.51  --dbg_backtrace                         false
% 47.24/6.51  --dbg_dump_prop_clauses                 false
% 47.24/6.51  --dbg_dump_prop_clauses_file            -
% 47.24/6.51  --dbg_out_stat                          false
% 47.24/6.51  ------ Parsing...
% 47.24/6.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.24/6.51  
% 47.24/6.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 47.24/6.51  
% 47.24/6.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.24/6.51  
% 47.24/6.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.24/6.51  ------ Proving...
% 47.24/6.51  ------ Problem Properties 
% 47.24/6.51  
% 47.24/6.51  
% 47.24/6.51  clauses                                 13
% 47.24/6.51  conjectures                             3
% 47.24/6.51  EPR                                     2
% 47.24/6.51  Horn                                    13
% 47.24/6.51  unary                                   4
% 47.24/6.51  binary                                  6
% 47.24/6.51  lits                                    25
% 47.24/6.51  lits eq                                 8
% 47.24/6.51  fd_pure                                 0
% 47.24/6.51  fd_pseudo                               0
% 47.24/6.51  fd_cond                                 0
% 47.24/6.51  fd_pseudo_cond                          0
% 47.24/6.51  AC symbols                              0
% 47.24/6.51  
% 47.24/6.51  ------ Schedule dynamic 5 is on 
% 47.24/6.51  
% 47.24/6.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.24/6.51  
% 47.24/6.51  
% 47.24/6.51  ------ 
% 47.24/6.51  Current options:
% 47.24/6.51  ------ 
% 47.24/6.51  
% 47.24/6.51  ------ Input Options
% 47.24/6.51  
% 47.24/6.51  --out_options                           all
% 47.24/6.51  --tptp_safe_out                         true
% 47.24/6.51  --problem_path                          ""
% 47.24/6.51  --include_path                          ""
% 47.24/6.51  --clausifier                            res/vclausify_rel
% 47.24/6.51  --clausifier_options                    --mode clausify
% 47.24/6.51  --stdin                                 false
% 47.24/6.51  --stats_out                             all
% 47.24/6.51  
% 47.24/6.51  ------ General Options
% 47.24/6.51  
% 47.24/6.51  --fof                                   false
% 47.24/6.51  --time_out_real                         305.
% 47.24/6.51  --time_out_virtual                      -1.
% 47.24/6.51  --symbol_type_check                     false
% 47.24/6.51  --clausify_out                          false
% 47.24/6.51  --sig_cnt_out                           false
% 47.24/6.51  --trig_cnt_out                          false
% 47.24/6.51  --trig_cnt_out_tolerance                1.
% 47.24/6.51  --trig_cnt_out_sk_spl                   false
% 47.24/6.51  --abstr_cl_out                          false
% 47.24/6.51  
% 47.24/6.51  ------ Global Options
% 47.24/6.51  
% 47.24/6.51  --schedule                              default
% 47.24/6.51  --add_important_lit                     false
% 47.24/6.51  --prop_solver_per_cl                    1000
% 47.24/6.51  --min_unsat_core                        false
% 47.24/6.51  --soft_assumptions                      false
% 47.24/6.51  --soft_lemma_size                       3
% 47.24/6.51  --prop_impl_unit_size                   0
% 47.24/6.51  --prop_impl_unit                        []
% 47.24/6.51  --share_sel_clauses                     true
% 47.24/6.51  --reset_solvers                         false
% 47.24/6.51  --bc_imp_inh                            [conj_cone]
% 47.24/6.51  --conj_cone_tolerance                   3.
% 47.24/6.51  --extra_neg_conj                        none
% 47.24/6.51  --large_theory_mode                     true
% 47.24/6.51  --prolific_symb_bound                   200
% 47.24/6.51  --lt_threshold                          2000
% 47.24/6.51  --clause_weak_htbl                      true
% 47.24/6.51  --gc_record_bc_elim                     false
% 47.24/6.51  
% 47.24/6.51  ------ Preprocessing Options
% 47.24/6.51  
% 47.24/6.51  --preprocessing_flag                    true
% 47.24/6.51  --time_out_prep_mult                    0.1
% 47.24/6.51  --splitting_mode                        input
% 47.24/6.51  --splitting_grd                         true
% 47.24/6.51  --splitting_cvd                         false
% 47.24/6.51  --splitting_cvd_svl                     false
% 47.24/6.51  --splitting_nvd                         32
% 47.24/6.51  --sub_typing                            true
% 47.24/6.51  --prep_gs_sim                           true
% 47.24/6.51  --prep_unflatten                        true
% 47.24/6.51  --prep_res_sim                          true
% 47.24/6.51  --prep_upred                            true
% 47.24/6.51  --prep_sem_filter                       exhaustive
% 47.24/6.51  --prep_sem_filter_out                   false
% 47.24/6.51  --pred_elim                             true
% 47.24/6.51  --res_sim_input                         true
% 47.24/6.51  --eq_ax_congr_red                       true
% 47.24/6.51  --pure_diseq_elim                       true
% 47.24/6.51  --brand_transform                       false
% 47.24/6.51  --non_eq_to_eq                          false
% 47.24/6.51  --prep_def_merge                        true
% 47.24/6.51  --prep_def_merge_prop_impl              false
% 47.24/6.51  --prep_def_merge_mbd                    true
% 47.24/6.51  --prep_def_merge_tr_red                 false
% 47.24/6.51  --prep_def_merge_tr_cl                  false
% 47.24/6.51  --smt_preprocessing                     true
% 47.24/6.51  --smt_ac_axioms                         fast
% 47.24/6.51  --preprocessed_out                      false
% 47.24/6.51  --preprocessed_stats                    false
% 47.24/6.51  
% 47.24/6.51  ------ Abstraction refinement Options
% 47.24/6.51  
% 47.24/6.51  --abstr_ref                             []
% 47.24/6.51  --abstr_ref_prep                        false
% 47.24/6.51  --abstr_ref_until_sat                   false
% 47.24/6.51  --abstr_ref_sig_restrict                funpre
% 47.24/6.51  --abstr_ref_af_restrict_to_split_sk     false
% 47.24/6.51  --abstr_ref_under                       []
% 47.24/6.51  
% 47.24/6.51  ------ SAT Options
% 47.24/6.51  
% 47.24/6.51  --sat_mode                              false
% 47.24/6.51  --sat_fm_restart_options                ""
% 47.24/6.51  --sat_gr_def                            false
% 47.24/6.51  --sat_epr_types                         true
% 47.24/6.51  --sat_non_cyclic_types                  false
% 47.24/6.51  --sat_finite_models                     false
% 47.24/6.51  --sat_fm_lemmas                         false
% 47.24/6.51  --sat_fm_prep                           false
% 47.24/6.51  --sat_fm_uc_incr                        true
% 47.24/6.51  --sat_out_model                         small
% 47.24/6.51  --sat_out_clauses                       false
% 47.24/6.51  
% 47.24/6.51  ------ QBF Options
% 47.24/6.51  
% 47.24/6.51  --qbf_mode                              false
% 47.24/6.51  --qbf_elim_univ                         false
% 47.24/6.51  --qbf_dom_inst                          none
% 47.24/6.51  --qbf_dom_pre_inst                      false
% 47.24/6.51  --qbf_sk_in                             false
% 47.24/6.51  --qbf_pred_elim                         true
% 47.24/6.51  --qbf_split                             512
% 47.24/6.51  
% 47.24/6.51  ------ BMC1 Options
% 47.24/6.51  
% 47.24/6.51  --bmc1_incremental                      false
% 47.24/6.51  --bmc1_axioms                           reachable_all
% 47.24/6.51  --bmc1_min_bound                        0
% 47.24/6.51  --bmc1_max_bound                        -1
% 47.24/6.51  --bmc1_max_bound_default                -1
% 47.24/6.51  --bmc1_symbol_reachability              true
% 47.24/6.51  --bmc1_property_lemmas                  false
% 47.24/6.51  --bmc1_k_induction                      false
% 47.24/6.51  --bmc1_non_equiv_states                 false
% 47.24/6.51  --bmc1_deadlock                         false
% 47.24/6.51  --bmc1_ucm                              false
% 47.24/6.51  --bmc1_add_unsat_core                   none
% 47.24/6.51  --bmc1_unsat_core_children              false
% 47.24/6.51  --bmc1_unsat_core_extrapolate_axioms    false
% 47.24/6.51  --bmc1_out_stat                         full
% 47.24/6.51  --bmc1_ground_init                      false
% 47.24/6.51  --bmc1_pre_inst_next_state              false
% 47.24/6.51  --bmc1_pre_inst_state                   false
% 47.24/6.51  --bmc1_pre_inst_reach_state             false
% 47.24/6.51  --bmc1_out_unsat_core                   false
% 47.24/6.51  --bmc1_aig_witness_out                  false
% 47.24/6.51  --bmc1_verbose                          false
% 47.24/6.51  --bmc1_dump_clauses_tptp                false
% 47.24/6.51  --bmc1_dump_unsat_core_tptp             false
% 47.24/6.51  --bmc1_dump_file                        -
% 47.24/6.51  --bmc1_ucm_expand_uc_limit              128
% 47.24/6.51  --bmc1_ucm_n_expand_iterations          6
% 47.24/6.51  --bmc1_ucm_extend_mode                  1
% 47.24/6.51  --bmc1_ucm_init_mode                    2
% 47.24/6.51  --bmc1_ucm_cone_mode                    none
% 47.24/6.51  --bmc1_ucm_reduced_relation_type        0
% 47.24/6.51  --bmc1_ucm_relax_model                  4
% 47.24/6.51  --bmc1_ucm_full_tr_after_sat            true
% 47.24/6.51  --bmc1_ucm_expand_neg_assumptions       false
% 47.24/6.51  --bmc1_ucm_layered_model                none
% 47.24/6.51  --bmc1_ucm_max_lemma_size               10
% 47.24/6.51  
% 47.24/6.51  ------ AIG Options
% 47.24/6.51  
% 47.24/6.51  --aig_mode                              false
% 47.24/6.51  
% 47.24/6.51  ------ Instantiation Options
% 47.24/6.51  
% 47.24/6.51  --instantiation_flag                    true
% 47.24/6.51  --inst_sos_flag                         false
% 47.24/6.51  --inst_sos_phase                        true
% 47.24/6.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.24/6.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.24/6.51  --inst_lit_sel_side                     none
% 47.24/6.51  --inst_solver_per_active                1400
% 47.24/6.51  --inst_solver_calls_frac                1.
% 47.24/6.51  --inst_passive_queue_type               priority_queues
% 47.24/6.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.24/6.51  --inst_passive_queues_freq              [25;2]
% 47.24/6.51  --inst_dismatching                      true
% 47.24/6.51  --inst_eager_unprocessed_to_passive     true
% 47.24/6.51  --inst_prop_sim_given                   true
% 47.24/6.51  --inst_prop_sim_new                     false
% 47.24/6.51  --inst_subs_new                         false
% 47.24/6.51  --inst_eq_res_simp                      false
% 47.24/6.51  --inst_subs_given                       false
% 47.24/6.51  --inst_orphan_elimination               true
% 47.24/6.51  --inst_learning_loop_flag               true
% 47.24/6.51  --inst_learning_start                   3000
% 47.24/6.51  --inst_learning_factor                  2
% 47.24/6.51  --inst_start_prop_sim_after_learn       3
% 47.24/6.51  --inst_sel_renew                        solver
% 47.24/6.51  --inst_lit_activity_flag                true
% 47.24/6.51  --inst_restr_to_given                   false
% 47.24/6.51  --inst_activity_threshold               500
% 47.24/6.51  --inst_out_proof                        true
% 47.24/6.51  
% 47.24/6.51  ------ Resolution Options
% 47.24/6.51  
% 47.24/6.51  --resolution_flag                       false
% 47.24/6.51  --res_lit_sel                           adaptive
% 47.24/6.51  --res_lit_sel_side                      none
% 47.24/6.51  --res_ordering                          kbo
% 47.24/6.51  --res_to_prop_solver                    active
% 47.24/6.51  --res_prop_simpl_new                    false
% 47.24/6.51  --res_prop_simpl_given                  true
% 47.24/6.51  --res_passive_queue_type                priority_queues
% 47.24/6.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.24/6.51  --res_passive_queues_freq               [15;5]
% 47.24/6.51  --res_forward_subs                      full
% 47.24/6.51  --res_backward_subs                     full
% 47.24/6.51  --res_forward_subs_resolution           true
% 47.24/6.51  --res_backward_subs_resolution          true
% 47.24/6.51  --res_orphan_elimination                true
% 47.24/6.51  --res_time_limit                        2.
% 47.24/6.51  --res_out_proof                         true
% 47.24/6.51  
% 47.24/6.51  ------ Superposition Options
% 47.24/6.51  
% 47.24/6.51  --superposition_flag                    true
% 47.24/6.51  --sup_passive_queue_type                priority_queues
% 47.24/6.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.24/6.51  --sup_passive_queues_freq               [8;1;4]
% 47.24/6.51  --demod_completeness_check              fast
% 47.24/6.51  --demod_use_ground                      true
% 47.24/6.51  --sup_to_prop_solver                    passive
% 47.24/6.51  --sup_prop_simpl_new                    true
% 47.24/6.51  --sup_prop_simpl_given                  true
% 47.24/6.51  --sup_fun_splitting                     false
% 47.24/6.51  --sup_smt_interval                      50000
% 47.24/6.51  
% 47.24/6.51  ------ Superposition Simplification Setup
% 47.24/6.51  
% 47.24/6.51  --sup_indices_passive                   []
% 47.24/6.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.24/6.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.24/6.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.24/6.51  --sup_full_triv                         [TrivRules;PropSubs]
% 47.24/6.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.24/6.51  --sup_full_bw                           [BwDemod]
% 47.24/6.51  --sup_immed_triv                        [TrivRules]
% 47.24/6.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.24/6.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.24/6.51  --sup_immed_bw_main                     []
% 47.24/6.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.24/6.51  --sup_input_triv                        [Unflattening;TrivRules]
% 47.24/6.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.24/6.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.24/6.51  
% 47.24/6.51  ------ Combination Options
% 47.24/6.51  
% 47.24/6.51  --comb_res_mult                         3
% 47.24/6.51  --comb_sup_mult                         2
% 47.24/6.51  --comb_inst_mult                        10
% 47.24/6.51  
% 47.24/6.51  ------ Debug Options
% 47.24/6.51  
% 47.24/6.51  --dbg_backtrace                         false
% 47.24/6.51  --dbg_dump_prop_clauses                 false
% 47.24/6.51  --dbg_dump_prop_clauses_file            -
% 47.24/6.51  --dbg_out_stat                          false
% 47.24/6.51  
% 47.24/6.51  
% 47.24/6.51  
% 47.24/6.51  
% 47.24/6.51  ------ Proving...
% 47.24/6.51  
% 47.24/6.51  
% 47.24/6.51  % SZS status Theorem for theBenchmark.p
% 47.24/6.51  
% 47.24/6.51  % SZS output start CNFRefutation for theBenchmark.p
% 47.24/6.51  
% 47.24/6.51  fof(f13,conjecture,(
% 47.24/6.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))))),
% 47.24/6.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.51  
% 47.24/6.51  fof(f14,negated_conjecture,(
% 47.24/6.51    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))))),
% 47.24/6.51    inference(negated_conjecture,[],[f13])).
% 47.24/6.51  
% 47.24/6.51  fof(f27,plain,(
% 47.24/6.51    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 47.24/6.51    inference(ennf_transformation,[],[f14])).
% 47.24/6.51  
% 47.24/6.51  fof(f28,plain,(
% 47.24/6.51    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 47.24/6.51    inference(flattening,[],[f27])).
% 47.24/6.51  
% 47.24/6.51  fof(f29,plain,(
% 47.24/6.51    ? [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) != k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 47.24/6.51    introduced(choice_axiom,[])).
% 47.24/6.51  
% 47.24/6.51  fof(f30,plain,(
% 47.24/6.51    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 47.24/6.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f29])).
% 47.24/6.51  
% 47.24/6.51  fof(f44,plain,(
% 47.24/6.51    v1_relat_1(sK2)),
% 47.24/6.51    inference(cnf_transformation,[],[f30])).
% 47.24/6.51  
% 47.24/6.51  fof(f8,axiom,(
% 47.24/6.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 47.24/6.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.51  
% 47.24/6.51  fof(f19,plain,(
% 47.24/6.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 47.24/6.51    inference(ennf_transformation,[],[f8])).
% 47.24/6.51  
% 47.24/6.51  fof(f38,plain,(
% 47.24/6.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 47.24/6.51    inference(cnf_transformation,[],[f19])).
% 47.24/6.51  
% 47.24/6.51  fof(f9,axiom,(
% 47.24/6.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 47.24/6.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.51  
% 47.24/6.51  fof(f20,plain,(
% 47.24/6.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 47.24/6.51    inference(ennf_transformation,[],[f9])).
% 47.24/6.51  
% 47.24/6.51  fof(f21,plain,(
% 47.24/6.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 47.24/6.51    inference(flattening,[],[f20])).
% 47.24/6.51  
% 47.24/6.51  fof(f39,plain,(
% 47.24/6.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 47.24/6.51    inference(cnf_transformation,[],[f21])).
% 47.24/6.51  
% 47.24/6.51  fof(f4,axiom,(
% 47.24/6.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 47.24/6.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.51  
% 47.24/6.51  fof(f15,plain,(
% 47.24/6.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 47.24/6.51    inference(ennf_transformation,[],[f4])).
% 47.24/6.51  
% 47.24/6.51  fof(f34,plain,(
% 47.24/6.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 47.24/6.51    inference(cnf_transformation,[],[f15])).
% 47.24/6.51  
% 47.24/6.51  fof(f5,axiom,(
% 47.24/6.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 47.24/6.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.51  
% 47.24/6.51  fof(f16,plain,(
% 47.24/6.51    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 47.24/6.51    inference(ennf_transformation,[],[f5])).
% 47.24/6.51  
% 47.24/6.51  fof(f35,plain,(
% 47.24/6.51    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 47.24/6.51    inference(cnf_transformation,[],[f16])).
% 47.24/6.51  
% 47.24/6.51  fof(f3,axiom,(
% 47.24/6.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 47.24/6.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.51  
% 47.24/6.51  fof(f33,plain,(
% 47.24/6.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 47.24/6.51    inference(cnf_transformation,[],[f3])).
% 47.24/6.51  
% 47.24/6.51  fof(f2,axiom,(
% 47.24/6.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 47.24/6.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.51  
% 47.24/6.51  fof(f32,plain,(
% 47.24/6.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 47.24/6.51    inference(cnf_transformation,[],[f2])).
% 47.24/6.51  
% 47.24/6.51  fof(f47,plain,(
% 47.24/6.51    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 47.24/6.51    inference(definition_unfolding,[],[f33,f32])).
% 47.24/6.52  
% 47.24/6.52  fof(f49,plain,(
% 47.24/6.52    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 47.24/6.52    inference(definition_unfolding,[],[f35,f47])).
% 47.24/6.52  
% 47.24/6.52  fof(f1,axiom,(
% 47.24/6.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 47.24/6.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.52  
% 47.24/6.52  fof(f31,plain,(
% 47.24/6.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 47.24/6.52    inference(cnf_transformation,[],[f1])).
% 47.24/6.52  
% 47.24/6.52  fof(f48,plain,(
% 47.24/6.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 47.24/6.52    inference(definition_unfolding,[],[f31,f32,f32])).
% 47.24/6.52  
% 47.24/6.52  fof(f11,axiom,(
% 47.24/6.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 47.24/6.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.52  
% 47.24/6.52  fof(f24,plain,(
% 47.24/6.52    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 47.24/6.52    inference(ennf_transformation,[],[f11])).
% 47.24/6.52  
% 47.24/6.52  fof(f42,plain,(
% 47.24/6.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 47.24/6.52    inference(cnf_transformation,[],[f24])).
% 47.24/6.52  
% 47.24/6.52  fof(f50,plain,(
% 47.24/6.52    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 47.24/6.52    inference(definition_unfolding,[],[f42,f47])).
% 47.24/6.52  
% 47.24/6.52  fof(f7,axiom,(
% 47.24/6.52    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 47.24/6.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.52  
% 47.24/6.52  fof(f18,plain,(
% 47.24/6.52    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 47.24/6.52    inference(ennf_transformation,[],[f7])).
% 47.24/6.52  
% 47.24/6.52  fof(f37,plain,(
% 47.24/6.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 47.24/6.52    inference(cnf_transformation,[],[f18])).
% 47.24/6.52  
% 47.24/6.52  fof(f45,plain,(
% 47.24/6.52    v1_funct_1(sK2)),
% 47.24/6.52    inference(cnf_transformation,[],[f30])).
% 47.24/6.52  
% 47.24/6.52  fof(f10,axiom,(
% 47.24/6.52    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 47.24/6.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.52  
% 47.24/6.52  fof(f22,plain,(
% 47.24/6.52    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 47.24/6.52    inference(ennf_transformation,[],[f10])).
% 47.24/6.52  
% 47.24/6.52  fof(f23,plain,(
% 47.24/6.52    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 47.24/6.52    inference(flattening,[],[f22])).
% 47.24/6.52  
% 47.24/6.52  fof(f41,plain,(
% 47.24/6.52    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 47.24/6.52    inference(cnf_transformation,[],[f23])).
% 47.24/6.52  
% 47.24/6.52  fof(f12,axiom,(
% 47.24/6.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 47.24/6.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.52  
% 47.24/6.52  fof(f25,plain,(
% 47.24/6.52    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 47.24/6.52    inference(ennf_transformation,[],[f12])).
% 47.24/6.52  
% 47.24/6.52  fof(f26,plain,(
% 47.24/6.52    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 47.24/6.52    inference(flattening,[],[f25])).
% 47.24/6.52  
% 47.24/6.52  fof(f43,plain,(
% 47.24/6.52    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 47.24/6.52    inference(cnf_transformation,[],[f26])).
% 47.24/6.52  
% 47.24/6.52  fof(f51,plain,(
% 47.24/6.52    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 47.24/6.52    inference(definition_unfolding,[],[f43,f47])).
% 47.24/6.52  
% 47.24/6.52  fof(f6,axiom,(
% 47.24/6.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 47.24/6.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.24/6.52  
% 47.24/6.52  fof(f17,plain,(
% 47.24/6.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 47.24/6.52    inference(ennf_transformation,[],[f6])).
% 47.24/6.52  
% 47.24/6.52  fof(f36,plain,(
% 47.24/6.52    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 47.24/6.52    inference(cnf_transformation,[],[f17])).
% 47.24/6.52  
% 47.24/6.52  fof(f46,plain,(
% 47.24/6.52    k3_xboole_0(k9_relat_1(sK2,sK0),sK1) != k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1)))),
% 47.24/6.52    inference(cnf_transformation,[],[f30])).
% 47.24/6.52  
% 47.24/6.52  fof(f52,plain,(
% 47.24/6.52    k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))))),
% 47.24/6.52    inference(definition_unfolding,[],[f46,f47,f47])).
% 47.24/6.52  
% 47.24/6.52  cnf(c_13,negated_conjecture,
% 47.24/6.52      ( v1_relat_1(sK2) ),
% 47.24/6.52      inference(cnf_transformation,[],[f44]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_277,negated_conjecture,
% 47.24/6.52      ( v1_relat_1(sK2) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_13]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_555,plain,
% 47.24/6.52      ( v1_relat_1(sK2) = iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_5,plain,
% 47.24/6.52      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 47.24/6.52      inference(cnf_transformation,[],[f38]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_284,plain,
% 47.24/6.52      ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),X0_42)
% 47.24/6.52      | ~ v1_relat_1(X0_41) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_5]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_549,plain,
% 47.24/6.52      ( r1_tarski(k1_relat_1(k7_relat_1(X0_41,X0_42)),X0_42) = iProver_top
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_284]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_6,plain,
% 47.24/6.52      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 47.24/6.52      | ~ v1_relat_1(X0)
% 47.24/6.52      | k7_relat_1(X0,X1) = X0 ),
% 47.24/6.52      inference(cnf_transformation,[],[f39]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_283,plain,
% 47.24/6.52      ( ~ r1_tarski(k1_relat_1(X0_41),X0_42)
% 47.24/6.52      | ~ v1_relat_1(X0_41)
% 47.24/6.52      | k7_relat_1(X0_41,X0_42) = X0_41 ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_6]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_550,plain,
% 47.24/6.52      ( k7_relat_1(X0_41,X0_42) = X0_41
% 47.24/6.52      | r1_tarski(k1_relat_1(X0_41),X0_42) != iProver_top
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_935,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(X0_41,X0_42),X0_42) = k7_relat_1(X0_41,X0_42)
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top
% 47.24/6.52      | v1_relat_1(k7_relat_1(X0_41,X0_42)) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_549,c_550]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 47.24/6.52      inference(cnf_transformation,[],[f34]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_288,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0_41) | v1_relat_1(k7_relat_1(X0_41,X0_42)) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_1]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_322,plain,
% 47.24/6.52      ( v1_relat_1(X0_41) != iProver_top
% 47.24/6.52      | v1_relat_1(k7_relat_1(X0_41,X0_42)) = iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_7528,plain,
% 47.24/6.52      ( v1_relat_1(X0_41) != iProver_top
% 47.24/6.52      | k7_relat_1(k7_relat_1(X0_41,X0_42),X0_42) = k7_relat_1(X0_41,X0_42) ),
% 47.24/6.52      inference(global_propositional_subsumption,
% 47.24/6.52                [status(thm)],
% 47.24/6.52                [c_935,c_322]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_7529,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(X0_41,X0_42),X0_42) = k7_relat_1(X0_41,X0_42)
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(renaming,[status(thm)],[c_7528]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_7536,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),X0_42) = k7_relat_1(sK2,X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_555,c_7529]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_2,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0)
% 47.24/6.52      | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 47.24/6.52      inference(cnf_transformation,[],[f49]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_287,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0_41)
% 47.24/6.52      | k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_2]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_546,plain,
% 47.24/6.52      ( k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_778,plain,
% 47.24/6.52      ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_555,c_546]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_0,plain,
% 47.24/6.52      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 47.24/6.52      inference(cnf_transformation,[],[f48]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_289,plain,
% 47.24/6.52      ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_0]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1012,plain,
% 47.24/6.52      ( k7_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k7_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_289,c_778]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1053,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),X1_42) = k7_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_1012,c_778]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1116,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X2_42),X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_778,c_1053]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1862,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X3_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_778,c_1116]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_2756,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42)),k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42)),X4_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X3_42),X4_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_778,c_1862]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_9084,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X2_42),X3_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42))) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_7536,c_2756]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_124047,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X2_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42))) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_7536,c_9084]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_545,plain,
% 47.24/6.52      ( v1_relat_1(X0_41) != iProver_top
% 47.24/6.52      | v1_relat_1(k7_relat_1(X0_41,X0_42)) = iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_779,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(X0_41,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42),X2_42)
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_545,c_546]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_3517,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_555,c_779]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_4343,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X0_42),X1_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_3517,c_1116]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_130157,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42))),X1_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_124047,c_4343]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1115,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X1_42),X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_1012,c_1053]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_2763,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X3_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X0_42))) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_289,c_1862]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_4311,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),X2_42),X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_1116,c_3517]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_4429,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))),X3_42) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X1_42),k1_setfam_1(k1_enumset1(X3_42,X3_42,X0_42))) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_2763,c_4311]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_4438,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),k1_setfam_1(k1_enumset1(X2_42,X2_42,X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X3_42),X2_42),X0_42),X1_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_1012,c_4311]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_4589,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42))),X3_42) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X3_42),X2_42),X1_42) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_4429,c_4438]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_4591,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42),X3_42) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X3_42),X2_42),X1_42) ),
% 47.24/6.52      inference(light_normalisation,[status(thm)],[c_4589,c_3517]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_124464,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X1_42),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42))),X3_42),X2_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_9084,c_4591]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_124517,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42),X3_42),X2_42) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_124464,c_1115]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_124518,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X2_42)),X3_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X3_42),X2_42) ),
% 47.24/6.52      inference(light_normalisation,[status(thm)],[c_124517,c_7536]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_130251,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X2_42),X1_42) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_130157,c_1115,c_124518]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_130252,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42)),X2_42))) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X2_42),X1_42) ),
% 47.24/6.52      inference(light_normalisation,[status(thm)],[c_130251,c_7536]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_9,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0)
% 47.24/6.52      | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 47.24/6.52      inference(cnf_transformation,[],[f50]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_281,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0_41)
% 47.24/6.52      | k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(X0_41,X1_42))) = k10_relat_1(k7_relat_1(X0_41,X0_42),X1_42) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_9]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_552,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(X0_41,X1_42))) = k10_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1330,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k10_relat_1(sK2,X1_42))) = k10_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_555,c_552]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1553,plain,
% 47.24/6.52      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k7_relat_1(k7_relat_1(sK2,k10_relat_1(sK2,X1_42)),X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_1330,c_1012]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_130729,plain,
% 47.24/6.52      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42)),k1_setfam_1(k1_enumset1(X0_42,X0_42,X0_42)),X1_42))),X2_42)) = k7_relat_1(k7_relat_1(k7_relat_1(sK2,k10_relat_1(sK2,X2_42)),X1_42),X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_130252,c_1553]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_131020,plain,
% 47.24/6.52      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),k1_setfam_1(k1_enumset1(X1_42,X1_42,X1_42))),X2_42)) = k7_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X2_42)),X1_42) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_130729,c_1012,c_1553]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_131021,plain,
% 47.24/6.52      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42),X2_42)) = k7_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_42),X2_42)),X0_42) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_131020,c_1115]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_131022,plain,
% 47.24/6.52      ( k7_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)),X2_42) = k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X2_42),X0_42),X1_42)) ),
% 47.24/6.52      inference(light_normalisation,[status(thm)],[c_131021,c_7536]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_4,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0)
% 47.24/6.52      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 47.24/6.52      inference(cnf_transformation,[],[f37]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_285,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0_41)
% 47.24/6.52      | k2_relat_1(k7_relat_1(X0_41,X0_42)) = k9_relat_1(X0_41,X0_42) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_4]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_548,plain,
% 47.24/6.52      ( k2_relat_1(k7_relat_1(X0_41,X0_42)) = k9_relat_1(X0_41,X0_42)
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_794,plain,
% 47.24/6.52      ( k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X0_42),X1_42)) = k9_relat_1(k7_relat_1(X0_41,X0_42),X1_42)
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_545,c_548]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_5779,plain,
% 47.24/6.52      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k9_relat_1(k7_relat_1(sK2,X0_42),X1_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_555,c_794]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_6703,plain,
% 47.24/6.52      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k9_relat_1(k7_relat_1(sK2,X1_42),X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_1053,c_5779]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_141046,plain,
% 47.24/6.52      ( k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42))) = k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X1_42),X2_42)) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_131022,c_6703]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_793,plain,
% 47.24/6.52      ( k2_relat_1(k7_relat_1(sK2,X0_42)) = k9_relat_1(sK2,X0_42) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_555,c_548]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_141442,plain,
% 47.24/6.52      ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X1_42),X2_42)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42),X2_42)) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_141046,c_793]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_12,negated_conjecture,
% 47.24/6.52      ( v1_funct_1(sK2) ),
% 47.24/6.52      inference(cnf_transformation,[],[f45]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_278,negated_conjecture,
% 47.24/6.52      ( v1_funct_1(sK2) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_12]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_554,plain,
% 47.24/6.52      ( v1_funct_1(sK2) = iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_7,plain,
% 47.24/6.52      ( ~ v1_funct_1(X0)
% 47.24/6.52      | v1_funct_1(k7_relat_1(X0,X1))
% 47.24/6.52      | ~ v1_relat_1(X0) ),
% 47.24/6.52      inference(cnf_transformation,[],[f41]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_282,plain,
% 47.24/6.52      ( ~ v1_funct_1(X0_41)
% 47.24/6.52      | v1_funct_1(k7_relat_1(X0_41,X0_42))
% 47.24/6.52      | ~ v1_relat_1(X0_41) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_7]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_551,plain,
% 47.24/6.52      ( v1_funct_1(X0_41) != iProver_top
% 47.24/6.52      | v1_funct_1(k7_relat_1(X0_41,X0_42)) = iProver_top
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_10,plain,
% 47.24/6.52      ( ~ v1_funct_1(X0)
% 47.24/6.52      | ~ v1_relat_1(X0)
% 47.24/6.52      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 47.24/6.52      inference(cnf_transformation,[],[f51]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_280,plain,
% 47.24/6.52      ( ~ v1_funct_1(X0_41)
% 47.24/6.52      | ~ v1_relat_1(X0_41)
% 47.24/6.52      | k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(X0_41,k1_relat_1(X0_41)))) = k9_relat_1(X0_41,k10_relat_1(X0_41,X0_42)) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_10]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_553,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(X0_41,k1_relat_1(X0_41)))) = k9_relat_1(X0_41,k10_relat_1(X0_41,X0_42))
% 47.24/6.52      | v1_funct_1(X0_41) != iProver_top
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1421,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(X0_41,X1_42),k1_relat_1(k7_relat_1(X0_41,X1_42))))) = k9_relat_1(k7_relat_1(X0_41,X1_42),k10_relat_1(k7_relat_1(X0_41,X1_42),X0_42))
% 47.24/6.52      | v1_funct_1(X0_41) != iProver_top
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top
% 47.24/6.52      | v1_relat_1(k7_relat_1(X0_41,X1_42)) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_551,c_553]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_56654,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(X0_41,X1_42),k1_relat_1(k7_relat_1(X0_41,X1_42))))) = k9_relat_1(k7_relat_1(X0_41,X1_42),k10_relat_1(k7_relat_1(X0_41,X1_42),X0_42))
% 47.24/6.52      | v1_funct_1(X0_41) != iProver_top
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(forward_subsumption_resolution,
% 47.24/6.52                [status(thm)],
% 47.24/6.52                [c_1421,c_545]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_56658,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(sK2,X1_42),k1_relat_1(k7_relat_1(sK2,X1_42))))) = k9_relat_1(k7_relat_1(sK2,X1_42),k10_relat_1(k7_relat_1(sK2,X1_42),X0_42))
% 47.24/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_554,c_56654]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_3,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0)
% 47.24/6.52      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 47.24/6.52      inference(cnf_transformation,[],[f36]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_286,plain,
% 47.24/6.52      ( ~ v1_relat_1(X0_41)
% 47.24/6.52      | k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_3]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_547,plain,
% 47.24/6.52      ( k9_relat_1(X0_41,k1_relat_1(X0_41)) = k2_relat_1(X0_41)
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_714,plain,
% 47.24/6.52      ( k9_relat_1(k7_relat_1(X0_41,X0_42),k1_relat_1(k7_relat_1(X0_41,X0_42))) = k2_relat_1(k7_relat_1(X0_41,X0_42))
% 47.24/6.52      | v1_relat_1(X0_41) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_545,c_547]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_2112,plain,
% 47.24/6.52      ( k9_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k2_relat_1(k7_relat_1(sK2,X0_42)) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_555,c_714]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_2124,plain,
% 47.24/6.52      ( k9_relat_1(k7_relat_1(sK2,X0_42),k1_relat_1(k7_relat_1(sK2,X0_42))) = k9_relat_1(sK2,X0_42) ),
% 47.24/6.52      inference(light_normalisation,[status(thm)],[c_2112,c_793]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_56701,plain,
% 47.24/6.52      ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k1_setfam_1(k1_enumset1(X1_42,X1_42,k9_relat_1(sK2,X0_42)))
% 47.24/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_56658,c_2124]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1016,plain,
% 47.24/6.52      ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = iProver_top
% 47.24/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_778,c_545]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_14,plain,
% 47.24/6.52      ( v1_relat_1(sK2) = iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1152,plain,
% 47.24/6.52      ( v1_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = iProver_top ),
% 47.24/6.52      inference(global_propositional_subsumption,
% 47.24/6.52                [status(thm)],
% 47.24/6.52                [c_1016,c_14]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_9092,plain,
% 47.24/6.52      ( v1_relat_1(k7_relat_1(sK2,X0_42)) = iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_7536,c_1152]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1014,plain,
% 47.24/6.52      ( v1_funct_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = iProver_top
% 47.24/6.52      | v1_funct_1(sK2) != iProver_top
% 47.24/6.52      | v1_relat_1(sK2) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_778,c_551]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_15,plain,
% 47.24/6.52      ( v1_funct_1(sK2) = iProver_top ),
% 47.24/6.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_2506,plain,
% 47.24/6.52      ( v1_funct_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = iProver_top ),
% 47.24/6.52      inference(global_propositional_subsumption,
% 47.24/6.52                [status(thm)],
% 47.24/6.52                [c_1014,c_14,c_15]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_9088,plain,
% 47.24/6.52      ( v1_funct_1(k7_relat_1(sK2,X0_42)) = iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_7536,c_2506]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_9238,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(k7_relat_1(sK2,X1_42),k1_relat_1(k7_relat_1(sK2,X1_42))))) = k9_relat_1(k7_relat_1(sK2,X1_42),k10_relat_1(k7_relat_1(sK2,X1_42),X0_42))
% 47.24/6.52      | v1_relat_1(k7_relat_1(sK2,X1_42)) != iProver_top ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_9088,c_553]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_9241,plain,
% 47.24/6.52      ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k1_setfam_1(k1_enumset1(X1_42,X1_42,k9_relat_1(sK2,X0_42)))
% 47.24/6.52      | v1_relat_1(k7_relat_1(sK2,X0_42)) != iProver_top ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_9238,c_2124]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_58177,plain,
% 47.24/6.52      ( k9_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k1_setfam_1(k1_enumset1(X1_42,X1_42,k9_relat_1(sK2,X0_42))) ),
% 47.24/6.52      inference(global_propositional_subsumption,
% 47.24/6.52                [status(thm)],
% 47.24/6.52                [c_56701,c_9092,c_9241]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_147027,plain,
% 47.24/6.52      ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X0_42),X1_42)) = k1_setfam_1(k1_enumset1(X1_42,X1_42,k9_relat_1(sK2,X0_42))) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_141442,c_58177]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_147044,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(X0_42,X0_42,k9_relat_1(sK2,X1_42))) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X1_42),X0_42)) ),
% 47.24/6.52      inference(light_normalisation,[status(thm)],[c_147027,c_7536]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1554,plain,
% 47.24/6.52      ( k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_42),X1_42)) = k7_relat_1(k7_relat_1(sK2,X0_42),k10_relat_1(sK2,X1_42)) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_1330,c_778]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1017,plain,
% 47.24/6.52      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_42,X0_42,X1_42))) = k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_42),X1_42)) ),
% 47.24/6.52      inference(superposition,[status(thm)],[c_778,c_793]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_11,negated_conjecture,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
% 47.24/6.52      inference(cnf_transformation,[],[f52]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_279,negated_conjecture,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) ),
% 47.24/6.52      inference(subtyping,[status(esa)],[c_11]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_644,plain,
% 47.24/6.52      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_289,c_279]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1242,plain,
% 47.24/6.52      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_1017,c_644]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1742,plain,
% 47.24/6.52      ( k2_relat_1(k7_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_1554,c_1242]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_1743,plain,
% 47.24/6.52      ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_1742,c_793]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_147379,plain,
% 47.24/6.52      ( k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) != k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 47.24/6.52      inference(demodulation,[status(thm)],[c_147044,c_1743]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_293,plain,( X0_43 = X0_43 ),theory(equality) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_9487,plain,
% 47.24/6.52      ( k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) = k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) ),
% 47.24/6.52      inference(instantiation,[status(thm)],[c_293]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_300,plain,
% 47.24/6.52      ( X0_43 != X1_43 | k1_setfam_1(X0_43) = k1_setfam_1(X1_43) ),
% 47.24/6.52      theory(equality) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_4905,plain,
% 47.24/6.52      ( X0_43 != k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))
% 47.24/6.52      | k1_setfam_1(X0_43) = k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 47.24/6.52      inference(instantiation,[status(thm)],[c_300]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(c_9486,plain,
% 47.24/6.52      ( k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)) != k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))
% 47.24/6.52      | k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) = k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))) ),
% 47.24/6.52      inference(instantiation,[status(thm)],[c_4905]) ).
% 47.24/6.52  
% 47.24/6.52  cnf(contradiction,plain,
% 47.24/6.52      ( $false ),
% 47.24/6.52      inference(minisat,[status(thm)],[c_147379,c_9487,c_9486]) ).
% 47.24/6.52  
% 47.24/6.52  
% 47.24/6.52  % SZS output end CNFRefutation for theBenchmark.p
% 47.24/6.52  
% 47.24/6.52  ------                               Statistics
% 47.24/6.52  
% 47.24/6.52  ------ General
% 47.24/6.52  
% 47.24/6.52  abstr_ref_over_cycles:                  0
% 47.24/6.52  abstr_ref_under_cycles:                 0
% 47.24/6.52  gc_basic_clause_elim:                   0
% 47.24/6.52  forced_gc_time:                         0
% 47.24/6.52  parsing_time:                           0.01
% 47.24/6.52  unif_index_cands_time:                  0.
% 47.24/6.52  unif_index_add_time:                    0.
% 47.24/6.52  orderings_time:                         0.
% 47.24/6.52  out_proof_time:                         0.015
% 47.24/6.52  total_time:                             5.71
% 47.24/6.52  num_of_symbols:                         44
% 47.24/6.52  num_of_terms:                           277306
% 47.24/6.52  
% 47.24/6.52  ------ Preprocessing
% 47.24/6.52  
% 47.24/6.52  num_of_splits:                          0
% 47.24/6.52  num_of_split_atoms:                     0
% 47.24/6.52  num_of_reused_defs:                     0
% 47.24/6.52  num_eq_ax_congr_red:                    3
% 47.24/6.52  num_of_sem_filtered_clauses:            1
% 47.24/6.52  num_of_subtypes:                        3
% 47.24/6.52  monotx_restored_types:                  0
% 47.24/6.52  sat_num_of_epr_types:                   0
% 47.24/6.52  sat_num_of_non_cyclic_types:            0
% 47.24/6.52  sat_guarded_non_collapsed_types:        1
% 47.24/6.52  num_pure_diseq_elim:                    0
% 47.24/6.52  simp_replaced_by:                       0
% 47.24/6.52  res_preprocessed:                       85
% 47.24/6.52  prep_upred:                             0
% 47.24/6.52  prep_unflattend:                        2
% 47.24/6.52  smt_new_axioms:                         0
% 47.24/6.52  pred_elim_cands:                        3
% 47.24/6.52  pred_elim:                              0
% 47.24/6.52  pred_elim_cl:                           0
% 47.24/6.52  pred_elim_cycles:                       2
% 47.24/6.52  merged_defs:                            0
% 47.24/6.52  merged_defs_ncl:                        0
% 47.24/6.52  bin_hyper_res:                          0
% 47.24/6.52  prep_cycles:                            4
% 47.24/6.52  pred_elim_time:                         0.001
% 47.24/6.52  splitting_time:                         0.
% 47.24/6.52  sem_filter_time:                        0.
% 47.24/6.52  monotx_time:                            0.
% 47.24/6.52  subtype_inf_time:                       0.
% 47.24/6.52  
% 47.24/6.52  ------ Problem properties
% 47.24/6.52  
% 47.24/6.52  clauses:                                13
% 47.24/6.52  conjectures:                            3
% 47.24/6.52  epr:                                    2
% 47.24/6.52  horn:                                   13
% 47.24/6.52  ground:                                 3
% 47.24/6.52  unary:                                  4
% 47.24/6.52  binary:                                 6
% 47.24/6.52  lits:                                   25
% 47.24/6.52  lits_eq:                                8
% 47.24/6.52  fd_pure:                                0
% 47.24/6.52  fd_pseudo:                              0
% 47.24/6.52  fd_cond:                                0
% 47.24/6.52  fd_pseudo_cond:                         0
% 47.24/6.52  ac_symbols:                             0
% 47.24/6.52  
% 47.24/6.52  ------ Propositional Solver
% 47.24/6.52  
% 47.24/6.52  prop_solver_calls:                      35
% 47.24/6.52  prop_fast_solver_calls:                 815
% 47.24/6.52  smt_solver_calls:                       0
% 47.24/6.52  smt_fast_solver_calls:                  0
% 47.24/6.52  prop_num_of_clauses:                    34649
% 47.24/6.52  prop_preprocess_simplified:             31790
% 47.24/6.52  prop_fo_subsumed:                       12
% 47.24/6.52  prop_solver_time:                       0.
% 47.24/6.52  smt_solver_time:                        0.
% 47.24/6.52  smt_fast_solver_time:                   0.
% 47.24/6.52  prop_fast_solver_time:                  0.
% 47.24/6.52  prop_unsat_core_time:                   0.002
% 47.24/6.52  
% 47.24/6.52  ------ QBF
% 47.24/6.52  
% 47.24/6.52  qbf_q_res:                              0
% 47.24/6.52  qbf_num_tautologies:                    0
% 47.24/6.52  qbf_prep_cycles:                        0
% 47.24/6.52  
% 47.24/6.52  ------ BMC1
% 47.24/6.52  
% 47.24/6.52  bmc1_current_bound:                     -1
% 47.24/6.52  bmc1_last_solved_bound:                 -1
% 47.24/6.52  bmc1_unsat_core_size:                   -1
% 47.24/6.52  bmc1_unsat_core_parents_size:           -1
% 47.24/6.52  bmc1_merge_next_fun:                    0
% 47.24/6.52  bmc1_unsat_core_clauses_time:           0.
% 47.24/6.52  
% 47.24/6.52  ------ Instantiation
% 47.24/6.52  
% 47.24/6.52  inst_num_of_clauses:                    4464
% 47.24/6.52  inst_num_in_passive:                    2164
% 47.24/6.52  inst_num_in_active:                     1824
% 47.24/6.52  inst_num_in_unprocessed:                478
% 47.24/6.52  inst_num_of_loops:                      1850
% 47.24/6.52  inst_num_of_learning_restarts:          0
% 47.24/6.52  inst_num_moves_active_passive:          19
% 47.24/6.52  inst_lit_activity:                      0
% 47.24/6.52  inst_lit_activity_moves:                0
% 47.24/6.52  inst_num_tautologies:                   0
% 47.24/6.52  inst_num_prop_implied:                  0
% 47.24/6.52  inst_num_existing_simplified:           0
% 47.24/6.52  inst_num_eq_res_simplified:             0
% 47.24/6.52  inst_num_child_elim:                    0
% 47.24/6.52  inst_num_of_dismatching_blockings:      4768
% 47.24/6.52  inst_num_of_non_proper_insts:           9561
% 47.24/6.52  inst_num_of_duplicates:                 0
% 47.24/6.52  inst_inst_num_from_inst_to_res:         0
% 47.24/6.52  inst_dismatching_checking_time:         0.
% 47.24/6.52  
% 47.24/6.52  ------ Resolution
% 47.24/6.52  
% 47.24/6.52  res_num_of_clauses:                     0
% 47.24/6.52  res_num_in_passive:                     0
% 47.24/6.52  res_num_in_active:                      0
% 47.24/6.52  res_num_of_loops:                       89
% 47.24/6.52  res_forward_subset_subsumed:            1504
% 47.24/6.52  res_backward_subset_subsumed:           6
% 47.24/6.52  res_forward_subsumed:                   0
% 47.24/6.52  res_backward_subsumed:                  0
% 47.24/6.52  res_forward_subsumption_resolution:     0
% 47.24/6.52  res_backward_subsumption_resolution:    0
% 47.24/6.52  res_clause_to_clause_subsumption:       147751
% 47.24/6.52  res_orphan_elimination:                 0
% 47.24/6.52  res_tautology_del:                      1165
% 47.24/6.52  res_num_eq_res_simplified:              0
% 47.24/6.52  res_num_sel_changes:                    0
% 47.24/6.52  res_moves_from_active_to_pass:          0
% 47.24/6.52  
% 47.24/6.52  ------ Superposition
% 47.24/6.52  
% 47.24/6.52  sup_time_total:                         0.
% 47.24/6.52  sup_time_generating:                    0.
% 47.24/6.52  sup_time_sim_full:                      0.
% 47.24/6.52  sup_time_sim_immed:                     0.
% 47.24/6.52  
% 47.24/6.52  sup_num_of_clauses:                     12644
% 47.24/6.52  sup_num_in_active:                      313
% 47.24/6.52  sup_num_in_passive:                     12331
% 47.24/6.52  sup_num_of_loops:                       368
% 47.24/6.52  sup_fw_superposition:                   20001
% 47.24/6.52  sup_bw_superposition:                   13779
% 47.24/6.52  sup_immediate_simplified:               17813
% 47.24/6.52  sup_given_eliminated:                   15
% 47.24/6.52  comparisons_done:                       0
% 47.24/6.52  comparisons_avoided:                    0
% 47.24/6.52  
% 47.24/6.52  ------ Simplifications
% 47.24/6.52  
% 47.24/6.52  
% 47.24/6.52  sim_fw_subset_subsumed:                 143
% 47.24/6.52  sim_bw_subset_subsumed:                 56
% 47.24/6.52  sim_fw_subsumed:                        1253
% 47.24/6.52  sim_bw_subsumed:                        260
% 47.24/6.52  sim_fw_subsumption_res:                 2
% 47.24/6.52  sim_bw_subsumption_res:                 0
% 47.24/6.52  sim_tautology_del:                      22
% 47.24/6.52  sim_eq_tautology_del:                   680
% 47.24/6.52  sim_eq_res_simp:                        0
% 47.24/6.52  sim_fw_demodulated:                     14656
% 47.24/6.52  sim_bw_demodulated:                     2057
% 47.24/6.52  sim_light_normalised:                   7251
% 47.24/6.52  sim_joinable_taut:                      0
% 47.24/6.52  sim_joinable_simp:                      0
% 47.24/6.52  sim_ac_normalised:                      0
% 47.24/6.52  sim_smt_subsumption:                    0
% 47.24/6.52  
%------------------------------------------------------------------------------
