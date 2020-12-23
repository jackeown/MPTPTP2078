%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:36 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 318 expanded)
%              Number of clauses        :   55 (  82 expanded)
%              Number of leaves         :   18 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  292 (1086 expanded)
%              Number of equality atoms :  102 ( 297 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f46,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f47,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f51])).

fof(f82,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f80,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f66,f70,f70])).

fof(f86,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f53,f85,f85])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f91,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f71,f85,f69])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f62,f70])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v2_funct_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_948,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_966,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2617,plain,
    ( k6_subset_1(sK0,k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_948,c_966])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_946,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_957,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5309,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_946,c_957])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_947,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_955,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6434,plain,
    ( k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_955])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1228,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_7603,plain,
    ( k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6434,c_28,c_27,c_25,c_1228])).

cnf(c_7609,plain,
    ( k9_relat_1(sK1,k6_subset_1(X0,k1_relat_1(sK1))) = k6_subset_1(k9_relat_1(sK1,X0),k2_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_5309,c_7603])).

cnf(c_10038,plain,
    ( k6_subset_1(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) = k9_relat_1(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2617,c_7609])).

cnf(c_0,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_10143,plain,
    ( k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,sK0))) = k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_10038,c_0])).

cnf(c_11,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_15,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_10148,plain,
    ( k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,sK0))) = k9_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_10143,c_11,c_15,c_7603])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_954,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5081,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_954])).

cnf(c_1218,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_5563,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5081,c_28,c_27,c_1218])).

cnf(c_9,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_961,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2614,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_961,c_966])).

cnf(c_5573,plain,
    ( k6_subset_1(k10_relat_1(sK1,k6_subset_1(X0,X1)),k10_relat_1(sK1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5563,c_2614])).

cnf(c_11710,plain,
    ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(sK1,k2_relat_1(sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10148,c_5573])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_956,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4299,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_946,c_956])).

cnf(c_11742,plain,
    ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11710,c_4299])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1310,plain,
    ( r1_tarski(X0,k1_relat_1(sK1))
    | k6_subset_1(X0,k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2009,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_20,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1193,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1896,plain,
    ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_23,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_relat_1(X2))
    | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1425,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(X0))
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(k9_relat_1(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(X0,sK0))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1874,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
    | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1425])).

cnf(c_21,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1213,plain,
    ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1354,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1213])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1190,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_24,negated_conjecture,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11742,c_2009,c_1896,c_1874,c_1354,c_1190,c_24,c_25,c_26,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:39:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.01/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/0.99  
% 4.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.01/0.99  
% 4.01/0.99  ------  iProver source info
% 4.01/0.99  
% 4.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.01/0.99  git: non_committed_changes: false
% 4.01/0.99  git: last_make_outside_of_git: false
% 4.01/0.99  
% 4.01/0.99  ------ 
% 4.01/0.99  ------ Parsing...
% 4.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.01/0.99  
% 4.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.01/0.99  
% 4.01/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.01/0.99  
% 4.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.01/0.99  ------ Proving...
% 4.01/0.99  ------ Problem Properties 
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  clauses                                 28
% 4.01/0.99  conjectures                             5
% 4.01/0.99  EPR                                     7
% 4.01/0.99  Horn                                    28
% 4.01/0.99  unary                                   13
% 4.01/0.99  binary                                  7
% 4.01/0.99  lits                                    55
% 4.01/0.99  lits eq                                 14
% 4.01/0.99  fd_pure                                 0
% 4.01/0.99  fd_pseudo                               0
% 4.01/0.99  fd_cond                                 1
% 4.01/0.99  fd_pseudo_cond                          1
% 4.01/0.99  AC symbols                              0
% 4.01/0.99  
% 4.01/0.99  ------ Input Options Time Limit: Unbounded
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  ------ 
% 4.01/0.99  Current options:
% 4.01/0.99  ------ 
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  ------ Proving...
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  % SZS status Theorem for theBenchmark.p
% 4.01/0.99  
% 4.01/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.01/0.99  
% 4.01/0.99  fof(f25,conjecture,(
% 4.01/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f26,negated_conjecture,(
% 4.01/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 4.01/0.99    inference(negated_conjecture,[],[f25])).
% 4.01/0.99  
% 4.01/0.99  fof(f46,plain,(
% 4.01/0.99    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.01/0.99    inference(ennf_transformation,[],[f26])).
% 4.01/0.99  
% 4.01/0.99  fof(f47,plain,(
% 4.01/0.99    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.01/0.99    inference(flattening,[],[f46])).
% 4.01/0.99  
% 4.01/0.99  fof(f51,plain,(
% 4.01/0.99    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 4.01/0.99    introduced(choice_axiom,[])).
% 4.01/0.99  
% 4.01/0.99  fof(f52,plain,(
% 4.01/0.99    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 4.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f51])).
% 4.01/0.99  
% 4.01/0.99  fof(f82,plain,(
% 4.01/0.99    r1_tarski(sK0,k1_relat_1(sK1))),
% 4.01/0.99    inference(cnf_transformation,[],[f52])).
% 4.01/0.99  
% 4.01/0.99  fof(f3,axiom,(
% 4.01/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f50,plain,(
% 4.01/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.01/0.99    inference(nnf_transformation,[],[f3])).
% 4.01/0.99  
% 4.01/0.99  fof(f58,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f50])).
% 4.01/0.99  
% 4.01/0.99  fof(f15,axiom,(
% 4.01/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f70,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f15])).
% 4.01/0.99  
% 4.01/0.99  fof(f87,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f58,f70])).
% 4.01/0.99  
% 4.01/0.99  fof(f80,plain,(
% 4.01/0.99    v1_relat_1(sK1)),
% 4.01/0.99    inference(cnf_transformation,[],[f52])).
% 4.01/0.99  
% 4.01/0.99  fof(f17,axiom,(
% 4.01/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f32,plain,(
% 4.01/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 4.01/0.99    inference(ennf_transformation,[],[f17])).
% 4.01/0.99  
% 4.01/0.99  fof(f72,plain,(
% 4.01/0.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f32])).
% 4.01/0.99  
% 4.01/0.99  fof(f81,plain,(
% 4.01/0.99    v1_funct_1(sK1)),
% 4.01/0.99    inference(cnf_transformation,[],[f52])).
% 4.01/0.99  
% 4.01/0.99  fof(f19,axiom,(
% 4.01/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f34,plain,(
% 4.01/0.99    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.01/0.99    inference(ennf_transformation,[],[f19])).
% 4.01/0.99  
% 4.01/0.99  fof(f35,plain,(
% 4.01/0.99    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.01/0.99    inference(flattening,[],[f34])).
% 4.01/0.99  
% 4.01/0.99  fof(f74,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f35])).
% 4.01/0.99  
% 4.01/0.99  fof(f83,plain,(
% 4.01/0.99    v2_funct_1(sK1)),
% 4.01/0.99    inference(cnf_transformation,[],[f52])).
% 4.01/0.99  
% 4.01/0.99  fof(f1,axiom,(
% 4.01/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f53,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f1])).
% 4.01/0.99  
% 4.01/0.99  fof(f11,axiom,(
% 4.01/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f66,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f11])).
% 4.01/0.99  
% 4.01/0.99  fof(f85,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 4.01/0.99    inference(definition_unfolding,[],[f66,f70,f70])).
% 4.01/0.99  
% 4.01/0.99  fof(f86,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 4.01/0.99    inference(definition_unfolding,[],[f53,f85,f85])).
% 4.01/0.99  
% 4.01/0.99  fof(f9,axiom,(
% 4.01/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f64,plain,(
% 4.01/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.01/0.99    inference(cnf_transformation,[],[f9])).
% 4.01/0.99  
% 4.01/0.99  fof(f91,plain,(
% 4.01/0.99    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 4.01/0.99    inference(definition_unfolding,[],[f64,f70])).
% 4.01/0.99  
% 4.01/0.99  fof(f16,axiom,(
% 4.01/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f71,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.01/0.99    inference(cnf_transformation,[],[f16])).
% 4.01/0.99  
% 4.01/0.99  fof(f14,axiom,(
% 4.01/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f69,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f14])).
% 4.01/0.99  
% 4.01/0.99  fof(f94,plain,(
% 4.01/0.99    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 4.01/0.99    inference(definition_unfolding,[],[f71,f85,f69])).
% 4.01/0.99  
% 4.01/0.99  fof(f20,axiom,(
% 4.01/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f36,plain,(
% 4.01/0.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.01/0.99    inference(ennf_transformation,[],[f20])).
% 4.01/0.99  
% 4.01/0.99  fof(f37,plain,(
% 4.01/0.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.01/0.99    inference(flattening,[],[f36])).
% 4.01/0.99  
% 4.01/0.99  fof(f75,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f37])).
% 4.01/0.99  
% 4.01/0.99  fof(f7,axiom,(
% 4.01/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f62,plain,(
% 4.01/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f7])).
% 4.01/0.99  
% 4.01/0.99  fof(f89,plain,(
% 4.01/0.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f62,f70])).
% 4.01/0.99  
% 4.01/0.99  fof(f18,axiom,(
% 4.01/0.99    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f33,plain,(
% 4.01/0.99    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.01/0.99    inference(ennf_transformation,[],[f18])).
% 4.01/0.99  
% 4.01/0.99  fof(f73,plain,(
% 4.01/0.99    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f33])).
% 4.01/0.99  
% 4.01/0.99  fof(f57,plain,(
% 4.01/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.01/0.99    inference(cnf_transformation,[],[f50])).
% 4.01/0.99  
% 4.01/0.99  fof(f88,plain,(
% 4.01/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 4.01/0.99    inference(definition_unfolding,[],[f57,f70])).
% 4.01/0.99  
% 4.01/0.99  fof(f21,axiom,(
% 4.01/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f38,plain,(
% 4.01/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.01/0.99    inference(ennf_transformation,[],[f21])).
% 4.01/0.99  
% 4.01/0.99  fof(f39,plain,(
% 4.01/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.01/0.99    inference(flattening,[],[f38])).
% 4.01/0.99  
% 4.01/0.99  fof(f76,plain,(
% 4.01/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f39])).
% 4.01/0.99  
% 4.01/0.99  fof(f24,axiom,(
% 4.01/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f44,plain,(
% 4.01/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,X1) | (~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.01/0.99    inference(ennf_transformation,[],[f24])).
% 4.01/0.99  
% 4.01/0.99  fof(f45,plain,(
% 4.01/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.01/0.99    inference(flattening,[],[f44])).
% 4.01/0.99  
% 4.01/0.99  fof(f79,plain,(
% 4.01/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~v2_funct_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f45])).
% 4.01/0.99  
% 4.01/0.99  fof(f22,axiom,(
% 4.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f40,plain,(
% 4.01/0.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 4.01/0.99    inference(ennf_transformation,[],[f22])).
% 4.01/0.99  
% 4.01/0.99  fof(f41,plain,(
% 4.01/0.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.01/0.99    inference(flattening,[],[f40])).
% 4.01/0.99  
% 4.01/0.99  fof(f77,plain,(
% 4.01/0.99    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f41])).
% 4.01/0.99  
% 4.01/0.99  fof(f2,axiom,(
% 4.01/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.01/0.99  
% 4.01/0.99  fof(f48,plain,(
% 4.01/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.01/0.99    inference(nnf_transformation,[],[f2])).
% 4.01/0.99  
% 4.01/0.99  fof(f49,plain,(
% 4.01/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.01/0.99    inference(flattening,[],[f48])).
% 4.01/0.99  
% 4.01/0.99  fof(f56,plain,(
% 4.01/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.01/0.99    inference(cnf_transformation,[],[f49])).
% 4.01/0.99  
% 4.01/0.99  fof(f84,plain,(
% 4.01/0.99    k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0),
% 4.01/0.99    inference(cnf_transformation,[],[f52])).
% 4.01/0.99  
% 4.01/0.99  cnf(c_26,negated_conjecture,
% 4.01/0.99      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 4.01/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_948,plain,
% 4.01/0.99      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_4,plain,
% 4.01/0.99      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f87]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_966,plain,
% 4.01/0.99      ( k6_subset_1(X0,X1) = k1_xboole_0
% 4.01/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2617,plain,
% 4.01/0.99      ( k6_subset_1(sK0,k1_relat_1(sK1)) = k1_xboole_0 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_948,c_966]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_28,negated_conjecture,
% 4.01/0.99      ( v1_relat_1(sK1) ),
% 4.01/0.99      inference(cnf_transformation,[],[f80]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_946,plain,
% 4.01/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_16,plain,
% 4.01/0.99      ( ~ v1_relat_1(X0)
% 4.01/0.99      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 4.01/0.99      inference(cnf_transformation,[],[f72]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_957,plain,
% 4.01/0.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 4.01/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_5309,plain,
% 4.01/0.99      ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_946,c_957]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_27,negated_conjecture,
% 4.01/0.99      ( v1_funct_1(sK1) ),
% 4.01/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_947,plain,
% 4.01/0.99      ( v1_funct_1(sK1) = iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_18,plain,
% 4.01/0.99      ( ~ v1_funct_1(X0)
% 4.01/0.99      | ~ v2_funct_1(X0)
% 4.01/0.99      | ~ v1_relat_1(X0)
% 4.01/0.99      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 4.01/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_955,plain,
% 4.01/0.99      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 4.01/0.99      | v1_funct_1(X0) != iProver_top
% 4.01/0.99      | v2_funct_1(X0) != iProver_top
% 4.01/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_6434,plain,
% 4.01/0.99      ( k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1))
% 4.01/0.99      | v2_funct_1(sK1) != iProver_top
% 4.01/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_947,c_955]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_25,negated_conjecture,
% 4.01/0.99      ( v2_funct_1(sK1) ),
% 4.01/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1228,plain,
% 4.01/0.99      ( ~ v1_funct_1(sK1)
% 4.01/0.99      | ~ v2_funct_1(sK1)
% 4.01/0.99      | ~ v1_relat_1(sK1)
% 4.01/0.99      | k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_7603,plain,
% 4.01/0.99      ( k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 4.01/0.99      inference(global_propositional_subsumption,
% 4.01/0.99                [status(thm)],
% 4.01/0.99                [c_6434,c_28,c_27,c_25,c_1228]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_7609,plain,
% 4.01/0.99      ( k9_relat_1(sK1,k6_subset_1(X0,k1_relat_1(sK1))) = k6_subset_1(k9_relat_1(sK1,X0),k2_relat_1(sK1)) ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_5309,c_7603]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_10038,plain,
% 4.01/0.99      ( k6_subset_1(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) = k9_relat_1(sK1,k1_xboole_0) ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_2617,c_7609]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_0,plain,
% 4.01/0.99      ( k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
% 4.01/0.99      inference(cnf_transformation,[],[f86]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_10143,plain,
% 4.01/0.99      ( k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,sK0))) = k6_subset_1(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k1_xboole_0)) ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_10038,c_0]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_11,plain,
% 4.01/0.99      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f91]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_15,plain,
% 4.01/0.99      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
% 4.01/0.99      inference(cnf_transformation,[],[f94]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_10148,plain,
% 4.01/0.99      ( k6_subset_1(k2_relat_1(sK1),k6_subset_1(k2_relat_1(sK1),k9_relat_1(sK1,sK0))) = k9_relat_1(sK1,sK0) ),
% 4.01/0.99      inference(demodulation,[status(thm)],[c_10143,c_11,c_15,c_7603]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_19,plain,
% 4.01/0.99      ( ~ v1_funct_1(X0)
% 4.01/0.99      | ~ v1_relat_1(X0)
% 4.01/0.99      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 4.01/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_954,plain,
% 4.01/0.99      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 4.01/0.99      | v1_funct_1(X0) != iProver_top
% 4.01/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_5081,plain,
% 4.01/0.99      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
% 4.01/0.99      | v1_relat_1(sK1) != iProver_top ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_947,c_954]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1218,plain,
% 4.01/0.99      ( ~ v1_funct_1(sK1)
% 4.01/0.99      | ~ v1_relat_1(sK1)
% 4.01/0.99      | k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_5563,plain,
% 4.01/0.99      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 4.01/0.99      inference(global_propositional_subsumption,
% 4.01/0.99                [status(thm)],
% 4.01/0.99                [c_5081,c_28,c_27,c_1218]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_9,plain,
% 4.01/0.99      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 4.01/0.99      inference(cnf_transformation,[],[f89]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_961,plain,
% 4.01/0.99      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2614,plain,
% 4.01/0.99      ( k6_subset_1(k6_subset_1(X0,X1),X0) = k1_xboole_0 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_961,c_966]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_5573,plain,
% 4.01/0.99      ( k6_subset_1(k10_relat_1(sK1,k6_subset_1(X0,X1)),k10_relat_1(sK1,X0)) = k1_xboole_0 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_5563,c_2614]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_11710,plain,
% 4.01/0.99      ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k10_relat_1(sK1,k2_relat_1(sK1))) = k1_xboole_0 ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_10148,c_5573]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_17,plain,
% 4.01/0.99      ( ~ v1_relat_1(X0)
% 4.01/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 4.01/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_956,plain,
% 4.01/0.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 4.01/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.01/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_4299,plain,
% 4.01/0.99      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 4.01/0.99      inference(superposition,[status(thm)],[c_946,c_956]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_11742,plain,
% 4.01/0.99      ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) = k1_xboole_0 ),
% 4.01/0.99      inference(light_normalisation,[status(thm)],[c_11710,c_4299]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_5,plain,
% 4.01/0.99      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f88]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1310,plain,
% 4.01/0.99      ( r1_tarski(X0,k1_relat_1(sK1))
% 4.01/0.99      | k6_subset_1(X0,k1_relat_1(sK1)) != k1_xboole_0 ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_2009,plain,
% 4.01/0.99      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
% 4.01/0.99      | k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1)) != k1_xboole_0 ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_1310]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_20,plain,
% 4.01/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 4.01/0.99      | ~ v1_funct_1(X0)
% 4.01/0.99      | ~ v1_relat_1(X0) ),
% 4.01/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1193,plain,
% 4.01/0.99      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)
% 4.01/0.99      | ~ v1_funct_1(sK1)
% 4.01/0.99      | ~ v1_relat_1(sK1) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1896,plain,
% 4.01/0.99      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
% 4.01/0.99      | ~ v1_funct_1(sK1)
% 4.01/0.99      | ~ v1_relat_1(sK1) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_1193]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_23,plain,
% 4.01/0.99      ( r1_tarski(X0,X1)
% 4.01/0.99      | ~ r1_tarski(X0,k1_relat_1(X2))
% 4.01/0.99      | ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 4.01/0.99      | ~ v1_funct_1(X2)
% 4.01/0.99      | ~ v2_funct_1(X2)
% 4.01/0.99      | ~ v1_relat_1(X2) ),
% 4.01/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1425,plain,
% 4.01/0.99      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(X0))
% 4.01/0.99      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 4.01/0.99      | ~ r1_tarski(k9_relat_1(X0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(X0,sK0))
% 4.01/0.99      | ~ v1_funct_1(X0)
% 4.01/0.99      | ~ v2_funct_1(X0)
% 4.01/0.99      | ~ v1_relat_1(X0) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1874,plain,
% 4.01/0.99      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),k1_relat_1(sK1))
% 4.01/0.99      | r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 4.01/0.99      | ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,k9_relat_1(sK1,sK0))),k9_relat_1(sK1,sK0))
% 4.01/0.99      | ~ v1_funct_1(sK1)
% 4.01/0.99      | ~ v2_funct_1(sK1)
% 4.01/0.99      | ~ v1_relat_1(sK1) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_1425]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_21,plain,
% 4.01/0.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 4.01/0.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 4.01/0.99      | ~ v1_relat_1(X1) ),
% 4.01/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1213,plain,
% 4.01/0.99      ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
% 4.01/0.99      | ~ r1_tarski(X0,k1_relat_1(sK1))
% 4.01/0.99      | ~ v1_relat_1(sK1) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1354,plain,
% 4.01/0.99      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 4.01/0.99      | ~ r1_tarski(sK0,k1_relat_1(sK1))
% 4.01/0.99      | ~ v1_relat_1(sK1) ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_1213]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1,plain,
% 4.01/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.01/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_1190,plain,
% 4.01/0.99      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
% 4.01/0.99      | ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 4.01/0.99      | k10_relat_1(sK1,k9_relat_1(sK1,sK0)) = sK0 ),
% 4.01/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(c_24,negated_conjecture,
% 4.01/0.99      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != sK0 ),
% 4.01/0.99      inference(cnf_transformation,[],[f84]) ).
% 4.01/0.99  
% 4.01/0.99  cnf(contradiction,plain,
% 4.01/0.99      ( $false ),
% 4.01/0.99      inference(minisat,
% 4.01/0.99                [status(thm)],
% 4.01/0.99                [c_11742,c_2009,c_1896,c_1874,c_1354,c_1190,c_24,c_25,
% 4.01/0.99                 c_26,c_27,c_28]) ).
% 4.01/0.99  
% 4.01/0.99  
% 4.01/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.01/0.99  
% 4.01/0.99  ------                               Statistics
% 4.01/0.99  
% 4.01/0.99  ------ Selected
% 4.01/0.99  
% 4.01/0.99  total_time:                             0.386
% 4.01/0.99  
%------------------------------------------------------------------------------
