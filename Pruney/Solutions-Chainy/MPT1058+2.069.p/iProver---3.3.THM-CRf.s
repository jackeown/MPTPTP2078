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
% DateTime   : Thu Dec  3 12:09:22 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 653 expanded)
%              Number of clauses        :   66 ( 200 expanded)
%              Number of leaves         :   24 ( 170 expanded)
%              Depth                    :   20
%              Number of atoms          :  253 ( 979 expanded)
%              Number of equality atoms :  153 ( 647 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43])).

fof(f76,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f22,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f21,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f81])).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f82])).

fof(f86,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f71,f83])).

fof(f74,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f77,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_546,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_561,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1963,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_561])).

cnf(c_15,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_39,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2563,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1963,c_39])).

cnf(c_2564,plain,
    ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2563])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_554,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2574,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2564,c_554])).

cnf(c_9169,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_39])).

cnf(c_9170,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9169])).

cnf(c_9177,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_546,c_9170])).

cnf(c_550,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_556,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1638,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_550,c_556])).

cnf(c_9282,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k2_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_9177,c_1638])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_555,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2439,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_550,c_555])).

cnf(c_19,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_547,plain,
    ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_548,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1273,plain,
    ( k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) = k10_relat_1(k6_relat_1(X0),X1)
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_547,c_548])).

cnf(c_20,plain,
    ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1277,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)
    | v1_funct_1(k6_relat_1(X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1273,c_20])).

cnf(c_14,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_42,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2613,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1277,c_39,c_42])).

cnf(c_7409,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2439,c_2613])).

cnf(c_7415,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_550,c_7409])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_552,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1548,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_550,c_552])).

cnf(c_7426,plain,
    ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_7415,c_1548])).

cnf(c_18,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_784,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_18,c_11])).

cnf(c_786,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_784,c_18])).

cnf(c_1254,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_786,c_12])).

cnf(c_3338,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_1548,c_1254])).

cnf(c_3660,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_3338,c_1638])).

cnf(c_7427,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_7426,c_12,c_3660])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_544,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_783,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_18,c_12])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_549,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1749,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X0,X1)),k6_relat_1(X2))) = k10_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_783,c_549])).

cnf(c_5016,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1749,c_1548,c_3660])).

cnf(c_5023,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_544,c_5016])).

cnf(c_7602,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(superposition,[status(thm)],[c_7427,c_5023])).

cnf(c_9285,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_9282,c_11,c_7602])).

cnf(c_9320,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_9285,c_7602])).

cnf(c_195,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_830,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_196,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_761,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
    | k10_relat_1(sK0,sK2) != X0
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_829,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_21,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9320,c_830,c_829,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:23:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.92/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/1.00  
% 3.92/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/1.00  
% 3.92/1.00  ------  iProver source info
% 3.92/1.00  
% 3.92/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.92/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/1.00  git: non_committed_changes: false
% 3.92/1.00  git: last_make_outside_of_git: false
% 3.92/1.00  
% 3.92/1.00  ------ 
% 3.92/1.00  
% 3.92/1.00  ------ Input Options
% 3.92/1.00  
% 3.92/1.00  --out_options                           all
% 3.92/1.00  --tptp_safe_out                         true
% 3.92/1.00  --problem_path                          ""
% 3.92/1.00  --include_path                          ""
% 3.92/1.00  --clausifier                            res/vclausify_rel
% 3.92/1.00  --clausifier_options                    --mode clausify
% 3.92/1.00  --stdin                                 false
% 3.92/1.00  --stats_out                             sel
% 3.92/1.00  
% 3.92/1.00  ------ General Options
% 3.92/1.00  
% 3.92/1.00  --fof                                   false
% 3.92/1.00  --time_out_real                         604.99
% 3.92/1.00  --time_out_virtual                      -1.
% 3.92/1.00  --symbol_type_check                     false
% 3.92/1.00  --clausify_out                          false
% 3.92/1.00  --sig_cnt_out                           false
% 3.92/1.01  --trig_cnt_out                          false
% 3.92/1.01  --trig_cnt_out_tolerance                1.
% 3.92/1.01  --trig_cnt_out_sk_spl                   false
% 3.92/1.01  --abstr_cl_out                          false
% 3.92/1.01  
% 3.92/1.01  ------ Global Options
% 3.92/1.01  
% 3.92/1.01  --schedule                              none
% 3.92/1.01  --add_important_lit                     false
% 3.92/1.01  --prop_solver_per_cl                    1000
% 3.92/1.01  --min_unsat_core                        false
% 3.92/1.01  --soft_assumptions                      false
% 3.92/1.01  --soft_lemma_size                       3
% 3.92/1.01  --prop_impl_unit_size                   0
% 3.92/1.01  --prop_impl_unit                        []
% 3.92/1.01  --share_sel_clauses                     true
% 3.92/1.01  --reset_solvers                         false
% 3.92/1.01  --bc_imp_inh                            [conj_cone]
% 3.92/1.01  --conj_cone_tolerance                   3.
% 3.92/1.01  --extra_neg_conj                        none
% 3.92/1.01  --large_theory_mode                     true
% 3.92/1.01  --prolific_symb_bound                   200
% 3.92/1.01  --lt_threshold                          2000
% 3.92/1.01  --clause_weak_htbl                      true
% 3.92/1.01  --gc_record_bc_elim                     false
% 3.92/1.01  
% 3.92/1.01  ------ Preprocessing Options
% 3.92/1.01  
% 3.92/1.01  --preprocessing_flag                    true
% 3.92/1.01  --time_out_prep_mult                    0.1
% 3.92/1.01  --splitting_mode                        input
% 3.92/1.01  --splitting_grd                         true
% 3.92/1.01  --splitting_cvd                         false
% 3.92/1.01  --splitting_cvd_svl                     false
% 3.92/1.01  --splitting_nvd                         32
% 3.92/1.01  --sub_typing                            true
% 3.92/1.01  --prep_gs_sim                           false
% 3.92/1.01  --prep_unflatten                        true
% 3.92/1.01  --prep_res_sim                          true
% 3.92/1.01  --prep_upred                            true
% 3.92/1.01  --prep_sem_filter                       exhaustive
% 3.92/1.01  --prep_sem_filter_out                   false
% 3.92/1.01  --pred_elim                             false
% 3.92/1.01  --res_sim_input                         true
% 3.92/1.01  --eq_ax_congr_red                       true
% 3.92/1.01  --pure_diseq_elim                       true
% 3.92/1.01  --brand_transform                       false
% 3.92/1.01  --non_eq_to_eq                          false
% 3.92/1.01  --prep_def_merge                        true
% 3.92/1.01  --prep_def_merge_prop_impl              false
% 3.92/1.01  --prep_def_merge_mbd                    true
% 3.92/1.01  --prep_def_merge_tr_red                 false
% 3.92/1.01  --prep_def_merge_tr_cl                  false
% 3.92/1.01  --smt_preprocessing                     true
% 3.92/1.01  --smt_ac_axioms                         fast
% 3.92/1.01  --preprocessed_out                      false
% 3.92/1.01  --preprocessed_stats                    false
% 3.92/1.01  
% 3.92/1.01  ------ Abstraction refinement Options
% 3.92/1.01  
% 3.92/1.01  --abstr_ref                             []
% 3.92/1.01  --abstr_ref_prep                        false
% 3.92/1.01  --abstr_ref_until_sat                   false
% 3.92/1.01  --abstr_ref_sig_restrict                funpre
% 3.92/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.92/1.01  --abstr_ref_under                       []
% 3.92/1.01  
% 3.92/1.01  ------ SAT Options
% 3.92/1.01  
% 3.92/1.01  --sat_mode                              false
% 3.92/1.01  --sat_fm_restart_options                ""
% 3.92/1.01  --sat_gr_def                            false
% 3.92/1.01  --sat_epr_types                         true
% 3.92/1.01  --sat_non_cyclic_types                  false
% 3.92/1.01  --sat_finite_models                     false
% 3.92/1.01  --sat_fm_lemmas                         false
% 3.92/1.01  --sat_fm_prep                           false
% 3.92/1.01  --sat_fm_uc_incr                        true
% 3.92/1.01  --sat_out_model                         small
% 3.92/1.01  --sat_out_clauses                       false
% 3.92/1.01  
% 3.92/1.01  ------ QBF Options
% 3.92/1.01  
% 3.92/1.01  --qbf_mode                              false
% 3.92/1.01  --qbf_elim_univ                         false
% 3.92/1.01  --qbf_dom_inst                          none
% 3.92/1.01  --qbf_dom_pre_inst                      false
% 3.92/1.01  --qbf_sk_in                             false
% 3.92/1.01  --qbf_pred_elim                         true
% 3.92/1.01  --qbf_split                             512
% 3.92/1.01  
% 3.92/1.01  ------ BMC1 Options
% 3.92/1.01  
% 3.92/1.01  --bmc1_incremental                      false
% 3.92/1.01  --bmc1_axioms                           reachable_all
% 3.92/1.01  --bmc1_min_bound                        0
% 3.92/1.01  --bmc1_max_bound                        -1
% 3.92/1.01  --bmc1_max_bound_default                -1
% 3.92/1.01  --bmc1_symbol_reachability              true
% 3.92/1.01  --bmc1_property_lemmas                  false
% 3.92/1.01  --bmc1_k_induction                      false
% 3.92/1.01  --bmc1_non_equiv_states                 false
% 3.92/1.01  --bmc1_deadlock                         false
% 3.92/1.01  --bmc1_ucm                              false
% 3.92/1.01  --bmc1_add_unsat_core                   none
% 3.92/1.01  --bmc1_unsat_core_children              false
% 3.92/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.92/1.01  --bmc1_out_stat                         full
% 3.92/1.01  --bmc1_ground_init                      false
% 3.92/1.01  --bmc1_pre_inst_next_state              false
% 3.92/1.01  --bmc1_pre_inst_state                   false
% 3.92/1.01  --bmc1_pre_inst_reach_state             false
% 3.92/1.01  --bmc1_out_unsat_core                   false
% 3.92/1.01  --bmc1_aig_witness_out                  false
% 3.92/1.01  --bmc1_verbose                          false
% 3.92/1.01  --bmc1_dump_clauses_tptp                false
% 3.92/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.92/1.01  --bmc1_dump_file                        -
% 3.92/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.92/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.92/1.01  --bmc1_ucm_extend_mode                  1
% 3.92/1.01  --bmc1_ucm_init_mode                    2
% 3.92/1.01  --bmc1_ucm_cone_mode                    none
% 3.92/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.92/1.01  --bmc1_ucm_relax_model                  4
% 3.92/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.92/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.92/1.01  --bmc1_ucm_layered_model                none
% 3.92/1.01  --bmc1_ucm_max_lemma_size               10
% 3.92/1.01  
% 3.92/1.01  ------ AIG Options
% 3.92/1.01  
% 3.92/1.01  --aig_mode                              false
% 3.92/1.01  
% 3.92/1.01  ------ Instantiation Options
% 3.92/1.01  
% 3.92/1.01  --instantiation_flag                    true
% 3.92/1.01  --inst_sos_flag                         false
% 3.92/1.01  --inst_sos_phase                        true
% 3.92/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.92/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.92/1.01  --inst_lit_sel_side                     num_symb
% 3.92/1.01  --inst_solver_per_active                1400
% 3.92/1.01  --inst_solver_calls_frac                1.
% 3.92/1.01  --inst_passive_queue_type               priority_queues
% 3.92/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.92/1.01  --inst_passive_queues_freq              [25;2]
% 3.92/1.01  --inst_dismatching                      true
% 3.92/1.01  --inst_eager_unprocessed_to_passive     true
% 3.92/1.01  --inst_prop_sim_given                   true
% 3.92/1.01  --inst_prop_sim_new                     false
% 3.92/1.01  --inst_subs_new                         false
% 3.92/1.01  --inst_eq_res_simp                      false
% 3.92/1.01  --inst_subs_given                       false
% 3.92/1.01  --inst_orphan_elimination               true
% 3.92/1.01  --inst_learning_loop_flag               true
% 3.92/1.01  --inst_learning_start                   3000
% 3.92/1.01  --inst_learning_factor                  2
% 3.92/1.01  --inst_start_prop_sim_after_learn       3
% 3.92/1.01  --inst_sel_renew                        solver
% 3.92/1.01  --inst_lit_activity_flag                true
% 3.92/1.01  --inst_restr_to_given                   false
% 3.92/1.01  --inst_activity_threshold               500
% 3.92/1.01  --inst_out_proof                        true
% 3.92/1.01  
% 3.92/1.01  ------ Resolution Options
% 3.92/1.01  
% 3.92/1.01  --resolution_flag                       true
% 3.92/1.01  --res_lit_sel                           adaptive
% 3.92/1.01  --res_lit_sel_side                      none
% 3.92/1.01  --res_ordering                          kbo
% 3.92/1.01  --res_to_prop_solver                    active
% 3.92/1.01  --res_prop_simpl_new                    false
% 3.92/1.01  --res_prop_simpl_given                  true
% 3.92/1.01  --res_passive_queue_type                priority_queues
% 3.92/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.92/1.01  --res_passive_queues_freq               [15;5]
% 3.92/1.01  --res_forward_subs                      full
% 3.92/1.01  --res_backward_subs                     full
% 3.92/1.01  --res_forward_subs_resolution           true
% 3.92/1.01  --res_backward_subs_resolution          true
% 3.92/1.01  --res_orphan_elimination                true
% 3.92/1.01  --res_time_limit                        2.
% 3.92/1.01  --res_out_proof                         true
% 3.92/1.01  
% 3.92/1.01  ------ Superposition Options
% 3.92/1.01  
% 3.92/1.01  --superposition_flag                    true
% 3.92/1.01  --sup_passive_queue_type                priority_queues
% 3.92/1.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.92/1.01  --sup_passive_queues_freq               [1;4]
% 3.92/1.01  --demod_completeness_check              fast
% 3.92/1.01  --demod_use_ground                      true
% 3.92/1.01  --sup_to_prop_solver                    passive
% 3.92/1.01  --sup_prop_simpl_new                    true
% 3.92/1.01  --sup_prop_simpl_given                  true
% 3.92/1.01  --sup_fun_splitting                     false
% 3.92/1.01  --sup_smt_interval                      50000
% 3.92/1.01  
% 3.92/1.01  ------ Superposition Simplification Setup
% 3.92/1.01  
% 3.92/1.01  --sup_indices_passive                   []
% 3.92/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.92/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.01  --sup_full_bw                           [BwDemod]
% 3.92/1.01  --sup_immed_triv                        [TrivRules]
% 3.92/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.01  --sup_immed_bw_main                     []
% 3.92/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.92/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.92/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.92/1.01  
% 3.92/1.01  ------ Combination Options
% 3.92/1.01  
% 3.92/1.01  --comb_res_mult                         3
% 3.92/1.01  --comb_sup_mult                         2
% 3.92/1.01  --comb_inst_mult                        10
% 3.92/1.01  
% 3.92/1.01  ------ Debug Options
% 3.92/1.01  
% 3.92/1.01  --dbg_backtrace                         false
% 3.92/1.01  --dbg_dump_prop_clauses                 false
% 3.92/1.01  --dbg_dump_prop_clauses_file            -
% 3.92/1.01  --dbg_out_stat                          false
% 3.92/1.01  ------ Parsing...
% 3.92/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/1.01  
% 3.92/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.92/1.01  
% 3.92/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/1.01  
% 3.92/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/1.01  ------ Proving...
% 3.92/1.01  ------ Problem Properties 
% 3.92/1.01  
% 3.92/1.01  
% 3.92/1.01  clauses                                 25
% 3.92/1.01  conjectures                             4
% 3.92/1.01  EPR                                     3
% 3.92/1.01  Horn                                    25
% 3.92/1.01  unary                                   13
% 3.92/1.01  binary                                  3
% 3.92/1.01  lits                                    48
% 3.92/1.01  lits eq                                 12
% 3.92/1.01  fd_pure                                 0
% 3.92/1.01  fd_pseudo                               0
% 3.92/1.01  fd_cond                                 0
% 3.92/1.01  fd_pseudo_cond                          0
% 3.92/1.01  AC symbols                              0
% 3.92/1.01  
% 3.92/1.01  ------ Input Options Time Limit: Unbounded
% 3.92/1.01  
% 3.92/1.01  
% 3.92/1.01  ------ 
% 3.92/1.01  Current options:
% 3.92/1.01  ------ 
% 3.92/1.01  
% 3.92/1.01  ------ Input Options
% 3.92/1.01  
% 3.92/1.01  --out_options                           all
% 3.92/1.01  --tptp_safe_out                         true
% 3.92/1.01  --problem_path                          ""
% 3.92/1.01  --include_path                          ""
% 3.92/1.01  --clausifier                            res/vclausify_rel
% 3.92/1.01  --clausifier_options                    --mode clausify
% 3.92/1.01  --stdin                                 false
% 3.92/1.01  --stats_out                             sel
% 3.92/1.01  
% 3.92/1.01  ------ General Options
% 3.92/1.01  
% 3.92/1.01  --fof                                   false
% 3.92/1.01  --time_out_real                         604.99
% 3.92/1.01  --time_out_virtual                      -1.
% 3.92/1.01  --symbol_type_check                     false
% 3.92/1.01  --clausify_out                          false
% 3.92/1.01  --sig_cnt_out                           false
% 3.92/1.01  --trig_cnt_out                          false
% 3.92/1.01  --trig_cnt_out_tolerance                1.
% 3.92/1.01  --trig_cnt_out_sk_spl                   false
% 3.92/1.01  --abstr_cl_out                          false
% 3.92/1.01  
% 3.92/1.01  ------ Global Options
% 3.92/1.01  
% 3.92/1.01  --schedule                              none
% 3.92/1.01  --add_important_lit                     false
% 3.92/1.01  --prop_solver_per_cl                    1000
% 3.92/1.01  --min_unsat_core                        false
% 3.92/1.01  --soft_assumptions                      false
% 3.92/1.01  --soft_lemma_size                       3
% 3.92/1.01  --prop_impl_unit_size                   0
% 3.92/1.01  --prop_impl_unit                        []
% 3.92/1.01  --share_sel_clauses                     true
% 3.92/1.01  --reset_solvers                         false
% 3.92/1.01  --bc_imp_inh                            [conj_cone]
% 3.92/1.01  --conj_cone_tolerance                   3.
% 3.92/1.01  --extra_neg_conj                        none
% 3.92/1.01  --large_theory_mode                     true
% 3.92/1.01  --prolific_symb_bound                   200
% 3.92/1.01  --lt_threshold                          2000
% 3.92/1.01  --clause_weak_htbl                      true
% 3.92/1.01  --gc_record_bc_elim                     false
% 3.92/1.01  
% 3.92/1.01  ------ Preprocessing Options
% 3.92/1.01  
% 3.92/1.01  --preprocessing_flag                    true
% 3.92/1.01  --time_out_prep_mult                    0.1
% 3.92/1.01  --splitting_mode                        input
% 3.92/1.01  --splitting_grd                         true
% 3.92/1.01  --splitting_cvd                         false
% 3.92/1.01  --splitting_cvd_svl                     false
% 3.92/1.01  --splitting_nvd                         32
% 3.92/1.01  --sub_typing                            true
% 3.92/1.01  --prep_gs_sim                           false
% 3.92/1.01  --prep_unflatten                        true
% 3.92/1.01  --prep_res_sim                          true
% 3.92/1.01  --prep_upred                            true
% 3.92/1.01  --prep_sem_filter                       exhaustive
% 3.92/1.01  --prep_sem_filter_out                   false
% 3.92/1.01  --pred_elim                             false
% 3.92/1.01  --res_sim_input                         true
% 3.92/1.01  --eq_ax_congr_red                       true
% 3.92/1.01  --pure_diseq_elim                       true
% 3.92/1.01  --brand_transform                       false
% 3.92/1.01  --non_eq_to_eq                          false
% 3.92/1.01  --prep_def_merge                        true
% 3.92/1.01  --prep_def_merge_prop_impl              false
% 3.92/1.01  --prep_def_merge_mbd                    true
% 3.92/1.01  --prep_def_merge_tr_red                 false
% 3.92/1.01  --prep_def_merge_tr_cl                  false
% 3.92/1.01  --smt_preprocessing                     true
% 3.92/1.01  --smt_ac_axioms                         fast
% 3.92/1.01  --preprocessed_out                      false
% 3.92/1.01  --preprocessed_stats                    false
% 3.92/1.01  
% 3.92/1.01  ------ Abstraction refinement Options
% 3.92/1.01  
% 3.92/1.01  --abstr_ref                             []
% 3.92/1.01  --abstr_ref_prep                        false
% 3.92/1.01  --abstr_ref_until_sat                   false
% 3.92/1.01  --abstr_ref_sig_restrict                funpre
% 3.92/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.92/1.01  --abstr_ref_under                       []
% 3.92/1.01  
% 3.92/1.01  ------ SAT Options
% 3.92/1.01  
% 3.92/1.01  --sat_mode                              false
% 3.92/1.01  --sat_fm_restart_options                ""
% 3.92/1.01  --sat_gr_def                            false
% 3.92/1.01  --sat_epr_types                         true
% 3.92/1.01  --sat_non_cyclic_types                  false
% 3.92/1.01  --sat_finite_models                     false
% 3.92/1.01  --sat_fm_lemmas                         false
% 3.92/1.01  --sat_fm_prep                           false
% 3.92/1.01  --sat_fm_uc_incr                        true
% 3.92/1.01  --sat_out_model                         small
% 3.92/1.01  --sat_out_clauses                       false
% 3.92/1.01  
% 3.92/1.01  ------ QBF Options
% 3.92/1.01  
% 3.92/1.01  --qbf_mode                              false
% 3.92/1.01  --qbf_elim_univ                         false
% 3.92/1.01  --qbf_dom_inst                          none
% 3.92/1.01  --qbf_dom_pre_inst                      false
% 3.92/1.01  --qbf_sk_in                             false
% 3.92/1.01  --qbf_pred_elim                         true
% 3.92/1.01  --qbf_split                             512
% 3.92/1.01  
% 3.92/1.01  ------ BMC1 Options
% 3.92/1.01  
% 3.92/1.01  --bmc1_incremental                      false
% 3.92/1.01  --bmc1_axioms                           reachable_all
% 3.92/1.01  --bmc1_min_bound                        0
% 3.92/1.01  --bmc1_max_bound                        -1
% 3.92/1.01  --bmc1_max_bound_default                -1
% 3.92/1.01  --bmc1_symbol_reachability              true
% 3.92/1.01  --bmc1_property_lemmas                  false
% 3.92/1.01  --bmc1_k_induction                      false
% 3.92/1.01  --bmc1_non_equiv_states                 false
% 3.92/1.01  --bmc1_deadlock                         false
% 3.92/1.01  --bmc1_ucm                              false
% 3.92/1.01  --bmc1_add_unsat_core                   none
% 3.92/1.01  --bmc1_unsat_core_children              false
% 3.92/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.92/1.01  --bmc1_out_stat                         full
% 3.92/1.01  --bmc1_ground_init                      false
% 3.92/1.01  --bmc1_pre_inst_next_state              false
% 3.92/1.01  --bmc1_pre_inst_state                   false
% 3.92/1.01  --bmc1_pre_inst_reach_state             false
% 3.92/1.01  --bmc1_out_unsat_core                   false
% 3.92/1.01  --bmc1_aig_witness_out                  false
% 3.92/1.01  --bmc1_verbose                          false
% 3.92/1.01  --bmc1_dump_clauses_tptp                false
% 3.92/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.92/1.01  --bmc1_dump_file                        -
% 3.92/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.92/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.92/1.01  --bmc1_ucm_extend_mode                  1
% 3.92/1.01  --bmc1_ucm_init_mode                    2
% 3.92/1.01  --bmc1_ucm_cone_mode                    none
% 3.92/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.92/1.01  --bmc1_ucm_relax_model                  4
% 3.92/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.92/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.92/1.01  --bmc1_ucm_layered_model                none
% 3.92/1.01  --bmc1_ucm_max_lemma_size               10
% 3.92/1.01  
% 3.92/1.01  ------ AIG Options
% 3.92/1.01  
% 3.92/1.01  --aig_mode                              false
% 3.92/1.01  
% 3.92/1.01  ------ Instantiation Options
% 3.92/1.01  
% 3.92/1.01  --instantiation_flag                    true
% 3.92/1.01  --inst_sos_flag                         false
% 3.92/1.01  --inst_sos_phase                        true
% 3.92/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.92/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.92/1.01  --inst_lit_sel_side                     num_symb
% 3.92/1.01  --inst_solver_per_active                1400
% 3.92/1.01  --inst_solver_calls_frac                1.
% 3.92/1.01  --inst_passive_queue_type               priority_queues
% 3.92/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.92/1.01  --inst_passive_queues_freq              [25;2]
% 3.92/1.01  --inst_dismatching                      true
% 3.92/1.01  --inst_eager_unprocessed_to_passive     true
% 3.92/1.01  --inst_prop_sim_given                   true
% 3.92/1.01  --inst_prop_sim_new                     false
% 3.92/1.01  --inst_subs_new                         false
% 3.92/1.01  --inst_eq_res_simp                      false
% 3.92/1.01  --inst_subs_given                       false
% 3.92/1.01  --inst_orphan_elimination               true
% 3.92/1.01  --inst_learning_loop_flag               true
% 3.92/1.01  --inst_learning_start                   3000
% 3.92/1.01  --inst_learning_factor                  2
% 3.92/1.01  --inst_start_prop_sim_after_learn       3
% 3.92/1.01  --inst_sel_renew                        solver
% 3.92/1.01  --inst_lit_activity_flag                true
% 3.92/1.01  --inst_restr_to_given                   false
% 3.92/1.01  --inst_activity_threshold               500
% 3.92/1.01  --inst_out_proof                        true
% 3.92/1.01  
% 3.92/1.01  ------ Resolution Options
% 3.92/1.01  
% 3.92/1.01  --resolution_flag                       true
% 3.92/1.01  --res_lit_sel                           adaptive
% 3.92/1.01  --res_lit_sel_side                      none
% 3.92/1.01  --res_ordering                          kbo
% 3.92/1.01  --res_to_prop_solver                    active
% 3.92/1.01  --res_prop_simpl_new                    false
% 3.92/1.01  --res_prop_simpl_given                  true
% 3.92/1.01  --res_passive_queue_type                priority_queues
% 3.92/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.92/1.01  --res_passive_queues_freq               [15;5]
% 3.92/1.01  --res_forward_subs                      full
% 3.92/1.01  --res_backward_subs                     full
% 3.92/1.01  --res_forward_subs_resolution           true
% 3.92/1.01  --res_backward_subs_resolution          true
% 3.92/1.01  --res_orphan_elimination                true
% 3.92/1.01  --res_time_limit                        2.
% 3.92/1.01  --res_out_proof                         true
% 3.92/1.01  
% 3.92/1.01  ------ Superposition Options
% 3.92/1.01  
% 3.92/1.01  --superposition_flag                    true
% 3.92/1.01  --sup_passive_queue_type                priority_queues
% 3.92/1.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.92/1.01  --sup_passive_queues_freq               [1;4]
% 3.92/1.01  --demod_completeness_check              fast
% 3.92/1.01  --demod_use_ground                      true
% 3.92/1.01  --sup_to_prop_solver                    passive
% 3.92/1.01  --sup_prop_simpl_new                    true
% 3.92/1.01  --sup_prop_simpl_given                  true
% 3.92/1.01  --sup_fun_splitting                     false
% 3.92/1.01  --sup_smt_interval                      50000
% 3.92/1.01  
% 3.92/1.01  ------ Superposition Simplification Setup
% 3.92/1.01  
% 3.92/1.01  --sup_indices_passive                   []
% 3.92/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.92/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.92/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.01  --sup_full_bw                           [BwDemod]
% 3.92/1.01  --sup_immed_triv                        [TrivRules]
% 3.92/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.92/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.01  --sup_immed_bw_main                     []
% 3.92/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.92/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.92/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.92/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.92/1.01  
% 3.92/1.01  ------ Combination Options
% 3.92/1.01  
% 3.92/1.01  --comb_res_mult                         3
% 3.92/1.01  --comb_sup_mult                         2
% 3.92/1.01  --comb_inst_mult                        10
% 3.92/1.01  
% 3.92/1.01  ------ Debug Options
% 3.92/1.01  
% 3.92/1.01  --dbg_backtrace                         false
% 3.92/1.01  --dbg_dump_prop_clauses                 false
% 3.92/1.01  --dbg_dump_prop_clauses_file            -
% 3.92/1.01  --dbg_out_stat                          false
% 3.92/1.01  
% 3.92/1.01  
% 3.92/1.01  
% 3.92/1.01  
% 3.92/1.01  ------ Proving...
% 3.92/1.01  
% 3.92/1.01  
% 3.92/1.01  % SZS status Theorem for theBenchmark.p
% 3.92/1.01  
% 3.92/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/1.01  
% 3.92/1.01  fof(f24,conjecture,(
% 3.92/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f25,negated_conjecture,(
% 3.92/1.01    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.92/1.01    inference(negated_conjecture,[],[f24])).
% 3.92/1.01  
% 3.92/1.01  fof(f40,plain,(
% 3.92/1.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.92/1.01    inference(ennf_transformation,[],[f25])).
% 3.92/1.01  
% 3.92/1.01  fof(f41,plain,(
% 3.92/1.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.92/1.01    inference(flattening,[],[f40])).
% 3.92/1.01  
% 3.92/1.01  fof(f44,plain,(
% 3.92/1.01    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 3.92/1.01    introduced(choice_axiom,[])).
% 3.92/1.01  
% 3.92/1.01  fof(f43,plain,(
% 3.92/1.01    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.92/1.01    introduced(choice_axiom,[])).
% 3.92/1.01  
% 3.92/1.01  fof(f45,plain,(
% 3.92/1.01    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.92/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43])).
% 3.92/1.01  
% 3.92/1.01  fof(f76,plain,(
% 3.92/1.01    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 3.92/1.01    inference(cnf_transformation,[],[f45])).
% 3.92/1.01  
% 3.92/1.01  fof(f16,axiom,(
% 3.92/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f64,plain,(
% 3.92/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.92/1.01    inference(cnf_transformation,[],[f16])).
% 3.92/1.01  
% 3.92/1.01  fof(f10,axiom,(
% 3.92/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f27,plain,(
% 3.92/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.92/1.01    inference(ennf_transformation,[],[f10])).
% 3.92/1.01  
% 3.92/1.01  fof(f42,plain,(
% 3.92/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.92/1.01    inference(nnf_transformation,[],[f27])).
% 3.92/1.01  
% 3.92/1.01  fof(f56,plain,(
% 3.92/1.01    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f42])).
% 3.92/1.01  
% 3.92/1.01  fof(f18,axiom,(
% 3.92/1.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f67,plain,(
% 3.92/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.92/1.01    inference(cnf_transformation,[],[f18])).
% 3.92/1.01  
% 3.92/1.01  fof(f14,axiom,(
% 3.92/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f32,plain,(
% 3.92/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.92/1.01    inference(ennf_transformation,[],[f14])).
% 3.92/1.01  
% 3.92/1.01  fof(f33,plain,(
% 3.92/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.92/1.01    inference(flattening,[],[f32])).
% 3.92/1.01  
% 3.92/1.01  fof(f62,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f33])).
% 3.92/1.01  
% 3.92/1.01  fof(f12,axiom,(
% 3.92/1.01    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f30,plain,(
% 3.92/1.01    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.92/1.01    inference(ennf_transformation,[],[f12])).
% 3.92/1.01  
% 3.92/1.01  fof(f60,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f30])).
% 3.92/1.01  
% 3.92/1.01  fof(f65,plain,(
% 3.92/1.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.92/1.01    inference(cnf_transformation,[],[f16])).
% 3.92/1.01  
% 3.92/1.01  fof(f13,axiom,(
% 3.92/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f31,plain,(
% 3.92/1.01    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.92/1.01    inference(ennf_transformation,[],[f13])).
% 3.92/1.01  
% 3.92/1.01  fof(f61,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f31])).
% 3.92/1.01  
% 3.92/1.01  fof(f22,axiom,(
% 3.92/1.01    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f72,plain,(
% 3.92/1.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.92/1.01    inference(cnf_transformation,[],[f22])).
% 3.92/1.01  
% 3.92/1.01  fof(f20,axiom,(
% 3.92/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f38,plain,(
% 3.92/1.01    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.92/1.01    inference(ennf_transformation,[],[f20])).
% 3.92/1.01  
% 3.92/1.01  fof(f39,plain,(
% 3.92/1.01    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.92/1.01    inference(flattening,[],[f38])).
% 3.92/1.01  
% 3.92/1.01  fof(f70,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f39])).
% 3.92/1.01  
% 3.92/1.01  fof(f23,axiom,(
% 3.92/1.01    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f73,plain,(
% 3.92/1.01    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 3.92/1.01    inference(cnf_transformation,[],[f23])).
% 3.92/1.01  
% 3.92/1.01  fof(f68,plain,(
% 3.92/1.01    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.92/1.01    inference(cnf_transformation,[],[f18])).
% 3.92/1.01  
% 3.92/1.01  fof(f17,axiom,(
% 3.92/1.01    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f36,plain,(
% 3.92/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.92/1.01    inference(ennf_transformation,[],[f17])).
% 3.92/1.01  
% 3.92/1.01  fof(f66,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f36])).
% 3.92/1.01  
% 3.92/1.01  fof(f21,axiom,(
% 3.92/1.01    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f71,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 3.92/1.01    inference(cnf_transformation,[],[f21])).
% 3.92/1.01  
% 3.92/1.01  fof(f9,axiom,(
% 3.92/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f54,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.92/1.01    inference(cnf_transformation,[],[f9])).
% 3.92/1.01  
% 3.92/1.01  fof(f2,axiom,(
% 3.92/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f47,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f2])).
% 3.92/1.01  
% 3.92/1.01  fof(f3,axiom,(
% 3.92/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f48,plain,(
% 3.92/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f3])).
% 3.92/1.01  
% 3.92/1.01  fof(f4,axiom,(
% 3.92/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f49,plain,(
% 3.92/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f4])).
% 3.92/1.01  
% 3.92/1.01  fof(f5,axiom,(
% 3.92/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f50,plain,(
% 3.92/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f5])).
% 3.92/1.01  
% 3.92/1.01  fof(f6,axiom,(
% 3.92/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f51,plain,(
% 3.92/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f6])).
% 3.92/1.01  
% 3.92/1.01  fof(f7,axiom,(
% 3.92/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f52,plain,(
% 3.92/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f7])).
% 3.92/1.01  
% 3.92/1.01  fof(f78,plain,(
% 3.92/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.92/1.01    inference(definition_unfolding,[],[f51,f52])).
% 3.92/1.01  
% 3.92/1.01  fof(f79,plain,(
% 3.92/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.92/1.01    inference(definition_unfolding,[],[f50,f78])).
% 3.92/1.01  
% 3.92/1.01  fof(f80,plain,(
% 3.92/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.92/1.01    inference(definition_unfolding,[],[f49,f79])).
% 3.92/1.01  
% 3.92/1.01  fof(f81,plain,(
% 3.92/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.92/1.01    inference(definition_unfolding,[],[f48,f80])).
% 3.92/1.01  
% 3.92/1.01  fof(f82,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.92/1.01    inference(definition_unfolding,[],[f47,f81])).
% 3.92/1.01  
% 3.92/1.01  fof(f83,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.92/1.01    inference(definition_unfolding,[],[f54,f82])).
% 3.92/1.01  
% 3.92/1.01  fof(f86,plain,(
% 3.92/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.92/1.01    inference(definition_unfolding,[],[f71,f83])).
% 3.92/1.01  
% 3.92/1.01  fof(f74,plain,(
% 3.92/1.01    v1_relat_1(sK0)),
% 3.92/1.01    inference(cnf_transformation,[],[f45])).
% 3.92/1.01  
% 3.92/1.01  fof(f19,axiom,(
% 3.92/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.92/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.01  
% 3.92/1.01  fof(f37,plain,(
% 3.92/1.01    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.92/1.01    inference(ennf_transformation,[],[f19])).
% 3.92/1.01  
% 3.92/1.01  fof(f69,plain,(
% 3.92/1.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.92/1.01    inference(cnf_transformation,[],[f37])).
% 3.92/1.01  
% 3.92/1.01  fof(f85,plain,(
% 3.92/1.01    ( ! [X2,X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.92/1.01    inference(definition_unfolding,[],[f69,f83])).
% 3.92/1.01  
% 3.92/1.01  fof(f77,plain,(
% 3.92/1.01    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 3.92/1.01    inference(cnf_transformation,[],[f45])).
% 3.92/1.01  
% 3.92/1.01  cnf(c_22,negated_conjecture,
% 3.92/1.01      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 3.92/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_546,plain,
% 3.92/1.01      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_12,plain,
% 3.92/1.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.92/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_2,plain,
% 3.92/1.01      ( v4_relat_1(X0,X1)
% 3.92/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.92/1.01      | ~ v1_relat_1(X0) ),
% 3.92/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_561,plain,
% 3.92/1.01      ( v4_relat_1(X0,X1) = iProver_top
% 3.92/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.92/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_1963,plain,
% 3.92/1.01      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 3.92/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.92/1.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_12,c_561]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_15,plain,
% 3.92/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.92/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_39,plain,
% 3.92/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_2563,plain,
% 3.92/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.92/1.01      | v4_relat_1(k6_relat_1(X0),X1) = iProver_top ),
% 3.92/1.01      inference(global_propositional_subsumption,
% 3.92/1.01                [status(thm)],
% 3.92/1.01                [c_1963,c_39]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_2564,plain,
% 3.92/1.01      ( v4_relat_1(k6_relat_1(X0),X1) = iProver_top
% 3.92/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.92/1.01      inference(renaming,[status(thm)],[c_2563]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_9,plain,
% 3.92/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.92/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_554,plain,
% 3.92/1.01      ( k7_relat_1(X0,X1) = X0
% 3.92/1.01      | v4_relat_1(X0,X1) != iProver_top
% 3.92/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_2574,plain,
% 3.92/1.01      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.92/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.92/1.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_2564,c_554]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_9169,plain,
% 3.92/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.92/1.01      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 3.92/1.01      inference(global_propositional_subsumption,
% 3.92/1.01                [status(thm)],
% 3.92/1.01                [c_2574,c_39]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_9170,plain,
% 3.92/1.01      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.92/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.92/1.01      inference(renaming,[status(thm)],[c_9169]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_9177,plain,
% 3.92/1.01      ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_546,c_9170]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_550,plain,
% 3.92/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_7,plain,
% 3.92/1.01      ( ~ v1_relat_1(X0)
% 3.92/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.92/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_556,plain,
% 3.92/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.92/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_1638,plain,
% 3.92/1.01      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_550,c_556]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_9282,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k2_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_9177,c_1638]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_11,plain,
% 3.92/1.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.92/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_8,plain,
% 3.92/1.01      ( ~ v1_relat_1(X0)
% 3.92/1.01      | ~ v1_relat_1(X1)
% 3.92/1.01      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 3.92/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_555,plain,
% 3.92/1.01      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.92/1.01      | v1_relat_1(X1) != iProver_top
% 3.92/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_2439,plain,
% 3.92/1.01      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 3.92/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_550,c_555]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_19,plain,
% 3.92/1.01      ( v2_funct_1(k6_relat_1(X0)) ),
% 3.92/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_547,plain,
% 3.92/1.01      ( v2_funct_1(k6_relat_1(X0)) = iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_17,plain,
% 3.92/1.01      ( ~ v2_funct_1(X0)
% 3.92/1.01      | ~ v1_funct_1(X0)
% 3.92/1.01      | ~ v1_relat_1(X0)
% 3.92/1.01      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 3.92/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_548,plain,
% 3.92/1.01      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 3.92/1.01      | v2_funct_1(X0) != iProver_top
% 3.92/1.01      | v1_funct_1(X0) != iProver_top
% 3.92/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_1273,plain,
% 3.92/1.01      ( k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) = k10_relat_1(k6_relat_1(X0),X1)
% 3.92/1.01      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 3.92/1.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_547,c_548]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_20,plain,
% 3.92/1.01      ( k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.92/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_1277,plain,
% 3.92/1.01      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1)
% 3.92/1.01      | v1_funct_1(k6_relat_1(X0)) != iProver_top
% 3.92/1.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.92/1.01      inference(light_normalisation,[status(thm)],[c_1273,c_20]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_14,plain,
% 3.92/1.01      ( v1_funct_1(k6_relat_1(X0)) ),
% 3.92/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_42,plain,
% 3.92/1.01      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_2613,plain,
% 3.92/1.01      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.92/1.01      inference(global_propositional_subsumption,
% 3.92/1.01                [status(thm)],
% 3.92/1.01                [c_1277,c_39,c_42]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_7409,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X0),X1))
% 3.92/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.92/1.01      inference(demodulation,[status(thm)],[c_2439,c_2613]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_7415,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_550,c_7409]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_13,plain,
% 3.92/1.01      ( ~ v1_relat_1(X0)
% 3.92/1.01      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.92/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_552,plain,
% 3.92/1.01      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.92/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_1548,plain,
% 3.92/1.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_550,c_552]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_7426,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 3.92/1.01      inference(light_normalisation,[status(thm)],[c_7415,c_1548]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_18,plain,
% 3.92/1.01      ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 3.92/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_784,plain,
% 3.92/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_18,c_11]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_786,plain,
% 3.92/1.01      ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 3.92/1.01      inference(demodulation,[status(thm)],[c_784,c_18]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_1254,plain,
% 3.92/1.01      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_786,c_12]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_3338,plain,
% 3.92/1.01      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.92/1.01      inference(demodulation,[status(thm)],[c_1548,c_1254]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_3660,plain,
% 3.92/1.01      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.92/1.01      inference(light_normalisation,[status(thm)],[c_3338,c_1638]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_7427,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
% 3.92/1.01      inference(demodulation,[status(thm)],[c_7426,c_12,c_3660]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_24,negated_conjecture,
% 3.92/1.01      ( v1_relat_1(sK0) ),
% 3.92/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_544,plain,
% 3.92/1.01      ( v1_relat_1(sK0) = iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_783,plain,
% 3.92/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_18,c_12]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_16,plain,
% 3.92/1.01      ( ~ v1_relat_1(X0)
% 3.92/1.01      | k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.92/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_549,plain,
% 3.92/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 3.92/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.92/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_1749,plain,
% 3.92/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(k10_relat_1(X0,X1)),k6_relat_1(X2))) = k10_relat_1(k7_relat_1(X0,X2),X1)
% 3.92/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.92/1.01      inference(demodulation,[status(thm)],[c_783,c_549]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_5016,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 3.92/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.92/1.01      inference(demodulation,[status(thm)],[c_1749,c_1548,c_3660]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_5023,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_544,c_5016]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_7602,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_7427,c_5023]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_9285,plain,
% 3.92/1.01      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
% 3.92/1.01      inference(demodulation,[status(thm)],[c_9282,c_11,c_7602]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_9320,plain,
% 3.92/1.01      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 3.92/1.01      inference(superposition,[status(thm)],[c_9285,c_7602]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_195,plain,( X0 = X0 ),theory(equality) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_830,plain,
% 3.92/1.01      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 3.92/1.01      inference(instantiation,[status(thm)],[c_195]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_196,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_761,plain,
% 3.92/1.01      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
% 3.92/1.01      | k10_relat_1(sK0,sK2) != X0
% 3.92/1.01      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 3.92/1.01      inference(instantiation,[status(thm)],[c_196]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_829,plain,
% 3.92/1.01      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
% 3.92/1.01      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 3.92/1.01      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 3.92/1.01      inference(instantiation,[status(thm)],[c_761]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(c_21,negated_conjecture,
% 3.92/1.01      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 3.92/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.92/1.01  
% 3.92/1.01  cnf(contradiction,plain,
% 3.92/1.01      ( $false ),
% 3.92/1.01      inference(minisat,[status(thm)],[c_9320,c_830,c_829,c_21]) ).
% 3.92/1.01  
% 3.92/1.01  
% 3.92/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/1.01  
% 3.92/1.01  ------                               Statistics
% 3.92/1.01  
% 3.92/1.01  ------ Selected
% 3.92/1.01  
% 3.92/1.01  total_time:                             0.406
% 3.92/1.01  
%------------------------------------------------------------------------------
