%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:21 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 184 expanded)
%              Number of clauses        :   42 (  49 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  158 ( 281 expanded)
%              Number of equality atoms :  107 ( 187 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48])).

fof(f80,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f82])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f83])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f85])).

fof(f87,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f61,f86])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f78,f87])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f88,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f54,f86,f86])).

fof(f22,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f76,f87])).

fof(f81,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_826,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_17,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_830,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2990,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_830])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4023,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2990,c_34])).

cnf(c_4024,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4023])).

cnf(c_4035,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(sK0) ),
    inference(superposition,[status(thm)],[c_826,c_4024])).

cnf(c_829,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_833,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2365,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_829,c_833])).

cnf(c_5213,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK0)) ),
    inference(superposition,[status(thm)],[c_4035,c_2365])).

cnf(c_14,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_5239,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_5213,c_14])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_832,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3613,plain,
    ( k9_relat_1(k6_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_829,c_832])).

cnf(c_12851,plain,
    ( k9_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_829,c_3613])).

cnf(c_12880,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_12851,c_14])).

cnf(c_24,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_825,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_827,plain,
    ( k2_wellord1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2102,plain,
    ( k2_wellord1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_825,c_827])).

cnf(c_4,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_19,plain,
    ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1151,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_19,c_14])).

cnf(c_2685,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_4,c_1151])).

cnf(c_6952,plain,
    ( k2_wellord1(sK2,k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2102,c_2685])).

cnf(c_13048,plain,
    ( k2_wellord1(sK2,k9_relat_1(k6_relat_1(X0),X1)) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
    inference(demodulation,[status(thm)],[c_12880,c_6952])).

cnf(c_13801,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(sK2,sK0) ),
    inference(superposition,[status(thm)],[c_5239,c_13048])).

cnf(c_382,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1438,plain,
    ( k2_wellord1(sK2,sK0) = k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_383,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1147,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X0
    | k2_wellord1(sK2,sK0) != X0
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_1437,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(sK2,sK0)
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_22,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13801,c_1438,c_1437,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:49:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.81/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.97  
% 3.81/0.97  ------  iProver source info
% 3.81/0.97  
% 3.81/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.97  git: non_committed_changes: false
% 3.81/0.97  git: last_make_outside_of_git: false
% 3.81/0.97  
% 3.81/0.97  ------ 
% 3.81/0.97  
% 3.81/0.97  ------ Input Options
% 3.81/0.97  
% 3.81/0.97  --out_options                           all
% 3.81/0.97  --tptp_safe_out                         true
% 3.81/0.97  --problem_path                          ""
% 3.81/0.97  --include_path                          ""
% 3.81/0.97  --clausifier                            res/vclausify_rel
% 3.81/0.97  --clausifier_options                    --mode clausify
% 3.81/0.97  --stdin                                 false
% 3.81/0.97  --stats_out                             sel
% 3.81/0.97  
% 3.81/0.97  ------ General Options
% 3.81/0.97  
% 3.81/0.97  --fof                                   false
% 3.81/0.97  --time_out_real                         604.99
% 3.81/0.97  --time_out_virtual                      -1.
% 3.81/0.97  --symbol_type_check                     false
% 3.81/0.97  --clausify_out                          false
% 3.81/0.97  --sig_cnt_out                           false
% 3.81/0.97  --trig_cnt_out                          false
% 3.81/0.97  --trig_cnt_out_tolerance                1.
% 3.81/0.97  --trig_cnt_out_sk_spl                   false
% 3.81/0.97  --abstr_cl_out                          false
% 3.81/0.97  
% 3.81/0.97  ------ Global Options
% 3.81/0.97  
% 3.81/0.97  --schedule                              none
% 3.81/0.97  --add_important_lit                     false
% 3.81/0.97  --prop_solver_per_cl                    1000
% 3.81/0.97  --min_unsat_core                        false
% 3.81/0.97  --soft_assumptions                      false
% 3.81/0.97  --soft_lemma_size                       3
% 3.81/0.97  --prop_impl_unit_size                   0
% 3.81/0.97  --prop_impl_unit                        []
% 3.81/0.97  --share_sel_clauses                     true
% 3.81/0.97  --reset_solvers                         false
% 3.81/0.97  --bc_imp_inh                            [conj_cone]
% 3.81/0.97  --conj_cone_tolerance                   3.
% 3.81/0.97  --extra_neg_conj                        none
% 3.81/0.97  --large_theory_mode                     true
% 3.81/0.97  --prolific_symb_bound                   200
% 3.81/0.97  --lt_threshold                          2000
% 3.81/0.97  --clause_weak_htbl                      true
% 3.81/0.97  --gc_record_bc_elim                     false
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing Options
% 3.81/0.97  
% 3.81/0.97  --preprocessing_flag                    true
% 3.81/0.97  --time_out_prep_mult                    0.1
% 3.81/0.97  --splitting_mode                        input
% 3.81/0.97  --splitting_grd                         true
% 3.81/0.97  --splitting_cvd                         false
% 3.81/0.97  --splitting_cvd_svl                     false
% 3.81/0.97  --splitting_nvd                         32
% 3.81/0.97  --sub_typing                            true
% 3.81/0.97  --prep_gs_sim                           false
% 3.81/0.97  --prep_unflatten                        true
% 3.81/0.97  --prep_res_sim                          true
% 3.81/0.97  --prep_upred                            true
% 3.81/0.97  --prep_sem_filter                       exhaustive
% 3.81/0.97  --prep_sem_filter_out                   false
% 3.81/0.97  --pred_elim                             false
% 3.81/0.97  --res_sim_input                         true
% 3.81/0.97  --eq_ax_congr_red                       true
% 3.81/0.97  --pure_diseq_elim                       true
% 3.81/0.97  --brand_transform                       false
% 3.81/0.97  --non_eq_to_eq                          false
% 3.81/0.97  --prep_def_merge                        true
% 3.81/0.97  --prep_def_merge_prop_impl              false
% 3.81/0.97  --prep_def_merge_mbd                    true
% 3.81/0.97  --prep_def_merge_tr_red                 false
% 3.81/0.97  --prep_def_merge_tr_cl                  false
% 3.81/0.97  --smt_preprocessing                     true
% 3.81/0.97  --smt_ac_axioms                         fast
% 3.81/0.97  --preprocessed_out                      false
% 3.81/0.97  --preprocessed_stats                    false
% 3.81/0.97  
% 3.81/0.97  ------ Abstraction refinement Options
% 3.81/0.97  
% 3.81/0.97  --abstr_ref                             []
% 3.81/0.97  --abstr_ref_prep                        false
% 3.81/0.97  --abstr_ref_until_sat                   false
% 3.81/0.97  --abstr_ref_sig_restrict                funpre
% 3.81/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.97  --abstr_ref_under                       []
% 3.81/0.97  
% 3.81/0.97  ------ SAT Options
% 3.81/0.97  
% 3.81/0.97  --sat_mode                              false
% 3.81/0.97  --sat_fm_restart_options                ""
% 3.81/0.97  --sat_gr_def                            false
% 3.81/0.97  --sat_epr_types                         true
% 3.81/0.97  --sat_non_cyclic_types                  false
% 3.81/0.97  --sat_finite_models                     false
% 3.81/0.97  --sat_fm_lemmas                         false
% 3.81/0.97  --sat_fm_prep                           false
% 3.81/0.97  --sat_fm_uc_incr                        true
% 3.81/0.97  --sat_out_model                         small
% 3.81/0.97  --sat_out_clauses                       false
% 3.81/0.97  
% 3.81/0.97  ------ QBF Options
% 3.81/0.97  
% 3.81/0.97  --qbf_mode                              false
% 3.81/0.97  --qbf_elim_univ                         false
% 3.81/0.97  --qbf_dom_inst                          none
% 3.81/0.97  --qbf_dom_pre_inst                      false
% 3.81/0.97  --qbf_sk_in                             false
% 3.81/0.97  --qbf_pred_elim                         true
% 3.81/0.97  --qbf_split                             512
% 3.81/0.97  
% 3.81/0.97  ------ BMC1 Options
% 3.81/0.97  
% 3.81/0.97  --bmc1_incremental                      false
% 3.81/0.97  --bmc1_axioms                           reachable_all
% 3.81/0.97  --bmc1_min_bound                        0
% 3.81/0.97  --bmc1_max_bound                        -1
% 3.81/0.97  --bmc1_max_bound_default                -1
% 3.81/0.97  --bmc1_symbol_reachability              true
% 3.81/0.97  --bmc1_property_lemmas                  false
% 3.81/0.97  --bmc1_k_induction                      false
% 3.81/0.97  --bmc1_non_equiv_states                 false
% 3.81/0.97  --bmc1_deadlock                         false
% 3.81/0.97  --bmc1_ucm                              false
% 3.81/0.97  --bmc1_add_unsat_core                   none
% 3.81/0.97  --bmc1_unsat_core_children              false
% 3.81/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.97  --bmc1_out_stat                         full
% 3.81/0.97  --bmc1_ground_init                      false
% 3.81/0.97  --bmc1_pre_inst_next_state              false
% 3.81/0.97  --bmc1_pre_inst_state                   false
% 3.81/0.97  --bmc1_pre_inst_reach_state             false
% 3.81/0.97  --bmc1_out_unsat_core                   false
% 3.81/0.97  --bmc1_aig_witness_out                  false
% 3.81/0.97  --bmc1_verbose                          false
% 3.81/0.97  --bmc1_dump_clauses_tptp                false
% 3.81/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.97  --bmc1_dump_file                        -
% 3.81/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.97  --bmc1_ucm_extend_mode                  1
% 3.81/0.97  --bmc1_ucm_init_mode                    2
% 3.81/0.97  --bmc1_ucm_cone_mode                    none
% 3.81/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.97  --bmc1_ucm_relax_model                  4
% 3.81/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.97  --bmc1_ucm_layered_model                none
% 3.81/0.97  --bmc1_ucm_max_lemma_size               10
% 3.81/0.97  
% 3.81/0.97  ------ AIG Options
% 3.81/0.97  
% 3.81/0.97  --aig_mode                              false
% 3.81/0.97  
% 3.81/0.97  ------ Instantiation Options
% 3.81/0.97  
% 3.81/0.97  --instantiation_flag                    true
% 3.81/0.97  --inst_sos_flag                         false
% 3.81/0.97  --inst_sos_phase                        true
% 3.81/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.97  --inst_lit_sel_side                     num_symb
% 3.81/0.97  --inst_solver_per_active                1400
% 3.81/0.97  --inst_solver_calls_frac                1.
% 3.81/0.97  --inst_passive_queue_type               priority_queues
% 3.81/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.97  --inst_passive_queues_freq              [25;2]
% 3.81/0.97  --inst_dismatching                      true
% 3.81/0.97  --inst_eager_unprocessed_to_passive     true
% 3.81/0.97  --inst_prop_sim_given                   true
% 3.81/0.97  --inst_prop_sim_new                     false
% 3.81/0.97  --inst_subs_new                         false
% 3.81/0.97  --inst_eq_res_simp                      false
% 3.81/0.97  --inst_subs_given                       false
% 3.81/0.97  --inst_orphan_elimination               true
% 3.81/0.97  --inst_learning_loop_flag               true
% 3.81/0.97  --inst_learning_start                   3000
% 3.81/0.97  --inst_learning_factor                  2
% 3.81/0.97  --inst_start_prop_sim_after_learn       3
% 3.81/0.97  --inst_sel_renew                        solver
% 3.81/0.97  --inst_lit_activity_flag                true
% 3.81/0.97  --inst_restr_to_given                   false
% 3.81/0.97  --inst_activity_threshold               500
% 3.81/0.97  --inst_out_proof                        true
% 3.81/0.97  
% 3.81/0.97  ------ Resolution Options
% 3.81/0.97  
% 3.81/0.97  --resolution_flag                       true
% 3.81/0.97  --res_lit_sel                           adaptive
% 3.81/0.97  --res_lit_sel_side                      none
% 3.81/0.97  --res_ordering                          kbo
% 3.81/0.97  --res_to_prop_solver                    active
% 3.81/0.97  --res_prop_simpl_new                    false
% 3.81/0.97  --res_prop_simpl_given                  true
% 3.81/0.97  --res_passive_queue_type                priority_queues
% 3.81/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.97  --res_passive_queues_freq               [15;5]
% 3.81/0.97  --res_forward_subs                      full
% 3.81/0.97  --res_backward_subs                     full
% 3.81/0.97  --res_forward_subs_resolution           true
% 3.81/0.97  --res_backward_subs_resolution          true
% 3.81/0.97  --res_orphan_elimination                true
% 3.81/0.97  --res_time_limit                        2.
% 3.81/0.97  --res_out_proof                         true
% 3.81/0.97  
% 3.81/0.97  ------ Superposition Options
% 3.81/0.97  
% 3.81/0.97  --superposition_flag                    true
% 3.81/0.97  --sup_passive_queue_type                priority_queues
% 3.81/0.97  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.97  --sup_passive_queues_freq               [1;4]
% 3.81/0.97  --demod_completeness_check              fast
% 3.81/0.97  --demod_use_ground                      true
% 3.81/0.97  --sup_to_prop_solver                    passive
% 3.81/0.97  --sup_prop_simpl_new                    true
% 3.81/0.97  --sup_prop_simpl_given                  true
% 3.81/0.97  --sup_fun_splitting                     false
% 3.81/0.97  --sup_smt_interval                      50000
% 3.81/0.97  
% 3.81/0.97  ------ Superposition Simplification Setup
% 3.81/0.97  
% 3.81/0.97  --sup_indices_passive                   []
% 3.81/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_full_bw                           [BwDemod]
% 3.81/0.97  --sup_immed_triv                        [TrivRules]
% 3.81/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_immed_bw_main                     []
% 3.81/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.97  
% 3.81/0.97  ------ Combination Options
% 3.81/0.97  
% 3.81/0.97  --comb_res_mult                         3
% 3.81/0.97  --comb_sup_mult                         2
% 3.81/0.97  --comb_inst_mult                        10
% 3.81/0.97  
% 3.81/0.97  ------ Debug Options
% 3.81/0.97  
% 3.81/0.97  --dbg_backtrace                         false
% 3.81/0.97  --dbg_dump_prop_clauses                 false
% 3.81/0.97  --dbg_dump_prop_clauses_file            -
% 3.81/0.97  --dbg_out_stat                          false
% 3.81/0.97  ------ Parsing...
% 3.81/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.97  ------ Proving...
% 3.81/0.97  ------ Problem Properties 
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  clauses                                 24
% 3.81/0.97  conjectures                             3
% 3.81/0.97  EPR                                     6
% 3.81/0.97  Horn                                    24
% 3.81/0.97  unary                                   9
% 3.81/0.97  binary                                  7
% 3.81/0.97  lits                                    47
% 3.81/0.97  lits eq                                 12
% 3.81/0.97  fd_pure                                 0
% 3.81/0.97  fd_pseudo                               0
% 3.81/0.97  fd_cond                                 0
% 3.81/0.97  fd_pseudo_cond                          1
% 3.81/0.97  AC symbols                              0
% 3.81/0.97  
% 3.81/0.97  ------ Input Options Time Limit: Unbounded
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  ------ 
% 3.81/0.97  Current options:
% 3.81/0.97  ------ 
% 3.81/0.97  
% 3.81/0.97  ------ Input Options
% 3.81/0.97  
% 3.81/0.97  --out_options                           all
% 3.81/0.97  --tptp_safe_out                         true
% 3.81/0.97  --problem_path                          ""
% 3.81/0.97  --include_path                          ""
% 3.81/0.97  --clausifier                            res/vclausify_rel
% 3.81/0.97  --clausifier_options                    --mode clausify
% 3.81/0.97  --stdin                                 false
% 3.81/0.97  --stats_out                             sel
% 3.81/0.97  
% 3.81/0.97  ------ General Options
% 3.81/0.97  
% 3.81/0.97  --fof                                   false
% 3.81/0.97  --time_out_real                         604.99
% 3.81/0.97  --time_out_virtual                      -1.
% 3.81/0.97  --symbol_type_check                     false
% 3.81/0.97  --clausify_out                          false
% 3.81/0.97  --sig_cnt_out                           false
% 3.81/0.97  --trig_cnt_out                          false
% 3.81/0.97  --trig_cnt_out_tolerance                1.
% 3.81/0.97  --trig_cnt_out_sk_spl                   false
% 3.81/0.97  --abstr_cl_out                          false
% 3.81/0.97  
% 3.81/0.97  ------ Global Options
% 3.81/0.97  
% 3.81/0.97  --schedule                              none
% 3.81/0.97  --add_important_lit                     false
% 3.81/0.97  --prop_solver_per_cl                    1000
% 3.81/0.97  --min_unsat_core                        false
% 3.81/0.97  --soft_assumptions                      false
% 3.81/0.97  --soft_lemma_size                       3
% 3.81/0.97  --prop_impl_unit_size                   0
% 3.81/0.97  --prop_impl_unit                        []
% 3.81/0.97  --share_sel_clauses                     true
% 3.81/0.97  --reset_solvers                         false
% 3.81/0.97  --bc_imp_inh                            [conj_cone]
% 3.81/0.97  --conj_cone_tolerance                   3.
% 3.81/0.97  --extra_neg_conj                        none
% 3.81/0.97  --large_theory_mode                     true
% 3.81/0.97  --prolific_symb_bound                   200
% 3.81/0.97  --lt_threshold                          2000
% 3.81/0.97  --clause_weak_htbl                      true
% 3.81/0.97  --gc_record_bc_elim                     false
% 3.81/0.97  
% 3.81/0.97  ------ Preprocessing Options
% 3.81/0.97  
% 3.81/0.97  --preprocessing_flag                    true
% 3.81/0.97  --time_out_prep_mult                    0.1
% 3.81/0.97  --splitting_mode                        input
% 3.81/0.97  --splitting_grd                         true
% 3.81/0.97  --splitting_cvd                         false
% 3.81/0.97  --splitting_cvd_svl                     false
% 3.81/0.97  --splitting_nvd                         32
% 3.81/0.97  --sub_typing                            true
% 3.81/0.97  --prep_gs_sim                           false
% 3.81/0.97  --prep_unflatten                        true
% 3.81/0.97  --prep_res_sim                          true
% 3.81/0.97  --prep_upred                            true
% 3.81/0.97  --prep_sem_filter                       exhaustive
% 3.81/0.97  --prep_sem_filter_out                   false
% 3.81/0.97  --pred_elim                             false
% 3.81/0.97  --res_sim_input                         true
% 3.81/0.97  --eq_ax_congr_red                       true
% 3.81/0.97  --pure_diseq_elim                       true
% 3.81/0.97  --brand_transform                       false
% 3.81/0.97  --non_eq_to_eq                          false
% 3.81/0.97  --prep_def_merge                        true
% 3.81/0.97  --prep_def_merge_prop_impl              false
% 3.81/0.97  --prep_def_merge_mbd                    true
% 3.81/0.97  --prep_def_merge_tr_red                 false
% 3.81/0.97  --prep_def_merge_tr_cl                  false
% 3.81/0.97  --smt_preprocessing                     true
% 3.81/0.97  --smt_ac_axioms                         fast
% 3.81/0.97  --preprocessed_out                      false
% 3.81/0.97  --preprocessed_stats                    false
% 3.81/0.97  
% 3.81/0.97  ------ Abstraction refinement Options
% 3.81/0.97  
% 3.81/0.97  --abstr_ref                             []
% 3.81/0.97  --abstr_ref_prep                        false
% 3.81/0.97  --abstr_ref_until_sat                   false
% 3.81/0.97  --abstr_ref_sig_restrict                funpre
% 3.81/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.97  --abstr_ref_under                       []
% 3.81/0.97  
% 3.81/0.97  ------ SAT Options
% 3.81/0.97  
% 3.81/0.97  --sat_mode                              false
% 3.81/0.97  --sat_fm_restart_options                ""
% 3.81/0.97  --sat_gr_def                            false
% 3.81/0.97  --sat_epr_types                         true
% 3.81/0.97  --sat_non_cyclic_types                  false
% 3.81/0.97  --sat_finite_models                     false
% 3.81/0.97  --sat_fm_lemmas                         false
% 3.81/0.97  --sat_fm_prep                           false
% 3.81/0.97  --sat_fm_uc_incr                        true
% 3.81/0.97  --sat_out_model                         small
% 3.81/0.97  --sat_out_clauses                       false
% 3.81/0.97  
% 3.81/0.97  ------ QBF Options
% 3.81/0.97  
% 3.81/0.97  --qbf_mode                              false
% 3.81/0.97  --qbf_elim_univ                         false
% 3.81/0.97  --qbf_dom_inst                          none
% 3.81/0.97  --qbf_dom_pre_inst                      false
% 3.81/0.97  --qbf_sk_in                             false
% 3.81/0.97  --qbf_pred_elim                         true
% 3.81/0.97  --qbf_split                             512
% 3.81/0.97  
% 3.81/0.97  ------ BMC1 Options
% 3.81/0.97  
% 3.81/0.97  --bmc1_incremental                      false
% 3.81/0.97  --bmc1_axioms                           reachable_all
% 3.81/0.97  --bmc1_min_bound                        0
% 3.81/0.97  --bmc1_max_bound                        -1
% 3.81/0.97  --bmc1_max_bound_default                -1
% 3.81/0.97  --bmc1_symbol_reachability              true
% 3.81/0.97  --bmc1_property_lemmas                  false
% 3.81/0.97  --bmc1_k_induction                      false
% 3.81/0.97  --bmc1_non_equiv_states                 false
% 3.81/0.97  --bmc1_deadlock                         false
% 3.81/0.97  --bmc1_ucm                              false
% 3.81/0.97  --bmc1_add_unsat_core                   none
% 3.81/0.97  --bmc1_unsat_core_children              false
% 3.81/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.97  --bmc1_out_stat                         full
% 3.81/0.97  --bmc1_ground_init                      false
% 3.81/0.97  --bmc1_pre_inst_next_state              false
% 3.81/0.97  --bmc1_pre_inst_state                   false
% 3.81/0.97  --bmc1_pre_inst_reach_state             false
% 3.81/0.97  --bmc1_out_unsat_core                   false
% 3.81/0.97  --bmc1_aig_witness_out                  false
% 3.81/0.97  --bmc1_verbose                          false
% 3.81/0.97  --bmc1_dump_clauses_tptp                false
% 3.81/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.97  --bmc1_dump_file                        -
% 3.81/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.97  --bmc1_ucm_extend_mode                  1
% 3.81/0.97  --bmc1_ucm_init_mode                    2
% 3.81/0.97  --bmc1_ucm_cone_mode                    none
% 3.81/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.97  --bmc1_ucm_relax_model                  4
% 3.81/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.97  --bmc1_ucm_layered_model                none
% 3.81/0.97  --bmc1_ucm_max_lemma_size               10
% 3.81/0.97  
% 3.81/0.97  ------ AIG Options
% 3.81/0.97  
% 3.81/0.97  --aig_mode                              false
% 3.81/0.97  
% 3.81/0.97  ------ Instantiation Options
% 3.81/0.97  
% 3.81/0.97  --instantiation_flag                    true
% 3.81/0.97  --inst_sos_flag                         false
% 3.81/0.97  --inst_sos_phase                        true
% 3.81/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.97  --inst_lit_sel_side                     num_symb
% 3.81/0.97  --inst_solver_per_active                1400
% 3.81/0.97  --inst_solver_calls_frac                1.
% 3.81/0.97  --inst_passive_queue_type               priority_queues
% 3.81/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.97  --inst_passive_queues_freq              [25;2]
% 3.81/0.97  --inst_dismatching                      true
% 3.81/0.97  --inst_eager_unprocessed_to_passive     true
% 3.81/0.97  --inst_prop_sim_given                   true
% 3.81/0.97  --inst_prop_sim_new                     false
% 3.81/0.97  --inst_subs_new                         false
% 3.81/0.97  --inst_eq_res_simp                      false
% 3.81/0.97  --inst_subs_given                       false
% 3.81/0.97  --inst_orphan_elimination               true
% 3.81/0.97  --inst_learning_loop_flag               true
% 3.81/0.97  --inst_learning_start                   3000
% 3.81/0.97  --inst_learning_factor                  2
% 3.81/0.97  --inst_start_prop_sim_after_learn       3
% 3.81/0.97  --inst_sel_renew                        solver
% 3.81/0.97  --inst_lit_activity_flag                true
% 3.81/0.97  --inst_restr_to_given                   false
% 3.81/0.97  --inst_activity_threshold               500
% 3.81/0.97  --inst_out_proof                        true
% 3.81/0.97  
% 3.81/0.97  ------ Resolution Options
% 3.81/0.97  
% 3.81/0.97  --resolution_flag                       true
% 3.81/0.97  --res_lit_sel                           adaptive
% 3.81/0.97  --res_lit_sel_side                      none
% 3.81/0.97  --res_ordering                          kbo
% 3.81/0.97  --res_to_prop_solver                    active
% 3.81/0.97  --res_prop_simpl_new                    false
% 3.81/0.97  --res_prop_simpl_given                  true
% 3.81/0.97  --res_passive_queue_type                priority_queues
% 3.81/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.97  --res_passive_queues_freq               [15;5]
% 3.81/0.97  --res_forward_subs                      full
% 3.81/0.97  --res_backward_subs                     full
% 3.81/0.97  --res_forward_subs_resolution           true
% 3.81/0.97  --res_backward_subs_resolution          true
% 3.81/0.97  --res_orphan_elimination                true
% 3.81/0.97  --res_time_limit                        2.
% 3.81/0.97  --res_out_proof                         true
% 3.81/0.97  
% 3.81/0.97  ------ Superposition Options
% 3.81/0.97  
% 3.81/0.97  --superposition_flag                    true
% 3.81/0.97  --sup_passive_queue_type                priority_queues
% 3.81/0.97  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.97  --sup_passive_queues_freq               [1;4]
% 3.81/0.97  --demod_completeness_check              fast
% 3.81/0.97  --demod_use_ground                      true
% 3.81/0.97  --sup_to_prop_solver                    passive
% 3.81/0.97  --sup_prop_simpl_new                    true
% 3.81/0.97  --sup_prop_simpl_given                  true
% 3.81/0.97  --sup_fun_splitting                     false
% 3.81/0.97  --sup_smt_interval                      50000
% 3.81/0.97  
% 3.81/0.97  ------ Superposition Simplification Setup
% 3.81/0.97  
% 3.81/0.97  --sup_indices_passive                   []
% 3.81/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_full_bw                           [BwDemod]
% 3.81/0.97  --sup_immed_triv                        [TrivRules]
% 3.81/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_immed_bw_main                     []
% 3.81/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.81/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.81/0.97  
% 3.81/0.97  ------ Combination Options
% 3.81/0.97  
% 3.81/0.97  --comb_res_mult                         3
% 3.81/0.97  --comb_sup_mult                         2
% 3.81/0.97  --comb_inst_mult                        10
% 3.81/0.97  
% 3.81/0.97  ------ Debug Options
% 3.81/0.97  
% 3.81/0.97  --dbg_backtrace                         false
% 3.81/0.97  --dbg_dump_prop_clauses                 false
% 3.81/0.97  --dbg_dump_prop_clauses_file            -
% 3.81/0.97  --dbg_out_stat                          false
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  ------ Proving...
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  % SZS status Theorem for theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  fof(f25,conjecture,(
% 3.81/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f26,negated_conjecture,(
% 3.81/0.97    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 3.81/0.97    inference(negated_conjecture,[],[f25])).
% 3.81/0.97  
% 3.81/0.97  fof(f43,plain,(
% 3.81/0.97    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 3.81/0.97    inference(ennf_transformation,[],[f26])).
% 3.81/0.97  
% 3.81/0.97  fof(f44,plain,(
% 3.81/0.97    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 3.81/0.97    inference(flattening,[],[f43])).
% 3.81/0.97  
% 3.81/0.97  fof(f48,plain,(
% 3.81/0.97    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 3.81/0.97    introduced(choice_axiom,[])).
% 3.81/0.97  
% 3.81/0.97  fof(f49,plain,(
% 3.81/0.97    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 3.81/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48])).
% 3.81/0.97  
% 3.81/0.97  fof(f80,plain,(
% 3.81/0.97    r1_tarski(sK0,sK1)),
% 3.81/0.97    inference(cnf_transformation,[],[f49])).
% 3.81/0.97  
% 3.81/0.97  fof(f18,axiom,(
% 3.81/0.97    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f71,plain,(
% 3.81/0.97    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.81/0.97    inference(cnf_transformation,[],[f18])).
% 3.81/0.97  
% 3.81/0.97  fof(f20,axiom,(
% 3.81/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f39,plain,(
% 3.81/0.97    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.81/0.97    inference(ennf_transformation,[],[f20])).
% 3.81/0.97  
% 3.81/0.97  fof(f40,plain,(
% 3.81/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.81/0.97    inference(flattening,[],[f39])).
% 3.81/0.97  
% 3.81/0.97  fof(f74,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f40])).
% 3.81/0.97  
% 3.81/0.97  fof(f21,axiom,(
% 3.81/0.97    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f27,plain,(
% 3.81/0.97    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.81/0.97    inference(pure_predicate_removal,[],[f21])).
% 3.81/0.97  
% 3.81/0.97  fof(f75,plain,(
% 3.81/0.97    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.81/0.97    inference(cnf_transformation,[],[f27])).
% 3.81/0.97  
% 3.81/0.97  fof(f15,axiom,(
% 3.81/0.97    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f34,plain,(
% 3.81/0.97    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.81/0.97    inference(ennf_transformation,[],[f15])).
% 3.81/0.97  
% 3.81/0.97  fof(f67,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f34])).
% 3.81/0.97  
% 3.81/0.97  fof(f72,plain,(
% 3.81/0.97    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.81/0.97    inference(cnf_transformation,[],[f18])).
% 3.81/0.97  
% 3.81/0.97  fof(f16,axiom,(
% 3.81/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f35,plain,(
% 3.81/0.97    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.81/0.97    inference(ennf_transformation,[],[f16])).
% 3.81/0.97  
% 3.81/0.97  fof(f68,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f35])).
% 3.81/0.97  
% 3.81/0.97  fof(f79,plain,(
% 3.81/0.97    v1_relat_1(sK2)),
% 3.81/0.97    inference(cnf_transformation,[],[f49])).
% 3.81/0.97  
% 3.81/0.97  fof(f24,axiom,(
% 3.81/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f42,plain,(
% 3.81/0.97    ! [X0,X1,X2] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.81/0.97    inference(ennf_transformation,[],[f24])).
% 3.81/0.97  
% 3.81/0.97  fof(f78,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f42])).
% 3.81/0.97  
% 3.81/0.97  fof(f10,axiom,(
% 3.81/0.97    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f61,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f10])).
% 3.81/0.97  
% 3.81/0.97  fof(f4,axiom,(
% 3.81/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f55,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f4])).
% 3.81/0.97  
% 3.81/0.97  fof(f5,axiom,(
% 3.81/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f56,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f5])).
% 3.81/0.97  
% 3.81/0.97  fof(f6,axiom,(
% 3.81/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f57,plain,(
% 3.81/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f6])).
% 3.81/0.97  
% 3.81/0.97  fof(f7,axiom,(
% 3.81/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f58,plain,(
% 3.81/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f7])).
% 3.81/0.97  
% 3.81/0.97  fof(f8,axiom,(
% 3.81/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f59,plain,(
% 3.81/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f8])).
% 3.81/0.97  
% 3.81/0.97  fof(f9,axiom,(
% 3.81/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f60,plain,(
% 3.81/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f9])).
% 3.81/0.97  
% 3.81/0.97  fof(f82,plain,(
% 3.81/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f59,f60])).
% 3.81/0.97  
% 3.81/0.97  fof(f83,plain,(
% 3.81/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f58,f82])).
% 3.81/0.97  
% 3.81/0.97  fof(f84,plain,(
% 3.81/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f57,f83])).
% 3.81/0.97  
% 3.81/0.97  fof(f85,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f56,f84])).
% 3.81/0.97  
% 3.81/0.97  fof(f86,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f55,f85])).
% 3.81/0.97  
% 3.81/0.97  fof(f87,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f61,f86])).
% 3.81/0.97  
% 3.81/0.97  fof(f90,plain,(
% 3.81/0.97    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f78,f87])).
% 3.81/0.97  
% 3.81/0.97  fof(f3,axiom,(
% 3.81/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f54,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.81/0.97    inference(cnf_transformation,[],[f3])).
% 3.81/0.97  
% 3.81/0.97  fof(f88,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 3.81/0.97    inference(definition_unfolding,[],[f54,f86,f86])).
% 3.81/0.97  
% 3.81/0.97  fof(f22,axiom,(
% 3.81/0.97    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.81/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/0.97  
% 3.81/0.97  fof(f76,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 3.81/0.97    inference(cnf_transformation,[],[f22])).
% 3.81/0.97  
% 3.81/0.97  fof(f89,plain,(
% 3.81/0.97    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.81/0.97    inference(definition_unfolding,[],[f76,f87])).
% 3.81/0.97  
% 3.81/0.97  fof(f81,plain,(
% 3.81/0.97    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 3.81/0.97    inference(cnf_transformation,[],[f49])).
% 3.81/0.97  
% 3.81/0.97  cnf(c_23,negated_conjecture,
% 3.81/0.97      ( r1_tarski(sK0,sK1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_826,plain,
% 3.81/0.97      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_15,plain,
% 3.81/0.97      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.81/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_17,plain,
% 3.81/0.97      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.81/0.97      | ~ v1_relat_1(X0)
% 3.81/0.97      | k7_relat_1(X0,X1) = X0 ),
% 3.81/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_830,plain,
% 3.81/0.97      ( k7_relat_1(X0,X1) = X0
% 3.81/0.97      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.81/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2990,plain,
% 3.81/0.97      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.81/0.97      | r1_tarski(X0,X1) != iProver_top
% 3.81/0.97      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_15,c_830]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_18,plain,
% 3.81/0.97      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.81/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_34,plain,
% 3.81/0.97      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_4023,plain,
% 3.81/0.97      ( r1_tarski(X0,X1) != iProver_top
% 3.81/0.97      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 3.81/0.97      inference(global_propositional_subsumption,
% 3.81/0.97                [status(thm)],
% 3.81/0.97                [c_2990,c_34]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_4024,plain,
% 3.81/0.97      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 3.81/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.81/0.97      inference(renaming,[status(thm)],[c_4023]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_4035,plain,
% 3.81/0.97      ( k7_relat_1(k6_relat_1(sK0),sK1) = k6_relat_1(sK0) ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_826,c_4024]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_829,plain,
% 3.81/0.97      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_10,plain,
% 3.81/0.97      ( ~ v1_relat_1(X0)
% 3.81/0.97      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.81/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_833,plain,
% 3.81/0.97      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.81/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2365,plain,
% 3.81/0.97      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_829,c_833]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_5213,plain,
% 3.81/0.97      ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK0)) ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_4035,c_2365]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_14,plain,
% 3.81/0.97      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.81/0.97      inference(cnf_transformation,[],[f72]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_5239,plain,
% 3.81/0.97      ( k9_relat_1(k6_relat_1(sK0),sK1) = sK0 ),
% 3.81/0.97      inference(demodulation,[status(thm)],[c_5213,c_14]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_11,plain,
% 3.81/0.97      ( ~ v1_relat_1(X0)
% 3.81/0.97      | ~ v1_relat_1(X1)
% 3.81/0.97      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 3.81/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_832,plain,
% 3.81/0.97      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 3.81/0.97      | v1_relat_1(X1) != iProver_top
% 3.81/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_3613,plain,
% 3.81/0.97      ( k9_relat_1(k6_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 3.81/0.97      | v1_relat_1(X1) != iProver_top ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_829,c_832]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_12851,plain,
% 3.81/0.97      ( k9_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_829,c_3613]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_12880,plain,
% 3.81/0.97      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k9_relat_1(k6_relat_1(X1),X0) ),
% 3.81/0.97      inference(demodulation,[status(thm)],[c_12851,c_14]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_24,negated_conjecture,
% 3.81/0.97      ( v1_relat_1(sK2) ),
% 3.81/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_825,plain,
% 3.81/0.97      ( v1_relat_1(sK2) = iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_21,plain,
% 3.81/0.97      ( ~ v1_relat_1(X0)
% 3.81/0.97      | k2_wellord1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2) ),
% 3.81/0.97      inference(cnf_transformation,[],[f90]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_827,plain,
% 3.81/0.97      ( k2_wellord1(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k2_wellord1(k2_wellord1(X0,X1),X2)
% 3.81/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.81/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2102,plain,
% 3.81/0.97      ( k2_wellord1(sK2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_825,c_827]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_4,plain,
% 3.81/0.97      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 3.81/0.97      inference(cnf_transformation,[],[f88]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_19,plain,
% 3.81/0.97      ( k6_relat_1(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 3.81/0.97      inference(cnf_transformation,[],[f89]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1151,plain,
% 3.81/0.97      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_19,c_14]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_2685,plain,
% 3.81/0.97      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_4,c_1151]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_6952,plain,
% 3.81/0.97      ( k2_wellord1(sK2,k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k2_wellord1(k2_wellord1(sK2,X0),X1) ),
% 3.81/0.97      inference(light_normalisation,[status(thm)],[c_2102,c_2685]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_13048,plain,
% 3.81/0.97      ( k2_wellord1(sK2,k9_relat_1(k6_relat_1(X0),X1)) = k2_wellord1(k2_wellord1(sK2,X1),X0) ),
% 3.81/0.97      inference(demodulation,[status(thm)],[c_12880,c_6952]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_13801,plain,
% 3.81/0.97      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) = k2_wellord1(sK2,sK0) ),
% 3.81/0.97      inference(superposition,[status(thm)],[c_5239,c_13048]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_382,plain,( X0 = X0 ),theory(equality) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1438,plain,
% 3.81/0.97      ( k2_wellord1(sK2,sK0) = k2_wellord1(sK2,sK0) ),
% 3.81/0.97      inference(instantiation,[status(thm)],[c_382]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_383,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1147,plain,
% 3.81/0.97      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != X0
% 3.81/0.97      | k2_wellord1(sK2,sK0) != X0
% 3.81/0.97      | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 3.81/0.97      inference(instantiation,[status(thm)],[c_383]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_1437,plain,
% 3.81/0.97      ( k2_wellord1(k2_wellord1(sK2,sK1),sK0) != k2_wellord1(sK2,sK0)
% 3.81/0.97      | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)
% 3.81/0.97      | k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) ),
% 3.81/0.97      inference(instantiation,[status(thm)],[c_1147]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(c_22,negated_conjecture,
% 3.81/0.97      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 3.81/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.81/0.97  
% 3.81/0.97  cnf(contradiction,plain,
% 3.81/0.97      ( $false ),
% 3.81/0.97      inference(minisat,[status(thm)],[c_13801,c_1438,c_1437,c_22]) ).
% 3.81/0.97  
% 3.81/0.97  
% 3.81/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.97  
% 3.81/0.97  ------                               Statistics
% 3.81/0.97  
% 3.81/0.97  ------ Selected
% 3.81/0.97  
% 3.81/0.97  total_time:                             0.389
% 3.81/0.97  
%------------------------------------------------------------------------------
