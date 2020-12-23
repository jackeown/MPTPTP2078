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
% DateTime   : Thu Dec  3 11:48:58 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 295 expanded)
%              Number of clauses        :   54 (  86 expanded)
%              Number of leaves         :   17 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          :  180 ( 447 expanded)
%              Number of equality atoms :  107 ( 290 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).

fof(f44,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f45,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_5,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_449,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_470,plain,
    ( r1_xboole_0(k6_subset_1(X0,X1),X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_449,c_8])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_451,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_984,plain,
    ( k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_470,c_451])).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_833,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k6_subset_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_1167,plain,
    ( k6_subset_1(X0,k6_subset_1(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_984,c_833])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_463,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_2])).

cnf(c_1169,plain,
    ( k6_subset_1(X0,k6_subset_1(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1167,c_463])).

cnf(c_1289,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_470])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_443,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_450,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1743,plain,
    ( r1_xboole_0(sK0,X0) = iProver_top
    | r1_xboole_0(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_443,c_450])).

cnf(c_1896,plain,
    ( r1_xboole_0(sK0,k6_subset_1(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_1743])).

cnf(c_2081,plain,
    ( k1_setfam_1(k2_tarski(sK0,k6_subset_1(X0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1896,c_451])).

cnf(c_2507,plain,
    ( k6_subset_1(sK0,k6_subset_1(X0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2081,c_8])).

cnf(c_2513,plain,
    ( k6_subset_1(sK0,k6_subset_1(X0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2507,c_463])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_442,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_448,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_446,plain,
    ( k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2396,plain,
    ( k7_relat_1(X0,k6_subset_1(k2_xboole_0(k1_relat_1(X0),X1),X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_446])).

cnf(c_16507,plain,
    ( k7_relat_1(sK2,k6_subset_1(k2_xboole_0(k1_relat_1(sK2),X0),X1)) = k6_subset_1(sK2,k7_relat_1(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_442,c_2396])).

cnf(c_831,plain,
    ( k6_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_8])).

cnf(c_841,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_831,c_463])).

cnf(c_1066,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_470])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_445,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1418,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_445])).

cnf(c_4117,plain,
    ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_442,c_1418])).

cnf(c_1162,plain,
    ( k1_setfam_1(k2_tarski(X0,k6_subset_1(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_984])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_447,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1736,plain,
    ( k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_442,c_447])).

cnf(c_1866,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0),k6_subset_1(X1,X0)) = k7_relat_1(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1162,c_1736])).

cnf(c_4306,plain,
    ( k7_relat_1(k7_relat_1(sK2,X0),k6_subset_1(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4117,c_1866])).

cnf(c_18291,plain,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),k6_subset_1(X1,k6_subset_1(k2_xboole_0(k1_relat_1(sK2),X2),X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_16507,c_4306])).

cnf(c_21229,plain,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2513,c_18291])).

cnf(c_146,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_573,plain,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(instantiation,[status(thm)],[c_146])).

cnf(c_574,plain,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_573])).

cnf(c_145,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_163,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_13,negated_conjecture,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21229,c_574,c_163,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:11:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.23/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.23/1.49  
% 7.23/1.49  ------  iProver source info
% 7.23/1.49  
% 7.23/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.23/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.23/1.49  git: non_committed_changes: false
% 7.23/1.49  git: last_make_outside_of_git: false
% 7.23/1.49  
% 7.23/1.49  ------ 
% 7.23/1.49  ------ Parsing...
% 7.23/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.23/1.49  
% 7.23/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.23/1.49  ------ Proving...
% 7.23/1.49  ------ Problem Properties 
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  clauses                                 16
% 7.23/1.49  conjectures                             3
% 7.23/1.49  EPR                                     3
% 7.23/1.49  Horn                                    16
% 7.23/1.49  unary                                   9
% 7.23/1.49  binary                                  3
% 7.23/1.49  lits                                    27
% 7.23/1.49  lits eq                                 11
% 7.23/1.49  fd_pure                                 0
% 7.23/1.49  fd_pseudo                               0
% 7.23/1.49  fd_cond                                 0
% 7.23/1.49  fd_pseudo_cond                          0
% 7.23/1.49  AC symbols                              0
% 7.23/1.49  
% 7.23/1.49  ------ Input Options Time Limit: Unbounded
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  ------ 
% 7.23/1.49  Current options:
% 7.23/1.49  ------ 
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  ------ Proving...
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  % SZS status Theorem for theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  fof(f6,axiom,(
% 7.23/1.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f34,plain,(
% 7.23/1.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f6])).
% 7.23/1.49  
% 7.23/1.49  fof(f2,axiom,(
% 7.23/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f30,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.23/1.49    inference(cnf_transformation,[],[f2])).
% 7.23/1.49  
% 7.23/1.49  fof(f10,axiom,(
% 7.23/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f38,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.23/1.49    inference(cnf_transformation,[],[f10])).
% 7.23/1.49  
% 7.23/1.49  fof(f46,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.23/1.49    inference(definition_unfolding,[],[f30,f38])).
% 7.23/1.49  
% 7.23/1.49  fof(f51,plain,(
% 7.23/1.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1)) )),
% 7.23/1.49    inference(definition_unfolding,[],[f34,f46])).
% 7.23/1.49  
% 7.23/1.49  fof(f9,axiom,(
% 7.23/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f37,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f9])).
% 7.23/1.49  
% 7.23/1.49  fof(f52,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1)) )),
% 7.23/1.49    inference(definition_unfolding,[],[f37,f46])).
% 7.23/1.49  
% 7.23/1.49  fof(f1,axiom,(
% 7.23/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f24,plain,(
% 7.23/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.23/1.49    inference(nnf_transformation,[],[f1])).
% 7.23/1.49  
% 7.23/1.49  fof(f28,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f24])).
% 7.23/1.49  
% 7.23/1.49  fof(f48,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.23/1.49    inference(definition_unfolding,[],[f28,f38])).
% 7.23/1.49  
% 7.23/1.49  fof(f8,axiom,(
% 7.23/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f36,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f8])).
% 7.23/1.49  
% 7.23/1.49  fof(f4,axiom,(
% 7.23/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f32,plain,(
% 7.23/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.23/1.49    inference(cnf_transformation,[],[f4])).
% 7.23/1.49  
% 7.23/1.49  fof(f50,plain,(
% 7.23/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 7.23/1.49    inference(definition_unfolding,[],[f32,f46])).
% 7.23/1.49  
% 7.23/1.49  fof(f3,axiom,(
% 7.23/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f31,plain,(
% 7.23/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.23/1.49    inference(cnf_transformation,[],[f3])).
% 7.23/1.49  
% 7.23/1.49  fof(f49,plain,(
% 7.23/1.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 7.23/1.49    inference(definition_unfolding,[],[f31,f38])).
% 7.23/1.49  
% 7.23/1.49  fof(f14,conjecture,(
% 7.23/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f15,negated_conjecture,(
% 7.23/1.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 7.23/1.49    inference(negated_conjecture,[],[f14])).
% 7.23/1.49  
% 7.23/1.49  fof(f22,plain,(
% 7.23/1.49    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 7.23/1.49    inference(ennf_transformation,[],[f15])).
% 7.23/1.49  
% 7.23/1.49  fof(f23,plain,(
% 7.23/1.49    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 7.23/1.49    inference(flattening,[],[f22])).
% 7.23/1.49  
% 7.23/1.49  fof(f26,plain,(
% 7.23/1.49    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 7.23/1.49    introduced(choice_axiom,[])).
% 7.23/1.49  
% 7.23/1.49  fof(f27,plain,(
% 7.23/1.49    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 7.23/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26])).
% 7.23/1.49  
% 7.23/1.49  fof(f44,plain,(
% 7.23/1.49    r1_tarski(sK0,sK1)),
% 7.23/1.49    inference(cnf_transformation,[],[f27])).
% 7.23/1.49  
% 7.23/1.49  fof(f5,axiom,(
% 7.23/1.49    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f16,plain,(
% 7.23/1.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.23/1.49    inference(ennf_transformation,[],[f5])).
% 7.23/1.49  
% 7.23/1.49  fof(f17,plain,(
% 7.23/1.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 7.23/1.49    inference(flattening,[],[f16])).
% 7.23/1.49  
% 7.23/1.49  fof(f33,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f17])).
% 7.23/1.49  
% 7.23/1.49  fof(f43,plain,(
% 7.23/1.49    v1_relat_1(sK2)),
% 7.23/1.49    inference(cnf_transformation,[],[f27])).
% 7.23/1.49  
% 7.23/1.49  fof(f7,axiom,(
% 7.23/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f35,plain,(
% 7.23/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.23/1.49    inference(cnf_transformation,[],[f7])).
% 7.23/1.49  
% 7.23/1.49  fof(f12,axiom,(
% 7.23/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f19,plain,(
% 7.23/1.49    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 7.23/1.49    inference(ennf_transformation,[],[f12])).
% 7.23/1.49  
% 7.23/1.49  fof(f20,plain,(
% 7.23/1.49    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.23/1.49    inference(flattening,[],[f19])).
% 7.23/1.49  
% 7.23/1.49  fof(f40,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f20])).
% 7.23/1.49  
% 7.23/1.49  fof(f13,axiom,(
% 7.23/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f21,plain,(
% 7.23/1.49    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.23/1.49    inference(ennf_transformation,[],[f13])).
% 7.23/1.49  
% 7.23/1.49  fof(f25,plain,(
% 7.23/1.49    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.23/1.49    inference(nnf_transformation,[],[f21])).
% 7.23/1.49  
% 7.23/1.49  fof(f42,plain,(
% 7.23/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f25])).
% 7.23/1.49  
% 7.23/1.49  fof(f11,axiom,(
% 7.23/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.23/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.49  
% 7.23/1.49  fof(f18,plain,(
% 7.23/1.49    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.23/1.49    inference(ennf_transformation,[],[f11])).
% 7.23/1.49  
% 7.23/1.49  fof(f39,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.23/1.49    inference(cnf_transformation,[],[f18])).
% 7.23/1.49  
% 7.23/1.49  fof(f53,plain,(
% 7.23/1.49    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 7.23/1.49    inference(definition_unfolding,[],[f39,f38])).
% 7.23/1.49  
% 7.23/1.49  fof(f45,plain,(
% 7.23/1.49    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 7.23/1.49    inference(cnf_transformation,[],[f27])).
% 7.23/1.49  
% 7.23/1.49  cnf(c_5,plain,
% 7.23/1.49      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_449,plain,
% 7.23/1.49      ( r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_8,plain,
% 7.23/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_470,plain,
% 7.23/1.49      ( r1_xboole_0(k6_subset_1(X0,X1),X1) = iProver_top ),
% 7.23/1.49      inference(light_normalisation,[status(thm)],[c_449,c_8]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1,plain,
% 7.23/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.23/1.49      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.23/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_451,plain,
% 7.23/1.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 7.23/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_984,plain,
% 7.23/1.49      ( k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),X1)) = k1_xboole_0 ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_470,c_451]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_7,plain,
% 7.23/1.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_833,plain,
% 7.23/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k6_subset_1(X0,X1) ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1167,plain,
% 7.23/1.49      ( k6_subset_1(X0,k6_subset_1(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_984,c_833]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_3,plain,
% 7.23/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 7.23/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2,plain,
% 7.23/1.49      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.23/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_463,plain,
% 7.23/1.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.23/1.49      inference(light_normalisation,[status(thm)],[c_3,c_2]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1169,plain,
% 7.23/1.49      ( k6_subset_1(X0,k6_subset_1(X1,X0)) = X0 ),
% 7.23/1.49      inference(light_normalisation,[status(thm)],[c_1167,c_463]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1289,plain,
% 7.23/1.49      ( r1_xboole_0(X0,k6_subset_1(X1,X0)) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_1169,c_470]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_14,negated_conjecture,
% 7.23/1.49      ( r1_tarski(sK0,sK1) ),
% 7.23/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_443,plain,
% 7.23/1.49      ( r1_tarski(sK0,sK1) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4,plain,
% 7.23/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 7.23/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_450,plain,
% 7.23/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.23/1.49      | r1_xboole_0(X1,X2) != iProver_top
% 7.23/1.49      | r1_xboole_0(X0,X2) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1743,plain,
% 7.23/1.49      ( r1_xboole_0(sK0,X0) = iProver_top
% 7.23/1.49      | r1_xboole_0(sK1,X0) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_443,c_450]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1896,plain,
% 7.23/1.49      ( r1_xboole_0(sK0,k6_subset_1(X0,sK1)) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_1289,c_1743]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2081,plain,
% 7.23/1.49      ( k1_setfam_1(k2_tarski(sK0,k6_subset_1(X0,sK1))) = k1_xboole_0 ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_1896,c_451]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2507,plain,
% 7.23/1.49      ( k6_subset_1(sK0,k6_subset_1(X0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2081,c_8]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2513,plain,
% 7.23/1.49      ( k6_subset_1(sK0,k6_subset_1(X0,sK1)) = sK0 ),
% 7.23/1.49      inference(demodulation,[status(thm)],[c_2507,c_463]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_15,negated_conjecture,
% 7.23/1.49      ( v1_relat_1(sK2) ),
% 7.23/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_442,plain,
% 7.23/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_6,plain,
% 7.23/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_448,plain,
% 7.23/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_10,plain,
% 7.23/1.49      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.23/1.49      | ~ v1_relat_1(X0)
% 7.23/1.49      | k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2)) ),
% 7.23/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_446,plain,
% 7.23/1.49      ( k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
% 7.23/1.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_2396,plain,
% 7.23/1.49      ( k7_relat_1(X0,k6_subset_1(k2_xboole_0(k1_relat_1(X0),X1),X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_448,c_446]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_16507,plain,
% 7.23/1.49      ( k7_relat_1(sK2,k6_subset_1(k2_xboole_0(k1_relat_1(sK2),X0),X1)) = k6_subset_1(sK2,k7_relat_1(sK2,X1)) ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_442,c_2396]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_831,plain,
% 7.23/1.49      ( k6_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2,c_8]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_841,plain,
% 7.23/1.49      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 7.23/1.49      inference(light_normalisation,[status(thm)],[c_831,c_463]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1066,plain,
% 7.23/1.49      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_841,c_470]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_11,plain,
% 7.23/1.49      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.23/1.49      | ~ v1_relat_1(X0)
% 7.23/1.49      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.23/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_445,plain,
% 7.23/1.49      ( k7_relat_1(X0,X1) = k1_xboole_0
% 7.23/1.49      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1418,plain,
% 7.23/1.49      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_1066,c_445]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4117,plain,
% 7.23/1.49      ( k7_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_442,c_1418]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1162,plain,
% 7.23/1.49      ( k1_setfam_1(k2_tarski(X0,k6_subset_1(X1,X0))) = k1_xboole_0 ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_7,c_984]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_9,plain,
% 7.23/1.49      ( ~ v1_relat_1(X0)
% 7.23/1.49      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.23/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_447,plain,
% 7.23/1.49      ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 7.23/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1736,plain,
% 7.23/1.49      ( k7_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK2,X0),X1) ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_442,c_447]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_1866,plain,
% 7.23/1.49      ( k7_relat_1(k7_relat_1(sK2,X0),k6_subset_1(X1,X0)) = k7_relat_1(sK2,k1_xboole_0) ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_1162,c_1736]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_4306,plain,
% 7.23/1.49      ( k7_relat_1(k7_relat_1(sK2,X0),k6_subset_1(X1,X0)) = k1_xboole_0 ),
% 7.23/1.49      inference(demodulation,[status(thm)],[c_4117,c_1866]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_18291,plain,
% 7.23/1.49      ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,X0)),k6_subset_1(X1,k6_subset_1(k2_xboole_0(k1_relat_1(sK2),X2),X0))) = k1_xboole_0 ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_16507,c_4306]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_21229,plain,
% 7.23/1.49      ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) = k1_xboole_0 ),
% 7.23/1.49      inference(superposition,[status(thm)],[c_2513,c_18291]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_146,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_573,plain,
% 7.23/1.49      ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != X0
% 7.23/1.49      | k1_xboole_0 != X0
% 7.23/1.49      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_146]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_574,plain,
% 7.23/1.49      ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0
% 7.23/1.49      | k1_xboole_0 = k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
% 7.23/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_573]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_145,plain,( X0 = X0 ),theory(equality) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_163,plain,
% 7.23/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.23/1.49      inference(instantiation,[status(thm)],[c_145]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(c_13,negated_conjecture,
% 7.23/1.49      ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
% 7.23/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.23/1.49  
% 7.23/1.49  cnf(contradiction,plain,
% 7.23/1.49      ( $false ),
% 7.23/1.49      inference(minisat,[status(thm)],[c_21229,c_574,c_163,c_13]) ).
% 7.23/1.49  
% 7.23/1.49  
% 7.23/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.23/1.49  
% 7.23/1.49  ------                               Statistics
% 7.23/1.49  
% 7.23/1.49  ------ Selected
% 7.23/1.49  
% 7.23/1.49  total_time:                             0.744
% 7.23/1.49  
%------------------------------------------------------------------------------
