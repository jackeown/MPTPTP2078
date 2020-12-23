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
% DateTime   : Thu Dec  3 12:09:13 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  107 (1025 expanded)
%              Number of clauses        :   69 ( 325 expanded)
%              Number of leaves         :   14 ( 267 expanded)
%              Depth                    :   24
%              Number of atoms          :  162 (1401 expanded)
%              Number of equality atoms :  115 (1011 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29])).

fof(f49,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f54,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f47,f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f37,f37])).

fof(f48,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f46,f51])).

fof(f50,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_431,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_434,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1510,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_434])).

cnf(c_11,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_23,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10881,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1510,c_23])).

cnf(c_10882,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10881])).

cnf(c_10889,plain,
    ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_431,c_10882])).

cnf(c_13,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_433,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_862,plain,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_433])).

cnf(c_924,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_862])).

cnf(c_936,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),k6_relat_1(X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_924])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_435,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3953,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_433,c_435])).

cnf(c_3955,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ),
    inference(superposition,[status(thm)],[c_862,c_435])).

cnf(c_3960,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(demodulation,[status(thm)],[c_3953,c_3955])).

cnf(c_4156,plain,
    ( v1_relat_1(k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_936,c_3953,c_3960])).

cnf(c_11865,plain,
    ( v1_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),k6_relat_1(X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10889,c_4156])).

cnf(c_6,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_864,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_6])).

cnf(c_2540,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k2_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_13,c_864])).

cnf(c_4,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_860,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_4,c_13])).

cnf(c_1615,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_860,c_6])).

cnf(c_2705,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) ),
    inference(superposition,[status(thm)],[c_13,c_1615])).

cnf(c_7826,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_2540,c_2705,c_3953])).

cnf(c_7850,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k6_relat_1(k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X0)))) ),
    inference(superposition,[status(thm)],[c_7826,c_860])).

cnf(c_863,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_13,c_7])).

cnf(c_7854,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) ),
    inference(superposition,[status(thm)],[c_7826,c_863])).

cnf(c_2560,plain,
    ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_864,c_13])).

cnf(c_3588,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_2560,c_863])).

cnf(c_3598,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ),
    inference(superposition,[status(thm)],[c_2560,c_1615])).

cnf(c_3617,plain,
    ( k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ),
    inference(demodulation,[status(thm)],[c_3588,c_3598])).

cnf(c_7861,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_7854,c_860,c_3617])).

cnf(c_7862,plain,
    ( k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) ),
    inference(demodulation,[status(thm)],[c_7861,c_3953,c_3960])).

cnf(c_8121,plain,
    ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))) ),
    inference(demodulation,[status(thm)],[c_7850,c_860,c_3953,c_7862])).

cnf(c_8122,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_8121,c_3953,c_3960])).

cnf(c_7852,plain,
    ( k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k6_relat_1(X2)) = k6_relat_1(k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)))) ),
    inference(superposition,[status(thm)],[c_7826,c_13])).

cnf(c_8117,plain,
    ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))) ),
    inference(light_normalisation,[status(thm)],[c_7852,c_860,c_7862])).

cnf(c_8118,plain,
    ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) ),
    inference(demodulation,[status(thm)],[c_8117,c_3953])).

cnf(c_8123,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_8122,c_8118])).

cnf(c_11874,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11865,c_8123])).

cnf(c_13240,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10889,c_11874])).

cnf(c_13592,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X1),X0) ),
    inference(superposition,[status(thm)],[c_13240,c_435])).

cnf(c_15022,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_10889,c_13592])).

cnf(c_15025,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k10_relat_1(sK0,sK2))) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0) ),
    inference(light_normalisation,[status(thm)],[c_15022,c_10889])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_430,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_432,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_857,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_430,c_432])).

cnf(c_1054,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(superposition,[status(thm)],[c_4,c_857])).

cnf(c_1140,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k10_relat_1(sK0,X1))) = k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)) ),
    inference(superposition,[status(thm)],[c_1054,c_13])).

cnf(c_15026,plain,
    ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0) ),
    inference(demodulation,[status(thm)],[c_15025,c_1140])).

cnf(c_15268,plain,
    ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_15026,c_10889])).

cnf(c_15356,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k2_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(superposition,[status(thm)],[c_15268,c_6])).

cnf(c_15411,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_15356,c_6])).

cnf(c_230,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_526,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_231,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_457,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
    | k10_relat_1(sK0,sK2) != X0
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_482,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_14,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15411,c_526,c_482,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:25:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.86/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/1.51  
% 7.86/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.86/1.51  
% 7.86/1.51  ------  iProver source info
% 7.86/1.51  
% 7.86/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.86/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.86/1.51  git: non_committed_changes: false
% 7.86/1.51  git: last_make_outside_of_git: false
% 7.86/1.51  
% 7.86/1.51  ------ 
% 7.86/1.51  
% 7.86/1.51  ------ Input Options
% 7.86/1.51  
% 7.86/1.51  --out_options                           all
% 7.86/1.51  --tptp_safe_out                         true
% 7.86/1.51  --problem_path                          ""
% 7.86/1.51  --include_path                          ""
% 7.86/1.51  --clausifier                            res/vclausify_rel
% 7.86/1.51  --clausifier_options                    ""
% 7.86/1.51  --stdin                                 false
% 7.86/1.51  --stats_out                             all
% 7.86/1.51  
% 7.86/1.51  ------ General Options
% 7.86/1.51  
% 7.86/1.51  --fof                                   false
% 7.86/1.51  --time_out_real                         305.
% 7.86/1.51  --time_out_virtual                      -1.
% 7.86/1.51  --symbol_type_check                     false
% 7.86/1.51  --clausify_out                          false
% 7.86/1.51  --sig_cnt_out                           false
% 7.86/1.51  --trig_cnt_out                          false
% 7.86/1.51  --trig_cnt_out_tolerance                1.
% 7.86/1.51  --trig_cnt_out_sk_spl                   false
% 7.86/1.51  --abstr_cl_out                          false
% 7.86/1.51  
% 7.86/1.51  ------ Global Options
% 7.86/1.51  
% 7.86/1.51  --schedule                              default
% 7.86/1.51  --add_important_lit                     false
% 7.86/1.51  --prop_solver_per_cl                    1000
% 7.86/1.51  --min_unsat_core                        false
% 7.86/1.51  --soft_assumptions                      false
% 7.86/1.51  --soft_lemma_size                       3
% 7.86/1.51  --prop_impl_unit_size                   0
% 7.86/1.51  --prop_impl_unit                        []
% 7.86/1.51  --share_sel_clauses                     true
% 7.86/1.51  --reset_solvers                         false
% 7.86/1.51  --bc_imp_inh                            [conj_cone]
% 7.86/1.51  --conj_cone_tolerance                   3.
% 7.86/1.51  --extra_neg_conj                        none
% 7.86/1.51  --large_theory_mode                     true
% 7.86/1.51  --prolific_symb_bound                   200
% 7.86/1.51  --lt_threshold                          2000
% 7.86/1.51  --clause_weak_htbl                      true
% 7.86/1.51  --gc_record_bc_elim                     false
% 7.86/1.51  
% 7.86/1.51  ------ Preprocessing Options
% 7.86/1.51  
% 7.86/1.51  --preprocessing_flag                    true
% 7.86/1.51  --time_out_prep_mult                    0.1
% 7.86/1.51  --splitting_mode                        input
% 7.86/1.51  --splitting_grd                         true
% 7.86/1.51  --splitting_cvd                         false
% 7.86/1.51  --splitting_cvd_svl                     false
% 7.86/1.51  --splitting_nvd                         32
% 7.86/1.51  --sub_typing                            true
% 7.86/1.51  --prep_gs_sim                           true
% 7.86/1.51  --prep_unflatten                        true
% 7.86/1.51  --prep_res_sim                          true
% 7.86/1.51  --prep_upred                            true
% 7.86/1.51  --prep_sem_filter                       exhaustive
% 7.86/1.51  --prep_sem_filter_out                   false
% 7.86/1.51  --pred_elim                             true
% 7.86/1.51  --res_sim_input                         true
% 7.86/1.51  --eq_ax_congr_red                       true
% 7.86/1.51  --pure_diseq_elim                       true
% 7.86/1.51  --brand_transform                       false
% 7.86/1.51  --non_eq_to_eq                          false
% 7.86/1.51  --prep_def_merge                        true
% 7.86/1.51  --prep_def_merge_prop_impl              false
% 7.86/1.51  --prep_def_merge_mbd                    true
% 7.86/1.51  --prep_def_merge_tr_red                 false
% 7.86/1.51  --prep_def_merge_tr_cl                  false
% 7.86/1.51  --smt_preprocessing                     true
% 7.86/1.51  --smt_ac_axioms                         fast
% 7.86/1.51  --preprocessed_out                      false
% 7.86/1.51  --preprocessed_stats                    false
% 7.86/1.51  
% 7.86/1.51  ------ Abstraction refinement Options
% 7.86/1.51  
% 7.86/1.51  --abstr_ref                             []
% 7.86/1.51  --abstr_ref_prep                        false
% 7.86/1.51  --abstr_ref_until_sat                   false
% 7.86/1.51  --abstr_ref_sig_restrict                funpre
% 7.86/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.86/1.51  --abstr_ref_under                       []
% 7.86/1.51  
% 7.86/1.51  ------ SAT Options
% 7.86/1.51  
% 7.86/1.51  --sat_mode                              false
% 7.86/1.51  --sat_fm_restart_options                ""
% 7.86/1.51  --sat_gr_def                            false
% 7.86/1.51  --sat_epr_types                         true
% 7.86/1.51  --sat_non_cyclic_types                  false
% 7.86/1.51  --sat_finite_models                     false
% 7.86/1.51  --sat_fm_lemmas                         false
% 7.86/1.51  --sat_fm_prep                           false
% 7.86/1.51  --sat_fm_uc_incr                        true
% 7.86/1.51  --sat_out_model                         small
% 7.86/1.51  --sat_out_clauses                       false
% 7.86/1.51  
% 7.86/1.51  ------ QBF Options
% 7.86/1.51  
% 7.86/1.51  --qbf_mode                              false
% 7.86/1.51  --qbf_elim_univ                         false
% 7.86/1.51  --qbf_dom_inst                          none
% 7.86/1.51  --qbf_dom_pre_inst                      false
% 7.86/1.51  --qbf_sk_in                             false
% 7.86/1.51  --qbf_pred_elim                         true
% 7.86/1.51  --qbf_split                             512
% 7.86/1.51  
% 7.86/1.51  ------ BMC1 Options
% 7.86/1.51  
% 7.86/1.51  --bmc1_incremental                      false
% 7.86/1.51  --bmc1_axioms                           reachable_all
% 7.86/1.51  --bmc1_min_bound                        0
% 7.86/1.51  --bmc1_max_bound                        -1
% 7.86/1.51  --bmc1_max_bound_default                -1
% 7.86/1.51  --bmc1_symbol_reachability              true
% 7.86/1.51  --bmc1_property_lemmas                  false
% 7.86/1.51  --bmc1_k_induction                      false
% 7.86/1.51  --bmc1_non_equiv_states                 false
% 7.86/1.51  --bmc1_deadlock                         false
% 7.86/1.51  --bmc1_ucm                              false
% 7.86/1.51  --bmc1_add_unsat_core                   none
% 7.86/1.51  --bmc1_unsat_core_children              false
% 7.86/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.86/1.51  --bmc1_out_stat                         full
% 7.86/1.51  --bmc1_ground_init                      false
% 7.86/1.51  --bmc1_pre_inst_next_state              false
% 7.86/1.51  --bmc1_pre_inst_state                   false
% 7.86/1.51  --bmc1_pre_inst_reach_state             false
% 7.86/1.51  --bmc1_out_unsat_core                   false
% 7.86/1.51  --bmc1_aig_witness_out                  false
% 7.86/1.51  --bmc1_verbose                          false
% 7.86/1.51  --bmc1_dump_clauses_tptp                false
% 7.86/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.86/1.51  --bmc1_dump_file                        -
% 7.86/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.86/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.86/1.51  --bmc1_ucm_extend_mode                  1
% 7.86/1.51  --bmc1_ucm_init_mode                    2
% 7.86/1.51  --bmc1_ucm_cone_mode                    none
% 7.86/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.86/1.51  --bmc1_ucm_relax_model                  4
% 7.86/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.86/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.86/1.51  --bmc1_ucm_layered_model                none
% 7.86/1.51  --bmc1_ucm_max_lemma_size               10
% 7.86/1.51  
% 7.86/1.51  ------ AIG Options
% 7.86/1.51  
% 7.86/1.51  --aig_mode                              false
% 7.86/1.51  
% 7.86/1.51  ------ Instantiation Options
% 7.86/1.51  
% 7.86/1.51  --instantiation_flag                    true
% 7.86/1.51  --inst_sos_flag                         true
% 7.86/1.51  --inst_sos_phase                        true
% 7.86/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.86/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.86/1.51  --inst_lit_sel_side                     num_symb
% 7.86/1.51  --inst_solver_per_active                1400
% 7.86/1.51  --inst_solver_calls_frac                1.
% 7.86/1.51  --inst_passive_queue_type               priority_queues
% 7.86/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.86/1.51  --inst_passive_queues_freq              [25;2]
% 7.86/1.51  --inst_dismatching                      true
% 7.86/1.51  --inst_eager_unprocessed_to_passive     true
% 7.86/1.51  --inst_prop_sim_given                   true
% 7.86/1.51  --inst_prop_sim_new                     false
% 7.86/1.51  --inst_subs_new                         false
% 7.86/1.51  --inst_eq_res_simp                      false
% 7.86/1.51  --inst_subs_given                       false
% 7.86/1.51  --inst_orphan_elimination               true
% 7.86/1.51  --inst_learning_loop_flag               true
% 7.86/1.51  --inst_learning_start                   3000
% 7.86/1.51  --inst_learning_factor                  2
% 7.86/1.51  --inst_start_prop_sim_after_learn       3
% 7.86/1.51  --inst_sel_renew                        solver
% 7.86/1.51  --inst_lit_activity_flag                true
% 7.86/1.51  --inst_restr_to_given                   false
% 7.86/1.51  --inst_activity_threshold               500
% 7.86/1.51  --inst_out_proof                        true
% 7.86/1.51  
% 7.86/1.51  ------ Resolution Options
% 7.86/1.51  
% 7.86/1.51  --resolution_flag                       true
% 7.86/1.51  --res_lit_sel                           adaptive
% 7.86/1.51  --res_lit_sel_side                      none
% 7.86/1.51  --res_ordering                          kbo
% 7.86/1.51  --res_to_prop_solver                    active
% 7.86/1.51  --res_prop_simpl_new                    false
% 7.86/1.51  --res_prop_simpl_given                  true
% 7.86/1.51  --res_passive_queue_type                priority_queues
% 7.86/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.86/1.51  --res_passive_queues_freq               [15;5]
% 7.86/1.51  --res_forward_subs                      full
% 7.86/1.51  --res_backward_subs                     full
% 7.86/1.51  --res_forward_subs_resolution           true
% 7.86/1.51  --res_backward_subs_resolution          true
% 7.86/1.51  --res_orphan_elimination                true
% 7.86/1.51  --res_time_limit                        2.
% 7.86/1.51  --res_out_proof                         true
% 7.86/1.51  
% 7.86/1.51  ------ Superposition Options
% 7.86/1.51  
% 7.86/1.51  --superposition_flag                    true
% 7.86/1.51  --sup_passive_queue_type                priority_queues
% 7.86/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.86/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.86/1.51  --demod_completeness_check              fast
% 7.86/1.51  --demod_use_ground                      true
% 7.86/1.51  --sup_to_prop_solver                    passive
% 7.86/1.51  --sup_prop_simpl_new                    true
% 7.86/1.51  --sup_prop_simpl_given                  true
% 7.86/1.51  --sup_fun_splitting                     true
% 7.86/1.51  --sup_smt_interval                      50000
% 7.86/1.51  
% 7.86/1.51  ------ Superposition Simplification Setup
% 7.86/1.51  
% 7.86/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.86/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.86/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.86/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.86/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.86/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.86/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.86/1.51  --sup_immed_triv                        [TrivRules]
% 7.86/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.51  --sup_immed_bw_main                     []
% 7.86/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.86/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.86/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.51  --sup_input_bw                          []
% 7.86/1.51  
% 7.86/1.51  ------ Combination Options
% 7.86/1.51  
% 7.86/1.51  --comb_res_mult                         3
% 7.86/1.51  --comb_sup_mult                         2
% 7.86/1.51  --comb_inst_mult                        10
% 7.86/1.51  
% 7.86/1.51  ------ Debug Options
% 7.86/1.51  
% 7.86/1.51  --dbg_backtrace                         false
% 7.86/1.51  --dbg_dump_prop_clauses                 false
% 7.86/1.51  --dbg_dump_prop_clauses_file            -
% 7.86/1.51  --dbg_out_stat                          false
% 7.86/1.51  ------ Parsing...
% 7.86/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.86/1.51  
% 7.86/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.86/1.51  
% 7.86/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.86/1.51  
% 7.86/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.86/1.51  ------ Proving...
% 7.86/1.51  ------ Problem Properties 
% 7.86/1.51  
% 7.86/1.51  
% 7.86/1.51  clauses                                 16
% 7.86/1.51  conjectures                             3
% 7.86/1.51  EPR                                     4
% 7.86/1.51  Horn                                    16
% 7.86/1.51  unary                                   9
% 7.86/1.51  binary                                  4
% 7.86/1.51  lits                                    26
% 7.86/1.51  lits eq                                 9
% 7.86/1.51  fd_pure                                 0
% 7.86/1.51  fd_pseudo                               0
% 7.86/1.51  fd_cond                                 0
% 7.86/1.51  fd_pseudo_cond                          1
% 7.86/1.51  AC symbols                              0
% 7.86/1.51  
% 7.86/1.51  ------ Schedule dynamic 5 is on 
% 7.86/1.51  
% 7.86/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.86/1.51  
% 7.86/1.51  
% 7.86/1.51  ------ 
% 7.86/1.51  Current options:
% 7.86/1.51  ------ 
% 7.86/1.51  
% 7.86/1.51  ------ Input Options
% 7.86/1.51  
% 7.86/1.51  --out_options                           all
% 7.86/1.51  --tptp_safe_out                         true
% 7.86/1.51  --problem_path                          ""
% 7.86/1.51  --include_path                          ""
% 7.86/1.51  --clausifier                            res/vclausify_rel
% 7.86/1.51  --clausifier_options                    ""
% 7.86/1.51  --stdin                                 false
% 7.86/1.51  --stats_out                             all
% 7.86/1.51  
% 7.86/1.51  ------ General Options
% 7.86/1.51  
% 7.86/1.51  --fof                                   false
% 7.86/1.51  --time_out_real                         305.
% 7.86/1.51  --time_out_virtual                      -1.
% 7.86/1.51  --symbol_type_check                     false
% 7.86/1.51  --clausify_out                          false
% 7.86/1.51  --sig_cnt_out                           false
% 7.86/1.51  --trig_cnt_out                          false
% 7.86/1.51  --trig_cnt_out_tolerance                1.
% 7.86/1.51  --trig_cnt_out_sk_spl                   false
% 7.86/1.51  --abstr_cl_out                          false
% 7.86/1.51  
% 7.86/1.51  ------ Global Options
% 7.86/1.51  
% 7.86/1.51  --schedule                              default
% 7.86/1.51  --add_important_lit                     false
% 7.86/1.51  --prop_solver_per_cl                    1000
% 7.86/1.51  --min_unsat_core                        false
% 7.86/1.51  --soft_assumptions                      false
% 7.86/1.51  --soft_lemma_size                       3
% 7.86/1.51  --prop_impl_unit_size                   0
% 7.86/1.51  --prop_impl_unit                        []
% 7.86/1.51  --share_sel_clauses                     true
% 7.86/1.51  --reset_solvers                         false
% 7.86/1.51  --bc_imp_inh                            [conj_cone]
% 7.86/1.51  --conj_cone_tolerance                   3.
% 7.86/1.51  --extra_neg_conj                        none
% 7.86/1.51  --large_theory_mode                     true
% 7.86/1.51  --prolific_symb_bound                   200
% 7.86/1.51  --lt_threshold                          2000
% 7.86/1.51  --clause_weak_htbl                      true
% 7.86/1.51  --gc_record_bc_elim                     false
% 7.86/1.51  
% 7.86/1.51  ------ Preprocessing Options
% 7.86/1.51  
% 7.86/1.51  --preprocessing_flag                    true
% 7.86/1.51  --time_out_prep_mult                    0.1
% 7.86/1.51  --splitting_mode                        input
% 7.86/1.51  --splitting_grd                         true
% 7.86/1.51  --splitting_cvd                         false
% 7.86/1.51  --splitting_cvd_svl                     false
% 7.86/1.51  --splitting_nvd                         32
% 7.86/1.51  --sub_typing                            true
% 7.86/1.51  --prep_gs_sim                           true
% 7.86/1.51  --prep_unflatten                        true
% 7.86/1.51  --prep_res_sim                          true
% 7.86/1.51  --prep_upred                            true
% 7.86/1.51  --prep_sem_filter                       exhaustive
% 7.86/1.51  --prep_sem_filter_out                   false
% 7.86/1.51  --pred_elim                             true
% 7.86/1.51  --res_sim_input                         true
% 7.86/1.51  --eq_ax_congr_red                       true
% 7.86/1.51  --pure_diseq_elim                       true
% 7.86/1.51  --brand_transform                       false
% 7.86/1.51  --non_eq_to_eq                          false
% 7.86/1.51  --prep_def_merge                        true
% 7.86/1.51  --prep_def_merge_prop_impl              false
% 7.86/1.51  --prep_def_merge_mbd                    true
% 7.86/1.51  --prep_def_merge_tr_red                 false
% 7.86/1.51  --prep_def_merge_tr_cl                  false
% 7.86/1.51  --smt_preprocessing                     true
% 7.86/1.51  --smt_ac_axioms                         fast
% 7.86/1.51  --preprocessed_out                      false
% 7.86/1.51  --preprocessed_stats                    false
% 7.86/1.51  
% 7.86/1.51  ------ Abstraction refinement Options
% 7.86/1.51  
% 7.86/1.51  --abstr_ref                             []
% 7.86/1.51  --abstr_ref_prep                        false
% 7.86/1.51  --abstr_ref_until_sat                   false
% 7.86/1.51  --abstr_ref_sig_restrict                funpre
% 7.86/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.86/1.51  --abstr_ref_under                       []
% 7.86/1.51  
% 7.86/1.51  ------ SAT Options
% 7.86/1.51  
% 7.86/1.51  --sat_mode                              false
% 7.86/1.51  --sat_fm_restart_options                ""
% 7.86/1.51  --sat_gr_def                            false
% 7.86/1.51  --sat_epr_types                         true
% 7.86/1.51  --sat_non_cyclic_types                  false
% 7.86/1.51  --sat_finite_models                     false
% 7.86/1.51  --sat_fm_lemmas                         false
% 7.86/1.51  --sat_fm_prep                           false
% 7.86/1.51  --sat_fm_uc_incr                        true
% 7.86/1.51  --sat_out_model                         small
% 7.86/1.51  --sat_out_clauses                       false
% 7.86/1.51  
% 7.86/1.51  ------ QBF Options
% 7.86/1.51  
% 7.86/1.51  --qbf_mode                              false
% 7.86/1.51  --qbf_elim_univ                         false
% 7.86/1.51  --qbf_dom_inst                          none
% 7.86/1.51  --qbf_dom_pre_inst                      false
% 7.86/1.51  --qbf_sk_in                             false
% 7.86/1.51  --qbf_pred_elim                         true
% 7.86/1.51  --qbf_split                             512
% 7.86/1.51  
% 7.86/1.51  ------ BMC1 Options
% 7.86/1.51  
% 7.86/1.51  --bmc1_incremental                      false
% 7.86/1.51  --bmc1_axioms                           reachable_all
% 7.86/1.51  --bmc1_min_bound                        0
% 7.86/1.51  --bmc1_max_bound                        -1
% 7.86/1.51  --bmc1_max_bound_default                -1
% 7.86/1.51  --bmc1_symbol_reachability              true
% 7.86/1.51  --bmc1_property_lemmas                  false
% 7.86/1.51  --bmc1_k_induction                      false
% 7.86/1.51  --bmc1_non_equiv_states                 false
% 7.86/1.51  --bmc1_deadlock                         false
% 7.86/1.51  --bmc1_ucm                              false
% 7.86/1.51  --bmc1_add_unsat_core                   none
% 7.86/1.51  --bmc1_unsat_core_children              false
% 7.86/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.86/1.51  --bmc1_out_stat                         full
% 7.86/1.51  --bmc1_ground_init                      false
% 7.86/1.51  --bmc1_pre_inst_next_state              false
% 7.86/1.51  --bmc1_pre_inst_state                   false
% 7.86/1.51  --bmc1_pre_inst_reach_state             false
% 7.86/1.51  --bmc1_out_unsat_core                   false
% 7.86/1.51  --bmc1_aig_witness_out                  false
% 7.86/1.51  --bmc1_verbose                          false
% 7.86/1.51  --bmc1_dump_clauses_tptp                false
% 7.86/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.86/1.51  --bmc1_dump_file                        -
% 7.86/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.86/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.86/1.51  --bmc1_ucm_extend_mode                  1
% 7.86/1.51  --bmc1_ucm_init_mode                    2
% 7.86/1.51  --bmc1_ucm_cone_mode                    none
% 7.86/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.86/1.51  --bmc1_ucm_relax_model                  4
% 7.86/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.86/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.86/1.51  --bmc1_ucm_layered_model                none
% 7.86/1.51  --bmc1_ucm_max_lemma_size               10
% 7.86/1.51  
% 7.86/1.51  ------ AIG Options
% 7.86/1.51  
% 7.86/1.51  --aig_mode                              false
% 7.86/1.51  
% 7.86/1.51  ------ Instantiation Options
% 7.86/1.51  
% 7.86/1.51  --instantiation_flag                    true
% 7.86/1.51  --inst_sos_flag                         true
% 7.86/1.51  --inst_sos_phase                        true
% 7.86/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.86/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.86/1.51  --inst_lit_sel_side                     none
% 7.86/1.51  --inst_solver_per_active                1400
% 7.86/1.51  --inst_solver_calls_frac                1.
% 7.86/1.51  --inst_passive_queue_type               priority_queues
% 7.86/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.86/1.51  --inst_passive_queues_freq              [25;2]
% 7.86/1.51  --inst_dismatching                      true
% 7.86/1.51  --inst_eager_unprocessed_to_passive     true
% 7.86/1.51  --inst_prop_sim_given                   true
% 7.86/1.51  --inst_prop_sim_new                     false
% 7.86/1.51  --inst_subs_new                         false
% 7.86/1.51  --inst_eq_res_simp                      false
% 7.86/1.51  --inst_subs_given                       false
% 7.86/1.51  --inst_orphan_elimination               true
% 7.86/1.51  --inst_learning_loop_flag               true
% 7.86/1.51  --inst_learning_start                   3000
% 7.86/1.51  --inst_learning_factor                  2
% 7.86/1.51  --inst_start_prop_sim_after_learn       3
% 7.86/1.51  --inst_sel_renew                        solver
% 7.86/1.51  --inst_lit_activity_flag                true
% 7.86/1.51  --inst_restr_to_given                   false
% 7.86/1.51  --inst_activity_threshold               500
% 7.86/1.51  --inst_out_proof                        true
% 7.86/1.51  
% 7.86/1.51  ------ Resolution Options
% 7.86/1.51  
% 7.86/1.51  --resolution_flag                       false
% 7.86/1.51  --res_lit_sel                           adaptive
% 7.86/1.51  --res_lit_sel_side                      none
% 7.86/1.51  --res_ordering                          kbo
% 7.86/1.51  --res_to_prop_solver                    active
% 7.86/1.51  --res_prop_simpl_new                    false
% 7.86/1.51  --res_prop_simpl_given                  true
% 7.86/1.51  --res_passive_queue_type                priority_queues
% 7.86/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.86/1.51  --res_passive_queues_freq               [15;5]
% 7.86/1.51  --res_forward_subs                      full
% 7.86/1.51  --res_backward_subs                     full
% 7.86/1.51  --res_forward_subs_resolution           true
% 7.86/1.51  --res_backward_subs_resolution          true
% 7.86/1.51  --res_orphan_elimination                true
% 7.86/1.51  --res_time_limit                        2.
% 7.86/1.51  --res_out_proof                         true
% 7.86/1.51  
% 7.86/1.51  ------ Superposition Options
% 7.86/1.51  
% 7.86/1.51  --superposition_flag                    true
% 7.86/1.51  --sup_passive_queue_type                priority_queues
% 7.86/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.86/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.86/1.51  --demod_completeness_check              fast
% 7.86/1.51  --demod_use_ground                      true
% 7.86/1.51  --sup_to_prop_solver                    passive
% 7.86/1.51  --sup_prop_simpl_new                    true
% 7.86/1.51  --sup_prop_simpl_given                  true
% 7.86/1.51  --sup_fun_splitting                     true
% 7.86/1.51  --sup_smt_interval                      50000
% 7.86/1.51  
% 7.86/1.51  ------ Superposition Simplification Setup
% 7.86/1.51  
% 7.86/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.86/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.86/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.86/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.86/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.86/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.86/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.86/1.51  --sup_immed_triv                        [TrivRules]
% 7.86/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.51  --sup_immed_bw_main                     []
% 7.86/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.86/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.86/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.86/1.51  --sup_input_bw                          []
% 7.86/1.51  
% 7.86/1.51  ------ Combination Options
% 7.86/1.51  
% 7.86/1.51  --comb_res_mult                         3
% 7.86/1.51  --comb_sup_mult                         2
% 7.86/1.51  --comb_inst_mult                        10
% 7.86/1.51  
% 7.86/1.51  ------ Debug Options
% 7.86/1.51  
% 7.86/1.51  --dbg_backtrace                         false
% 7.86/1.51  --dbg_dump_prop_clauses                 false
% 7.86/1.51  --dbg_dump_prop_clauses_file            -
% 7.86/1.51  --dbg_out_stat                          false
% 7.86/1.51  
% 7.86/1.51  
% 7.86/1.51  
% 7.86/1.51  
% 7.86/1.51  ------ Proving...
% 7.86/1.51  
% 7.86/1.51  
% 7.86/1.51  % SZS status Theorem for theBenchmark.p
% 7.86/1.51  
% 7.86/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.86/1.51  
% 7.86/1.51  fof(f14,conjecture,(
% 7.86/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f15,negated_conjecture,(
% 7.86/1.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.86/1.51    inference(negated_conjecture,[],[f14])).
% 7.86/1.51  
% 7.86/1.51  fof(f16,plain,(
% 7.86/1.51    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.86/1.51    inference(pure_predicate_removal,[],[f15])).
% 7.86/1.51  
% 7.86/1.51  fof(f26,plain,(
% 7.86/1.51    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 7.86/1.51    inference(ennf_transformation,[],[f16])).
% 7.86/1.51  
% 7.86/1.51  fof(f30,plain,(
% 7.86/1.51    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 7.86/1.51    introduced(choice_axiom,[])).
% 7.86/1.51  
% 7.86/1.51  fof(f29,plain,(
% 7.86/1.51    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 7.86/1.51    introduced(choice_axiom,[])).
% 7.86/1.51  
% 7.86/1.51  fof(f31,plain,(
% 7.86/1.51    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 7.86/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29])).
% 7.86/1.51  
% 7.86/1.51  fof(f49,plain,(
% 7.86/1.51    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 7.86/1.51    inference(cnf_transformation,[],[f31])).
% 7.86/1.51  
% 7.86/1.51  fof(f7,axiom,(
% 7.86/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f40,plain,(
% 7.86/1.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.86/1.51    inference(cnf_transformation,[],[f7])).
% 7.86/1.51  
% 7.86/1.51  fof(f10,axiom,(
% 7.86/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f23,plain,(
% 7.86/1.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.86/1.51    inference(ennf_transformation,[],[f10])).
% 7.86/1.51  
% 7.86/1.51  fof(f24,plain,(
% 7.86/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.86/1.51    inference(flattening,[],[f23])).
% 7.86/1.51  
% 7.86/1.51  fof(f44,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.86/1.51    inference(cnf_transformation,[],[f24])).
% 7.86/1.51  
% 7.86/1.51  fof(f11,axiom,(
% 7.86/1.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f17,plain,(
% 7.86/1.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 7.86/1.51    inference(pure_predicate_removal,[],[f11])).
% 7.86/1.51  
% 7.86/1.51  fof(f45,plain,(
% 7.86/1.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.86/1.51    inference(cnf_transformation,[],[f17])).
% 7.86/1.51  
% 7.86/1.51  fof(f13,axiom,(
% 7.86/1.51    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f47,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 7.86/1.51    inference(cnf_transformation,[],[f13])).
% 7.86/1.51  
% 7.86/1.51  fof(f5,axiom,(
% 7.86/1.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f38,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.86/1.51    inference(cnf_transformation,[],[f5])).
% 7.86/1.51  
% 7.86/1.51  fof(f4,axiom,(
% 7.86/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f37,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.86/1.51    inference(cnf_transformation,[],[f4])).
% 7.86/1.51  
% 7.86/1.51  fof(f51,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.86/1.51    inference(definition_unfolding,[],[f38,f37])).
% 7.86/1.51  
% 7.86/1.51  fof(f54,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 7.86/1.51    inference(definition_unfolding,[],[f47,f51])).
% 7.86/1.51  
% 7.86/1.51  fof(f9,axiom,(
% 7.86/1.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f22,plain,(
% 7.86/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 7.86/1.51    inference(ennf_transformation,[],[f9])).
% 7.86/1.51  
% 7.86/1.51  fof(f43,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 7.86/1.51    inference(cnf_transformation,[],[f22])).
% 7.86/1.51  
% 7.86/1.51  fof(f41,plain,(
% 7.86/1.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.86/1.51    inference(cnf_transformation,[],[f7])).
% 7.86/1.51  
% 7.86/1.51  fof(f3,axiom,(
% 7.86/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f36,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.86/1.51    inference(cnf_transformation,[],[f3])).
% 7.86/1.51  
% 7.86/1.51  fof(f52,plain,(
% 7.86/1.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.86/1.51    inference(definition_unfolding,[],[f36,f37,f37])).
% 7.86/1.51  
% 7.86/1.51  fof(f48,plain,(
% 7.86/1.51    v1_relat_1(sK0)),
% 7.86/1.51    inference(cnf_transformation,[],[f31])).
% 7.86/1.51  
% 7.86/1.51  fof(f12,axiom,(
% 7.86/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.86/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.51  
% 7.86/1.51  fof(f25,plain,(
% 7.86/1.51    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.86/1.51    inference(ennf_transformation,[],[f12])).
% 7.86/1.51  
% 7.86/1.51  fof(f46,plain,(
% 7.86/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.86/1.51    inference(cnf_transformation,[],[f25])).
% 7.86/1.51  
% 7.86/1.51  fof(f53,plain,(
% 7.86/1.51    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.86/1.51    inference(definition_unfolding,[],[f46,f51])).
% 7.86/1.51  
% 7.86/1.51  fof(f50,plain,(
% 7.86/1.51    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 7.86/1.51    inference(cnf_transformation,[],[f31])).
% 7.86/1.51  
% 7.86/1.51  cnf(c_15,negated_conjecture,
% 7.86/1.51      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 7.86/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_431,plain,
% 7.86/1.51      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 7.86/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_7,plain,
% 7.86/1.51      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.86/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_10,plain,
% 7.86/1.51      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.86/1.51      | ~ v1_relat_1(X0)
% 7.86/1.51      | k7_relat_1(X0,X1) = X0 ),
% 7.86/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_434,plain,
% 7.86/1.51      ( k7_relat_1(X0,X1) = X0
% 7.86/1.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.86/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.86/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_1510,plain,
% 7.86/1.51      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.86/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.86/1.51      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_7,c_434]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_11,plain,
% 7.86/1.51      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.86/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_23,plain,
% 7.86/1.51      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.86/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_10881,plain,
% 7.86/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.86/1.51      | k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0) ),
% 7.86/1.51      inference(global_propositional_subsumption,
% 7.86/1.51                [status(thm)],
% 7.86/1.51                [c_1510,c_23]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_10882,plain,
% 7.86/1.51      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X0)
% 7.86/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.86/1.51      inference(renaming,[status(thm)],[c_10881]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_10889,plain,
% 7.86/1.51      ( k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_431,c_10882]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_13,plain,
% 7.86/1.51      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 7.86/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_433,plain,
% 7.86/1.51      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.86/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_862,plain,
% 7.86/1.51      ( v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = iProver_top ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_13,c_433]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_924,plain,
% 7.86/1.51      ( v1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) = iProver_top ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_13,c_862]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_936,plain,
% 7.86/1.51      ( v1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))),k6_relat_1(X3))) = iProver_top ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_13,c_924]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_9,plain,
% 7.86/1.51      ( ~ v1_relat_1(X0)
% 7.86/1.51      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.86/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_435,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.86/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.86/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_3953,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_433,c_435]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_3955,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_862,c_435]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_3960,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_3953,c_3955]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_4156,plain,
% 7.86/1.51      ( v1_relat_1(k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3))) = iProver_top ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_936,c_3953,c_3960]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_11865,plain,
% 7.86/1.51      ( v1_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),k6_relat_1(X1))) = iProver_top ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_10889,c_4156]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_6,plain,
% 7.86/1.51      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.86/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_864,plain,
% 7.86/1.51      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_13,c_6]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_2540,plain,
% 7.86/1.51      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k2_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)),k6_relat_1(X0))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_13,c_864]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_4,plain,
% 7.86/1.51      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 7.86/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_860,plain,
% 7.86/1.51      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_4,c_13]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_1615,plain,
% 7.86/1.51      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_860,c_6]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_2705,plain,
% 7.86/1.51      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_13,c_1615]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_7826,plain,
% 7.86/1.51      ( k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X0))) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_2540,c_2705,c_3953]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_7850,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k6_relat_1(k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X0)))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_7826,c_860]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_863,plain,
% 7.86/1.51      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_13,c_7]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_7854,plain,
% 7.86/1.51      ( k1_relat_1(k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_7826,c_863]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_2560,plain,
% 7.86/1.51      ( k6_relat_1(k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_864,c_13]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_3588,plain,
% 7.86/1.51      ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),k6_relat_1(X0))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_2560,c_863]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_3598,plain,
% 7.86/1.51      ( k1_setfam_1(k1_enumset1(X0,X0,k2_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_2560,c_1615]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_3617,plain,
% 7.86/1.51      ( k1_relat_1(k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) = k2_relat_1(k5_relat_1(k6_relat_1(X2),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_3588,c_3598]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_7861,plain,
% 7.86/1.51      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))) = k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X1),X2),k6_relat_1(X0))) ),
% 7.86/1.51      inference(light_normalisation,[status(thm)],[c_7854,c_860,c_3617]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_7862,plain,
% 7.86/1.51      ( k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2))) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_7861,c_3953,c_3960]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_8121,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0))) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_7850,c_860,c_3953,c_7862]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_8122,plain,
% 7.86/1.51      ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_8121,c_3953,c_3960]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_7852,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k6_relat_1(X2)) = k6_relat_1(k2_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_7826,c_13]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_8117,plain,
% 7.86/1.51      ( k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2))) ),
% 7.86/1.51      inference(light_normalisation,[status(thm)],[c_7852,c_860,c_7862]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_8118,plain,
% 7.86/1.51      ( k6_relat_1(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2))) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_8117,c_3953]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_8123,plain,
% 7.86/1.51      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_8122,c_8118]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_11874,plain,
% 7.86/1.51      ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0),X1)) = iProver_top ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_11865,c_8123]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_13240,plain,
% 7.86/1.51      ( v1_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0)) = iProver_top ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_10889,c_11874]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_13592,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X1),X0) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_13240,c_435]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_15022,plain,
% 7.86/1.51      ( k7_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1),X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k10_relat_1(sK0,sK2))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_10889,c_13592]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_15025,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k10_relat_1(sK0,sK2))) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0) ),
% 7.86/1.51      inference(light_normalisation,[status(thm)],[c_15022,c_10889]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_16,negated_conjecture,
% 7.86/1.51      ( v1_relat_1(sK0) ),
% 7.86/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_430,plain,
% 7.86/1.51      ( v1_relat_1(sK0) = iProver_top ),
% 7.86/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_12,plain,
% 7.86/1.51      ( ~ v1_relat_1(X0)
% 7.86/1.51      | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.86/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_432,plain,
% 7.86/1.51      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.86/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.86/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_857,plain,
% 7.86/1.51      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_430,c_432]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_1054,plain,
% 7.86/1.51      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_4,c_857]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_1140,plain,
% 7.86/1.51      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(k10_relat_1(sK0,X1))) = k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_1054,c_13]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_15026,plain,
% 7.86/1.51      ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),X0) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_15025,c_1140]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_15268,plain,
% 7.86/1.51      ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = k6_relat_1(k10_relat_1(sK0,sK2)) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_15026,c_10889]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_15356,plain,
% 7.86/1.51      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k2_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
% 7.86/1.51      inference(superposition,[status(thm)],[c_15268,c_6]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_15411,plain,
% 7.86/1.51      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 7.86/1.51      inference(demodulation,[status(thm)],[c_15356,c_6]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_230,plain,( X0 = X0 ),theory(equality) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_526,plain,
% 7.86/1.51      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 7.86/1.51      inference(instantiation,[status(thm)],[c_230]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_231,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_457,plain,
% 7.86/1.51      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
% 7.86/1.51      | k10_relat_1(sK0,sK2) != X0
% 7.86/1.51      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.86/1.51      inference(instantiation,[status(thm)],[c_231]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_482,plain,
% 7.86/1.51      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
% 7.86/1.51      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 7.86/1.51      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 7.86/1.51      inference(instantiation,[status(thm)],[c_457]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(c_14,negated_conjecture,
% 7.86/1.51      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.86/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.86/1.51  
% 7.86/1.51  cnf(contradiction,plain,
% 7.86/1.51      ( $false ),
% 7.86/1.51      inference(minisat,[status(thm)],[c_15411,c_526,c_482,c_14]) ).
% 7.86/1.51  
% 7.86/1.51  
% 7.86/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.86/1.51  
% 7.86/1.51  ------                               Statistics
% 7.86/1.51  
% 7.86/1.51  ------ General
% 7.86/1.51  
% 7.86/1.51  abstr_ref_over_cycles:                  0
% 7.86/1.51  abstr_ref_under_cycles:                 0
% 7.86/1.51  gc_basic_clause_elim:                   0
% 7.86/1.51  forced_gc_time:                         0
% 7.86/1.51  parsing_time:                           0.013
% 7.86/1.51  unif_index_cands_time:                  0.
% 7.86/1.51  unif_index_add_time:                    0.
% 7.86/1.51  orderings_time:                         0.
% 7.86/1.51  out_proof_time:                         0.015
% 7.86/1.51  total_time:                             0.91
% 7.86/1.51  num_of_symbols:                         44
% 7.86/1.51  num_of_terms:                           26006
% 7.86/1.51  
% 7.86/1.51  ------ Preprocessing
% 7.86/1.51  
% 7.86/1.51  num_of_splits:                          0
% 7.86/1.51  num_of_split_atoms:                     0
% 7.86/1.51  num_of_reused_defs:                     0
% 7.86/1.51  num_eq_ax_congr_red:                    6
% 7.86/1.51  num_of_sem_filtered_clauses:            1
% 7.86/1.51  num_of_subtypes:                        0
% 7.86/1.51  monotx_restored_types:                  0
% 7.86/1.51  sat_num_of_epr_types:                   0
% 7.86/1.51  sat_num_of_non_cyclic_types:            0
% 7.86/1.51  sat_guarded_non_collapsed_types:        0
% 7.86/1.51  num_pure_diseq_elim:                    0
% 7.86/1.51  simp_replaced_by:                       0
% 7.86/1.51  res_preprocessed:                       89
% 7.86/1.51  prep_upred:                             0
% 7.86/1.51  prep_unflattend:                        0
% 7.86/1.51  smt_new_axioms:                         0
% 7.86/1.51  pred_elim_cands:                        2
% 7.86/1.51  pred_elim:                              0
% 7.86/1.51  pred_elim_cl:                           0
% 7.86/1.51  pred_elim_cycles:                       2
% 7.86/1.51  merged_defs:                            0
% 7.86/1.51  merged_defs_ncl:                        0
% 7.86/1.51  bin_hyper_res:                          0
% 7.86/1.51  prep_cycles:                            4
% 7.86/1.51  pred_elim_time:                         0.
% 7.86/1.51  splitting_time:                         0.
% 7.86/1.51  sem_filter_time:                        0.
% 7.86/1.51  monotx_time:                            0.
% 7.86/1.51  subtype_inf_time:                       0.
% 7.86/1.51  
% 7.86/1.51  ------ Problem properties
% 7.86/1.51  
% 7.86/1.51  clauses:                                16
% 7.86/1.51  conjectures:                            3
% 7.86/1.51  epr:                                    4
% 7.86/1.51  horn:                                   16
% 7.86/1.51  ground:                                 3
% 7.86/1.51  unary:                                  9
% 7.86/1.51  binary:                                 4
% 7.86/1.51  lits:                                   26
% 7.86/1.51  lits_eq:                                9
% 7.86/1.51  fd_pure:                                0
% 7.86/1.51  fd_pseudo:                              0
% 7.86/1.51  fd_cond:                                0
% 7.86/1.51  fd_pseudo_cond:                         1
% 7.86/1.51  ac_symbols:                             0
% 7.86/1.51  
% 7.86/1.51  ------ Propositional Solver
% 7.86/1.51  
% 7.86/1.51  prop_solver_calls:                      34
% 7.86/1.51  prop_fast_solver_calls:                 525
% 7.86/1.51  smt_solver_calls:                       0
% 7.86/1.51  smt_fast_solver_calls:                  0
% 7.86/1.51  prop_num_of_clauses:                    6555
% 7.86/1.51  prop_preprocess_simplified:             12317
% 7.86/1.51  prop_fo_subsumed:                       2
% 7.86/1.51  prop_solver_time:                       0.
% 7.86/1.51  smt_solver_time:                        0.
% 7.86/1.51  smt_fast_solver_time:                   0.
% 7.86/1.51  prop_fast_solver_time:                  0.
% 7.86/1.51  prop_unsat_core_time:                   0.001
% 7.86/1.51  
% 7.86/1.51  ------ QBF
% 7.86/1.51  
% 7.86/1.51  qbf_q_res:                              0
% 7.86/1.51  qbf_num_tautologies:                    0
% 7.86/1.51  qbf_prep_cycles:                        0
% 7.86/1.51  
% 7.86/1.51  ------ BMC1
% 7.86/1.51  
% 7.86/1.51  bmc1_current_bound:                     -1
% 7.86/1.51  bmc1_last_solved_bound:                 -1
% 7.86/1.51  bmc1_unsat_core_size:                   -1
% 7.86/1.51  bmc1_unsat_core_parents_size:           -1
% 7.86/1.51  bmc1_merge_next_fun:                    0
% 7.86/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.86/1.51  
% 7.86/1.51  ------ Instantiation
% 7.86/1.51  
% 7.86/1.51  inst_num_of_clauses:                    1769
% 7.86/1.51  inst_num_in_passive:                    753
% 7.86/1.51  inst_num_in_active:                     658
% 7.86/1.51  inst_num_in_unprocessed:                358
% 7.86/1.51  inst_num_of_loops:                      700
% 7.86/1.51  inst_num_of_learning_restarts:          0
% 7.86/1.51  inst_num_moves_active_passive:          38
% 7.86/1.51  inst_lit_activity:                      0
% 7.86/1.51  inst_lit_activity_moves:                0
% 7.86/1.51  inst_num_tautologies:                   0
% 7.86/1.51  inst_num_prop_implied:                  0
% 7.86/1.51  inst_num_existing_simplified:           0
% 7.86/1.51  inst_num_eq_res_simplified:             0
% 7.86/1.51  inst_num_child_elim:                    0
% 7.86/1.51  inst_num_of_dismatching_blockings:      919
% 7.86/1.51  inst_num_of_non_proper_insts:           2412
% 7.86/1.51  inst_num_of_duplicates:                 0
% 7.86/1.51  inst_inst_num_from_inst_to_res:         0
% 7.86/1.51  inst_dismatching_checking_time:         0.
% 7.86/1.51  
% 7.86/1.51  ------ Resolution
% 7.86/1.51  
% 7.86/1.51  res_num_of_clauses:                     0
% 7.86/1.51  res_num_in_passive:                     0
% 7.86/1.51  res_num_in_active:                      0
% 7.86/1.51  res_num_of_loops:                       93
% 7.86/1.51  res_forward_subset_subsumed:            384
% 7.86/1.51  res_backward_subset_subsumed:           0
% 7.86/1.51  res_forward_subsumed:                   0
% 7.86/1.51  res_backward_subsumed:                  0
% 7.86/1.51  res_forward_subsumption_resolution:     0
% 7.86/1.51  res_backward_subsumption_resolution:    0
% 7.86/1.51  res_clause_to_clause_subsumption:       2739
% 7.86/1.51  res_orphan_elimination:                 0
% 7.86/1.51  res_tautology_del:                      296
% 7.86/1.51  res_num_eq_res_simplified:              0
% 7.86/1.51  res_num_sel_changes:                    0
% 7.86/1.51  res_moves_from_active_to_pass:          0
% 7.86/1.51  
% 7.86/1.51  ------ Superposition
% 7.86/1.51  
% 7.86/1.51  sup_time_total:                         0.
% 7.86/1.51  sup_time_generating:                    0.
% 7.86/1.51  sup_time_sim_full:                      0.
% 7.86/1.51  sup_time_sim_immed:                     0.
% 7.86/1.51  
% 7.86/1.51  sup_num_of_clauses:                     867
% 7.86/1.51  sup_num_in_active:                      131
% 7.86/1.51  sup_num_in_passive:                     736
% 7.86/1.51  sup_num_of_loops:                       139
% 7.86/1.51  sup_fw_superposition:                   1943
% 7.86/1.51  sup_bw_superposition:                   1095
% 7.86/1.51  sup_immediate_simplified:               787
% 7.86/1.51  sup_given_eliminated:                   3
% 7.86/1.51  comparisons_done:                       0
% 7.86/1.51  comparisons_avoided:                    0
% 7.86/1.51  
% 7.86/1.51  ------ Simplifications
% 7.86/1.51  
% 7.86/1.51  
% 7.86/1.51  sim_fw_subset_subsumed:                 3
% 7.86/1.51  sim_bw_subset_subsumed:                 1
% 7.86/1.51  sim_fw_subsumed:                        368
% 7.86/1.51  sim_bw_subsumed:                        0
% 7.86/1.51  sim_fw_subsumption_res:                 0
% 7.86/1.51  sim_bw_subsumption_res:                 0
% 7.86/1.51  sim_tautology_del:                      2
% 7.86/1.51  sim_eq_tautology_del:                   61
% 7.86/1.51  sim_eq_res_simp:                        0
% 7.86/1.51  sim_fw_demodulated:                     405
% 7.86/1.51  sim_bw_demodulated:                     60
% 7.86/1.51  sim_light_normalised:                   175
% 7.86/1.51  sim_joinable_taut:                      0
% 7.86/1.51  sim_joinable_simp:                      0
% 7.86/1.51  sim_ac_normalised:                      0
% 7.86/1.51  sim_smt_subsumption:                    0
% 7.86/1.51  
%------------------------------------------------------------------------------
