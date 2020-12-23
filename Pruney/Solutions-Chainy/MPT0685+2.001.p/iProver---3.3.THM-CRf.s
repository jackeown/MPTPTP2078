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
% DateTime   : Thu Dec  3 11:51:26 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 443 expanded)
%              Number of clauses        :   43 ( 138 expanded)
%              Number of leaves         :   18 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 601 expanded)
%              Number of equality atoms :  101 ( 396 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f52,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f51,f51])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f28,f51])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f28])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).

fof(f46,plain,(
    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(definition_unfolding,[],[f46,f28])).

fof(f45,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_237,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_242,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_785,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_237,c_242])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_238,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_402,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_237,c_238])).

cnf(c_1274,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_785,c_402])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_747,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_239,plain,
    ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_722,plain,
    ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_237,c_239])).

cnf(c_6,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_727,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(light_normalisation,[status(thm)],[c_722,c_6])).

cnf(c_1241,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_747,c_727])).

cnf(c_2926,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(demodulation,[status(thm)],[c_1274,c_1241])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_240,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1225,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_237,c_240])).

cnf(c_1984,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_237,c_1225])).

cnf(c_1990,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_1984,c_785])).

cnf(c_1991,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1990,c_6])).

cnf(c_2947,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_2926,c_1991])).

cnf(c_3370,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_2947])).

cnf(c_3413,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_3370,c_2947])).

cnf(c_10,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_751,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_727,c_10])).

cnf(c_2929,plain,
    ( k1_relat_1(k8_relat_1(sK0,k6_relat_1(k10_relat_1(sK2,sK1)))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1274,c_751])).

cnf(c_2937,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_2929,c_1991])).

cnf(c_3418,plain,
    ( k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_3413,c_2937])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_236,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_241,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1257,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_237,c_241])).

cnf(c_2694,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ),
    inference(superposition,[status(thm)],[c_236,c_1257])).

cnf(c_403,plain,
    ( k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_236,c_238])).

cnf(c_2696,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2694,c_403])).

cnf(c_3419,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_3418,c_2696])).

cnf(c_3420,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3419])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.66/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.01  
% 2.66/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/1.01  
% 2.66/1.01  ------  iProver source info
% 2.66/1.01  
% 2.66/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.66/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/1.01  git: non_committed_changes: false
% 2.66/1.01  git: last_make_outside_of_git: false
% 2.66/1.01  
% 2.66/1.01  ------ 
% 2.66/1.01  
% 2.66/1.01  ------ Input Options
% 2.66/1.01  
% 2.66/1.01  --out_options                           all
% 2.66/1.01  --tptp_safe_out                         true
% 2.66/1.01  --problem_path                          ""
% 2.66/1.01  --include_path                          ""
% 2.66/1.01  --clausifier                            res/vclausify_rel
% 2.66/1.01  --clausifier_options                    --mode clausify
% 2.66/1.01  --stdin                                 false
% 2.66/1.01  --stats_out                             all
% 2.66/1.01  
% 2.66/1.01  ------ General Options
% 2.66/1.01  
% 2.66/1.01  --fof                                   false
% 2.66/1.01  --time_out_real                         305.
% 2.66/1.01  --time_out_virtual                      -1.
% 2.66/1.01  --symbol_type_check                     false
% 2.66/1.01  --clausify_out                          false
% 2.66/1.01  --sig_cnt_out                           false
% 2.66/1.01  --trig_cnt_out                          false
% 2.66/1.01  --trig_cnt_out_tolerance                1.
% 2.66/1.01  --trig_cnt_out_sk_spl                   false
% 2.66/1.01  --abstr_cl_out                          false
% 2.66/1.01  
% 2.66/1.01  ------ Global Options
% 2.66/1.01  
% 2.66/1.01  --schedule                              default
% 2.66/1.01  --add_important_lit                     false
% 2.66/1.01  --prop_solver_per_cl                    1000
% 2.66/1.01  --min_unsat_core                        false
% 2.66/1.01  --soft_assumptions                      false
% 2.66/1.01  --soft_lemma_size                       3
% 2.66/1.01  --prop_impl_unit_size                   0
% 2.66/1.01  --prop_impl_unit                        []
% 2.66/1.01  --share_sel_clauses                     true
% 2.66/1.01  --reset_solvers                         false
% 2.66/1.01  --bc_imp_inh                            [conj_cone]
% 2.66/1.01  --conj_cone_tolerance                   3.
% 2.66/1.01  --extra_neg_conj                        none
% 2.66/1.01  --large_theory_mode                     true
% 2.66/1.01  --prolific_symb_bound                   200
% 2.66/1.01  --lt_threshold                          2000
% 2.66/1.01  --clause_weak_htbl                      true
% 2.66/1.01  --gc_record_bc_elim                     false
% 2.66/1.01  
% 2.66/1.01  ------ Preprocessing Options
% 2.66/1.01  
% 2.66/1.01  --preprocessing_flag                    true
% 2.66/1.01  --time_out_prep_mult                    0.1
% 2.66/1.01  --splitting_mode                        input
% 2.66/1.01  --splitting_grd                         true
% 2.66/1.01  --splitting_cvd                         false
% 2.66/1.01  --splitting_cvd_svl                     false
% 2.66/1.01  --splitting_nvd                         32
% 2.66/1.01  --sub_typing                            true
% 2.66/1.01  --prep_gs_sim                           true
% 2.66/1.01  --prep_unflatten                        true
% 2.66/1.01  --prep_res_sim                          true
% 2.66/1.01  --prep_upred                            true
% 2.66/1.01  --prep_sem_filter                       exhaustive
% 2.66/1.01  --prep_sem_filter_out                   false
% 2.66/1.01  --pred_elim                             true
% 2.66/1.01  --res_sim_input                         true
% 2.66/1.01  --eq_ax_congr_red                       true
% 2.66/1.01  --pure_diseq_elim                       true
% 2.66/1.01  --brand_transform                       false
% 2.66/1.01  --non_eq_to_eq                          false
% 2.66/1.01  --prep_def_merge                        true
% 2.66/1.01  --prep_def_merge_prop_impl              false
% 2.66/1.01  --prep_def_merge_mbd                    true
% 2.66/1.01  --prep_def_merge_tr_red                 false
% 2.66/1.01  --prep_def_merge_tr_cl                  false
% 2.66/1.01  --smt_preprocessing                     true
% 2.66/1.01  --smt_ac_axioms                         fast
% 2.66/1.01  --preprocessed_out                      false
% 2.66/1.01  --preprocessed_stats                    false
% 2.66/1.01  
% 2.66/1.01  ------ Abstraction refinement Options
% 2.66/1.01  
% 2.66/1.01  --abstr_ref                             []
% 2.66/1.01  --abstr_ref_prep                        false
% 2.66/1.01  --abstr_ref_until_sat                   false
% 2.66/1.01  --abstr_ref_sig_restrict                funpre
% 2.66/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.01  --abstr_ref_under                       []
% 2.66/1.01  
% 2.66/1.01  ------ SAT Options
% 2.66/1.01  
% 2.66/1.01  --sat_mode                              false
% 2.66/1.01  --sat_fm_restart_options                ""
% 2.66/1.01  --sat_gr_def                            false
% 2.66/1.01  --sat_epr_types                         true
% 2.66/1.01  --sat_non_cyclic_types                  false
% 2.66/1.01  --sat_finite_models                     false
% 2.66/1.01  --sat_fm_lemmas                         false
% 2.66/1.01  --sat_fm_prep                           false
% 2.66/1.01  --sat_fm_uc_incr                        true
% 2.66/1.01  --sat_out_model                         small
% 2.66/1.01  --sat_out_clauses                       false
% 2.66/1.01  
% 2.66/1.01  ------ QBF Options
% 2.66/1.01  
% 2.66/1.01  --qbf_mode                              false
% 2.66/1.01  --qbf_elim_univ                         false
% 2.66/1.01  --qbf_dom_inst                          none
% 2.66/1.01  --qbf_dom_pre_inst                      false
% 2.66/1.01  --qbf_sk_in                             false
% 2.66/1.01  --qbf_pred_elim                         true
% 2.66/1.01  --qbf_split                             512
% 2.66/1.01  
% 2.66/1.01  ------ BMC1 Options
% 2.66/1.01  
% 2.66/1.01  --bmc1_incremental                      false
% 2.66/1.01  --bmc1_axioms                           reachable_all
% 2.66/1.01  --bmc1_min_bound                        0
% 2.66/1.01  --bmc1_max_bound                        -1
% 2.66/1.01  --bmc1_max_bound_default                -1
% 2.66/1.01  --bmc1_symbol_reachability              true
% 2.66/1.01  --bmc1_property_lemmas                  false
% 2.66/1.01  --bmc1_k_induction                      false
% 2.66/1.01  --bmc1_non_equiv_states                 false
% 2.66/1.01  --bmc1_deadlock                         false
% 2.66/1.01  --bmc1_ucm                              false
% 2.66/1.01  --bmc1_add_unsat_core                   none
% 2.66/1.01  --bmc1_unsat_core_children              false
% 2.66/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.01  --bmc1_out_stat                         full
% 2.66/1.01  --bmc1_ground_init                      false
% 2.66/1.01  --bmc1_pre_inst_next_state              false
% 2.66/1.01  --bmc1_pre_inst_state                   false
% 2.66/1.01  --bmc1_pre_inst_reach_state             false
% 2.66/1.01  --bmc1_out_unsat_core                   false
% 2.66/1.01  --bmc1_aig_witness_out                  false
% 2.66/1.01  --bmc1_verbose                          false
% 2.66/1.01  --bmc1_dump_clauses_tptp                false
% 2.66/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.01  --bmc1_dump_file                        -
% 2.66/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.01  --bmc1_ucm_extend_mode                  1
% 2.66/1.01  --bmc1_ucm_init_mode                    2
% 2.66/1.01  --bmc1_ucm_cone_mode                    none
% 2.66/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.01  --bmc1_ucm_relax_model                  4
% 2.66/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.01  --bmc1_ucm_layered_model                none
% 2.66/1.01  --bmc1_ucm_max_lemma_size               10
% 2.66/1.01  
% 2.66/1.01  ------ AIG Options
% 2.66/1.01  
% 2.66/1.01  --aig_mode                              false
% 2.66/1.01  
% 2.66/1.01  ------ Instantiation Options
% 2.66/1.01  
% 2.66/1.01  --instantiation_flag                    true
% 2.66/1.01  --inst_sos_flag                         false
% 2.66/1.01  --inst_sos_phase                        true
% 2.66/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.01  --inst_lit_sel_side                     num_symb
% 2.66/1.01  --inst_solver_per_active                1400
% 2.66/1.01  --inst_solver_calls_frac                1.
% 2.66/1.01  --inst_passive_queue_type               priority_queues
% 2.66/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.01  --inst_passive_queues_freq              [25;2]
% 2.66/1.01  --inst_dismatching                      true
% 2.66/1.01  --inst_eager_unprocessed_to_passive     true
% 2.66/1.01  --inst_prop_sim_given                   true
% 2.66/1.01  --inst_prop_sim_new                     false
% 2.66/1.01  --inst_subs_new                         false
% 2.66/1.01  --inst_eq_res_simp                      false
% 2.66/1.01  --inst_subs_given                       false
% 2.66/1.01  --inst_orphan_elimination               true
% 2.66/1.01  --inst_learning_loop_flag               true
% 2.66/1.01  --inst_learning_start                   3000
% 2.66/1.01  --inst_learning_factor                  2
% 2.66/1.01  --inst_start_prop_sim_after_learn       3
% 2.66/1.01  --inst_sel_renew                        solver
% 2.66/1.01  --inst_lit_activity_flag                true
% 2.66/1.01  --inst_restr_to_given                   false
% 2.66/1.01  --inst_activity_threshold               500
% 2.66/1.01  --inst_out_proof                        true
% 2.66/1.01  
% 2.66/1.01  ------ Resolution Options
% 2.66/1.01  
% 2.66/1.01  --resolution_flag                       true
% 2.66/1.01  --res_lit_sel                           adaptive
% 2.66/1.01  --res_lit_sel_side                      none
% 2.66/1.01  --res_ordering                          kbo
% 2.66/1.01  --res_to_prop_solver                    active
% 2.66/1.01  --res_prop_simpl_new                    false
% 2.66/1.01  --res_prop_simpl_given                  true
% 2.66/1.01  --res_passive_queue_type                priority_queues
% 2.66/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.01  --res_passive_queues_freq               [15;5]
% 2.66/1.01  --res_forward_subs                      full
% 2.66/1.01  --res_backward_subs                     full
% 2.66/1.01  --res_forward_subs_resolution           true
% 2.66/1.01  --res_backward_subs_resolution          true
% 2.66/1.01  --res_orphan_elimination                true
% 2.66/1.01  --res_time_limit                        2.
% 2.66/1.01  --res_out_proof                         true
% 2.66/1.01  
% 2.66/1.01  ------ Superposition Options
% 2.66/1.01  
% 2.66/1.01  --superposition_flag                    true
% 2.66/1.01  --sup_passive_queue_type                priority_queues
% 2.66/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.01  --demod_completeness_check              fast
% 2.66/1.01  --demod_use_ground                      true
% 2.66/1.01  --sup_to_prop_solver                    passive
% 2.66/1.01  --sup_prop_simpl_new                    true
% 2.66/1.01  --sup_prop_simpl_given                  true
% 2.66/1.01  --sup_fun_splitting                     false
% 2.66/1.01  --sup_smt_interval                      50000
% 2.66/1.01  
% 2.66/1.01  ------ Superposition Simplification Setup
% 2.66/1.01  
% 2.66/1.01  --sup_indices_passive                   []
% 2.66/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.01  --sup_full_bw                           [BwDemod]
% 2.66/1.01  --sup_immed_triv                        [TrivRules]
% 2.66/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.01  --sup_immed_bw_main                     []
% 2.66/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.01  
% 2.66/1.01  ------ Combination Options
% 2.66/1.01  
% 2.66/1.01  --comb_res_mult                         3
% 2.66/1.01  --comb_sup_mult                         2
% 2.66/1.01  --comb_inst_mult                        10
% 2.66/1.01  
% 2.66/1.01  ------ Debug Options
% 2.66/1.01  
% 2.66/1.01  --dbg_backtrace                         false
% 2.66/1.01  --dbg_dump_prop_clauses                 false
% 2.66/1.01  --dbg_dump_prop_clauses_file            -
% 2.66/1.01  --dbg_out_stat                          false
% 2.66/1.01  ------ Parsing...
% 2.66/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/1.01  
% 2.66/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.66/1.01  
% 2.66/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/1.01  
% 2.66/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/1.01  ------ Proving...
% 2.66/1.01  ------ Problem Properties 
% 2.66/1.01  
% 2.66/1.01  
% 2.66/1.01  clauses                                 12
% 2.66/1.01  conjectures                             2
% 2.66/1.01  EPR                                     1
% 2.66/1.01  Horn                                    12
% 2.66/1.01  unary                                   7
% 2.66/1.01  binary                                  3
% 2.66/1.01  lits                                    19
% 2.66/1.01  lits eq                                 10
% 2.66/1.01  fd_pure                                 0
% 2.66/1.01  fd_pseudo                               0
% 2.66/1.01  fd_cond                                 0
% 2.66/1.01  fd_pseudo_cond                          0
% 2.66/1.01  AC symbols                              0
% 2.66/1.01  
% 2.66/1.01  ------ Schedule dynamic 5 is on 
% 2.66/1.01  
% 2.66/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/1.01  
% 2.66/1.01  
% 2.66/1.01  ------ 
% 2.66/1.01  Current options:
% 2.66/1.01  ------ 
% 2.66/1.01  
% 2.66/1.01  ------ Input Options
% 2.66/1.01  
% 2.66/1.01  --out_options                           all
% 2.66/1.01  --tptp_safe_out                         true
% 2.66/1.01  --problem_path                          ""
% 2.66/1.01  --include_path                          ""
% 2.66/1.01  --clausifier                            res/vclausify_rel
% 2.66/1.01  --clausifier_options                    --mode clausify
% 2.66/1.01  --stdin                                 false
% 2.66/1.01  --stats_out                             all
% 2.66/1.01  
% 2.66/1.01  ------ General Options
% 2.66/1.01  
% 2.66/1.01  --fof                                   false
% 2.66/1.01  --time_out_real                         305.
% 2.66/1.01  --time_out_virtual                      -1.
% 2.66/1.01  --symbol_type_check                     false
% 2.66/1.01  --clausify_out                          false
% 2.66/1.01  --sig_cnt_out                           false
% 2.66/1.01  --trig_cnt_out                          false
% 2.66/1.01  --trig_cnt_out_tolerance                1.
% 2.66/1.01  --trig_cnt_out_sk_spl                   false
% 2.66/1.01  --abstr_cl_out                          false
% 2.66/1.01  
% 2.66/1.01  ------ Global Options
% 2.66/1.01  
% 2.66/1.01  --schedule                              default
% 2.66/1.01  --add_important_lit                     false
% 2.66/1.01  --prop_solver_per_cl                    1000
% 2.66/1.01  --min_unsat_core                        false
% 2.66/1.01  --soft_assumptions                      false
% 2.66/1.01  --soft_lemma_size                       3
% 2.66/1.01  --prop_impl_unit_size                   0
% 2.66/1.01  --prop_impl_unit                        []
% 2.66/1.01  --share_sel_clauses                     true
% 2.66/1.01  --reset_solvers                         false
% 2.66/1.01  --bc_imp_inh                            [conj_cone]
% 2.66/1.01  --conj_cone_tolerance                   3.
% 2.66/1.01  --extra_neg_conj                        none
% 2.66/1.01  --large_theory_mode                     true
% 2.66/1.01  --prolific_symb_bound                   200
% 2.66/1.01  --lt_threshold                          2000
% 2.66/1.01  --clause_weak_htbl                      true
% 2.66/1.01  --gc_record_bc_elim                     false
% 2.66/1.01  
% 2.66/1.01  ------ Preprocessing Options
% 2.66/1.01  
% 2.66/1.01  --preprocessing_flag                    true
% 2.66/1.01  --time_out_prep_mult                    0.1
% 2.66/1.01  --splitting_mode                        input
% 2.66/1.01  --splitting_grd                         true
% 2.66/1.01  --splitting_cvd                         false
% 2.66/1.01  --splitting_cvd_svl                     false
% 2.66/1.01  --splitting_nvd                         32
% 2.66/1.01  --sub_typing                            true
% 2.66/1.01  --prep_gs_sim                           true
% 2.66/1.01  --prep_unflatten                        true
% 2.66/1.01  --prep_res_sim                          true
% 2.66/1.01  --prep_upred                            true
% 2.66/1.01  --prep_sem_filter                       exhaustive
% 2.66/1.01  --prep_sem_filter_out                   false
% 2.66/1.01  --pred_elim                             true
% 2.66/1.01  --res_sim_input                         true
% 2.66/1.01  --eq_ax_congr_red                       true
% 2.66/1.01  --pure_diseq_elim                       true
% 2.66/1.01  --brand_transform                       false
% 2.66/1.01  --non_eq_to_eq                          false
% 2.66/1.01  --prep_def_merge                        true
% 2.66/1.01  --prep_def_merge_prop_impl              false
% 2.66/1.01  --prep_def_merge_mbd                    true
% 2.66/1.01  --prep_def_merge_tr_red                 false
% 2.66/1.01  --prep_def_merge_tr_cl                  false
% 2.66/1.01  --smt_preprocessing                     true
% 2.66/1.01  --smt_ac_axioms                         fast
% 2.66/1.01  --preprocessed_out                      false
% 2.66/1.01  --preprocessed_stats                    false
% 2.66/1.01  
% 2.66/1.01  ------ Abstraction refinement Options
% 2.66/1.01  
% 2.66/1.01  --abstr_ref                             []
% 2.66/1.01  --abstr_ref_prep                        false
% 2.66/1.01  --abstr_ref_until_sat                   false
% 2.66/1.01  --abstr_ref_sig_restrict                funpre
% 2.66/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.01  --abstr_ref_under                       []
% 2.66/1.01  
% 2.66/1.01  ------ SAT Options
% 2.66/1.01  
% 2.66/1.01  --sat_mode                              false
% 2.66/1.01  --sat_fm_restart_options                ""
% 2.66/1.01  --sat_gr_def                            false
% 2.66/1.01  --sat_epr_types                         true
% 2.66/1.01  --sat_non_cyclic_types                  false
% 2.66/1.01  --sat_finite_models                     false
% 2.66/1.01  --sat_fm_lemmas                         false
% 2.66/1.01  --sat_fm_prep                           false
% 2.66/1.01  --sat_fm_uc_incr                        true
% 2.66/1.01  --sat_out_model                         small
% 2.66/1.01  --sat_out_clauses                       false
% 2.66/1.01  
% 2.66/1.01  ------ QBF Options
% 2.66/1.01  
% 2.66/1.01  --qbf_mode                              false
% 2.66/1.01  --qbf_elim_univ                         false
% 2.66/1.01  --qbf_dom_inst                          none
% 2.66/1.01  --qbf_dom_pre_inst                      false
% 2.66/1.01  --qbf_sk_in                             false
% 2.66/1.01  --qbf_pred_elim                         true
% 2.66/1.01  --qbf_split                             512
% 2.66/1.01  
% 2.66/1.01  ------ BMC1 Options
% 2.66/1.01  
% 2.66/1.01  --bmc1_incremental                      false
% 2.66/1.01  --bmc1_axioms                           reachable_all
% 2.66/1.01  --bmc1_min_bound                        0
% 2.66/1.01  --bmc1_max_bound                        -1
% 2.66/1.01  --bmc1_max_bound_default                -1
% 2.66/1.01  --bmc1_symbol_reachability              true
% 2.66/1.01  --bmc1_property_lemmas                  false
% 2.66/1.01  --bmc1_k_induction                      false
% 2.66/1.01  --bmc1_non_equiv_states                 false
% 2.66/1.01  --bmc1_deadlock                         false
% 2.66/1.01  --bmc1_ucm                              false
% 2.66/1.01  --bmc1_add_unsat_core                   none
% 2.66/1.01  --bmc1_unsat_core_children              false
% 2.66/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.01  --bmc1_out_stat                         full
% 2.66/1.01  --bmc1_ground_init                      false
% 2.66/1.01  --bmc1_pre_inst_next_state              false
% 2.66/1.01  --bmc1_pre_inst_state                   false
% 2.66/1.01  --bmc1_pre_inst_reach_state             false
% 2.66/1.01  --bmc1_out_unsat_core                   false
% 2.66/1.01  --bmc1_aig_witness_out                  false
% 2.66/1.01  --bmc1_verbose                          false
% 2.66/1.01  --bmc1_dump_clauses_tptp                false
% 2.66/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.01  --bmc1_dump_file                        -
% 2.66/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.01  --bmc1_ucm_extend_mode                  1
% 2.66/1.01  --bmc1_ucm_init_mode                    2
% 2.66/1.01  --bmc1_ucm_cone_mode                    none
% 2.66/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.01  --bmc1_ucm_relax_model                  4
% 2.66/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.01  --bmc1_ucm_layered_model                none
% 2.66/1.01  --bmc1_ucm_max_lemma_size               10
% 2.66/1.01  
% 2.66/1.01  ------ AIG Options
% 2.66/1.01  
% 2.66/1.01  --aig_mode                              false
% 2.66/1.01  
% 2.66/1.01  ------ Instantiation Options
% 2.66/1.01  
% 2.66/1.01  --instantiation_flag                    true
% 2.66/1.01  --inst_sos_flag                         false
% 2.66/1.01  --inst_sos_phase                        true
% 2.66/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.01  --inst_lit_sel_side                     none
% 2.66/1.01  --inst_solver_per_active                1400
% 2.66/1.01  --inst_solver_calls_frac                1.
% 2.66/1.01  --inst_passive_queue_type               priority_queues
% 2.66/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.01  --inst_passive_queues_freq              [25;2]
% 2.66/1.01  --inst_dismatching                      true
% 2.66/1.01  --inst_eager_unprocessed_to_passive     true
% 2.66/1.01  --inst_prop_sim_given                   true
% 2.66/1.01  --inst_prop_sim_new                     false
% 2.66/1.01  --inst_subs_new                         false
% 2.66/1.01  --inst_eq_res_simp                      false
% 2.66/1.01  --inst_subs_given                       false
% 2.66/1.01  --inst_orphan_elimination               true
% 2.66/1.01  --inst_learning_loop_flag               true
% 2.66/1.01  --inst_learning_start                   3000
% 2.66/1.01  --inst_learning_factor                  2
% 2.66/1.01  --inst_start_prop_sim_after_learn       3
% 2.66/1.01  --inst_sel_renew                        solver
% 2.66/1.01  --inst_lit_activity_flag                true
% 2.66/1.01  --inst_restr_to_given                   false
% 2.66/1.01  --inst_activity_threshold               500
% 2.66/1.01  --inst_out_proof                        true
% 2.66/1.01  
% 2.66/1.01  ------ Resolution Options
% 2.66/1.01  
% 2.66/1.01  --resolution_flag                       false
% 2.66/1.01  --res_lit_sel                           adaptive
% 2.66/1.01  --res_lit_sel_side                      none
% 2.66/1.01  --res_ordering                          kbo
% 2.66/1.01  --res_to_prop_solver                    active
% 2.66/1.01  --res_prop_simpl_new                    false
% 2.66/1.01  --res_prop_simpl_given                  true
% 2.66/1.01  --res_passive_queue_type                priority_queues
% 2.66/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.01  --res_passive_queues_freq               [15;5]
% 2.66/1.01  --res_forward_subs                      full
% 2.66/1.01  --res_backward_subs                     full
% 2.66/1.01  --res_forward_subs_resolution           true
% 2.66/1.01  --res_backward_subs_resolution          true
% 2.66/1.01  --res_orphan_elimination                true
% 2.66/1.01  --res_time_limit                        2.
% 2.66/1.01  --res_out_proof                         true
% 2.66/1.01  
% 2.66/1.01  ------ Superposition Options
% 2.66/1.01  
% 2.66/1.01  --superposition_flag                    true
% 2.66/1.01  --sup_passive_queue_type                priority_queues
% 2.66/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.01  --demod_completeness_check              fast
% 2.66/1.01  --demod_use_ground                      true
% 2.66/1.01  --sup_to_prop_solver                    passive
% 2.66/1.01  --sup_prop_simpl_new                    true
% 2.66/1.01  --sup_prop_simpl_given                  true
% 2.66/1.01  --sup_fun_splitting                     false
% 2.66/1.01  --sup_smt_interval                      50000
% 2.66/1.01  
% 2.66/1.01  ------ Superposition Simplification Setup
% 2.66/1.01  
% 2.66/1.01  --sup_indices_passive                   []
% 2.66/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.01  --sup_full_bw                           [BwDemod]
% 2.66/1.01  --sup_immed_triv                        [TrivRules]
% 2.66/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.01  --sup_immed_bw_main                     []
% 2.66/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.01  
% 2.66/1.01  ------ Combination Options
% 2.66/1.01  
% 2.66/1.01  --comb_res_mult                         3
% 2.66/1.01  --comb_sup_mult                         2
% 2.66/1.01  --comb_inst_mult                        10
% 2.66/1.01  
% 2.66/1.01  ------ Debug Options
% 2.66/1.01  
% 2.66/1.01  --dbg_backtrace                         false
% 2.66/1.01  --dbg_dump_prop_clauses                 false
% 2.66/1.01  --dbg_dump_prop_clauses_file            -
% 2.66/1.01  --dbg_out_stat                          false
% 2.66/1.01  
% 2.66/1.01  
% 2.66/1.01  
% 2.66/1.01  
% 2.66/1.01  ------ Proving...
% 2.66/1.01  
% 2.66/1.01  
% 2.66/1.01  % SZS status Theorem for theBenchmark.p
% 2.66/1.01  
% 2.66/1.01   Resolution empty clause
% 2.66/1.01  
% 2.66/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/1.01  
% 2.66/1.01  fof(f2,axiom,(
% 2.66/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f29,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f2])).
% 2.66/1.01  
% 2.66/1.01  fof(f3,axiom,(
% 2.66/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f30,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f3])).
% 2.66/1.01  
% 2.66/1.01  fof(f4,axiom,(
% 2.66/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f31,plain,(
% 2.66/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f4])).
% 2.66/1.01  
% 2.66/1.01  fof(f5,axiom,(
% 2.66/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f32,plain,(
% 2.66/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f5])).
% 2.66/1.01  
% 2.66/1.01  fof(f6,axiom,(
% 2.66/1.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f33,plain,(
% 2.66/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f6])).
% 2.66/1.01  
% 2.66/1.01  fof(f7,axiom,(
% 2.66/1.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f34,plain,(
% 2.66/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f7])).
% 2.66/1.01  
% 2.66/1.01  fof(f8,axiom,(
% 2.66/1.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f35,plain,(
% 2.66/1.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f8])).
% 2.66/1.01  
% 2.66/1.01  fof(f47,plain,(
% 2.66/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.66/1.01    inference(definition_unfolding,[],[f34,f35])).
% 2.66/1.01  
% 2.66/1.01  fof(f48,plain,(
% 2.66/1.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.66/1.01    inference(definition_unfolding,[],[f33,f47])).
% 2.66/1.01  
% 2.66/1.01  fof(f49,plain,(
% 2.66/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.66/1.01    inference(definition_unfolding,[],[f32,f48])).
% 2.66/1.01  
% 2.66/1.01  fof(f50,plain,(
% 2.66/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.66/1.01    inference(definition_unfolding,[],[f31,f49])).
% 2.66/1.01  
% 2.66/1.01  fof(f51,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.66/1.01    inference(definition_unfolding,[],[f30,f50])).
% 2.66/1.01  
% 2.66/1.01  fof(f52,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 2.66/1.01    inference(definition_unfolding,[],[f29,f51,f51])).
% 2.66/1.01  
% 2.66/1.01  fof(f16,axiom,(
% 2.66/1.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f19,plain,(
% 2.66/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.66/1.01    inference(pure_predicate_removal,[],[f16])).
% 2.66/1.01  
% 2.66/1.01  fof(f44,plain,(
% 2.66/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.66/1.01    inference(cnf_transformation,[],[f19])).
% 2.66/1.01  
% 2.66/1.01  fof(f10,axiom,(
% 2.66/1.01    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f20,plain,(
% 2.66/1.01    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.66/1.01    inference(ennf_transformation,[],[f10])).
% 2.66/1.01  
% 2.66/1.01  fof(f37,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f20])).
% 2.66/1.01  
% 2.66/1.01  fof(f15,axiom,(
% 2.66/1.01    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f24,plain,(
% 2.66/1.01    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.66/1.01    inference(ennf_transformation,[],[f15])).
% 2.66/1.01  
% 2.66/1.01  fof(f43,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f24])).
% 2.66/1.01  
% 2.66/1.01  fof(f9,axiom,(
% 2.66/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f36,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.66/1.01    inference(cnf_transformation,[],[f9])).
% 2.66/1.01  
% 2.66/1.01  fof(f1,axiom,(
% 2.66/1.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f28,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f1])).
% 2.66/1.01  
% 2.66/1.01  fof(f53,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.66/1.01    inference(definition_unfolding,[],[f36,f28,f51])).
% 2.66/1.01  
% 2.66/1.01  fof(f14,axiom,(
% 2.66/1.01    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f23,plain,(
% 2.66/1.01    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.66/1.01    inference(ennf_transformation,[],[f14])).
% 2.66/1.01  
% 2.66/1.01  fof(f42,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f23])).
% 2.66/1.01  
% 2.66/1.01  fof(f54,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.66/1.01    inference(definition_unfolding,[],[f42,f28])).
% 2.66/1.01  
% 2.66/1.01  fof(f13,axiom,(
% 2.66/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f40,plain,(
% 2.66/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.66/1.01    inference(cnf_transformation,[],[f13])).
% 2.66/1.01  
% 2.66/1.01  fof(f12,axiom,(
% 2.66/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f22,plain,(
% 2.66/1.01    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.66/1.01    inference(ennf_transformation,[],[f12])).
% 2.66/1.01  
% 2.66/1.01  fof(f39,plain,(
% 2.66/1.01    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f22])).
% 2.66/1.01  
% 2.66/1.01  fof(f17,conjecture,(
% 2.66/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f18,negated_conjecture,(
% 2.66/1.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 2.66/1.01    inference(negated_conjecture,[],[f17])).
% 2.66/1.01  
% 2.66/1.01  fof(f25,plain,(
% 2.66/1.01    ? [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(X2))),
% 2.66/1.01    inference(ennf_transformation,[],[f18])).
% 2.66/1.01  
% 2.66/1.01  fof(f26,plain,(
% 2.66/1.01    ? [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(X2)) => (k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) & v1_relat_1(sK2))),
% 2.66/1.01    introduced(choice_axiom,[])).
% 2.66/1.01  
% 2.66/1.01  fof(f27,plain,(
% 2.66/1.01    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) & v1_relat_1(sK2)),
% 2.66/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).
% 2.66/1.01  
% 2.66/1.01  fof(f46,plain,(
% 2.66/1.01    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 2.66/1.01    inference(cnf_transformation,[],[f27])).
% 2.66/1.01  
% 2.66/1.01  fof(f55,plain,(
% 2.66/1.01    k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 2.66/1.01    inference(definition_unfolding,[],[f46,f28])).
% 2.66/1.01  
% 2.66/1.01  fof(f45,plain,(
% 2.66/1.01    v1_relat_1(sK2)),
% 2.66/1.01    inference(cnf_transformation,[],[f27])).
% 2.66/1.01  
% 2.66/1.01  fof(f11,axiom,(
% 2.66/1.01    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)))),
% 2.66/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.66/1.01  
% 2.66/1.01  fof(f21,plain,(
% 2.66/1.01    ! [X0,X1] : (! [X2] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.66/1.01    inference(ennf_transformation,[],[f11])).
% 2.66/1.01  
% 2.66/1.01  fof(f38,plain,(
% 2.66/1.01    ( ! [X2,X0,X1] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 2.66/1.01    inference(cnf_transformation,[],[f21])).
% 2.66/1.01  
% 2.66/1.01  cnf(c_0,plain,
% 2.66/1.01      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
% 2.66/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_9,plain,
% 2.66/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.66/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_237,plain,
% 2.66/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.66/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_2,plain,
% 2.66/1.01      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 2.66/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_242,plain,
% 2.66/1.01      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 2.66/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.66/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_785,plain,
% 2.66/1.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_237,c_242]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_8,plain,
% 2.66/1.01      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 2.66/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_238,plain,
% 2.66/1.01      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 2.66/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.66/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_402,plain,
% 2.66/1.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_237,c_238]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_1274,plain,
% 2.66/1.01      ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_785,c_402]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_1,plain,
% 2.66/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 2.66/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_747,plain,
% 2.66/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_7,plain,
% 2.66/1.01      ( ~ v1_relat_1(X0)
% 2.66/1.01      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 2.66/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_239,plain,
% 2.66/1.01      ( k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 2.66/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.66/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_722,plain,
% 2.66/1.01      ( k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_237,c_239]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_6,plain,
% 2.66/1.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.66/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_727,plain,
% 2.66/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 2.66/1.01      inference(light_normalisation,[status(thm)],[c_722,c_6]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_1241,plain,
% 2.66/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_747,c_727]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_2926,plain,
% 2.66/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_1274,c_1241]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_4,plain,
% 2.66/1.01      ( ~ v1_relat_1(X0)
% 2.66/1.01      | ~ v1_relat_1(X1)
% 2.66/1.01      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 2.66/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_240,plain,
% 2.66/1.01      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 2.66/1.01      | v1_relat_1(X1) != iProver_top
% 2.66/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.66/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_1225,plain,
% 2.66/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 2.66/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_237,c_240]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_1984,plain,
% 2.66/1.01      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_237,c_1225]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_1990,plain,
% 2.66/1.01      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 2.66/1.01      inference(light_normalisation,[status(thm)],[c_1984,c_785]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_1991,plain,
% 2.66/1.01      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X1),X0) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_1990,c_6]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_2947,plain,
% 2.66/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k10_relat_1(k6_relat_1(X0),X1) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_2926,c_1991]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_3370,plain,
% 2.66/1.01      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k10_relat_1(k6_relat_1(X1),X0) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_0,c_2947]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_3413,plain,
% 2.66/1.01      ( k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X1),X0) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_3370,c_2947]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_10,negated_conjecture,
% 2.66/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.66/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_751,plain,
% 2.66/1.01      ( k1_relat_1(k7_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_727,c_10]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_2929,plain,
% 2.66/1.01      ( k1_relat_1(k8_relat_1(sK0,k6_relat_1(k10_relat_1(sK2,sK1)))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_1274,c_751]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_2937,plain,
% 2.66/1.01      ( k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_2929,c_1991]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_3418,plain,
% 2.66/1.01      ( k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_3413,c_2937]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_11,negated_conjecture,
% 2.66/1.01      ( v1_relat_1(sK2) ),
% 2.66/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_236,plain,
% 2.66/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.66/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_3,plain,
% 2.66/1.01      ( ~ v1_relat_1(X0)
% 2.66/1.01      | ~ v1_relat_1(X1)
% 2.66/1.01      | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
% 2.66/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_241,plain,
% 2.66/1.01      ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
% 2.66/1.01      | v1_relat_1(X0) != iProver_top
% 2.66/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.66/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_1257,plain,
% 2.66/1.01      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
% 2.66/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_237,c_241]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_2694,plain,
% 2.66/1.01      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_236,c_1257]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_403,plain,
% 2.66/1.01      ( k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
% 2.66/1.01      inference(superposition,[status(thm)],[c_236,c_238]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_2696,plain,
% 2.66/1.01      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 2.66/1.01      inference(light_normalisation,[status(thm)],[c_2694,c_403]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_3419,plain,
% 2.66/1.01      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 2.66/1.01      inference(demodulation,[status(thm)],[c_3418,c_2696]) ).
% 2.66/1.01  
% 2.66/1.01  cnf(c_3420,plain,
% 2.66/1.01      ( $false ),
% 2.66/1.01      inference(equality_resolution_simp,[status(thm)],[c_3419]) ).
% 2.66/1.01  
% 2.66/1.01  
% 2.66/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/1.01  
% 2.66/1.01  ------                               Statistics
% 2.66/1.01  
% 2.66/1.01  ------ General
% 2.66/1.01  
% 2.66/1.01  abstr_ref_over_cycles:                  0
% 2.66/1.01  abstr_ref_under_cycles:                 0
% 2.66/1.01  gc_basic_clause_elim:                   0
% 2.66/1.01  forced_gc_time:                         0
% 2.66/1.01  parsing_time:                           0.015
% 2.66/1.01  unif_index_cands_time:                  0.
% 2.66/1.01  unif_index_add_time:                    0.
% 2.66/1.01  orderings_time:                         0.
% 2.66/1.01  out_proof_time:                         0.008
% 2.66/1.01  total_time:                             0.163
% 2.66/1.01  num_of_symbols:                         45
% 2.66/1.01  num_of_terms:                           5592
% 2.66/1.01  
% 2.66/1.01  ------ Preprocessing
% 2.66/1.01  
% 2.66/1.01  num_of_splits:                          0
% 2.66/1.01  num_of_split_atoms:                     0
% 2.66/1.01  num_of_reused_defs:                     0
% 2.66/1.01  num_eq_ax_congr_red:                    22
% 2.66/1.01  num_of_sem_filtered_clauses:            1
% 2.66/1.01  num_of_subtypes:                        0
% 2.66/1.01  monotx_restored_types:                  0
% 2.66/1.01  sat_num_of_epr_types:                   0
% 2.66/1.01  sat_num_of_non_cyclic_types:            0
% 2.66/1.01  sat_guarded_non_collapsed_types:        0
% 2.66/1.01  num_pure_diseq_elim:                    0
% 2.66/1.01  simp_replaced_by:                       0
% 2.66/1.01  res_preprocessed:                       57
% 2.66/1.01  prep_upred:                             0
% 2.66/1.01  prep_unflattend:                        0
% 2.66/1.01  smt_new_axioms:                         0
% 2.66/1.01  pred_elim_cands:                        1
% 2.66/1.01  pred_elim:                              0
% 2.66/1.01  pred_elim_cl:                           0
% 2.66/1.01  pred_elim_cycles:                       1
% 2.66/1.01  merged_defs:                            0
% 2.66/1.01  merged_defs_ncl:                        0
% 2.66/1.01  bin_hyper_res:                          0
% 2.66/1.01  prep_cycles:                            3
% 2.66/1.01  pred_elim_time:                         0.
% 2.66/1.01  splitting_time:                         0.
% 2.66/1.01  sem_filter_time:                        0.
% 2.66/1.01  monotx_time:                            0.
% 2.66/1.01  subtype_inf_time:                       0.
% 2.66/1.01  
% 2.66/1.01  ------ Problem properties
% 2.66/1.01  
% 2.66/1.01  clauses:                                12
% 2.66/1.01  conjectures:                            2
% 2.66/1.01  epr:                                    1
% 2.66/1.01  horn:                                   12
% 2.66/1.01  ground:                                 2
% 2.66/1.01  unary:                                  7
% 2.66/1.01  binary:                                 3
% 2.66/1.01  lits:                                   19
% 2.66/1.01  lits_eq:                                10
% 2.66/1.01  fd_pure:                                0
% 2.66/1.01  fd_pseudo:                              0
% 2.66/1.01  fd_cond:                                0
% 2.66/1.01  fd_pseudo_cond:                         0
% 2.66/1.01  ac_symbols:                             0
% 2.66/1.01  
% 2.66/1.01  ------ Propositional Solver
% 2.66/1.01  
% 2.66/1.01  prop_solver_calls:                      24
% 2.66/1.01  prop_fast_solver_calls:                 294
% 2.66/1.01  smt_solver_calls:                       0
% 2.66/1.01  smt_fast_solver_calls:                  0
% 2.66/1.01  prop_num_of_clauses:                    1667
% 2.66/1.01  prop_preprocess_simplified:             3083
% 2.66/1.01  prop_fo_subsumed:                       0
% 2.66/1.01  prop_solver_time:                       0.
% 2.66/1.01  smt_solver_time:                        0.
% 2.66/1.01  smt_fast_solver_time:                   0.
% 2.66/1.01  prop_fast_solver_time:                  0.
% 2.66/1.01  prop_unsat_core_time:                   0.
% 2.66/1.01  
% 2.66/1.01  ------ QBF
% 2.66/1.01  
% 2.66/1.01  qbf_q_res:                              0
% 2.66/1.01  qbf_num_tautologies:                    0
% 2.66/1.01  qbf_prep_cycles:                        0
% 2.66/1.01  
% 2.66/1.01  ------ BMC1
% 2.66/1.01  
% 2.66/1.01  bmc1_current_bound:                     -1
% 2.66/1.01  bmc1_last_solved_bound:                 -1
% 2.66/1.01  bmc1_unsat_core_size:                   -1
% 2.66/1.01  bmc1_unsat_core_parents_size:           -1
% 2.66/1.01  bmc1_merge_next_fun:                    0
% 2.66/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.66/1.01  
% 2.66/1.01  ------ Instantiation
% 2.66/1.01  
% 2.66/1.01  inst_num_of_clauses:                    507
% 2.66/1.01  inst_num_in_passive:                    110
% 2.66/1.01  inst_num_in_active:                     317
% 2.66/1.01  inst_num_in_unprocessed:                80
% 2.66/1.01  inst_num_of_loops:                      320
% 2.66/1.01  inst_num_of_learning_restarts:          0
% 2.66/1.01  inst_num_moves_active_passive:          0
% 2.66/1.01  inst_lit_activity:                      0
% 2.66/1.01  inst_lit_activity_moves:                0
% 2.66/1.01  inst_num_tautologies:                   0
% 2.66/1.01  inst_num_prop_implied:                  0
% 2.66/1.01  inst_num_existing_simplified:           0
% 2.66/1.01  inst_num_eq_res_simplified:             0
% 2.66/1.01  inst_num_child_elim:                    0
% 2.66/1.01  inst_num_of_dismatching_blockings:      34
% 2.66/1.01  inst_num_of_non_proper_insts:           270
% 2.66/1.01  inst_num_of_duplicates:                 0
% 2.66/1.01  inst_inst_num_from_inst_to_res:         0
% 2.66/1.01  inst_dismatching_checking_time:         0.
% 2.66/1.01  
% 2.66/1.01  ------ Resolution
% 2.66/1.01  
% 2.66/1.01  res_num_of_clauses:                     0
% 2.66/1.01  res_num_in_passive:                     0
% 2.66/1.01  res_num_in_active:                      0
% 2.66/1.01  res_num_of_loops:                       60
% 2.66/1.01  res_forward_subset_subsumed:            41
% 2.66/1.01  res_backward_subset_subsumed:           0
% 2.66/1.01  res_forward_subsumed:                   0
% 2.66/1.01  res_backward_subsumed:                  0
% 2.66/1.01  res_forward_subsumption_resolution:     0
% 2.66/1.01  res_backward_subsumption_resolution:    0
% 2.66/1.01  res_clause_to_clause_subsumption:       168
% 2.66/1.01  res_orphan_elimination:                 0
% 2.66/1.01  res_tautology_del:                      36
% 2.66/1.01  res_num_eq_res_simplified:              0
% 2.66/1.01  res_num_sel_changes:                    0
% 2.66/1.01  res_moves_from_active_to_pass:          0
% 2.66/1.01  
% 2.66/1.01  ------ Superposition
% 2.66/1.01  
% 2.66/1.01  sup_time_total:                         0.
% 2.66/1.01  sup_time_generating:                    0.
% 2.66/1.01  sup_time_sim_full:                      0.
% 2.66/1.01  sup_time_sim_immed:                     0.
% 2.66/1.01  
% 2.66/1.01  sup_num_of_clauses:                     88
% 2.66/1.01  sup_num_in_active:                      46
% 2.66/1.01  sup_num_in_passive:                     42
% 2.66/1.01  sup_num_of_loops:                       63
% 2.66/1.01  sup_fw_superposition:                   188
% 2.66/1.01  sup_bw_superposition:                   138
% 2.66/1.01  sup_immediate_simplified:               146
% 2.66/1.01  sup_given_eliminated:                   1
% 2.66/1.01  comparisons_done:                       0
% 2.66/1.01  comparisons_avoided:                    0
% 2.66/1.01  
% 2.66/1.01  ------ Simplifications
% 2.66/1.01  
% 2.66/1.01  
% 2.66/1.01  sim_fw_subset_subsumed:                 0
% 2.66/1.01  sim_bw_subset_subsumed:                 0
% 2.66/1.01  sim_fw_subsumed:                        22
% 2.66/1.01  sim_bw_subsumed:                        0
% 2.66/1.01  sim_fw_subsumption_res:                 0
% 2.66/1.01  sim_bw_subsumption_res:                 0
% 2.66/1.01  sim_tautology_del:                      0
% 2.66/1.01  sim_eq_tautology_del:                   80
% 2.66/1.01  sim_eq_res_simp:                        0
% 2.66/1.01  sim_fw_demodulated:                     79
% 2.66/1.01  sim_bw_demodulated:                     17
% 2.66/1.01  sim_light_normalised:                   117
% 2.66/1.01  sim_joinable_taut:                      0
% 2.66/1.01  sim_joinable_simp:                      0
% 2.66/1.01  sim_ac_normalised:                      0
% 2.66/1.01  sim_smt_subsumption:                    0
% 2.66/1.01  
%------------------------------------------------------------------------------
