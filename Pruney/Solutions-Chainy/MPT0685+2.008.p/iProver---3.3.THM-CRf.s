%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:27 EST 2020

% Result     : Theorem 11.44s
% Output     : CNFRefutation 11.44s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 353 expanded)
%              Number of clauses        :   45 ( 153 expanded)
%              Number of leaves         :   12 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  127 ( 513 expanded)
%              Number of equality atoms :   84 ( 317 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1)
        & v1_relat_1(X2) )
   => ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] : k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f38,f25])).

fof(f35,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f40,plain,(
    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(definition_unfolding,[],[f40,f25])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_239,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_240,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_243,plain,
    ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2372,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_240,c_243])).

cnf(c_30061,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ),
    inference(superposition,[status(thm)],[c_239,c_2372])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_241,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_700,plain,
    ( k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_239,c_241])).

cnf(c_30110,plain,
    ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_30061,c_700])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_242,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1412,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_240,c_242])).

cnf(c_14413,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_240,c_1412])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_244,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1650,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_240,c_244])).

cnf(c_14461,plain,
    ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_14413,c_1650])).

cnf(c_6,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,plain,
    ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_408,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_5])).

cnf(c_407,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_6])).

cnf(c_850,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_408,c_407])).

cnf(c_12655,plain,
    ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(light_normalisation,[status(thm)],[c_850,c_1650])).

cnf(c_14462,plain,
    ( k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_14461,c_6,c_12655])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_245,plain,
    ( k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3689,plain,
    ( k4_xboole_0(k2_relat_1(k6_relat_1(X0)),k4_xboole_0(k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_240,c_245])).

cnf(c_3718,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_3689,c_5])).

cnf(c_3815,plain,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(demodulation,[status(thm)],[c_3718,c_408])).

cnf(c_12474,plain,
    ( k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(light_normalisation,[status(thm)],[c_3815,c_1650])).

cnf(c_15008,plain,
    ( k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_14462,c_12474])).

cnf(c_15159,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_15008,c_14462])).

cnf(c_10,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3814,plain,
    ( k2_relat_1(k8_relat_1(k10_relat_1(sK2,sK1),k6_relat_1(sK0))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_3718,c_10])).

cnf(c_12477,plain,
    ( k2_relat_1(k8_relat_1(sK0,k6_relat_1(k10_relat_1(sK2,sK1)))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_12474,c_3814])).

cnf(c_15024,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_14462,c_12477])).

cnf(c_15233,plain,
    ( k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_15159,c_15024])).

cnf(c_30368,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_30110,c_15233])).

cnf(c_100,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_524,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30368,c_524])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.44/2.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.44/2.03  
% 11.44/2.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.44/2.03  
% 11.44/2.03  ------  iProver source info
% 11.44/2.03  
% 11.44/2.03  git: date: 2020-06-30 10:37:57 +0100
% 11.44/2.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.44/2.03  git: non_committed_changes: false
% 11.44/2.03  git: last_make_outside_of_git: false
% 11.44/2.03  
% 11.44/2.03  ------ 
% 11.44/2.03  
% 11.44/2.03  ------ Input Options
% 11.44/2.03  
% 11.44/2.03  --out_options                           all
% 11.44/2.03  --tptp_safe_out                         true
% 11.44/2.03  --problem_path                          ""
% 11.44/2.03  --include_path                          ""
% 11.44/2.03  --clausifier                            res/vclausify_rel
% 11.44/2.03  --clausifier_options                    --mode clausify
% 11.44/2.03  --stdin                                 false
% 11.44/2.03  --stats_out                             all
% 11.44/2.03  
% 11.44/2.03  ------ General Options
% 11.44/2.03  
% 11.44/2.03  --fof                                   false
% 11.44/2.03  --time_out_real                         305.
% 11.44/2.03  --time_out_virtual                      -1.
% 11.44/2.03  --symbol_type_check                     false
% 11.44/2.03  --clausify_out                          false
% 11.44/2.03  --sig_cnt_out                           false
% 11.44/2.03  --trig_cnt_out                          false
% 11.44/2.03  --trig_cnt_out_tolerance                1.
% 11.44/2.03  --trig_cnt_out_sk_spl                   false
% 11.44/2.03  --abstr_cl_out                          false
% 11.44/2.03  
% 11.44/2.03  ------ Global Options
% 11.44/2.03  
% 11.44/2.03  --schedule                              default
% 11.44/2.03  --add_important_lit                     false
% 11.44/2.03  --prop_solver_per_cl                    1000
% 11.44/2.03  --min_unsat_core                        false
% 11.44/2.03  --soft_assumptions                      false
% 11.44/2.03  --soft_lemma_size                       3
% 11.44/2.03  --prop_impl_unit_size                   0
% 11.44/2.03  --prop_impl_unit                        []
% 11.44/2.03  --share_sel_clauses                     true
% 11.44/2.03  --reset_solvers                         false
% 11.44/2.03  --bc_imp_inh                            [conj_cone]
% 11.44/2.03  --conj_cone_tolerance                   3.
% 11.44/2.03  --extra_neg_conj                        none
% 11.44/2.03  --large_theory_mode                     true
% 11.44/2.03  --prolific_symb_bound                   200
% 11.44/2.03  --lt_threshold                          2000
% 11.44/2.03  --clause_weak_htbl                      true
% 11.44/2.03  --gc_record_bc_elim                     false
% 11.44/2.03  
% 11.44/2.03  ------ Preprocessing Options
% 11.44/2.03  
% 11.44/2.03  --preprocessing_flag                    true
% 11.44/2.03  --time_out_prep_mult                    0.1
% 11.44/2.03  --splitting_mode                        input
% 11.44/2.03  --splitting_grd                         true
% 11.44/2.03  --splitting_cvd                         false
% 11.44/2.03  --splitting_cvd_svl                     false
% 11.44/2.03  --splitting_nvd                         32
% 11.44/2.03  --sub_typing                            true
% 11.44/2.03  --prep_gs_sim                           true
% 11.44/2.03  --prep_unflatten                        true
% 11.44/2.03  --prep_res_sim                          true
% 11.44/2.03  --prep_upred                            true
% 11.44/2.03  --prep_sem_filter                       exhaustive
% 11.44/2.03  --prep_sem_filter_out                   false
% 11.44/2.03  --pred_elim                             true
% 11.44/2.03  --res_sim_input                         true
% 11.44/2.03  --eq_ax_congr_red                       true
% 11.44/2.03  --pure_diseq_elim                       true
% 11.44/2.03  --brand_transform                       false
% 11.44/2.03  --non_eq_to_eq                          false
% 11.44/2.03  --prep_def_merge                        true
% 11.44/2.03  --prep_def_merge_prop_impl              false
% 11.44/2.03  --prep_def_merge_mbd                    true
% 11.44/2.03  --prep_def_merge_tr_red                 false
% 11.44/2.03  --prep_def_merge_tr_cl                  false
% 11.44/2.03  --smt_preprocessing                     true
% 11.44/2.03  --smt_ac_axioms                         fast
% 11.44/2.03  --preprocessed_out                      false
% 11.44/2.03  --preprocessed_stats                    false
% 11.44/2.03  
% 11.44/2.03  ------ Abstraction refinement Options
% 11.44/2.03  
% 11.44/2.03  --abstr_ref                             []
% 11.44/2.03  --abstr_ref_prep                        false
% 11.44/2.03  --abstr_ref_until_sat                   false
% 11.44/2.03  --abstr_ref_sig_restrict                funpre
% 11.44/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.44/2.03  --abstr_ref_under                       []
% 11.44/2.03  
% 11.44/2.03  ------ SAT Options
% 11.44/2.03  
% 11.44/2.03  --sat_mode                              false
% 11.44/2.03  --sat_fm_restart_options                ""
% 11.44/2.03  --sat_gr_def                            false
% 11.44/2.03  --sat_epr_types                         true
% 11.44/2.03  --sat_non_cyclic_types                  false
% 11.44/2.03  --sat_finite_models                     false
% 11.44/2.03  --sat_fm_lemmas                         false
% 11.44/2.03  --sat_fm_prep                           false
% 11.44/2.03  --sat_fm_uc_incr                        true
% 11.44/2.03  --sat_out_model                         small
% 11.44/2.03  --sat_out_clauses                       false
% 11.44/2.03  
% 11.44/2.03  ------ QBF Options
% 11.44/2.03  
% 11.44/2.03  --qbf_mode                              false
% 11.44/2.03  --qbf_elim_univ                         false
% 11.44/2.03  --qbf_dom_inst                          none
% 11.44/2.03  --qbf_dom_pre_inst                      false
% 11.44/2.03  --qbf_sk_in                             false
% 11.44/2.03  --qbf_pred_elim                         true
% 11.44/2.03  --qbf_split                             512
% 11.44/2.03  
% 11.44/2.03  ------ BMC1 Options
% 11.44/2.03  
% 11.44/2.03  --bmc1_incremental                      false
% 11.44/2.03  --bmc1_axioms                           reachable_all
% 11.44/2.03  --bmc1_min_bound                        0
% 11.44/2.03  --bmc1_max_bound                        -1
% 11.44/2.03  --bmc1_max_bound_default                -1
% 11.44/2.03  --bmc1_symbol_reachability              true
% 11.44/2.03  --bmc1_property_lemmas                  false
% 11.44/2.03  --bmc1_k_induction                      false
% 11.44/2.03  --bmc1_non_equiv_states                 false
% 11.44/2.03  --bmc1_deadlock                         false
% 11.44/2.03  --bmc1_ucm                              false
% 11.44/2.03  --bmc1_add_unsat_core                   none
% 11.44/2.03  --bmc1_unsat_core_children              false
% 11.44/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.44/2.03  --bmc1_out_stat                         full
% 11.44/2.03  --bmc1_ground_init                      false
% 11.44/2.03  --bmc1_pre_inst_next_state              false
% 11.44/2.03  --bmc1_pre_inst_state                   false
% 11.44/2.03  --bmc1_pre_inst_reach_state             false
% 11.44/2.03  --bmc1_out_unsat_core                   false
% 11.44/2.03  --bmc1_aig_witness_out                  false
% 11.44/2.03  --bmc1_verbose                          false
% 11.44/2.03  --bmc1_dump_clauses_tptp                false
% 11.44/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.44/2.03  --bmc1_dump_file                        -
% 11.44/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.44/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.44/2.03  --bmc1_ucm_extend_mode                  1
% 11.44/2.03  --bmc1_ucm_init_mode                    2
% 11.44/2.03  --bmc1_ucm_cone_mode                    none
% 11.44/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.44/2.03  --bmc1_ucm_relax_model                  4
% 11.44/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.44/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.44/2.03  --bmc1_ucm_layered_model                none
% 11.44/2.03  --bmc1_ucm_max_lemma_size               10
% 11.44/2.03  
% 11.44/2.03  ------ AIG Options
% 11.44/2.03  
% 11.44/2.03  --aig_mode                              false
% 11.44/2.03  
% 11.44/2.03  ------ Instantiation Options
% 11.44/2.03  
% 11.44/2.03  --instantiation_flag                    true
% 11.44/2.03  --inst_sos_flag                         false
% 11.44/2.03  --inst_sos_phase                        true
% 11.44/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.44/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.44/2.03  --inst_lit_sel_side                     num_symb
% 11.44/2.03  --inst_solver_per_active                1400
% 11.44/2.03  --inst_solver_calls_frac                1.
% 11.44/2.03  --inst_passive_queue_type               priority_queues
% 11.44/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.44/2.03  --inst_passive_queues_freq              [25;2]
% 11.44/2.03  --inst_dismatching                      true
% 11.44/2.03  --inst_eager_unprocessed_to_passive     true
% 11.44/2.03  --inst_prop_sim_given                   true
% 11.44/2.03  --inst_prop_sim_new                     false
% 11.44/2.03  --inst_subs_new                         false
% 11.44/2.03  --inst_eq_res_simp                      false
% 11.44/2.03  --inst_subs_given                       false
% 11.44/2.03  --inst_orphan_elimination               true
% 11.44/2.03  --inst_learning_loop_flag               true
% 11.44/2.03  --inst_learning_start                   3000
% 11.44/2.03  --inst_learning_factor                  2
% 11.44/2.03  --inst_start_prop_sim_after_learn       3
% 11.44/2.03  --inst_sel_renew                        solver
% 11.44/2.03  --inst_lit_activity_flag                true
% 11.44/2.03  --inst_restr_to_given                   false
% 11.44/2.03  --inst_activity_threshold               500
% 11.44/2.03  --inst_out_proof                        true
% 11.44/2.03  
% 11.44/2.03  ------ Resolution Options
% 11.44/2.03  
% 11.44/2.03  --resolution_flag                       true
% 11.44/2.03  --res_lit_sel                           adaptive
% 11.44/2.03  --res_lit_sel_side                      none
% 11.44/2.03  --res_ordering                          kbo
% 11.44/2.03  --res_to_prop_solver                    active
% 11.44/2.03  --res_prop_simpl_new                    false
% 11.44/2.03  --res_prop_simpl_given                  true
% 11.44/2.03  --res_passive_queue_type                priority_queues
% 11.44/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.44/2.03  --res_passive_queues_freq               [15;5]
% 11.44/2.03  --res_forward_subs                      full
% 11.44/2.03  --res_backward_subs                     full
% 11.44/2.03  --res_forward_subs_resolution           true
% 11.44/2.03  --res_backward_subs_resolution          true
% 11.44/2.03  --res_orphan_elimination                true
% 11.44/2.03  --res_time_limit                        2.
% 11.44/2.03  --res_out_proof                         true
% 11.44/2.03  
% 11.44/2.03  ------ Superposition Options
% 11.44/2.03  
% 11.44/2.03  --superposition_flag                    true
% 11.44/2.03  --sup_passive_queue_type                priority_queues
% 11.44/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.44/2.03  --sup_passive_queues_freq               [8;1;4]
% 11.44/2.03  --demod_completeness_check              fast
% 11.44/2.03  --demod_use_ground                      true
% 11.44/2.03  --sup_to_prop_solver                    passive
% 11.44/2.03  --sup_prop_simpl_new                    true
% 11.44/2.03  --sup_prop_simpl_given                  true
% 11.44/2.03  --sup_fun_splitting                     false
% 11.44/2.03  --sup_smt_interval                      50000
% 11.44/2.03  
% 11.44/2.03  ------ Superposition Simplification Setup
% 11.44/2.03  
% 11.44/2.03  --sup_indices_passive                   []
% 11.44/2.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.44/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.03  --sup_full_bw                           [BwDemod]
% 11.44/2.03  --sup_immed_triv                        [TrivRules]
% 11.44/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.44/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.03  --sup_immed_bw_main                     []
% 11.44/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.44/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/2.03  
% 11.44/2.03  ------ Combination Options
% 11.44/2.03  
% 11.44/2.03  --comb_res_mult                         3
% 11.44/2.03  --comb_sup_mult                         2
% 11.44/2.03  --comb_inst_mult                        10
% 11.44/2.03  
% 11.44/2.03  ------ Debug Options
% 11.44/2.03  
% 11.44/2.03  --dbg_backtrace                         false
% 11.44/2.03  --dbg_dump_prop_clauses                 false
% 11.44/2.03  --dbg_dump_prop_clauses_file            -
% 11.44/2.03  --dbg_out_stat                          false
% 11.44/2.03  ------ Parsing...
% 11.44/2.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.44/2.03  
% 11.44/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.44/2.03  
% 11.44/2.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.44/2.03  
% 11.44/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.44/2.03  ------ Proving...
% 11.44/2.03  ------ Problem Properties 
% 11.44/2.03  
% 11.44/2.03  
% 11.44/2.03  clauses                                 12
% 11.44/2.03  conjectures                             2
% 11.44/2.03  EPR                                     1
% 11.44/2.03  Horn                                    12
% 11.44/2.03  unary                                   7
% 11.44/2.03  binary                                  3
% 11.44/2.03  lits                                    19
% 11.44/2.03  lits eq                                 10
% 11.44/2.03  fd_pure                                 0
% 11.44/2.03  fd_pseudo                               0
% 11.44/2.03  fd_cond                                 0
% 11.44/2.03  fd_pseudo_cond                          0
% 11.44/2.03  AC symbols                              0
% 11.44/2.03  
% 11.44/2.03  ------ Schedule dynamic 5 is on 
% 11.44/2.03  
% 11.44/2.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.44/2.03  
% 11.44/2.03  
% 11.44/2.03  ------ 
% 11.44/2.03  Current options:
% 11.44/2.03  ------ 
% 11.44/2.03  
% 11.44/2.03  ------ Input Options
% 11.44/2.03  
% 11.44/2.03  --out_options                           all
% 11.44/2.03  --tptp_safe_out                         true
% 11.44/2.03  --problem_path                          ""
% 11.44/2.03  --include_path                          ""
% 11.44/2.03  --clausifier                            res/vclausify_rel
% 11.44/2.03  --clausifier_options                    --mode clausify
% 11.44/2.03  --stdin                                 false
% 11.44/2.03  --stats_out                             all
% 11.44/2.03  
% 11.44/2.03  ------ General Options
% 11.44/2.03  
% 11.44/2.03  --fof                                   false
% 11.44/2.03  --time_out_real                         305.
% 11.44/2.03  --time_out_virtual                      -1.
% 11.44/2.03  --symbol_type_check                     false
% 11.44/2.03  --clausify_out                          false
% 11.44/2.03  --sig_cnt_out                           false
% 11.44/2.03  --trig_cnt_out                          false
% 11.44/2.03  --trig_cnt_out_tolerance                1.
% 11.44/2.03  --trig_cnt_out_sk_spl                   false
% 11.44/2.03  --abstr_cl_out                          false
% 11.44/2.03  
% 11.44/2.03  ------ Global Options
% 11.44/2.03  
% 11.44/2.03  --schedule                              default
% 11.44/2.03  --add_important_lit                     false
% 11.44/2.03  --prop_solver_per_cl                    1000
% 11.44/2.03  --min_unsat_core                        false
% 11.44/2.03  --soft_assumptions                      false
% 11.44/2.03  --soft_lemma_size                       3
% 11.44/2.03  --prop_impl_unit_size                   0
% 11.44/2.03  --prop_impl_unit                        []
% 11.44/2.03  --share_sel_clauses                     true
% 11.44/2.03  --reset_solvers                         false
% 11.44/2.03  --bc_imp_inh                            [conj_cone]
% 11.44/2.03  --conj_cone_tolerance                   3.
% 11.44/2.03  --extra_neg_conj                        none
% 11.44/2.03  --large_theory_mode                     true
% 11.44/2.03  --prolific_symb_bound                   200
% 11.44/2.03  --lt_threshold                          2000
% 11.44/2.03  --clause_weak_htbl                      true
% 11.44/2.03  --gc_record_bc_elim                     false
% 11.44/2.03  
% 11.44/2.03  ------ Preprocessing Options
% 11.44/2.03  
% 11.44/2.03  --preprocessing_flag                    true
% 11.44/2.03  --time_out_prep_mult                    0.1
% 11.44/2.03  --splitting_mode                        input
% 11.44/2.03  --splitting_grd                         true
% 11.44/2.03  --splitting_cvd                         false
% 11.44/2.03  --splitting_cvd_svl                     false
% 11.44/2.03  --splitting_nvd                         32
% 11.44/2.03  --sub_typing                            true
% 11.44/2.03  --prep_gs_sim                           true
% 11.44/2.03  --prep_unflatten                        true
% 11.44/2.03  --prep_res_sim                          true
% 11.44/2.03  --prep_upred                            true
% 11.44/2.03  --prep_sem_filter                       exhaustive
% 11.44/2.03  --prep_sem_filter_out                   false
% 11.44/2.03  --pred_elim                             true
% 11.44/2.03  --res_sim_input                         true
% 11.44/2.03  --eq_ax_congr_red                       true
% 11.44/2.03  --pure_diseq_elim                       true
% 11.44/2.03  --brand_transform                       false
% 11.44/2.03  --non_eq_to_eq                          false
% 11.44/2.03  --prep_def_merge                        true
% 11.44/2.03  --prep_def_merge_prop_impl              false
% 11.44/2.03  --prep_def_merge_mbd                    true
% 11.44/2.03  --prep_def_merge_tr_red                 false
% 11.44/2.03  --prep_def_merge_tr_cl                  false
% 11.44/2.03  --smt_preprocessing                     true
% 11.44/2.03  --smt_ac_axioms                         fast
% 11.44/2.03  --preprocessed_out                      false
% 11.44/2.03  --preprocessed_stats                    false
% 11.44/2.03  
% 11.44/2.03  ------ Abstraction refinement Options
% 11.44/2.03  
% 11.44/2.03  --abstr_ref                             []
% 11.44/2.03  --abstr_ref_prep                        false
% 11.44/2.03  --abstr_ref_until_sat                   false
% 11.44/2.03  --abstr_ref_sig_restrict                funpre
% 11.44/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.44/2.03  --abstr_ref_under                       []
% 11.44/2.03  
% 11.44/2.03  ------ SAT Options
% 11.44/2.03  
% 11.44/2.03  --sat_mode                              false
% 11.44/2.03  --sat_fm_restart_options                ""
% 11.44/2.03  --sat_gr_def                            false
% 11.44/2.03  --sat_epr_types                         true
% 11.44/2.03  --sat_non_cyclic_types                  false
% 11.44/2.03  --sat_finite_models                     false
% 11.44/2.03  --sat_fm_lemmas                         false
% 11.44/2.03  --sat_fm_prep                           false
% 11.44/2.03  --sat_fm_uc_incr                        true
% 11.44/2.03  --sat_out_model                         small
% 11.44/2.03  --sat_out_clauses                       false
% 11.44/2.03  
% 11.44/2.03  ------ QBF Options
% 11.44/2.03  
% 11.44/2.03  --qbf_mode                              false
% 11.44/2.03  --qbf_elim_univ                         false
% 11.44/2.03  --qbf_dom_inst                          none
% 11.44/2.03  --qbf_dom_pre_inst                      false
% 11.44/2.03  --qbf_sk_in                             false
% 11.44/2.03  --qbf_pred_elim                         true
% 11.44/2.03  --qbf_split                             512
% 11.44/2.03  
% 11.44/2.03  ------ BMC1 Options
% 11.44/2.03  
% 11.44/2.03  --bmc1_incremental                      false
% 11.44/2.03  --bmc1_axioms                           reachable_all
% 11.44/2.03  --bmc1_min_bound                        0
% 11.44/2.03  --bmc1_max_bound                        -1
% 11.44/2.03  --bmc1_max_bound_default                -1
% 11.44/2.03  --bmc1_symbol_reachability              true
% 11.44/2.03  --bmc1_property_lemmas                  false
% 11.44/2.03  --bmc1_k_induction                      false
% 11.44/2.03  --bmc1_non_equiv_states                 false
% 11.44/2.03  --bmc1_deadlock                         false
% 11.44/2.03  --bmc1_ucm                              false
% 11.44/2.03  --bmc1_add_unsat_core                   none
% 11.44/2.03  --bmc1_unsat_core_children              false
% 11.44/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.44/2.03  --bmc1_out_stat                         full
% 11.44/2.03  --bmc1_ground_init                      false
% 11.44/2.03  --bmc1_pre_inst_next_state              false
% 11.44/2.03  --bmc1_pre_inst_state                   false
% 11.44/2.03  --bmc1_pre_inst_reach_state             false
% 11.44/2.03  --bmc1_out_unsat_core                   false
% 11.44/2.03  --bmc1_aig_witness_out                  false
% 11.44/2.03  --bmc1_verbose                          false
% 11.44/2.03  --bmc1_dump_clauses_tptp                false
% 11.44/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.44/2.03  --bmc1_dump_file                        -
% 11.44/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.44/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.44/2.03  --bmc1_ucm_extend_mode                  1
% 11.44/2.03  --bmc1_ucm_init_mode                    2
% 11.44/2.03  --bmc1_ucm_cone_mode                    none
% 11.44/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.44/2.03  --bmc1_ucm_relax_model                  4
% 11.44/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.44/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.44/2.03  --bmc1_ucm_layered_model                none
% 11.44/2.03  --bmc1_ucm_max_lemma_size               10
% 11.44/2.03  
% 11.44/2.03  ------ AIG Options
% 11.44/2.03  
% 11.44/2.03  --aig_mode                              false
% 11.44/2.03  
% 11.44/2.03  ------ Instantiation Options
% 11.44/2.03  
% 11.44/2.03  --instantiation_flag                    true
% 11.44/2.03  --inst_sos_flag                         false
% 11.44/2.03  --inst_sos_phase                        true
% 11.44/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.44/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.44/2.03  --inst_lit_sel_side                     none
% 11.44/2.03  --inst_solver_per_active                1400
% 11.44/2.03  --inst_solver_calls_frac                1.
% 11.44/2.03  --inst_passive_queue_type               priority_queues
% 11.44/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.44/2.03  --inst_passive_queues_freq              [25;2]
% 11.44/2.03  --inst_dismatching                      true
% 11.44/2.03  --inst_eager_unprocessed_to_passive     true
% 11.44/2.03  --inst_prop_sim_given                   true
% 11.44/2.03  --inst_prop_sim_new                     false
% 11.44/2.03  --inst_subs_new                         false
% 11.44/2.03  --inst_eq_res_simp                      false
% 11.44/2.03  --inst_subs_given                       false
% 11.44/2.03  --inst_orphan_elimination               true
% 11.44/2.03  --inst_learning_loop_flag               true
% 11.44/2.03  --inst_learning_start                   3000
% 11.44/2.03  --inst_learning_factor                  2
% 11.44/2.03  --inst_start_prop_sim_after_learn       3
% 11.44/2.03  --inst_sel_renew                        solver
% 11.44/2.03  --inst_lit_activity_flag                true
% 11.44/2.03  --inst_restr_to_given                   false
% 11.44/2.03  --inst_activity_threshold               500
% 11.44/2.03  --inst_out_proof                        true
% 11.44/2.03  
% 11.44/2.03  ------ Resolution Options
% 11.44/2.03  
% 11.44/2.03  --resolution_flag                       false
% 11.44/2.03  --res_lit_sel                           adaptive
% 11.44/2.03  --res_lit_sel_side                      none
% 11.44/2.03  --res_ordering                          kbo
% 11.44/2.03  --res_to_prop_solver                    active
% 11.44/2.03  --res_prop_simpl_new                    false
% 11.44/2.03  --res_prop_simpl_given                  true
% 11.44/2.03  --res_passive_queue_type                priority_queues
% 11.44/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.44/2.03  --res_passive_queues_freq               [15;5]
% 11.44/2.03  --res_forward_subs                      full
% 11.44/2.03  --res_backward_subs                     full
% 11.44/2.03  --res_forward_subs_resolution           true
% 11.44/2.03  --res_backward_subs_resolution          true
% 11.44/2.03  --res_orphan_elimination                true
% 11.44/2.03  --res_time_limit                        2.
% 11.44/2.03  --res_out_proof                         true
% 11.44/2.03  
% 11.44/2.03  ------ Superposition Options
% 11.44/2.03  
% 11.44/2.03  --superposition_flag                    true
% 11.44/2.03  --sup_passive_queue_type                priority_queues
% 11.44/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.44/2.03  --sup_passive_queues_freq               [8;1;4]
% 11.44/2.03  --demod_completeness_check              fast
% 11.44/2.03  --demod_use_ground                      true
% 11.44/2.03  --sup_to_prop_solver                    passive
% 11.44/2.03  --sup_prop_simpl_new                    true
% 11.44/2.03  --sup_prop_simpl_given                  true
% 11.44/2.03  --sup_fun_splitting                     false
% 11.44/2.03  --sup_smt_interval                      50000
% 11.44/2.03  
% 11.44/2.03  ------ Superposition Simplification Setup
% 11.44/2.03  
% 11.44/2.03  --sup_indices_passive                   []
% 11.44/2.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.44/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.44/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.03  --sup_full_bw                           [BwDemod]
% 11.44/2.03  --sup_immed_triv                        [TrivRules]
% 11.44/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.44/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.03  --sup_immed_bw_main                     []
% 11.44/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.44/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.44/2.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.44/2.03  
% 11.44/2.03  ------ Combination Options
% 11.44/2.03  
% 11.44/2.03  --comb_res_mult                         3
% 11.44/2.03  --comb_sup_mult                         2
% 11.44/2.03  --comb_inst_mult                        10
% 11.44/2.03  
% 11.44/2.03  ------ Debug Options
% 11.44/2.03  
% 11.44/2.03  --dbg_backtrace                         false
% 11.44/2.03  --dbg_dump_prop_clauses                 false
% 11.44/2.03  --dbg_dump_prop_clauses_file            -
% 11.44/2.03  --dbg_out_stat                          false
% 11.44/2.03  
% 11.44/2.03  
% 11.44/2.03  
% 11.44/2.03  
% 11.44/2.03  ------ Proving...
% 11.44/2.03  
% 11.44/2.03  
% 11.44/2.03  % SZS status Theorem for theBenchmark.p
% 11.44/2.03  
% 11.44/2.03  % SZS output start CNFRefutation for theBenchmark.p
% 11.44/2.03  
% 11.44/2.03  fof(f14,conjecture,(
% 11.44/2.03    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f15,negated_conjecture,(
% 11.44/2.03    ~! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 11.44/2.03    inference(negated_conjecture,[],[f14])).
% 11.44/2.03  
% 11.44/2.03  fof(f22,plain,(
% 11.44/2.03    ? [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(X2))),
% 11.44/2.03    inference(ennf_transformation,[],[f15])).
% 11.44/2.03  
% 11.44/2.03  fof(f23,plain,(
% 11.44/2.03    ? [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) != k10_relat_1(k7_relat_1(X2,X0),X1) & v1_relat_1(X2)) => (k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) & v1_relat_1(sK2))),
% 11.44/2.03    introduced(choice_axiom,[])).
% 11.44/2.03  
% 11.44/2.03  fof(f24,plain,(
% 11.44/2.03    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) & v1_relat_1(sK2)),
% 11.44/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 11.44/2.03  
% 11.44/2.03  fof(f39,plain,(
% 11.44/2.03    v1_relat_1(sK2)),
% 11.44/2.03    inference(cnf_transformation,[],[f24])).
% 11.44/2.03  
% 11.44/2.03  fof(f12,axiom,(
% 11.44/2.03    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f16,plain,(
% 11.44/2.03    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 11.44/2.03    inference(pure_predicate_removal,[],[f12])).
% 11.44/2.03  
% 11.44/2.03  fof(f37,plain,(
% 11.44/2.03    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.44/2.03    inference(cnf_transformation,[],[f16])).
% 11.44/2.03  
% 11.44/2.03  fof(f8,axiom,(
% 11.44/2.03    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0)))),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f19,plain,(
% 11.44/2.03    ! [X0,X1] : (! [X2] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 11.44/2.03    inference(ennf_transformation,[],[f8])).
% 11.44/2.03  
% 11.44/2.03  fof(f32,plain,(
% 11.44/2.03    ( ! [X2,X0,X1] : (k10_relat_1(X1,k10_relat_1(X2,X0)) = k10_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 11.44/2.03    inference(cnf_transformation,[],[f19])).
% 11.44/2.03  
% 11.44/2.03  fof(f11,axiom,(
% 11.44/2.03    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f21,plain,(
% 11.44/2.03    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.44/2.03    inference(ennf_transformation,[],[f11])).
% 11.44/2.03  
% 11.44/2.03  fof(f36,plain,(
% 11.44/2.03    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.44/2.03    inference(cnf_transformation,[],[f21])).
% 11.44/2.03  
% 11.44/2.03  fof(f9,axiom,(
% 11.44/2.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))))),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f20,plain,(
% 11.44/2.03    ! [X0] : (! [X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.44/2.03    inference(ennf_transformation,[],[f9])).
% 11.44/2.03  
% 11.44/2.03  fof(f33,plain,(
% 11.44/2.03    ( ! [X0,X1] : (k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.44/2.03    inference(cnf_transformation,[],[f20])).
% 11.44/2.03  
% 11.44/2.03  fof(f7,axiom,(
% 11.44/2.03    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f18,plain,(
% 11.44/2.03    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 11.44/2.03    inference(ennf_transformation,[],[f7])).
% 11.44/2.03  
% 11.44/2.03  fof(f31,plain,(
% 11.44/2.03    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 11.44/2.03    inference(cnf_transformation,[],[f18])).
% 11.44/2.03  
% 11.44/2.03  fof(f10,axiom,(
% 11.44/2.03    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f34,plain,(
% 11.44/2.03    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.44/2.03    inference(cnf_transformation,[],[f10])).
% 11.44/2.03  
% 11.44/2.03  fof(f13,axiom,(
% 11.44/2.03    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f38,plain,(
% 11.44/2.03    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 11.44/2.03    inference(cnf_transformation,[],[f13])).
% 11.44/2.03  
% 11.44/2.03  fof(f1,axiom,(
% 11.44/2.03    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f25,plain,(
% 11.44/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.44/2.03    inference(cnf_transformation,[],[f1])).
% 11.44/2.03  
% 11.44/2.03  fof(f45,plain,(
% 11.44/2.03    ( ! [X0,X1] : (k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 11.44/2.03    inference(definition_unfolding,[],[f38,f25])).
% 11.44/2.03  
% 11.44/2.03  fof(f35,plain,(
% 11.44/2.03    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.44/2.03    inference(cnf_transformation,[],[f10])).
% 11.44/2.03  
% 11.44/2.03  fof(f6,axiom,(
% 11.44/2.03    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 11.44/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.03  
% 11.44/2.03  fof(f17,plain,(
% 11.44/2.03    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 11.44/2.03    inference(ennf_transformation,[],[f6])).
% 11.44/2.03  
% 11.44/2.03  fof(f30,plain,(
% 11.44/2.03    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 11.44/2.03    inference(cnf_transformation,[],[f17])).
% 11.44/2.03  
% 11.44/2.03  fof(f44,plain,(
% 11.44/2.03    ( ! [X0,X1] : (k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 11.44/2.03    inference(definition_unfolding,[],[f30,f25])).
% 11.44/2.03  
% 11.44/2.03  fof(f40,plain,(
% 11.44/2.03    k3_xboole_0(sK0,k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 11.44/2.03    inference(cnf_transformation,[],[f24])).
% 11.44/2.03  
% 11.44/2.03  fof(f46,plain,(
% 11.44/2.03    k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 11.44/2.03    inference(definition_unfolding,[],[f40,f25])).
% 11.44/2.03  
% 11.44/2.03  cnf(c_11,negated_conjecture,
% 11.44/2.03      ( v1_relat_1(sK2) ),
% 11.44/2.03      inference(cnf_transformation,[],[f39]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_239,plain,
% 11.44/2.03      ( v1_relat_1(sK2) = iProver_top ),
% 11.44/2.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_8,plain,
% 11.44/2.03      ( v1_relat_1(k6_relat_1(X0)) ),
% 11.44/2.03      inference(cnf_transformation,[],[f37]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_240,plain,
% 11.44/2.03      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 11.44/2.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_3,plain,
% 11.44/2.03      ( ~ v1_relat_1(X0)
% 11.44/2.03      | ~ v1_relat_1(X1)
% 11.44/2.03      | k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2)) ),
% 11.44/2.03      inference(cnf_transformation,[],[f32]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_243,plain,
% 11.44/2.03      ( k10_relat_1(k5_relat_1(X0,X1),X2) = k10_relat_1(X0,k10_relat_1(X1,X2))
% 11.44/2.03      | v1_relat_1(X0) != iProver_top
% 11.44/2.03      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_2372,plain,
% 11.44/2.03      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(X1,X2)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2)
% 11.44/2.03      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_240,c_243]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_30061,plain,
% 11.44/2.03      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k5_relat_1(k6_relat_1(X0),sK2),X1) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_239,c_2372]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_7,plain,
% 11.44/2.03      ( ~ v1_relat_1(X0)
% 11.44/2.03      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 11.44/2.03      inference(cnf_transformation,[],[f36]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_241,plain,
% 11.44/2.03      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 11.44/2.03      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_700,plain,
% 11.44/2.03      ( k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_239,c_241]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_30110,plain,
% 11.44/2.03      ( k10_relat_1(k6_relat_1(X0),k10_relat_1(sK2,X1)) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 11.44/2.03      inference(light_normalisation,[status(thm)],[c_30061,c_700]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_4,plain,
% 11.44/2.03      ( ~ v1_relat_1(X0)
% 11.44/2.03      | ~ v1_relat_1(X1)
% 11.44/2.03      | k1_relat_1(k5_relat_1(X1,X0)) = k10_relat_1(X1,k1_relat_1(X0)) ),
% 11.44/2.03      inference(cnf_transformation,[],[f33]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_242,plain,
% 11.44/2.03      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
% 11.44/2.03      | v1_relat_1(X1) != iProver_top
% 11.44/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_1412,plain,
% 11.44/2.03      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),X1)) = k10_relat_1(k6_relat_1(X0),k1_relat_1(X1))
% 11.44/2.03      | v1_relat_1(X1) != iProver_top ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_240,c_242]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_14413,plain,
% 11.44/2.03      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_240,c_1412]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_2,plain,
% 11.44/2.03      ( ~ v1_relat_1(X0)
% 11.44/2.03      | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 11.44/2.03      inference(cnf_transformation,[],[f31]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_244,plain,
% 11.44/2.03      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 11.44/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_1650,plain,
% 11.44/2.03      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_240,c_244]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_14461,plain,
% 11.44/2.03      ( k10_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X1))) = k1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 11.44/2.03      inference(light_normalisation,[status(thm)],[c_14413,c_1650]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_6,plain,
% 11.44/2.03      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 11.44/2.03      inference(cnf_transformation,[],[f34]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_9,plain,
% 11.44/2.03      ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 11.44/2.03      inference(cnf_transformation,[],[f45]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_5,plain,
% 11.44/2.03      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 11.44/2.03      inference(cnf_transformation,[],[f35]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_408,plain,
% 11.44/2.03      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_9,c_5]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_407,plain,
% 11.44/2.03      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_9,c_6]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_850,plain,
% 11.44/2.03      ( k1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_408,c_407]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_12655,plain,
% 11.44/2.03      ( k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 11.44/2.03      inference(light_normalisation,[status(thm)],[c_850,c_1650]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_14462,plain,
% 11.44/2.03      ( k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X1),X0) ),
% 11.44/2.03      inference(demodulation,[status(thm)],[c_14461,c_6,c_12655]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_1,plain,
% 11.44/2.03      ( ~ v1_relat_1(X0)
% 11.44/2.03      | k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 11.44/2.03      inference(cnf_transformation,[],[f44]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_245,plain,
% 11.44/2.03      ( k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0))
% 11.44/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.44/2.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_3689,plain,
% 11.44/2.03      ( k4_xboole_0(k2_relat_1(k6_relat_1(X0)),k4_xboole_0(k2_relat_1(k6_relat_1(X0)),X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_240,c_245]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_3718,plain,
% 11.44/2.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 11.44/2.03      inference(light_normalisation,[status(thm)],[c_3689,c_5]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_3815,plain,
% 11.44/2.03      ( k2_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
% 11.44/2.03      inference(demodulation,[status(thm)],[c_3718,c_408]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_12474,plain,
% 11.44/2.03      ( k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
% 11.44/2.03      inference(light_normalisation,[status(thm)],[c_3815,c_1650]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_15008,plain,
% 11.44/2.03      ( k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k10_relat_1(k6_relat_1(X0),X1) ),
% 11.44/2.03      inference(demodulation,[status(thm)],[c_14462,c_12474]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_15159,plain,
% 11.44/2.03      ( k10_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X1),X0) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_15008,c_14462]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_10,negated_conjecture,
% 11.44/2.03      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 11.44/2.03      inference(cnf_transformation,[],[f46]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_3814,plain,
% 11.44/2.03      ( k2_relat_1(k8_relat_1(k10_relat_1(sK2,sK1),k6_relat_1(sK0))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 11.44/2.03      inference(demodulation,[status(thm)],[c_3718,c_10]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_12477,plain,
% 11.44/2.03      ( k2_relat_1(k8_relat_1(sK0,k6_relat_1(k10_relat_1(sK2,sK1)))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 11.44/2.03      inference(demodulation,[status(thm)],[c_12474,c_3814]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_15024,plain,
% 11.44/2.03      ( k10_relat_1(k6_relat_1(k10_relat_1(sK2,sK1)),sK0) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 11.44/2.03      inference(demodulation,[status(thm)],[c_14462,c_12477]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_15233,plain,
% 11.44/2.03      ( k10_relat_1(k6_relat_1(sK0),k10_relat_1(sK2,sK1)) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 11.44/2.03      inference(superposition,[status(thm)],[c_15159,c_15024]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_30368,plain,
% 11.44/2.03      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 11.44/2.03      inference(demodulation,[status(thm)],[c_30110,c_15233]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_100,plain,( X0 = X0 ),theory(equality) ).
% 11.44/2.03  
% 11.44/2.03  cnf(c_524,plain,
% 11.44/2.03      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 11.44/2.03      inference(instantiation,[status(thm)],[c_100]) ).
% 11.44/2.03  
% 11.44/2.03  cnf(contradiction,plain,
% 11.44/2.03      ( $false ),
% 11.44/2.03      inference(minisat,[status(thm)],[c_30368,c_524]) ).
% 11.44/2.03  
% 11.44/2.03  
% 11.44/2.03  % SZS output end CNFRefutation for theBenchmark.p
% 11.44/2.03  
% 11.44/2.03  ------                               Statistics
% 11.44/2.03  
% 11.44/2.03  ------ General
% 11.44/2.03  
% 11.44/2.03  abstr_ref_over_cycles:                  0
% 11.44/2.03  abstr_ref_under_cycles:                 0
% 11.44/2.03  gc_basic_clause_elim:                   0
% 11.44/2.03  forced_gc_time:                         0
% 11.44/2.03  parsing_time:                           0.013
% 11.44/2.03  unif_index_cands_time:                  0.
% 11.44/2.03  unif_index_add_time:                    0.
% 11.44/2.03  orderings_time:                         0.
% 11.44/2.03  out_proof_time:                         0.009
% 11.44/2.03  total_time:                             1.095
% 11.44/2.03  num_of_symbols:                         45
% 11.44/2.03  num_of_terms:                           54959
% 11.44/2.03  
% 11.44/2.03  ------ Preprocessing
% 11.44/2.03  
% 11.44/2.03  num_of_splits:                          0
% 11.44/2.03  num_of_split_atoms:                     0
% 11.44/2.03  num_of_reused_defs:                     0
% 11.44/2.03  num_eq_ax_congr_red:                    14
% 11.44/2.03  num_of_sem_filtered_clauses:            1
% 11.44/2.03  num_of_subtypes:                        0
% 11.44/2.03  monotx_restored_types:                  0
% 11.44/2.03  sat_num_of_epr_types:                   0
% 11.44/2.03  sat_num_of_non_cyclic_types:            0
% 11.44/2.03  sat_guarded_non_collapsed_types:        0
% 11.44/2.03  num_pure_diseq_elim:                    0
% 11.44/2.03  simp_replaced_by:                       0
% 11.44/2.03  res_preprocessed:                       59
% 11.44/2.03  prep_upred:                             0
% 11.44/2.03  prep_unflattend:                        0
% 11.44/2.03  smt_new_axioms:                         0
% 11.44/2.03  pred_elim_cands:                        1
% 11.44/2.03  pred_elim:                              0
% 11.44/2.03  pred_elim_cl:                           0
% 11.44/2.03  pred_elim_cycles:                       1
% 11.44/2.03  merged_defs:                            0
% 11.44/2.03  merged_defs_ncl:                        0
% 11.44/2.03  bin_hyper_res:                          0
% 11.44/2.03  prep_cycles:                            3
% 11.44/2.03  pred_elim_time:                         0.
% 11.44/2.03  splitting_time:                         0.
% 11.44/2.03  sem_filter_time:                        0.
% 11.44/2.03  monotx_time:                            0.001
% 11.44/2.03  subtype_inf_time:                       0.
% 11.44/2.03  
% 11.44/2.03  ------ Problem properties
% 11.44/2.03  
% 11.44/2.03  clauses:                                12
% 11.44/2.03  conjectures:                            2
% 11.44/2.03  epr:                                    1
% 11.44/2.03  horn:                                   12
% 11.44/2.03  ground:                                 2
% 11.44/2.03  unary:                                  7
% 11.44/2.03  binary:                                 3
% 11.44/2.03  lits:                                   19
% 11.44/2.03  lits_eq:                                10
% 11.44/2.03  fd_pure:                                0
% 11.44/2.03  fd_pseudo:                              0
% 11.44/2.03  fd_cond:                                0
% 11.44/2.03  fd_pseudo_cond:                         0
% 11.44/2.03  ac_symbols:                             0
% 11.44/2.03  
% 11.44/2.03  ------ Propositional Solver
% 11.44/2.03  
% 11.44/2.03  prop_solver_calls:                      27
% 11.44/2.03  prop_fast_solver_calls:                 677
% 11.44/2.03  smt_solver_calls:                       0
% 11.44/2.03  smt_fast_solver_calls:                  0
% 11.44/2.03  prop_num_of_clauses:                    11185
% 11.44/2.03  prop_preprocess_simplified:             11723
% 11.44/2.03  prop_fo_subsumed:                       0
% 11.44/2.03  prop_solver_time:                       0.
% 11.44/2.03  smt_solver_time:                        0.
% 11.44/2.03  smt_fast_solver_time:                   0.
% 11.44/2.03  prop_fast_solver_time:                  0.
% 11.44/2.03  prop_unsat_core_time:                   0.001
% 11.44/2.03  
% 11.44/2.03  ------ QBF
% 11.44/2.03  
% 11.44/2.03  qbf_q_res:                              0
% 11.44/2.03  qbf_num_tautologies:                    0
% 11.44/2.03  qbf_prep_cycles:                        0
% 11.44/2.03  
% 11.44/2.03  ------ BMC1
% 11.44/2.03  
% 11.44/2.03  bmc1_current_bound:                     -1
% 11.44/2.03  bmc1_last_solved_bound:                 -1
% 11.44/2.03  bmc1_unsat_core_size:                   -1
% 11.44/2.03  bmc1_unsat_core_parents_size:           -1
% 11.44/2.03  bmc1_merge_next_fun:                    0
% 11.44/2.03  bmc1_unsat_core_clauses_time:           0.
% 11.44/2.03  
% 11.44/2.03  ------ Instantiation
% 11.44/2.03  
% 11.44/2.03  inst_num_of_clauses:                    3241
% 11.44/2.03  inst_num_in_passive:                    314
% 11.44/2.03  inst_num_in_active:                     1553
% 11.44/2.03  inst_num_in_unprocessed:                1377
% 11.44/2.03  inst_num_of_loops:                      1590
% 11.44/2.03  inst_num_of_learning_restarts:          0
% 11.44/2.03  inst_num_moves_active_passive:          32
% 11.44/2.03  inst_lit_activity:                      0
% 11.44/2.03  inst_lit_activity_moves:                1
% 11.44/2.03  inst_num_tautologies:                   0
% 11.44/2.03  inst_num_prop_implied:                  0
% 11.44/2.03  inst_num_existing_simplified:           0
% 11.44/2.03  inst_num_eq_res_simplified:             0
% 11.44/2.03  inst_num_child_elim:                    0
% 11.44/2.03  inst_num_of_dismatching_blockings:      3652
% 11.44/2.03  inst_num_of_non_proper_insts:           4054
% 11.44/2.03  inst_num_of_duplicates:                 0
% 11.44/2.03  inst_inst_num_from_inst_to_res:         0
% 11.44/2.03  inst_dismatching_checking_time:         0.
% 11.44/2.03  
% 11.44/2.03  ------ Resolution
% 11.44/2.03  
% 11.44/2.03  res_num_of_clauses:                     0
% 11.44/2.03  res_num_in_passive:                     0
% 11.44/2.03  res_num_in_active:                      0
% 11.44/2.03  res_num_of_loops:                       62
% 11.44/2.03  res_forward_subset_subsumed:            616
% 11.44/2.03  res_backward_subset_subsumed:           20
% 11.44/2.03  res_forward_subsumed:                   0
% 11.44/2.03  res_backward_subsumed:                  0
% 11.44/2.03  res_forward_subsumption_resolution:     0
% 11.44/2.03  res_backward_subsumption_resolution:    0
% 11.44/2.03  res_clause_to_clause_subsumption:       3609
% 11.44/2.03  res_orphan_elimination:                 0
% 11.44/2.03  res_tautology_del:                      463
% 11.44/2.03  res_num_eq_res_simplified:              0
% 11.44/2.03  res_num_sel_changes:                    0
% 11.44/2.03  res_moves_from_active_to_pass:          0
% 11.44/2.03  
% 11.44/2.03  ------ Superposition
% 11.44/2.03  
% 11.44/2.03  sup_time_total:                         0.
% 11.44/2.03  sup_time_generating:                    0.
% 11.44/2.03  sup_time_sim_full:                      0.
% 11.44/2.03  sup_time_sim_immed:                     0.
% 11.44/2.03  
% 11.44/2.03  sup_num_of_clauses:                     2005
% 11.44/2.03  sup_num_in_active:                      170
% 11.44/2.03  sup_num_in_passive:                     1835
% 11.44/2.03  sup_num_of_loops:                       316
% 11.44/2.03  sup_fw_superposition:                   1130
% 11.44/2.03  sup_bw_superposition:                   2051
% 11.44/2.03  sup_immediate_simplified:               2114
% 11.44/2.03  sup_given_eliminated:                   2
% 11.44/2.03  comparisons_done:                       0
% 11.44/2.03  comparisons_avoided:                    0
% 11.44/2.03  
% 11.44/2.03  ------ Simplifications
% 11.44/2.03  
% 11.44/2.03  
% 11.44/2.03  sim_fw_subset_subsumed:                 0
% 11.44/2.03  sim_bw_subset_subsumed:                 0
% 11.44/2.03  sim_fw_subsumed:                        169
% 11.44/2.03  sim_bw_subsumed:                        12
% 11.44/2.03  sim_fw_subsumption_res:                 0
% 11.44/2.03  sim_bw_subsumption_res:                 0
% 11.44/2.03  sim_tautology_del:                      0
% 11.44/2.03  sim_eq_tautology_del:                   212
% 11.44/2.03  sim_eq_res_simp:                        0
% 11.44/2.03  sim_fw_demodulated:                     1187
% 11.44/2.03  sim_bw_demodulated:                     276
% 11.44/2.03  sim_light_normalised:                   1018
% 11.44/2.03  sim_joinable_taut:                      0
% 11.44/2.03  sim_joinable_simp:                      0
% 11.44/2.03  sim_ac_normalised:                      0
% 11.44/2.03  sim_smt_subsumption:                    0
% 11.44/2.03  
%------------------------------------------------------------------------------
