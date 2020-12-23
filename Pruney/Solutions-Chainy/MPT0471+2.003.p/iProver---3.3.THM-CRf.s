%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:20 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 463 expanded)
%              Number of clauses        :   58 ( 149 expanded)
%              Number of leaves         :   26 ( 119 expanded)
%              Depth                    :   19
%              Number of atoms          :  191 ( 632 expanded)
%              Number of equality atoms :  133 ( 390 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f53])).

fof(f69,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f92,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f101,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f98,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f99,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))
      & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f81,f106])).

fof(f108,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f78,f107])).

fof(f109,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f77,f108])).

fof(f110,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f83,f109])).

fof(f111,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f66,f110])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k3_tarski(k6_enumset1(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) ),
    inference(definition_unfolding,[],[f76,f111])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f110])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f97,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f96,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f121,plain,(
    ! [X0] :
      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f96,f110])).

fof(f20,axiom,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f17,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f112,plain,(
    ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f82,f107])).

fof(f116,plain,(
    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f86,f112])).

fof(f22,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f33,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f33])).

fof(f36,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f34])).

fof(f105,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_5,plain,
    ( v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1214,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1215,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1419,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1214,c_1215])).

cnf(c_1421,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1419,c_1214])).

cnf(c_20,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1207,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1536,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1207])).

cnf(c_28,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1199,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3287,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1536,c_1199])).

cnf(c_26,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1201,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1728,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_1215])).

cnf(c_1868,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1421,c_1728])).

cnf(c_3294,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3287,c_1868])).

cnf(c_27,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1200,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4627,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)) = iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3294,c_1200])).

cnf(c_29,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1198,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3153,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1536,c_1198])).

cnf(c_4635,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4627,c_3153])).

cnf(c_12,plain,
    ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_11,plain,
    ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2077,plain,
    ( k3_tarski(k6_enumset1(k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_3,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2079,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_3])).

cnf(c_2239,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2077,c_3,c_2079])).

cnf(c_4636,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4635,c_2239])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_53,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_55,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_68,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_70,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_68])).

cnf(c_6049,plain,
    ( r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4636,c_55,c_70,c_1421])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1211,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2932,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2079,c_1211])).

cnf(c_6055,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6049,c_2932])).

cnf(c_6069,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6055,c_3294])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1203,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1945,plain,
    ( k3_tarski(k6_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1536,c_1203])).

cnf(c_1946,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1945,c_1868])).

cnf(c_6502,plain,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k3_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6069,c_1946])).

cnf(c_14,plain,
    ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_6503,plain,
    ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6502,c_14])).

cnf(c_18,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6504,plain,
    ( k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6503,c_18])).

cnf(c_583,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1406,plain,
    ( k3_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_1407,plain,
    ( k3_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_582,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_615,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_582])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f105])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6504,c_1407,c_615,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.07/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/1.00  
% 3.07/1.00  ------  iProver source info
% 3.07/1.00  
% 3.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/1.00  git: non_committed_changes: false
% 3.07/1.00  git: last_make_outside_of_git: false
% 3.07/1.00  
% 3.07/1.00  ------ 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options
% 3.07/1.00  
% 3.07/1.00  --out_options                           all
% 3.07/1.00  --tptp_safe_out                         true
% 3.07/1.00  --problem_path                          ""
% 3.07/1.00  --include_path                          ""
% 3.07/1.00  --clausifier                            res/vclausify_rel
% 3.07/1.00  --clausifier_options                    --mode clausify
% 3.07/1.00  --stdin                                 false
% 3.07/1.00  --stats_out                             all
% 3.07/1.00  
% 3.07/1.00  ------ General Options
% 3.07/1.00  
% 3.07/1.00  --fof                                   false
% 3.07/1.00  --time_out_real                         305.
% 3.07/1.00  --time_out_virtual                      -1.
% 3.07/1.00  --symbol_type_check                     false
% 3.07/1.00  --clausify_out                          false
% 3.07/1.00  --sig_cnt_out                           false
% 3.07/1.00  --trig_cnt_out                          false
% 3.07/1.00  --trig_cnt_out_tolerance                1.
% 3.07/1.00  --trig_cnt_out_sk_spl                   false
% 3.07/1.00  --abstr_cl_out                          false
% 3.07/1.00  
% 3.07/1.00  ------ Global Options
% 3.07/1.00  
% 3.07/1.00  --schedule                              default
% 3.07/1.00  --add_important_lit                     false
% 3.07/1.00  --prop_solver_per_cl                    1000
% 3.07/1.00  --min_unsat_core                        false
% 3.07/1.00  --soft_assumptions                      false
% 3.07/1.00  --soft_lemma_size                       3
% 3.07/1.00  --prop_impl_unit_size                   0
% 3.07/1.00  --prop_impl_unit                        []
% 3.07/1.00  --share_sel_clauses                     true
% 3.07/1.00  --reset_solvers                         false
% 3.07/1.00  --bc_imp_inh                            [conj_cone]
% 3.07/1.00  --conj_cone_tolerance                   3.
% 3.07/1.00  --extra_neg_conj                        none
% 3.07/1.00  --large_theory_mode                     true
% 3.07/1.00  --prolific_symb_bound                   200
% 3.07/1.00  --lt_threshold                          2000
% 3.07/1.00  --clause_weak_htbl                      true
% 3.07/1.00  --gc_record_bc_elim                     false
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing Options
% 3.07/1.00  
% 3.07/1.00  --preprocessing_flag                    true
% 3.07/1.00  --time_out_prep_mult                    0.1
% 3.07/1.00  --splitting_mode                        input
% 3.07/1.00  --splitting_grd                         true
% 3.07/1.00  --splitting_cvd                         false
% 3.07/1.00  --splitting_cvd_svl                     false
% 3.07/1.00  --splitting_nvd                         32
% 3.07/1.00  --sub_typing                            true
% 3.07/1.00  --prep_gs_sim                           true
% 3.07/1.00  --prep_unflatten                        true
% 3.07/1.00  --prep_res_sim                          true
% 3.07/1.00  --prep_upred                            true
% 3.07/1.00  --prep_sem_filter                       exhaustive
% 3.07/1.00  --prep_sem_filter_out                   false
% 3.07/1.00  --pred_elim                             true
% 3.07/1.00  --res_sim_input                         true
% 3.07/1.00  --eq_ax_congr_red                       true
% 3.07/1.00  --pure_diseq_elim                       true
% 3.07/1.00  --brand_transform                       false
% 3.07/1.00  --non_eq_to_eq                          false
% 3.07/1.00  --prep_def_merge                        true
% 3.07/1.00  --prep_def_merge_prop_impl              false
% 3.07/1.00  --prep_def_merge_mbd                    true
% 3.07/1.00  --prep_def_merge_tr_red                 false
% 3.07/1.00  --prep_def_merge_tr_cl                  false
% 3.07/1.00  --smt_preprocessing                     true
% 3.07/1.00  --smt_ac_axioms                         fast
% 3.07/1.00  --preprocessed_out                      false
% 3.07/1.00  --preprocessed_stats                    false
% 3.07/1.00  
% 3.07/1.00  ------ Abstraction refinement Options
% 3.07/1.00  
% 3.07/1.00  --abstr_ref                             []
% 3.07/1.00  --abstr_ref_prep                        false
% 3.07/1.00  --abstr_ref_until_sat                   false
% 3.07/1.00  --abstr_ref_sig_restrict                funpre
% 3.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/1.00  --abstr_ref_under                       []
% 3.07/1.00  
% 3.07/1.00  ------ SAT Options
% 3.07/1.00  
% 3.07/1.00  --sat_mode                              false
% 3.07/1.00  --sat_fm_restart_options                ""
% 3.07/1.00  --sat_gr_def                            false
% 3.07/1.00  --sat_epr_types                         true
% 3.07/1.00  --sat_non_cyclic_types                  false
% 3.07/1.00  --sat_finite_models                     false
% 3.07/1.00  --sat_fm_lemmas                         false
% 3.07/1.00  --sat_fm_prep                           false
% 3.07/1.00  --sat_fm_uc_incr                        true
% 3.07/1.00  --sat_out_model                         small
% 3.07/1.00  --sat_out_clauses                       false
% 3.07/1.00  
% 3.07/1.00  ------ QBF Options
% 3.07/1.00  
% 3.07/1.00  --qbf_mode                              false
% 3.07/1.00  --qbf_elim_univ                         false
% 3.07/1.00  --qbf_dom_inst                          none
% 3.07/1.00  --qbf_dom_pre_inst                      false
% 3.07/1.00  --qbf_sk_in                             false
% 3.07/1.00  --qbf_pred_elim                         true
% 3.07/1.00  --qbf_split                             512
% 3.07/1.00  
% 3.07/1.00  ------ BMC1 Options
% 3.07/1.00  
% 3.07/1.00  --bmc1_incremental                      false
% 3.07/1.00  --bmc1_axioms                           reachable_all
% 3.07/1.00  --bmc1_min_bound                        0
% 3.07/1.00  --bmc1_max_bound                        -1
% 3.07/1.00  --bmc1_max_bound_default                -1
% 3.07/1.00  --bmc1_symbol_reachability              true
% 3.07/1.00  --bmc1_property_lemmas                  false
% 3.07/1.00  --bmc1_k_induction                      false
% 3.07/1.00  --bmc1_non_equiv_states                 false
% 3.07/1.00  --bmc1_deadlock                         false
% 3.07/1.00  --bmc1_ucm                              false
% 3.07/1.00  --bmc1_add_unsat_core                   none
% 3.07/1.00  --bmc1_unsat_core_children              false
% 3.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/1.00  --bmc1_out_stat                         full
% 3.07/1.00  --bmc1_ground_init                      false
% 3.07/1.00  --bmc1_pre_inst_next_state              false
% 3.07/1.00  --bmc1_pre_inst_state                   false
% 3.07/1.00  --bmc1_pre_inst_reach_state             false
% 3.07/1.00  --bmc1_out_unsat_core                   false
% 3.07/1.00  --bmc1_aig_witness_out                  false
% 3.07/1.00  --bmc1_verbose                          false
% 3.07/1.00  --bmc1_dump_clauses_tptp                false
% 3.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.07/1.00  --bmc1_dump_file                        -
% 3.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.07/1.00  --bmc1_ucm_extend_mode                  1
% 3.07/1.00  --bmc1_ucm_init_mode                    2
% 3.07/1.00  --bmc1_ucm_cone_mode                    none
% 3.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.07/1.00  --bmc1_ucm_relax_model                  4
% 3.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/1.00  --bmc1_ucm_layered_model                none
% 3.07/1.00  --bmc1_ucm_max_lemma_size               10
% 3.07/1.00  
% 3.07/1.00  ------ AIG Options
% 3.07/1.00  
% 3.07/1.00  --aig_mode                              false
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation Options
% 3.07/1.00  
% 3.07/1.00  --instantiation_flag                    true
% 3.07/1.00  --inst_sos_flag                         false
% 3.07/1.00  --inst_sos_phase                        true
% 3.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel_side                     num_symb
% 3.07/1.00  --inst_solver_per_active                1400
% 3.07/1.00  --inst_solver_calls_frac                1.
% 3.07/1.00  --inst_passive_queue_type               priority_queues
% 3.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/1.00  --inst_passive_queues_freq              [25;2]
% 3.07/1.00  --inst_dismatching                      true
% 3.07/1.00  --inst_eager_unprocessed_to_passive     true
% 3.07/1.00  --inst_prop_sim_given                   true
% 3.07/1.00  --inst_prop_sim_new                     false
% 3.07/1.00  --inst_subs_new                         false
% 3.07/1.00  --inst_eq_res_simp                      false
% 3.07/1.00  --inst_subs_given                       false
% 3.07/1.00  --inst_orphan_elimination               true
% 3.07/1.00  --inst_learning_loop_flag               true
% 3.07/1.00  --inst_learning_start                   3000
% 3.07/1.00  --inst_learning_factor                  2
% 3.07/1.00  --inst_start_prop_sim_after_learn       3
% 3.07/1.00  --inst_sel_renew                        solver
% 3.07/1.00  --inst_lit_activity_flag                true
% 3.07/1.00  --inst_restr_to_given                   false
% 3.07/1.00  --inst_activity_threshold               500
% 3.07/1.00  --inst_out_proof                        true
% 3.07/1.00  
% 3.07/1.00  ------ Resolution Options
% 3.07/1.00  
% 3.07/1.00  --resolution_flag                       true
% 3.07/1.00  --res_lit_sel                           adaptive
% 3.07/1.00  --res_lit_sel_side                      none
% 3.07/1.00  --res_ordering                          kbo
% 3.07/1.00  --res_to_prop_solver                    active
% 3.07/1.00  --res_prop_simpl_new                    false
% 3.07/1.00  --res_prop_simpl_given                  true
% 3.07/1.00  --res_passive_queue_type                priority_queues
% 3.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/1.00  --res_passive_queues_freq               [15;5]
% 3.07/1.00  --res_forward_subs                      full
% 3.07/1.00  --res_backward_subs                     full
% 3.07/1.00  --res_forward_subs_resolution           true
% 3.07/1.00  --res_backward_subs_resolution          true
% 3.07/1.00  --res_orphan_elimination                true
% 3.07/1.00  --res_time_limit                        2.
% 3.07/1.00  --res_out_proof                         true
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Options
% 3.07/1.00  
% 3.07/1.00  --superposition_flag                    true
% 3.07/1.00  --sup_passive_queue_type                priority_queues
% 3.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.07/1.00  --demod_completeness_check              fast
% 3.07/1.00  --demod_use_ground                      true
% 3.07/1.00  --sup_to_prop_solver                    passive
% 3.07/1.00  --sup_prop_simpl_new                    true
% 3.07/1.00  --sup_prop_simpl_given                  true
% 3.07/1.00  --sup_fun_splitting                     false
% 3.07/1.00  --sup_smt_interval                      50000
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Simplification Setup
% 3.07/1.00  
% 3.07/1.00  --sup_indices_passive                   []
% 3.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_full_bw                           [BwDemod]
% 3.07/1.00  --sup_immed_triv                        [TrivRules]
% 3.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_immed_bw_main                     []
% 3.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  
% 3.07/1.00  ------ Combination Options
% 3.07/1.00  
% 3.07/1.00  --comb_res_mult                         3
% 3.07/1.00  --comb_sup_mult                         2
% 3.07/1.00  --comb_inst_mult                        10
% 3.07/1.00  
% 3.07/1.00  ------ Debug Options
% 3.07/1.00  
% 3.07/1.00  --dbg_backtrace                         false
% 3.07/1.00  --dbg_dump_prop_clauses                 false
% 3.07/1.00  --dbg_dump_prop_clauses_file            -
% 3.07/1.00  --dbg_out_stat                          false
% 3.07/1.00  ------ Parsing...
% 3.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/1.00  ------ Proving...
% 3.07/1.00  ------ Problem Properties 
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  clauses                                 34
% 3.07/1.00  conjectures                             1
% 3.07/1.00  EPR                                     4
% 3.07/1.00  Horn                                    31
% 3.07/1.00  unary                                   12
% 3.07/1.00  binary                                  18
% 3.07/1.00  lits                                    60
% 3.07/1.00  lits eq                                 22
% 3.07/1.00  fd_pure                                 0
% 3.07/1.00  fd_pseudo                               0
% 3.07/1.00  fd_cond                                 2
% 3.07/1.00  fd_pseudo_cond                          1
% 3.07/1.00  AC symbols                              0
% 3.07/1.00  
% 3.07/1.00  ------ Schedule dynamic 5 is on 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  ------ 
% 3.07/1.00  Current options:
% 3.07/1.00  ------ 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options
% 3.07/1.00  
% 3.07/1.00  --out_options                           all
% 3.07/1.00  --tptp_safe_out                         true
% 3.07/1.00  --problem_path                          ""
% 3.07/1.00  --include_path                          ""
% 3.07/1.00  --clausifier                            res/vclausify_rel
% 3.07/1.00  --clausifier_options                    --mode clausify
% 3.07/1.00  --stdin                                 false
% 3.07/1.00  --stats_out                             all
% 3.07/1.00  
% 3.07/1.00  ------ General Options
% 3.07/1.00  
% 3.07/1.00  --fof                                   false
% 3.07/1.00  --time_out_real                         305.
% 3.07/1.00  --time_out_virtual                      -1.
% 3.07/1.00  --symbol_type_check                     false
% 3.07/1.00  --clausify_out                          false
% 3.07/1.00  --sig_cnt_out                           false
% 3.07/1.00  --trig_cnt_out                          false
% 3.07/1.00  --trig_cnt_out_tolerance                1.
% 3.07/1.00  --trig_cnt_out_sk_spl                   false
% 3.07/1.00  --abstr_cl_out                          false
% 3.07/1.00  
% 3.07/1.00  ------ Global Options
% 3.07/1.00  
% 3.07/1.00  --schedule                              default
% 3.07/1.00  --add_important_lit                     false
% 3.07/1.00  --prop_solver_per_cl                    1000
% 3.07/1.00  --min_unsat_core                        false
% 3.07/1.00  --soft_assumptions                      false
% 3.07/1.00  --soft_lemma_size                       3
% 3.07/1.00  --prop_impl_unit_size                   0
% 3.07/1.00  --prop_impl_unit                        []
% 3.07/1.00  --share_sel_clauses                     true
% 3.07/1.00  --reset_solvers                         false
% 3.07/1.00  --bc_imp_inh                            [conj_cone]
% 3.07/1.00  --conj_cone_tolerance                   3.
% 3.07/1.00  --extra_neg_conj                        none
% 3.07/1.00  --large_theory_mode                     true
% 3.07/1.00  --prolific_symb_bound                   200
% 3.07/1.00  --lt_threshold                          2000
% 3.07/1.00  --clause_weak_htbl                      true
% 3.07/1.00  --gc_record_bc_elim                     false
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing Options
% 3.07/1.00  
% 3.07/1.00  --preprocessing_flag                    true
% 3.07/1.00  --time_out_prep_mult                    0.1
% 3.07/1.00  --splitting_mode                        input
% 3.07/1.00  --splitting_grd                         true
% 3.07/1.00  --splitting_cvd                         false
% 3.07/1.00  --splitting_cvd_svl                     false
% 3.07/1.00  --splitting_nvd                         32
% 3.07/1.00  --sub_typing                            true
% 3.07/1.00  --prep_gs_sim                           true
% 3.07/1.00  --prep_unflatten                        true
% 3.07/1.00  --prep_res_sim                          true
% 3.07/1.00  --prep_upred                            true
% 3.07/1.00  --prep_sem_filter                       exhaustive
% 3.07/1.00  --prep_sem_filter_out                   false
% 3.07/1.00  --pred_elim                             true
% 3.07/1.00  --res_sim_input                         true
% 3.07/1.00  --eq_ax_congr_red                       true
% 3.07/1.00  --pure_diseq_elim                       true
% 3.07/1.00  --brand_transform                       false
% 3.07/1.00  --non_eq_to_eq                          false
% 3.07/1.00  --prep_def_merge                        true
% 3.07/1.00  --prep_def_merge_prop_impl              false
% 3.07/1.00  --prep_def_merge_mbd                    true
% 3.07/1.00  --prep_def_merge_tr_red                 false
% 3.07/1.00  --prep_def_merge_tr_cl                  false
% 3.07/1.00  --smt_preprocessing                     true
% 3.07/1.00  --smt_ac_axioms                         fast
% 3.07/1.00  --preprocessed_out                      false
% 3.07/1.00  --preprocessed_stats                    false
% 3.07/1.00  
% 3.07/1.00  ------ Abstraction refinement Options
% 3.07/1.00  
% 3.07/1.00  --abstr_ref                             []
% 3.07/1.00  --abstr_ref_prep                        false
% 3.07/1.00  --abstr_ref_until_sat                   false
% 3.07/1.00  --abstr_ref_sig_restrict                funpre
% 3.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/1.00  --abstr_ref_under                       []
% 3.07/1.00  
% 3.07/1.00  ------ SAT Options
% 3.07/1.00  
% 3.07/1.00  --sat_mode                              false
% 3.07/1.00  --sat_fm_restart_options                ""
% 3.07/1.00  --sat_gr_def                            false
% 3.07/1.00  --sat_epr_types                         true
% 3.07/1.00  --sat_non_cyclic_types                  false
% 3.07/1.00  --sat_finite_models                     false
% 3.07/1.00  --sat_fm_lemmas                         false
% 3.07/1.00  --sat_fm_prep                           false
% 3.07/1.00  --sat_fm_uc_incr                        true
% 3.07/1.00  --sat_out_model                         small
% 3.07/1.00  --sat_out_clauses                       false
% 3.07/1.00  
% 3.07/1.00  ------ QBF Options
% 3.07/1.00  
% 3.07/1.00  --qbf_mode                              false
% 3.07/1.00  --qbf_elim_univ                         false
% 3.07/1.00  --qbf_dom_inst                          none
% 3.07/1.00  --qbf_dom_pre_inst                      false
% 3.07/1.00  --qbf_sk_in                             false
% 3.07/1.00  --qbf_pred_elim                         true
% 3.07/1.00  --qbf_split                             512
% 3.07/1.00  
% 3.07/1.00  ------ BMC1 Options
% 3.07/1.00  
% 3.07/1.00  --bmc1_incremental                      false
% 3.07/1.00  --bmc1_axioms                           reachable_all
% 3.07/1.00  --bmc1_min_bound                        0
% 3.07/1.00  --bmc1_max_bound                        -1
% 3.07/1.00  --bmc1_max_bound_default                -1
% 3.07/1.00  --bmc1_symbol_reachability              true
% 3.07/1.00  --bmc1_property_lemmas                  false
% 3.07/1.00  --bmc1_k_induction                      false
% 3.07/1.00  --bmc1_non_equiv_states                 false
% 3.07/1.00  --bmc1_deadlock                         false
% 3.07/1.00  --bmc1_ucm                              false
% 3.07/1.00  --bmc1_add_unsat_core                   none
% 3.07/1.00  --bmc1_unsat_core_children              false
% 3.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/1.00  --bmc1_out_stat                         full
% 3.07/1.00  --bmc1_ground_init                      false
% 3.07/1.00  --bmc1_pre_inst_next_state              false
% 3.07/1.00  --bmc1_pre_inst_state                   false
% 3.07/1.00  --bmc1_pre_inst_reach_state             false
% 3.07/1.00  --bmc1_out_unsat_core                   false
% 3.07/1.00  --bmc1_aig_witness_out                  false
% 3.07/1.00  --bmc1_verbose                          false
% 3.07/1.00  --bmc1_dump_clauses_tptp                false
% 3.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.07/1.00  --bmc1_dump_file                        -
% 3.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.07/1.00  --bmc1_ucm_extend_mode                  1
% 3.07/1.00  --bmc1_ucm_init_mode                    2
% 3.07/1.00  --bmc1_ucm_cone_mode                    none
% 3.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.07/1.00  --bmc1_ucm_relax_model                  4
% 3.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/1.00  --bmc1_ucm_layered_model                none
% 3.07/1.00  --bmc1_ucm_max_lemma_size               10
% 3.07/1.00  
% 3.07/1.00  ------ AIG Options
% 3.07/1.00  
% 3.07/1.00  --aig_mode                              false
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation Options
% 3.07/1.00  
% 3.07/1.00  --instantiation_flag                    true
% 3.07/1.00  --inst_sos_flag                         false
% 3.07/1.00  --inst_sos_phase                        true
% 3.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel_side                     none
% 3.07/1.00  --inst_solver_per_active                1400
% 3.07/1.00  --inst_solver_calls_frac                1.
% 3.07/1.00  --inst_passive_queue_type               priority_queues
% 3.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/1.00  --inst_passive_queues_freq              [25;2]
% 3.07/1.00  --inst_dismatching                      true
% 3.07/1.00  --inst_eager_unprocessed_to_passive     true
% 3.07/1.00  --inst_prop_sim_given                   true
% 3.07/1.00  --inst_prop_sim_new                     false
% 3.07/1.00  --inst_subs_new                         false
% 3.07/1.00  --inst_eq_res_simp                      false
% 3.07/1.00  --inst_subs_given                       false
% 3.07/1.00  --inst_orphan_elimination               true
% 3.07/1.00  --inst_learning_loop_flag               true
% 3.07/1.00  --inst_learning_start                   3000
% 3.07/1.00  --inst_learning_factor                  2
% 3.07/1.00  --inst_start_prop_sim_after_learn       3
% 3.07/1.00  --inst_sel_renew                        solver
% 3.07/1.00  --inst_lit_activity_flag                true
% 3.07/1.00  --inst_restr_to_given                   false
% 3.07/1.00  --inst_activity_threshold               500
% 3.07/1.00  --inst_out_proof                        true
% 3.07/1.00  
% 3.07/1.00  ------ Resolution Options
% 3.07/1.00  
% 3.07/1.00  --resolution_flag                       false
% 3.07/1.00  --res_lit_sel                           adaptive
% 3.07/1.00  --res_lit_sel_side                      none
% 3.07/1.00  --res_ordering                          kbo
% 3.07/1.00  --res_to_prop_solver                    active
% 3.07/1.00  --res_prop_simpl_new                    false
% 3.07/1.00  --res_prop_simpl_given                  true
% 3.07/1.00  --res_passive_queue_type                priority_queues
% 3.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/1.00  --res_passive_queues_freq               [15;5]
% 3.07/1.00  --res_forward_subs                      full
% 3.07/1.00  --res_backward_subs                     full
% 3.07/1.00  --res_forward_subs_resolution           true
% 3.07/1.00  --res_backward_subs_resolution          true
% 3.07/1.00  --res_orphan_elimination                true
% 3.07/1.00  --res_time_limit                        2.
% 3.07/1.00  --res_out_proof                         true
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Options
% 3.07/1.00  
% 3.07/1.00  --superposition_flag                    true
% 3.07/1.00  --sup_passive_queue_type                priority_queues
% 3.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.07/1.00  --demod_completeness_check              fast
% 3.07/1.00  --demod_use_ground                      true
% 3.07/1.00  --sup_to_prop_solver                    passive
% 3.07/1.00  --sup_prop_simpl_new                    true
% 3.07/1.00  --sup_prop_simpl_given                  true
% 3.07/1.00  --sup_fun_splitting                     false
% 3.07/1.00  --sup_smt_interval                      50000
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Simplification Setup
% 3.07/1.00  
% 3.07/1.00  --sup_indices_passive                   []
% 3.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_full_bw                           [BwDemod]
% 3.07/1.00  --sup_immed_triv                        [TrivRules]
% 3.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_immed_bw_main                     []
% 3.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  
% 3.07/1.00  ------ Combination Options
% 3.07/1.00  
% 3.07/1.00  --comb_res_mult                         3
% 3.07/1.00  --comb_sup_mult                         2
% 3.07/1.00  --comb_inst_mult                        10
% 3.07/1.00  
% 3.07/1.00  ------ Debug Options
% 3.07/1.00  
% 3.07/1.00  --dbg_backtrace                         false
% 3.07/1.00  --dbg_dump_prop_clauses                 false
% 3.07/1.00  --dbg_dump_prop_clauses_file            -
% 3.07/1.00  --dbg_out_stat                          false
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  ------ Proving...
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  % SZS status Theorem for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  fof(f5,axiom,(
% 3.07/1.00    ? [X0] : v1_xboole_0(X0)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f53,plain,(
% 3.07/1.00    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 3.07/1.00    introduced(choice_axiom,[])).
% 3.07/1.00  
% 3.07/1.00  fof(f54,plain,(
% 3.07/1.00    v1_xboole_0(sK1)),
% 3.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f5,f53])).
% 3.07/1.00  
% 3.07/1.00  fof(f69,plain,(
% 3.07/1.00    v1_xboole_0(sK1)),
% 3.07/1.00    inference(cnf_transformation,[],[f54])).
% 3.07/1.00  
% 3.07/1.00  fof(f4,axiom,(
% 3.07/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f38,plain,(
% 3.07/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f4])).
% 3.07/1.00  
% 3.07/1.00  fof(f68,plain,(
% 3.07/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f38])).
% 3.07/1.00  
% 3.07/1.00  fof(f24,axiom,(
% 3.07/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f40,plain,(
% 3.07/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f24])).
% 3.07/1.00  
% 3.07/1.00  fof(f92,plain,(
% 3.07/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f40])).
% 3.07/1.00  
% 3.07/1.00  fof(f30,axiom,(
% 3.07/1.00    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f46,plain,(
% 3.07/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f30])).
% 3.07/1.00  
% 3.07/1.00  fof(f101,plain,(
% 3.07/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f46])).
% 3.07/1.00  
% 3.07/1.00  fof(f28,axiom,(
% 3.07/1.00    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f44,plain,(
% 3.07/1.00    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f28])).
% 3.07/1.00  
% 3.07/1.00  fof(f98,plain,(
% 3.07/1.00    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f44])).
% 3.07/1.00  
% 3.07/1.00  fof(f29,axiom,(
% 3.07/1.00    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f45,plain,(
% 3.07/1.00    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f29])).
% 3.07/1.00  
% 3.07/1.00  fof(f99,plain,(
% 3.07/1.00    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f45])).
% 3.07/1.00  
% 3.07/1.00  fof(f100,plain,(
% 3.07/1.00    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f46])).
% 3.07/1.00  
% 3.07/1.00  fof(f19,axiom,(
% 3.07/1.00    ! [X0,X1,X2] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) & k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k4_xboole_0(X0,X1),X2))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f85,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k4_xboole_0(X0,X1))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f19])).
% 3.07/1.00  
% 3.07/1.00  fof(f11,axiom,(
% 3.07/1.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f76,plain,(
% 3.07/1.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.07/1.00    inference(cnf_transformation,[],[f11])).
% 3.07/1.00  
% 3.07/1.00  fof(f2,axiom,(
% 3.07/1.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f66,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f2])).
% 3.07/1.00  
% 3.07/1.00  fof(f18,axiom,(
% 3.07/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f83,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f18])).
% 3.07/1.00  
% 3.07/1.00  fof(f12,axiom,(
% 3.07/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f77,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f12])).
% 3.07/1.00  
% 3.07/1.00  fof(f13,axiom,(
% 3.07/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f78,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f13])).
% 3.07/1.00  
% 3.07/1.00  fof(f16,axiom,(
% 3.07/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f81,plain,(
% 3.07/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f16])).
% 3.07/1.00  
% 3.07/1.00  fof(f14,axiom,(
% 3.07/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f79,plain,(
% 3.07/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f14])).
% 3.07/1.00  
% 3.07/1.00  fof(f15,axiom,(
% 3.07/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f80,plain,(
% 3.07/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f15])).
% 3.07/1.00  
% 3.07/1.00  fof(f106,plain,(
% 3.07/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.07/1.00    inference(definition_unfolding,[],[f79,f80])).
% 3.07/1.00  
% 3.07/1.00  fof(f107,plain,(
% 3.07/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.07/1.00    inference(definition_unfolding,[],[f81,f106])).
% 3.07/1.00  
% 3.07/1.00  fof(f108,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.07/1.00    inference(definition_unfolding,[],[f78,f107])).
% 3.07/1.00  
% 3.07/1.00  fof(f109,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.07/1.00    inference(definition_unfolding,[],[f77,f108])).
% 3.07/1.00  
% 3.07/1.00  fof(f110,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.07/1.00    inference(definition_unfolding,[],[f83,f109])).
% 3.07/1.00  
% 3.07/1.00  fof(f111,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k6_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 3.07/1.00    inference(definition_unfolding,[],[f66,f110])).
% 3.07/1.00  
% 3.07/1.00  fof(f115,plain,(
% 3.07/1.00    ( ! [X0] : (k1_xboole_0 = k3_tarski(k6_enumset1(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) )),
% 3.07/1.00    inference(definition_unfolding,[],[f76,f111])).
% 3.07/1.00  
% 3.07/1.00  fof(f3,axiom,(
% 3.07/1.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f35,plain,(
% 3.07/1.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.07/1.00    inference(rectify,[],[f3])).
% 3.07/1.00  
% 3.07/1.00  fof(f67,plain,(
% 3.07/1.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.07/1.00    inference(cnf_transformation,[],[f35])).
% 3.07/1.00  
% 3.07/1.00  fof(f113,plain,(
% 3.07/1.00    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.07/1.00    inference(definition_unfolding,[],[f67,f110])).
% 3.07/1.00  
% 3.07/1.00  fof(f27,axiom,(
% 3.07/1.00    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f43,plain,(
% 3.07/1.00    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f27])).
% 3.07/1.00  
% 3.07/1.00  fof(f97,plain,(
% 3.07/1.00    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f43])).
% 3.07/1.00  
% 3.07/1.00  fof(f7,axiom,(
% 3.07/1.00    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f39,plain,(
% 3.07/1.00    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.07/1.00    inference(ennf_transformation,[],[f7])).
% 3.07/1.00  
% 3.07/1.00  fof(f72,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f39])).
% 3.07/1.00  
% 3.07/1.00  fof(f26,axiom,(
% 3.07/1.00    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f42,plain,(
% 3.07/1.00    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.07/1.00    inference(ennf_transformation,[],[f26])).
% 3.07/1.00  
% 3.07/1.00  fof(f96,plain,(
% 3.07/1.00    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f42])).
% 3.07/1.00  
% 3.07/1.00  fof(f121,plain,(
% 3.07/1.00    ( ! [X0] : (k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(definition_unfolding,[],[f96,f110])).
% 3.07/1.00  
% 3.07/1.00  fof(f20,axiom,(
% 3.07/1.00    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f86,plain,(
% 3.07/1.00    k1_tarski(k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.07/1.00    inference(cnf_transformation,[],[f20])).
% 3.07/1.00  
% 3.07/1.00  fof(f17,axiom,(
% 3.07/1.00    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f82,plain,(
% 3.07/1.00    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f17])).
% 3.07/1.00  
% 3.07/1.00  fof(f112,plain,(
% 3.07/1.00    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.07/1.00    inference(definition_unfolding,[],[f82,f107])).
% 3.07/1.00  
% 3.07/1.00  fof(f116,plain,(
% 3.07/1.00    k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0)),
% 3.07/1.00    inference(definition_unfolding,[],[f86,f112])).
% 3.07/1.00  
% 3.07/1.00  fof(f22,axiom,(
% 3.07/1.00    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f90,plain,(
% 3.07/1.00    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.07/1.00    inference(cnf_transformation,[],[f22])).
% 3.07/1.00  
% 3.07/1.00  fof(f33,conjecture,(
% 3.07/1.00    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f34,negated_conjecture,(
% 3.07/1.00    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 3.07/1.00    inference(negated_conjecture,[],[f33])).
% 3.07/1.00  
% 3.07/1.00  fof(f36,plain,(
% 3.07/1.00    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 3.07/1.00    inference(flattening,[],[f34])).
% 3.07/1.00  
% 3.07/1.00  fof(f105,plain,(
% 3.07/1.00    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 3.07/1.00    inference(cnf_transformation,[],[f36])).
% 3.07/1.00  
% 3.07/1.00  cnf(c_5,plain,
% 3.07/1.00      ( v1_xboole_0(sK1) ),
% 3.07/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1214,plain,
% 3.07/1.00      ( v1_xboole_0(sK1) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4,plain,
% 3.07/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.07/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1215,plain,
% 3.07/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1419,plain,
% 3.07/1.00      ( sK1 = k1_xboole_0 ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1214,c_1215]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1421,plain,
% 3.07/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_1419,c_1214]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_20,plain,
% 3.07/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1207,plain,
% 3.07/1.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1536,plain,
% 3.07/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1421,c_1207]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_28,plain,
% 3.07/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1199,plain,
% 3.07/1.00      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 3.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3287,plain,
% 3.07/1.00      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1536,c_1199]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_26,plain,
% 3.07/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1201,plain,
% 3.07/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.07/1.00      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1728,plain,
% 3.07/1.00      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1201,c_1215]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1868,plain,
% 3.07/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1421,c_1728]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3294,plain,
% 3.07/1.00      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.07/1.00      inference(light_normalisation,[status(thm)],[c_3287,c_1868]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_27,plain,
% 3.07/1.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 3.07/1.00      | ~ v1_relat_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1200,plain,
% 3.07/1.00      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 3.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4627,plain,
% 3.07/1.00      ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k1_xboole_0)) = iProver_top
% 3.07/1.00      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_3294,c_1200]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_29,plain,
% 3.07/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1198,plain,
% 3.07/1.00      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 3.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3153,plain,
% 3.07/1.00      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1536,c_1198]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4635,plain,
% 3.07/1.00      ( r1_tarski(k4_relat_1(k1_xboole_0),k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
% 3.07/1.00      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 3.07/1.00      inference(light_normalisation,[status(thm)],[c_4627,c_3153]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_12,plain,
% 3.07/1.00      ( k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k4_xboole_0(X1,X2)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_11,plain,
% 3.07/1.00      ( k3_tarski(k6_enumset1(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) = k1_xboole_0 ),
% 3.07/1.00      inference(cnf_transformation,[],[f115]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2077,plain,
% 3.07/1.00      ( k3_tarski(k6_enumset1(k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)),k2_zfmisc_1(X0,k4_xboole_0(X1,X1)))) = k1_xboole_0 ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3,plain,
% 3.07/1.00      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.07/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2079,plain,
% 3.07/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_11,c_3]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2239,plain,
% 3.07/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2077,c_3,c_2079]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4636,plain,
% 3.07/1.00      ( r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 3.07/1.00      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_4635,c_2239]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_25,plain,
% 3.07/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_53,plain,
% 3.07/1.00      ( v1_relat_1(X0) != iProver_top
% 3.07/1.00      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_55,plain,
% 3.07/1.00      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 3.07/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_53]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_68,plain,
% 3.07/1.00      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_70,plain,
% 3.07/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.07/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_68]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6049,plain,
% 3.07/1.00      ( r1_tarski(k4_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_4636,c_55,c_70,c_1421]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_8,plain,
% 3.07/1.00      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 3.07/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1211,plain,
% 3.07/1.00      ( k1_xboole_0 = X0
% 3.07/1.00      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2932,plain,
% 3.07/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2079,c_1211]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6055,plain,
% 3.07/1.00      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_6049,c_2932]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6069,plain,
% 3.07/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_6055,c_3294]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_24,plain,
% 3.07/1.00      ( ~ v1_relat_1(X0)
% 3.07/1.00      | k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1203,plain,
% 3.07/1.00      ( k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 3.07/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1945,plain,
% 3.07/1.00      ( k3_tarski(k6_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0) ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1536,c_1203]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1946,plain,
% 3.07/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))) = k3_relat_1(k1_xboole_0) ),
% 3.07/1.00      inference(light_normalisation,[status(thm)],[c_1945,c_1868]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6502,plain,
% 3.07/1.00      ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k3_relat_1(k1_xboole_0) ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_6069,c_1946]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_14,plain,
% 3.07/1.00      ( k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6503,plain,
% 3.07/1.00      ( k3_tarski(k1_zfmisc_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0) ),
% 3.07/1.00      inference(light_normalisation,[status(thm)],[c_6502,c_14]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_18,plain,
% 3.07/1.00      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.07/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6504,plain,
% 3.07/1.00      ( k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_6503,c_18]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_583,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1406,plain,
% 3.07/1.00      ( k3_relat_1(k1_xboole_0) != X0
% 3.07/1.00      | k1_xboole_0 != X0
% 3.07/1.00      | k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_583]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1407,plain,
% 3.07/1.00      ( k3_relat_1(k1_xboole_0) != k1_xboole_0
% 3.07/1.00      | k1_xboole_0 = k3_relat_1(k1_xboole_0)
% 3.07/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1406]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_582,plain,( X0 = X0 ),theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_615,plain,
% 3.07/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_582]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_33,negated_conjecture,
% 3.07/1.00      ( k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(contradiction,plain,
% 3.07/1.00      ( $false ),
% 3.07/1.00      inference(minisat,[status(thm)],[c_6504,c_1407,c_615,c_33]) ).
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  ------                               Statistics
% 3.07/1.00  
% 3.07/1.00  ------ General
% 3.07/1.00  
% 3.07/1.00  abstr_ref_over_cycles:                  0
% 3.07/1.00  abstr_ref_under_cycles:                 0
% 3.07/1.00  gc_basic_clause_elim:                   0
% 3.07/1.00  forced_gc_time:                         0
% 3.07/1.00  parsing_time:                           0.011
% 3.07/1.00  unif_index_cands_time:                  0.
% 3.07/1.00  unif_index_add_time:                    0.
% 3.07/1.00  orderings_time:                         0.
% 3.07/1.00  out_proof_time:                         0.01
% 3.07/1.00  total_time:                             0.228
% 3.07/1.00  num_of_symbols:                         53
% 3.07/1.00  num_of_terms:                           6755
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing
% 3.07/1.00  
% 3.07/1.00  num_of_splits:                          0
% 3.07/1.00  num_of_split_atoms:                     0
% 3.07/1.00  num_of_reused_defs:                     0
% 3.07/1.00  num_eq_ax_congr_red:                    12
% 3.07/1.00  num_of_sem_filtered_clauses:            1
% 3.07/1.00  num_of_subtypes:                        0
% 3.07/1.00  monotx_restored_types:                  0
% 3.07/1.00  sat_num_of_epr_types:                   0
% 3.07/1.00  sat_num_of_non_cyclic_types:            0
% 3.07/1.00  sat_guarded_non_collapsed_types:        0
% 3.07/1.00  num_pure_diseq_elim:                    0
% 3.07/1.00  simp_replaced_by:                       0
% 3.07/1.00  res_preprocessed:                       137
% 3.07/1.00  prep_upred:                             0
% 3.07/1.00  prep_unflattend:                        22
% 3.07/1.00  smt_new_axioms:                         0
% 3.07/1.00  pred_elim_cands:                        4
% 3.07/1.00  pred_elim:                              0
% 3.07/1.00  pred_elim_cl:                           0
% 3.07/1.00  pred_elim_cycles:                       1
% 3.07/1.00  merged_defs:                            6
% 3.07/1.00  merged_defs_ncl:                        0
% 3.07/1.00  bin_hyper_res:                          6
% 3.07/1.00  prep_cycles:                            3
% 3.07/1.00  pred_elim_time:                         0.003
% 3.07/1.00  splitting_time:                         0.
% 3.07/1.00  sem_filter_time:                        0.
% 3.07/1.00  monotx_time:                            0.
% 3.07/1.00  subtype_inf_time:                       0.
% 3.07/1.00  
% 3.07/1.00  ------ Problem properties
% 3.07/1.00  
% 3.07/1.00  clauses:                                34
% 3.07/1.00  conjectures:                            1
% 3.07/1.00  epr:                                    4
% 3.07/1.00  horn:                                   31
% 3.07/1.00  ground:                                 3
% 3.07/1.00  unary:                                  12
% 3.07/1.00  binary:                                 18
% 3.07/1.00  lits:                                   60
% 3.07/1.00  lits_eq:                                22
% 3.07/1.00  fd_pure:                                0
% 3.07/1.00  fd_pseudo:                              0
% 3.07/1.00  fd_cond:                                2
% 3.07/1.00  fd_pseudo_cond:                         1
% 3.07/1.00  ac_symbols:                             0
% 3.07/1.00  
% 3.07/1.00  ------ Propositional Solver
% 3.07/1.00  
% 3.07/1.00  prop_solver_calls:                      24
% 3.07/1.00  prop_fast_solver_calls:                 740
% 3.07/1.00  smt_solver_calls:                       0
% 3.07/1.00  smt_fast_solver_calls:                  0
% 3.07/1.00  prop_num_of_clauses:                    2613
% 3.07/1.00  prop_preprocess_simplified:             8437
% 3.07/1.00  prop_fo_subsumed:                       1
% 3.07/1.00  prop_solver_time:                       0.
% 3.07/1.00  smt_solver_time:                        0.
% 3.07/1.00  smt_fast_solver_time:                   0.
% 3.07/1.00  prop_fast_solver_time:                  0.
% 3.07/1.00  prop_unsat_core_time:                   0.
% 3.07/1.00  
% 3.07/1.00  ------ QBF
% 3.07/1.00  
% 3.07/1.00  qbf_q_res:                              0
% 3.07/1.00  qbf_num_tautologies:                    0
% 3.07/1.00  qbf_prep_cycles:                        0
% 3.07/1.00  
% 3.07/1.00  ------ BMC1
% 3.07/1.00  
% 3.07/1.00  bmc1_current_bound:                     -1
% 3.07/1.00  bmc1_last_solved_bound:                 -1
% 3.07/1.00  bmc1_unsat_core_size:                   -1
% 3.07/1.00  bmc1_unsat_core_parents_size:           -1
% 3.07/1.00  bmc1_merge_next_fun:                    0
% 3.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation
% 3.07/1.00  
% 3.07/1.00  inst_num_of_clauses:                    920
% 3.07/1.00  inst_num_in_passive:                    485
% 3.07/1.00  inst_num_in_active:                     367
% 3.07/1.00  inst_num_in_unprocessed:                68
% 3.07/1.00  inst_num_of_loops:                      410
% 3.07/1.00  inst_num_of_learning_restarts:          0
% 3.07/1.00  inst_num_moves_active_passive:          40
% 3.07/1.00  inst_lit_activity:                      0
% 3.07/1.00  inst_lit_activity_moves:                0
% 3.07/1.00  inst_num_tautologies:                   0
% 3.07/1.00  inst_num_prop_implied:                  0
% 3.07/1.00  inst_num_existing_simplified:           0
% 3.07/1.00  inst_num_eq_res_simplified:             0
% 3.07/1.00  inst_num_child_elim:                    0
% 3.07/1.00  inst_num_of_dismatching_blockings:      154
% 3.07/1.00  inst_num_of_non_proper_insts:           683
% 3.07/1.00  inst_num_of_duplicates:                 0
% 3.07/1.00  inst_inst_num_from_inst_to_res:         0
% 3.07/1.00  inst_dismatching_checking_time:         0.
% 3.07/1.00  
% 3.07/1.00  ------ Resolution
% 3.07/1.00  
% 3.07/1.00  res_num_of_clauses:                     0
% 3.07/1.00  res_num_in_passive:                     0
% 3.07/1.00  res_num_in_active:                      0
% 3.07/1.00  res_num_of_loops:                       140
% 3.07/1.00  res_forward_subset_subsumed:            51
% 3.07/1.00  res_backward_subset_subsumed:           0
% 3.07/1.00  res_forward_subsumed:                   0
% 3.07/1.00  res_backward_subsumed:                  0
% 3.07/1.00  res_forward_subsumption_resolution:     0
% 3.07/1.00  res_backward_subsumption_resolution:    0
% 3.07/1.00  res_clause_to_clause_subsumption:       429
% 3.07/1.00  res_orphan_elimination:                 0
% 3.07/1.00  res_tautology_del:                      69
% 3.07/1.00  res_num_eq_res_simplified:              0
% 3.07/1.00  res_num_sel_changes:                    0
% 3.07/1.00  res_moves_from_active_to_pass:          0
% 3.07/1.00  
% 3.07/1.00  ------ Superposition
% 3.07/1.00  
% 3.07/1.00  sup_time_total:                         0.
% 3.07/1.00  sup_time_generating:                    0.
% 3.07/1.00  sup_time_sim_full:                      0.
% 3.07/1.00  sup_time_sim_immed:                     0.
% 3.07/1.00  
% 3.07/1.00  sup_num_of_clauses:                     118
% 3.07/1.00  sup_num_in_active:                      66
% 3.07/1.00  sup_num_in_passive:                     52
% 3.07/1.00  sup_num_of_loops:                       81
% 3.07/1.00  sup_fw_superposition:                   147
% 3.07/1.00  sup_bw_superposition:                   57
% 3.07/1.00  sup_immediate_simplified:               92
% 3.07/1.00  sup_given_eliminated:                   2
% 3.07/1.00  comparisons_done:                       0
% 3.07/1.00  comparisons_avoided:                    0
% 3.07/1.00  
% 3.07/1.00  ------ Simplifications
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  sim_fw_subset_subsumed:                 11
% 3.07/1.00  sim_bw_subset_subsumed:                 0
% 3.07/1.00  sim_fw_subsumed:                        18
% 3.07/1.00  sim_bw_subsumed:                        0
% 3.07/1.00  sim_fw_subsumption_res:                 0
% 3.07/1.00  sim_bw_subsumption_res:                 0
% 3.07/1.00  sim_tautology_del:                      1
% 3.07/1.00  sim_eq_tautology_del:                   24
% 3.07/1.00  sim_eq_res_simp:                        4
% 3.07/1.00  sim_fw_demodulated:                     37
% 3.07/1.00  sim_bw_demodulated:                     15
% 3.07/1.00  sim_light_normalised:                   64
% 3.07/1.00  sim_joinable_taut:                      0
% 3.07/1.00  sim_joinable_simp:                      0
% 3.07/1.00  sim_ac_normalised:                      0
% 3.07/1.00  sim_smt_subsumption:                    0
% 3.07/1.00  
%------------------------------------------------------------------------------
