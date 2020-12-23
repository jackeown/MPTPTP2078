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
% DateTime   : Thu Dec  3 11:46:54 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 138 expanded)
%              Number of clauses        :   45 (  58 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  150 ( 274 expanded)
%              Number of equality atoms :   88 ( 139 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
     => ( k9_relat_1(X0,sK1) != k9_relat_1(k7_relat_1(X0,sK2),sK1)
        & r1_tarski(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X1) != k9_relat_1(k7_relat_1(sK0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f34,f25])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_299,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_303,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1576,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_303])).

cnf(c_0,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_307,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1600,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1576,c_307])).

cnf(c_1604,plain,
    ( k8_relat_1(sK2,k6_relat_1(sK1)) = k6_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_299,c_1600])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_304,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_752,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_307,c_304])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_300,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_536,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_307,c_300])).

cnf(c_2575,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_752,c_536])).

cnf(c_2582,plain,
    ( k7_relat_1(k6_relat_1(sK2),sK1) = k6_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1604,c_2575])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_301,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_643,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_307,c_301])).

cnf(c_7,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_653,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_643,c_7])).

cnf(c_3126,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_2582,c_653])).

cnf(c_3131,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3126,c_7])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_298,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_305,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_820,plain,
    ( k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_298,c_305])).

cnf(c_4122,plain,
    ( k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3131,c_820])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_306,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_302,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_734,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) = k9_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_306,c_302])).

cnf(c_5377,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_298,c_734])).

cnf(c_5409,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k2_relat_1(k7_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4122,c_5377])).

cnf(c_735,plain,
    ( k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_298,c_302])).

cnf(c_5441,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5409,c_735])).

cnf(c_10,negated_conjecture,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_5988,plain,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5441,c_10])).

cnf(c_110,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1698,plain,
    ( k9_relat_1(sK0,sK1) = k9_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5988,c_1698])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.40/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/0.98  
% 3.40/0.98  ------  iProver source info
% 3.40/0.98  
% 3.40/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.40/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/0.98  git: non_committed_changes: false
% 3.40/0.98  git: last_make_outside_of_git: false
% 3.40/0.98  
% 3.40/0.98  ------ 
% 3.40/0.98  ------ Parsing...
% 3.40/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/0.98  ------ Proving...
% 3.40/0.98  ------ Problem Properties 
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  clauses                                 13
% 3.40/0.98  conjectures                             3
% 3.40/0.98  EPR                                     2
% 3.40/0.98  Horn                                    13
% 3.40/0.98  unary                                   6
% 3.40/0.98  binary                                  6
% 3.40/0.98  lits                                    21
% 3.40/0.98  lits eq                                 9
% 3.40/0.98  fd_pure                                 0
% 3.40/0.98  fd_pseudo                               0
% 3.40/0.98  fd_cond                                 0
% 3.40/0.98  fd_pseudo_cond                          0
% 3.40/0.98  AC symbols                              0
% 3.40/0.98  
% 3.40/0.98  ------ Input Options Time Limit: Unbounded
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ 
% 3.40/0.98  Current options:
% 3.40/0.98  ------ 
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ Proving...
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  % SZS status Theorem for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  fof(f11,conjecture,(
% 3.40/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f12,negated_conjecture,(
% 3.40/0.98    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 3.40/0.98    inference(negated_conjecture,[],[f11])).
% 3.40/0.98  
% 3.40/0.98  fof(f21,plain,(
% 3.40/0.98    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 3.40/0.98    inference(ennf_transformation,[],[f12])).
% 3.40/0.98  
% 3.40/0.98  fof(f23,plain,(
% 3.40/0.98    ( ! [X0] : (? [X1,X2] : (k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1) & r1_tarski(X1,X2)) => (k9_relat_1(X0,sK1) != k9_relat_1(k7_relat_1(X0,sK2),sK1) & r1_tarski(sK1,sK2))) )),
% 3.40/0.98    introduced(choice_axiom,[])).
% 3.40/0.98  
% 3.40/0.98  fof(f22,plain,(
% 3.40/0.98    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(sK0,X1) != k9_relat_1(k7_relat_1(sK0,X2),X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 3.40/0.98    introduced(choice_axiom,[])).
% 3.40/0.98  
% 3.40/0.98  fof(f24,plain,(
% 3.40/0.98    (k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 3.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 3.40/0.98  
% 3.40/0.98  fof(f37,plain,(
% 3.40/0.98    r1_tarski(sK1,sK2)),
% 3.40/0.98    inference(cnf_transformation,[],[f24])).
% 3.40/0.98  
% 3.40/0.98  fof(f8,axiom,(
% 3.40/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f33,plain,(
% 3.40/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.40/0.98    inference(cnf_transformation,[],[f8])).
% 3.40/0.98  
% 3.40/0.98  fof(f6,axiom,(
% 3.40/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f16,plain,(
% 3.40/0.98    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.40/0.98    inference(ennf_transformation,[],[f6])).
% 3.40/0.98  
% 3.40/0.98  fof(f17,plain,(
% 3.40/0.98    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.40/0.98    inference(flattening,[],[f16])).
% 3.40/0.98  
% 3.40/0.98  fof(f30,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f17])).
% 3.40/0.98  
% 3.40/0.98  fof(f2,axiom,(
% 3.40/0.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f26,plain,(
% 3.40/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.40/0.98    inference(cnf_transformation,[],[f2])).
% 3.40/0.98  
% 3.40/0.98  fof(f5,axiom,(
% 3.40/0.98    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f15,plain,(
% 3.40/0.98    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 3.40/0.98    inference(ennf_transformation,[],[f5])).
% 3.40/0.98  
% 3.40/0.98  fof(f29,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f15])).
% 3.40/0.98  
% 3.40/0.98  fof(f10,axiom,(
% 3.40/0.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f20,plain,(
% 3.40/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.40/0.98    inference(ennf_transformation,[],[f10])).
% 3.40/0.98  
% 3.40/0.98  fof(f35,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f20])).
% 3.40/0.98  
% 3.40/0.98  fof(f9,axiom,(
% 3.40/0.98    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f19,plain,(
% 3.40/0.98    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.40/0.98    inference(ennf_transformation,[],[f9])).
% 3.40/0.98  
% 3.40/0.98  fof(f34,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f19])).
% 3.40/0.98  
% 3.40/0.98  fof(f1,axiom,(
% 3.40/0.98    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f25,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f1])).
% 3.40/0.98  
% 3.40/0.98  fof(f40,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f34,f25])).
% 3.40/0.98  
% 3.40/0.98  fof(f32,plain,(
% 3.40/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.40/0.98    inference(cnf_transformation,[],[f8])).
% 3.40/0.98  
% 3.40/0.98  fof(f36,plain,(
% 3.40/0.98    v1_relat_1(sK0)),
% 3.40/0.98    inference(cnf_transformation,[],[f24])).
% 3.40/0.98  
% 3.40/0.98  fof(f4,axiom,(
% 3.40/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f14,plain,(
% 3.40/0.98    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.40/0.98    inference(ennf_transformation,[],[f4])).
% 3.40/0.98  
% 3.40/0.98  fof(f28,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f14])).
% 3.40/0.98  
% 3.40/0.98  fof(f39,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f28,f25])).
% 3.40/0.98  
% 3.40/0.98  fof(f3,axiom,(
% 3.40/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f13,plain,(
% 3.40/0.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.40/0.98    inference(ennf_transformation,[],[f3])).
% 3.40/0.98  
% 3.40/0.98  fof(f27,plain,(
% 3.40/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f13])).
% 3.40/0.98  
% 3.40/0.98  fof(f7,axiom,(
% 3.40/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.40/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f18,plain,(
% 3.40/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.40/0.98    inference(ennf_transformation,[],[f7])).
% 3.40/0.98  
% 3.40/0.98  fof(f31,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f18])).
% 3.40/0.98  
% 3.40/0.98  fof(f38,plain,(
% 3.40/0.98    k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1)),
% 3.40/0.98    inference(cnf_transformation,[],[f24])).
% 3.40/0.98  
% 3.40/0.98  cnf(c_11,negated_conjecture,
% 3.40/0.98      ( r1_tarski(sK1,sK2) ),
% 3.40/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_299,plain,
% 3.40/0.98      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_6,plain,
% 3.40/0.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 3.40/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_4,plain,
% 3.40/0.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.40/0.98      | ~ v1_relat_1(X0)
% 3.40/0.98      | k8_relat_1(X1,X0) = X0 ),
% 3.40/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_303,plain,
% 3.40/0.98      ( k8_relat_1(X0,X1) = X1
% 3.40/0.98      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 3.40/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1576,plain,
% 3.40/0.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 3.40/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.40/0.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_6,c_303]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_0,plain,
% 3.40/0.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.40/0.98      inference(cnf_transformation,[],[f26]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_307,plain,
% 3.40/0.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1600,plain,
% 3.40/0.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 3.40/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.40/0.98      inference(forward_subsumption_resolution,
% 3.40/0.98                [status(thm)],
% 3.40/0.98                [c_1576,c_307]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1604,plain,
% 3.40/0.98      ( k8_relat_1(sK2,k6_relat_1(sK1)) = k6_relat_1(sK1) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_299,c_1600]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_3,plain,
% 3.40/0.98      ( ~ v1_relat_1(X0)
% 3.40/0.98      | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 3.40/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_304,plain,
% 3.40/0.98      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 3.40/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_752,plain,
% 3.40/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_307,c_304]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_9,plain,
% 3.40/0.98      ( ~ v1_relat_1(X0)
% 3.40/0.98      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.40/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_300,plain,
% 3.40/0.98      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.40/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_536,plain,
% 3.40/0.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_307,c_300]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_2575,plain,
% 3.40/0.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 3.40/0.98      inference(light_normalisation,[status(thm)],[c_752,c_536]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_2582,plain,
% 3.40/0.98      ( k7_relat_1(k6_relat_1(sK2),sK1) = k6_relat_1(sK1) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_1604,c_2575]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_8,plain,
% 3.40/0.98      ( ~ v1_relat_1(X0)
% 3.40/0.98      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.40/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_301,plain,
% 3.40/0.98      ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 3.40/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_643,plain,
% 3.40/0.98      ( k1_setfam_1(k2_tarski(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_307,c_301]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_7,plain,
% 3.40/0.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.40/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_653,plain,
% 3.40/0.98      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 3.40/0.98      inference(light_normalisation,[status(thm)],[c_643,c_7]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_3126,plain,
% 3.40/0.98      ( k1_setfam_1(k2_tarski(sK2,sK1)) = k1_relat_1(k6_relat_1(sK1)) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_2582,c_653]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_3131,plain,
% 3.40/0.98      ( k1_setfam_1(k2_tarski(sK2,sK1)) = sK1 ),
% 3.40/0.98      inference(demodulation,[status(thm)],[c_3126,c_7]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_12,negated_conjecture,
% 3.40/0.98      ( v1_relat_1(sK0) ),
% 3.40/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_298,plain,
% 3.40/0.98      ( v1_relat_1(sK0) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_2,plain,
% 3.40/0.98      ( ~ v1_relat_1(X0)
% 3.40/0.98      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.40/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_305,plain,
% 3.40/0.98      ( k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 3.40/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_820,plain,
% 3.40/0.98      ( k7_relat_1(sK0,k1_setfam_1(k2_tarski(X0,X1))) = k7_relat_1(k7_relat_1(sK0,X0),X1) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_298,c_305]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_4122,plain,
% 3.40/0.98      ( k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_3131,c_820]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1,plain,
% 3.40/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.40/0.98      inference(cnf_transformation,[],[f27]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_306,plain,
% 3.40/0.98      ( v1_relat_1(X0) != iProver_top
% 3.40/0.98      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_5,plain,
% 3.40/0.98      ( ~ v1_relat_1(X0)
% 3.40/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.40/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_302,plain,
% 3.40/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.40/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_734,plain,
% 3.40/0.98      ( k2_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2)) = k9_relat_1(k7_relat_1(X0,X1),X2)
% 3.40/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_306,c_302]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_5377,plain,
% 3.40/0.98      ( k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_298,c_734]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_5409,plain,
% 3.40/0.98      ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k2_relat_1(k7_relat_1(sK0,sK1)) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_4122,c_5377]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_735,plain,
% 3.40/0.98      ( k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_298,c_302]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_5441,plain,
% 3.40/0.98      ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
% 3.40/0.98      inference(demodulation,[status(thm)],[c_5409,c_735]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_10,negated_conjecture,
% 3.40/0.98      ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
% 3.40/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_5988,plain,
% 3.40/0.98      ( k9_relat_1(sK0,sK1) != k9_relat_1(sK0,sK1) ),
% 3.40/0.98      inference(demodulation,[status(thm)],[c_5441,c_10]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_110,plain,( X0 = X0 ),theory(equality) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1698,plain,
% 3.40/0.98      ( k9_relat_1(sK0,sK1) = k9_relat_1(sK0,sK1) ),
% 3.40/0.98      inference(instantiation,[status(thm)],[c_110]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(contradiction,plain,
% 3.40/0.98      ( $false ),
% 3.40/0.98      inference(minisat,[status(thm)],[c_5988,c_1698]) ).
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  ------                               Statistics
% 3.40/0.98  
% 3.40/0.98  ------ Selected
% 3.40/0.98  
% 3.40/0.98  total_time:                             0.218
% 3.40/0.98  
%------------------------------------------------------------------------------
