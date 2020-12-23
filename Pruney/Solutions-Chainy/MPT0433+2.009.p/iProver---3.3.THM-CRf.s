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
% DateTime   : Thu Dec  3 11:42:52 EST 2020

% Result     : Theorem 8.02s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 284 expanded)
%              Number of clauses        :   58 ( 103 expanded)
%              Number of leaves         :   17 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  206 ( 510 expanded)
%              Number of equality atoms :   91 ( 217 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f31,f31])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23,f22])).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f39,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f39,f40,f40])).

cnf(c_5,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_429,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_615,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_429])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_431,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1083,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_615,c_431])).

cnf(c_1310,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1083])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_432,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1433,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_1310,c_432])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_423,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_424,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_79,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_80,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_79])).

cnf(c_101,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_80])).

cnf(c_422,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_1313,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1083,c_422])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_426,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2877,plain,
    ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_relat_1(X2)) = k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_426])).

cnf(c_22126,plain,
    ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_2877])).

cnf(c_22819,plain,
    ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),sK0)) ),
    inference(superposition,[status(thm)],[c_423,c_22126])).

cnf(c_23098,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_22819,c_429])).

cnf(c_23708,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1433,c_23098])).

cnf(c_22818,plain,
    ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),sK1)) ),
    inference(superposition,[status(thm)],[c_424,c_22126])).

cnf(c_1312,plain,
    ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1083,c_432])).

cnf(c_22843,plain,
    ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_22818,c_1312])).

cnf(c_23456,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_22843,c_429])).

cnf(c_23470,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_23456])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_8905,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK0))
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8906,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK1)) != iProver_top
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8905])).

cnf(c_138,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_767,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))
    | k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != X0
    | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != X1 ),
    inference(instantiation,[status(thm)],[c_138])).

cnf(c_960,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))
    | k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != X1 ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_4054,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),X0)
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))
    | k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0)))
    | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != X0 ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_8528,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))))
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))
    | k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0)))
    | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_4054])).

cnf(c_8529,plain,
    ( k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0)))
    | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))) != iProver_top
    | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8528])).

cnf(c_143,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_961,plain,
    ( k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_1199,plain,
    ( k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k1_relat_1(k1_setfam_1(X0))
    | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) != k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_3649,plain,
    ( k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0)))
    | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_1916,plain,
    ( k1_enumset1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_140,plain,
    ( X0 != X1
    | k1_setfam_1(X0) = k1_setfam_1(X1) ),
    theory(equality)).

cnf(c_1200,plain,
    ( k1_enumset1(sK0,sK0,sK1) != X0
    | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) = k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_1915,plain,
    ( k1_enumset1(sK0,sK0,sK1) != k1_enumset1(sK1,sK1,sK0)
    | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) = k1_setfam_1(k1_enumset1(sK1,sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1200])).

cnf(c_1901,plain,
    ( k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)) = k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1189,plain,
    ( k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)) != X0
    | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) = k1_setfam_1(X0) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_1900,plain,
    ( k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)) != k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))
    | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,plain,
    ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23708,c_23470,c_8906,c_8529,c_3649,c_1916,c_1915,c_1901,c_1900,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 8.02/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.02/1.49  
% 8.02/1.49  ------  iProver source info
% 8.02/1.49  
% 8.02/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.02/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.02/1.49  git: non_committed_changes: false
% 8.02/1.49  git: last_make_outside_of_git: false
% 8.02/1.49  
% 8.02/1.49  ------ 
% 8.02/1.49  ------ Parsing...
% 8.02/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.02/1.49  
% 8.02/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.02/1.49  ------ Proving...
% 8.02/1.49  ------ Problem Properties 
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  clauses                                 13
% 8.02/1.49  conjectures                             3
% 8.02/1.49  EPR                                     3
% 8.02/1.49  Horn                                    13
% 8.02/1.49  unary                                   6
% 8.02/1.49  binary                                  4
% 8.02/1.49  lits                                    23
% 8.02/1.49  lits eq                                 4
% 8.02/1.49  fd_pure                                 0
% 8.02/1.49  fd_pseudo                               0
% 8.02/1.49  fd_cond                                 0
% 8.02/1.49  fd_pseudo_cond                          0
% 8.02/1.49  AC symbols                              0
% 8.02/1.49  
% 8.02/1.49  ------ Input Options Time Limit: Unbounded
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  ------ 
% 8.02/1.49  Current options:
% 8.02/1.49  ------ 
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  ------ Proving...
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  % SZS status Theorem for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  fof(f6,axiom,(
% 8.02/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f30,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f6])).
% 8.02/1.49  
% 8.02/1.49  fof(f7,axiom,(
% 8.02/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f31,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f7])).
% 8.02/1.49  
% 8.02/1.49  fof(f44,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 8.02/1.49    inference(definition_unfolding,[],[f30,f31,f31])).
% 8.02/1.49  
% 8.02/1.49  fof(f4,axiom,(
% 8.02/1.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f28,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 8.02/1.49    inference(cnf_transformation,[],[f4])).
% 8.02/1.49  
% 8.02/1.49  fof(f8,axiom,(
% 8.02/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f32,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 8.02/1.49    inference(cnf_transformation,[],[f8])).
% 8.02/1.49  
% 8.02/1.49  fof(f40,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 8.02/1.49    inference(definition_unfolding,[],[f32,f31])).
% 8.02/1.49  
% 8.02/1.49  fof(f43,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = X0) )),
% 8.02/1.49    inference(definition_unfolding,[],[f28,f40])).
% 8.02/1.49  
% 8.02/1.49  fof(f5,axiom,(
% 8.02/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f29,plain,(
% 8.02/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.02/1.49    inference(cnf_transformation,[],[f5])).
% 8.02/1.49  
% 8.02/1.49  fof(f2,axiom,(
% 8.02/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f15,plain,(
% 8.02/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 8.02/1.49    inference(ennf_transformation,[],[f2])).
% 8.02/1.49  
% 8.02/1.49  fof(f26,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 8.02/1.49    inference(cnf_transformation,[],[f15])).
% 8.02/1.49  
% 8.02/1.49  fof(f41,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) )),
% 8.02/1.49    inference(definition_unfolding,[],[f26,f40])).
% 8.02/1.49  
% 8.02/1.49  fof(f1,axiom,(
% 8.02/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f14,plain,(
% 8.02/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 8.02/1.49    inference(ennf_transformation,[],[f1])).
% 8.02/1.49  
% 8.02/1.49  fof(f25,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f14])).
% 8.02/1.49  
% 8.02/1.49  fof(f12,conjecture,(
% 8.02/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f13,negated_conjecture,(
% 8.02/1.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 8.02/1.49    inference(negated_conjecture,[],[f12])).
% 8.02/1.49  
% 8.02/1.49  fof(f20,plain,(
% 8.02/1.49    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 8.02/1.49    inference(ennf_transformation,[],[f13])).
% 8.02/1.49  
% 8.02/1.49  fof(f23,plain,(
% 8.02/1.49    ( ! [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(sK1))) & v1_relat_1(sK1))) )),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f22,plain,(
% 8.02/1.49    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 8.02/1.49    introduced(choice_axiom,[])).
% 8.02/1.49  
% 8.02/1.49  fof(f24,plain,(
% 8.02/1.49    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 8.02/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23,f22])).
% 8.02/1.49  
% 8.02/1.49  fof(f37,plain,(
% 8.02/1.49    v1_relat_1(sK0)),
% 8.02/1.49    inference(cnf_transformation,[],[f24])).
% 8.02/1.49  
% 8.02/1.49  fof(f38,plain,(
% 8.02/1.49    v1_relat_1(sK1)),
% 8.02/1.49    inference(cnf_transformation,[],[f24])).
% 8.02/1.49  
% 8.02/1.49  fof(f10,axiom,(
% 8.02/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f18,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 8.02/1.49    inference(ennf_transformation,[],[f10])).
% 8.02/1.49  
% 8.02/1.49  fof(f35,plain,(
% 8.02/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f18])).
% 8.02/1.49  
% 8.02/1.49  fof(f9,axiom,(
% 8.02/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f21,plain,(
% 8.02/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.02/1.49    inference(nnf_transformation,[],[f9])).
% 8.02/1.49  
% 8.02/1.49  fof(f34,plain,(
% 8.02/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f21])).
% 8.02/1.49  
% 8.02/1.49  fof(f11,axiom,(
% 8.02/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f19,plain,(
% 8.02/1.49    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 8.02/1.49    inference(ennf_transformation,[],[f11])).
% 8.02/1.49  
% 8.02/1.49  fof(f36,plain,(
% 8.02/1.49    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f19])).
% 8.02/1.49  
% 8.02/1.49  fof(f3,axiom,(
% 8.02/1.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 8.02/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.02/1.49  
% 8.02/1.49  fof(f16,plain,(
% 8.02/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 8.02/1.49    inference(ennf_transformation,[],[f3])).
% 8.02/1.49  
% 8.02/1.49  fof(f17,plain,(
% 8.02/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 8.02/1.49    inference(flattening,[],[f16])).
% 8.02/1.49  
% 8.02/1.49  fof(f27,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 8.02/1.49    inference(cnf_transformation,[],[f17])).
% 8.02/1.49  
% 8.02/1.49  fof(f42,plain,(
% 8.02/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 8.02/1.49    inference(definition_unfolding,[],[f27,f40])).
% 8.02/1.49  
% 8.02/1.49  fof(f39,plain,(
% 8.02/1.49    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 8.02/1.49    inference(cnf_transformation,[],[f24])).
% 8.02/1.49  
% 8.02/1.49  fof(f45,plain,(
% 8.02/1.49    ~r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 8.02/1.49    inference(definition_unfolding,[],[f39,f40,f40])).
% 8.02/1.49  
% 8.02/1.49  cnf(c_5,plain,
% 8.02/1.49      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f44]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3,plain,
% 8.02/1.49      ( k2_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = X0 ),
% 8.02/1.49      inference(cnf_transformation,[],[f43]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4,plain,
% 8.02/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f29]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_429,plain,
% 8.02/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_615,plain,
% 8.02/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_3,c_429]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1,plain,
% 8.02/1.49      ( r1_tarski(X0,X1)
% 8.02/1.49      | ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 8.02/1.49      inference(cnf_transformation,[],[f41]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_431,plain,
% 8.02/1.49      ( r1_tarski(X0,X1) = iProver_top
% 8.02/1.49      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1083,plain,
% 8.02/1.49      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_615,c_431]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1310,plain,
% 8.02/1.49      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_5,c_1083]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_0,plain,
% 8.02/1.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 8.02/1.49      inference(cnf_transformation,[],[f25]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_432,plain,
% 8.02/1.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1433,plain,
% 8.02/1.49      ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X1) = X1 ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_1310,c_432]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_12,negated_conjecture,
% 8.02/1.49      ( v1_relat_1(sK0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f37]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_423,plain,
% 8.02/1.49      ( v1_relat_1(sK0) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_11,negated_conjecture,
% 8.02/1.49      ( v1_relat_1(sK1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f38]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_424,plain,
% 8.02/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8,plain,
% 8.02/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.02/1.49      | ~ v1_relat_1(X1)
% 8.02/1.49      | v1_relat_1(X0) ),
% 8.02/1.49      inference(cnf_transformation,[],[f35]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_6,plain,
% 8.02/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.02/1.49      inference(cnf_transformation,[],[f34]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_79,plain,
% 8.02/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.02/1.49      inference(prop_impl,[status(thm)],[c_6]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_80,plain,
% 8.02/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.02/1.49      inference(renaming,[status(thm)],[c_79]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_101,plain,
% 8.02/1.49      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 8.02/1.49      inference(bin_hyper_res,[status(thm)],[c_8,c_80]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_422,plain,
% 8.02/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.02/1.49      | v1_relat_1(X1) != iProver_top
% 8.02/1.49      | v1_relat_1(X0) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1313,plain,
% 8.02/1.49      ( v1_relat_1(X0) != iProver_top
% 8.02/1.49      | v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_1083,c_422]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_9,plain,
% 8.02/1.49      ( ~ v1_relat_1(X0)
% 8.02/1.49      | ~ v1_relat_1(X1)
% 8.02/1.49      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 8.02/1.49      inference(cnf_transformation,[],[f36]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_426,plain,
% 8.02/1.49      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
% 8.02/1.49      | v1_relat_1(X0) != iProver_top
% 8.02/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2877,plain,
% 8.02/1.49      ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_relat_1(X2)) = k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X2))
% 8.02/1.49      | v1_relat_1(X0) != iProver_top
% 8.02/1.49      | v1_relat_1(X2) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_1313,c_426]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_22126,plain,
% 8.02/1.49      ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),X1))
% 8.02/1.49      | v1_relat_1(X1) != iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_424,c_2877]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_22819,plain,
% 8.02/1.49      ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),sK0)) ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_423,c_22126]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_23098,plain,
% 8.02/1.49      ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),sK0))) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_22819,c_429]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_23708,plain,
% 8.02/1.49      ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK0)) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_1433,c_23098]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_22818,plain,
% 8.02/1.49      ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),sK1)) ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_424,c_22126]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1312,plain,
% 8.02/1.49      ( k2_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = X0 ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_1083,c_432]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_22843,plain,
% 8.02/1.49      ( k2_xboole_0(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
% 8.02/1.49      inference(demodulation,[status(thm)],[c_22818,c_1312]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_23456,plain,
% 8.02/1.49      ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0))),k1_relat_1(sK1)) = iProver_top ),
% 8.02/1.49      inference(superposition,[status(thm)],[c_22843,c_429]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_23470,plain,
% 8.02/1.49      ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK1)) = iProver_top ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_23456]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_2,plain,
% 8.02/1.49      ( ~ r1_tarski(X0,X1)
% 8.02/1.49      | ~ r1_tarski(X0,X2)
% 8.02/1.49      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 8.02/1.49      inference(cnf_transformation,[],[f42]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8905,plain,
% 8.02/1.49      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK1))
% 8.02/1.49      | ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK0))
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8906,plain,
% 8.02/1.49      ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK1)) != iProver_top
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_relat_1(sK0)) != iProver_top
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_8905]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_138,plain,
% 8.02/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 8.02/1.49      theory(equality) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_767,plain,
% 8.02/1.49      ( ~ r1_tarski(X0,X1)
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))
% 8.02/1.49      | k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != X0
% 8.02/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != X1 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_138]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_960,plain,
% 8.02/1.49      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))
% 8.02/1.49      | k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k1_relat_1(X0)
% 8.02/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != X1 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_767]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_4054,plain,
% 8.02/1.49      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),X0)
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))
% 8.02/1.49      | k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0)))
% 8.02/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != X0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_960]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8528,plain,
% 8.02/1.49      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))))
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))
% 8.02/1.49      | k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0)))
% 8.02/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_4054]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_8529,plain,
% 8.02/1.49      ( k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) != k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0)))
% 8.02/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) != k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0))),k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))) != iProver_top
% 8.02/1.49      | r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) = iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_8528]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_143,plain,
% 8.02/1.49      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 8.02/1.49      theory(equality) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_961,plain,
% 8.02/1.49      ( k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k1_relat_1(X0)
% 8.02/1.49      | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) != X0 ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_143]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1199,plain,
% 8.02/1.49      ( k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k1_relat_1(k1_setfam_1(X0))
% 8.02/1.49      | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) != k1_setfam_1(X0) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_961]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_3649,plain,
% 8.02/1.49      ( k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) = k1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK0)))
% 8.02/1.49      | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,sK0)) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1199]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1916,plain,
% 8.02/1.49      ( k1_enumset1(sK0,sK0,sK1) = k1_enumset1(sK1,sK1,sK0) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_140,plain,
% 8.02/1.49      ( X0 != X1 | k1_setfam_1(X0) = k1_setfam_1(X1) ),
% 8.02/1.49      theory(equality) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1200,plain,
% 8.02/1.49      ( k1_enumset1(sK0,sK0,sK1) != X0
% 8.02/1.49      | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) = k1_setfam_1(X0) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_140]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1915,plain,
% 8.02/1.49      ( k1_enumset1(sK0,sK0,sK1) != k1_enumset1(sK1,sK1,sK0)
% 8.02/1.49      | k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) = k1_setfam_1(k1_enumset1(sK1,sK1,sK0)) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1200]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1901,plain,
% 8.02/1.49      ( k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)) = k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1189,plain,
% 8.02/1.49      ( k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)) != X0
% 8.02/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) = k1_setfam_1(X0) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_140]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_1900,plain,
% 8.02/1.49      ( k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)) != k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))
% 8.02/1.49      | k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))) = k1_setfam_1(k1_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))) ),
% 8.02/1.49      inference(instantiation,[status(thm)],[c_1189]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_10,negated_conjecture,
% 8.02/1.49      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
% 8.02/1.49      inference(cnf_transformation,[],[f45]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(c_15,plain,
% 8.02/1.49      ( r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) != iProver_top ),
% 8.02/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.02/1.49  
% 8.02/1.49  cnf(contradiction,plain,
% 8.02/1.49      ( $false ),
% 8.02/1.49      inference(minisat,
% 8.02/1.49                [status(thm)],
% 8.02/1.49                [c_23708,c_23470,c_8906,c_8529,c_3649,c_1916,c_1915,
% 8.02/1.49                 c_1901,c_1900,c_15]) ).
% 8.02/1.49  
% 8.02/1.49  
% 8.02/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.02/1.49  
% 8.02/1.49  ------                               Statistics
% 8.02/1.49  
% 8.02/1.49  ------ Selected
% 8.02/1.49  
% 8.02/1.49  total_time:                             0.811
% 8.02/1.49  
%------------------------------------------------------------------------------
