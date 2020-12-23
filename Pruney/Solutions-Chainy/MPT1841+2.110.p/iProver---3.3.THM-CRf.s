%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:10 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 176 expanded)
%              Number of clauses        :   36 (  49 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  198 ( 515 expanded)
%              Number of equality atoms :   66 (  82 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK1),X0)
        & m1_subset_1(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f46,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f47,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f53,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f49])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_enumset1(X0,X0,X0))))) ),
    inference(definition_unfolding,[],[f39,f51,f52])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_494,plain,
    ( m1_subset_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_495,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_786,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1)
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_494,c_495])).

cnf(c_10,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_55,plain,
    ( ~ v1_zfmisc_1(X1)
    | ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_5])).

cnf(c_56,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_zfmisc_1(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_55])).

cnf(c_9,negated_conjecture,
    ( v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_56,c_9])).

cnf(c_112,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | ~ v1_subset_1(X0,sK0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(c_132,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | v1_xboole_0(X0)
    | k6_domain_1(sK0,sK1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_112])).

cnf(c_133,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_132])).

cnf(c_492,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_12,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_13,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_134,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(k6_domain_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_544,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_545,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,sK0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_562,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_492,c_13,c_14,c_134,c_545])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_497,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_732,plain,
    ( k6_domain_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_562,c_497])).

cnf(c_787,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_786,c_732])).

cnf(c_1118,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_787,c_13])).

cnf(c_0,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_enumset1(X0,X0,X0))))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_790,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_791,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_790,c_2,c_3])).

cnf(c_1121,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1118,c_791])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:57:39 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 0.99/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.99/0.92  
% 0.99/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.99/0.92  
% 0.99/0.92  ------  iProver source info
% 0.99/0.92  
% 0.99/0.92  git: date: 2020-06-30 10:37:57 +0100
% 0.99/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.99/0.92  git: non_committed_changes: false
% 0.99/0.92  git: last_make_outside_of_git: false
% 0.99/0.92  
% 0.99/0.92  ------ 
% 0.99/0.92  
% 0.99/0.92  ------ Input Options
% 0.99/0.92  
% 0.99/0.92  --out_options                           all
% 0.99/0.92  --tptp_safe_out                         true
% 0.99/0.92  --problem_path                          ""
% 0.99/0.92  --include_path                          ""
% 0.99/0.92  --clausifier                            res/vclausify_rel
% 0.99/0.92  --clausifier_options                    --mode clausify
% 0.99/0.92  --stdin                                 false
% 0.99/0.92  --stats_out                             all
% 0.99/0.92  
% 0.99/0.92  ------ General Options
% 0.99/0.92  
% 0.99/0.92  --fof                                   false
% 0.99/0.92  --time_out_real                         305.
% 0.99/0.92  --time_out_virtual                      -1.
% 0.99/0.92  --symbol_type_check                     false
% 0.99/0.92  --clausify_out                          false
% 0.99/0.92  --sig_cnt_out                           false
% 0.99/0.92  --trig_cnt_out                          false
% 0.99/0.92  --trig_cnt_out_tolerance                1.
% 0.99/0.92  --trig_cnt_out_sk_spl                   false
% 0.99/0.92  --abstr_cl_out                          false
% 0.99/0.92  
% 0.99/0.92  ------ Global Options
% 0.99/0.92  
% 0.99/0.92  --schedule                              default
% 0.99/0.92  --add_important_lit                     false
% 0.99/0.92  --prop_solver_per_cl                    1000
% 0.99/0.92  --min_unsat_core                        false
% 0.99/0.92  --soft_assumptions                      false
% 0.99/0.92  --soft_lemma_size                       3
% 0.99/0.92  --prop_impl_unit_size                   0
% 0.99/0.92  --prop_impl_unit                        []
% 0.99/0.92  --share_sel_clauses                     true
% 0.99/0.92  --reset_solvers                         false
% 0.99/0.92  --bc_imp_inh                            [conj_cone]
% 0.99/0.92  --conj_cone_tolerance                   3.
% 0.99/0.92  --extra_neg_conj                        none
% 0.99/0.92  --large_theory_mode                     true
% 0.99/0.92  --prolific_symb_bound                   200
% 0.99/0.92  --lt_threshold                          2000
% 0.99/0.92  --clause_weak_htbl                      true
% 0.99/0.92  --gc_record_bc_elim                     false
% 0.99/0.92  
% 0.99/0.92  ------ Preprocessing Options
% 0.99/0.92  
% 0.99/0.92  --preprocessing_flag                    true
% 0.99/0.92  --time_out_prep_mult                    0.1
% 0.99/0.92  --splitting_mode                        input
% 0.99/0.92  --splitting_grd                         true
% 0.99/0.92  --splitting_cvd                         false
% 0.99/0.92  --splitting_cvd_svl                     false
% 0.99/0.92  --splitting_nvd                         32
% 0.99/0.92  --sub_typing                            true
% 0.99/0.92  --prep_gs_sim                           true
% 0.99/0.92  --prep_unflatten                        true
% 0.99/0.92  --prep_res_sim                          true
% 0.99/0.92  --prep_upred                            true
% 0.99/0.92  --prep_sem_filter                       exhaustive
% 0.99/0.92  --prep_sem_filter_out                   false
% 0.99/0.92  --pred_elim                             true
% 0.99/0.92  --res_sim_input                         true
% 0.99/0.92  --eq_ax_congr_red                       true
% 0.99/0.92  --pure_diseq_elim                       true
% 0.99/0.92  --brand_transform                       false
% 0.99/0.92  --non_eq_to_eq                          false
% 0.99/0.92  --prep_def_merge                        true
% 0.99/0.92  --prep_def_merge_prop_impl              false
% 0.99/0.92  --prep_def_merge_mbd                    true
% 0.99/0.92  --prep_def_merge_tr_red                 false
% 0.99/0.92  --prep_def_merge_tr_cl                  false
% 0.99/0.92  --smt_preprocessing                     true
% 0.99/0.92  --smt_ac_axioms                         fast
% 0.99/0.92  --preprocessed_out                      false
% 0.99/0.92  --preprocessed_stats                    false
% 0.99/0.92  
% 0.99/0.92  ------ Abstraction refinement Options
% 0.99/0.92  
% 0.99/0.92  --abstr_ref                             []
% 0.99/0.92  --abstr_ref_prep                        false
% 0.99/0.92  --abstr_ref_until_sat                   false
% 0.99/0.92  --abstr_ref_sig_restrict                funpre
% 0.99/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/0.92  --abstr_ref_under                       []
% 0.99/0.92  
% 0.99/0.92  ------ SAT Options
% 0.99/0.92  
% 0.99/0.92  --sat_mode                              false
% 0.99/0.92  --sat_fm_restart_options                ""
% 0.99/0.92  --sat_gr_def                            false
% 0.99/0.92  --sat_epr_types                         true
% 0.99/0.92  --sat_non_cyclic_types                  false
% 0.99/0.92  --sat_finite_models                     false
% 0.99/0.92  --sat_fm_lemmas                         false
% 0.99/0.92  --sat_fm_prep                           false
% 0.99/0.92  --sat_fm_uc_incr                        true
% 0.99/0.92  --sat_out_model                         small
% 0.99/0.92  --sat_out_clauses                       false
% 0.99/0.92  
% 0.99/0.92  ------ QBF Options
% 0.99/0.92  
% 0.99/0.92  --qbf_mode                              false
% 0.99/0.92  --qbf_elim_univ                         false
% 0.99/0.92  --qbf_dom_inst                          none
% 0.99/0.92  --qbf_dom_pre_inst                      false
% 0.99/0.92  --qbf_sk_in                             false
% 0.99/0.92  --qbf_pred_elim                         true
% 0.99/0.92  --qbf_split                             512
% 0.99/0.92  
% 0.99/0.92  ------ BMC1 Options
% 0.99/0.92  
% 0.99/0.92  --bmc1_incremental                      false
% 0.99/0.92  --bmc1_axioms                           reachable_all
% 0.99/0.92  --bmc1_min_bound                        0
% 0.99/0.92  --bmc1_max_bound                        -1
% 0.99/0.92  --bmc1_max_bound_default                -1
% 0.99/0.92  --bmc1_symbol_reachability              true
% 0.99/0.92  --bmc1_property_lemmas                  false
% 0.99/0.92  --bmc1_k_induction                      false
% 0.99/0.92  --bmc1_non_equiv_states                 false
% 0.99/0.92  --bmc1_deadlock                         false
% 0.99/0.92  --bmc1_ucm                              false
% 0.99/0.92  --bmc1_add_unsat_core                   none
% 0.99/0.92  --bmc1_unsat_core_children              false
% 0.99/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/0.92  --bmc1_out_stat                         full
% 0.99/0.92  --bmc1_ground_init                      false
% 0.99/0.92  --bmc1_pre_inst_next_state              false
% 0.99/0.92  --bmc1_pre_inst_state                   false
% 0.99/0.92  --bmc1_pre_inst_reach_state             false
% 0.99/0.92  --bmc1_out_unsat_core                   false
% 0.99/0.92  --bmc1_aig_witness_out                  false
% 0.99/0.92  --bmc1_verbose                          false
% 0.99/0.92  --bmc1_dump_clauses_tptp                false
% 0.99/0.92  --bmc1_dump_unsat_core_tptp             false
% 0.99/0.92  --bmc1_dump_file                        -
% 0.99/0.92  --bmc1_ucm_expand_uc_limit              128
% 0.99/0.92  --bmc1_ucm_n_expand_iterations          6
% 0.99/0.92  --bmc1_ucm_extend_mode                  1
% 0.99/0.92  --bmc1_ucm_init_mode                    2
% 0.99/0.92  --bmc1_ucm_cone_mode                    none
% 0.99/0.92  --bmc1_ucm_reduced_relation_type        0
% 0.99/0.92  --bmc1_ucm_relax_model                  4
% 0.99/0.92  --bmc1_ucm_full_tr_after_sat            true
% 0.99/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/0.92  --bmc1_ucm_layered_model                none
% 0.99/0.92  --bmc1_ucm_max_lemma_size               10
% 0.99/0.92  
% 0.99/0.92  ------ AIG Options
% 0.99/0.92  
% 0.99/0.92  --aig_mode                              false
% 0.99/0.92  
% 0.99/0.92  ------ Instantiation Options
% 0.99/0.92  
% 0.99/0.92  --instantiation_flag                    true
% 0.99/0.92  --inst_sos_flag                         false
% 0.99/0.92  --inst_sos_phase                        true
% 0.99/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/0.92  --inst_lit_sel_side                     num_symb
% 0.99/0.92  --inst_solver_per_active                1400
% 0.99/0.92  --inst_solver_calls_frac                1.
% 0.99/0.92  --inst_passive_queue_type               priority_queues
% 0.99/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/0.92  --inst_passive_queues_freq              [25;2]
% 0.99/0.92  --inst_dismatching                      true
% 0.99/0.92  --inst_eager_unprocessed_to_passive     true
% 0.99/0.92  --inst_prop_sim_given                   true
% 0.99/0.92  --inst_prop_sim_new                     false
% 0.99/0.92  --inst_subs_new                         false
% 0.99/0.92  --inst_eq_res_simp                      false
% 0.99/0.92  --inst_subs_given                       false
% 0.99/0.92  --inst_orphan_elimination               true
% 0.99/0.92  --inst_learning_loop_flag               true
% 0.99/0.92  --inst_learning_start                   3000
% 0.99/0.92  --inst_learning_factor                  2
% 0.99/0.92  --inst_start_prop_sim_after_learn       3
% 0.99/0.92  --inst_sel_renew                        solver
% 0.99/0.92  --inst_lit_activity_flag                true
% 0.99/0.92  --inst_restr_to_given                   false
% 0.99/0.92  --inst_activity_threshold               500
% 0.99/0.92  --inst_out_proof                        true
% 0.99/0.92  
% 0.99/0.92  ------ Resolution Options
% 0.99/0.92  
% 0.99/0.92  --resolution_flag                       true
% 0.99/0.92  --res_lit_sel                           adaptive
% 0.99/0.92  --res_lit_sel_side                      none
% 0.99/0.92  --res_ordering                          kbo
% 0.99/0.92  --res_to_prop_solver                    active
% 0.99/0.92  --res_prop_simpl_new                    false
% 0.99/0.92  --res_prop_simpl_given                  true
% 0.99/0.92  --res_passive_queue_type                priority_queues
% 0.99/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/0.92  --res_passive_queues_freq               [15;5]
% 0.99/0.92  --res_forward_subs                      full
% 0.99/0.92  --res_backward_subs                     full
% 0.99/0.92  --res_forward_subs_resolution           true
% 0.99/0.92  --res_backward_subs_resolution          true
% 0.99/0.92  --res_orphan_elimination                true
% 0.99/0.92  --res_time_limit                        2.
% 0.99/0.92  --res_out_proof                         true
% 0.99/0.92  
% 0.99/0.92  ------ Superposition Options
% 0.99/0.92  
% 0.99/0.92  --superposition_flag                    true
% 0.99/0.92  --sup_passive_queue_type                priority_queues
% 0.99/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/0.92  --sup_passive_queues_freq               [8;1;4]
% 0.99/0.92  --demod_completeness_check              fast
% 0.99/0.92  --demod_use_ground                      true
% 0.99/0.92  --sup_to_prop_solver                    passive
% 0.99/0.92  --sup_prop_simpl_new                    true
% 0.99/0.92  --sup_prop_simpl_given                  true
% 0.99/0.92  --sup_fun_splitting                     false
% 0.99/0.92  --sup_smt_interval                      50000
% 0.99/0.92  
% 0.99/0.92  ------ Superposition Simplification Setup
% 0.99/0.92  
% 0.99/0.92  --sup_indices_passive                   []
% 0.99/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.92  --sup_full_bw                           [BwDemod]
% 0.99/0.92  --sup_immed_triv                        [TrivRules]
% 0.99/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.92  --sup_immed_bw_main                     []
% 0.99/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.92  
% 0.99/0.92  ------ Combination Options
% 0.99/0.92  
% 0.99/0.92  --comb_res_mult                         3
% 0.99/0.92  --comb_sup_mult                         2
% 0.99/0.92  --comb_inst_mult                        10
% 0.99/0.92  
% 0.99/0.92  ------ Debug Options
% 0.99/0.92  
% 0.99/0.92  --dbg_backtrace                         false
% 0.99/0.92  --dbg_dump_prop_clauses                 false
% 0.99/0.92  --dbg_dump_prop_clauses_file            -
% 0.99/0.92  --dbg_out_stat                          false
% 0.99/0.92  ------ Parsing...
% 0.99/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.99/0.92  
% 0.99/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.99/0.92  
% 0.99/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.99/0.92  
% 0.99/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.99/0.92  ------ Proving...
% 0.99/0.92  ------ Problem Properties 
% 0.99/0.92  
% 0.99/0.92  
% 0.99/0.92  clauses                                 10
% 0.99/0.92  conjectures                             2
% 0.99/0.92  EPR                                     3
% 0.99/0.92  Horn                                    8
% 0.99/0.92  unary                                   6
% 0.99/0.92  binary                                  2
% 0.99/0.92  lits                                    16
% 0.99/0.92  lits eq                                 6
% 0.99/0.92  fd_pure                                 0
% 0.99/0.92  fd_pseudo                               0
% 0.99/0.92  fd_cond                                 1
% 0.99/0.92  fd_pseudo_cond                          0
% 0.99/0.92  AC symbols                              0
% 0.99/0.92  
% 0.99/0.92  ------ Schedule dynamic 5 is on 
% 0.99/0.92  
% 0.99/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.99/0.92  
% 0.99/0.92  
% 0.99/0.92  ------ 
% 0.99/0.92  Current options:
% 0.99/0.92  ------ 
% 0.99/0.92  
% 0.99/0.92  ------ Input Options
% 0.99/0.92  
% 0.99/0.92  --out_options                           all
% 0.99/0.92  --tptp_safe_out                         true
% 0.99/0.92  --problem_path                          ""
% 0.99/0.92  --include_path                          ""
% 0.99/0.92  --clausifier                            res/vclausify_rel
% 0.99/0.92  --clausifier_options                    --mode clausify
% 0.99/0.92  --stdin                                 false
% 0.99/0.92  --stats_out                             all
% 0.99/0.92  
% 0.99/0.92  ------ General Options
% 0.99/0.92  
% 0.99/0.92  --fof                                   false
% 0.99/0.92  --time_out_real                         305.
% 0.99/0.92  --time_out_virtual                      -1.
% 0.99/0.92  --symbol_type_check                     false
% 0.99/0.92  --clausify_out                          false
% 0.99/0.92  --sig_cnt_out                           false
% 0.99/0.92  --trig_cnt_out                          false
% 0.99/0.92  --trig_cnt_out_tolerance                1.
% 0.99/0.92  --trig_cnt_out_sk_spl                   false
% 0.99/0.92  --abstr_cl_out                          false
% 0.99/0.92  
% 0.99/0.92  ------ Global Options
% 0.99/0.92  
% 0.99/0.92  --schedule                              default
% 0.99/0.92  --add_important_lit                     false
% 0.99/0.92  --prop_solver_per_cl                    1000
% 0.99/0.92  --min_unsat_core                        false
% 0.99/0.92  --soft_assumptions                      false
% 0.99/0.92  --soft_lemma_size                       3
% 0.99/0.92  --prop_impl_unit_size                   0
% 0.99/0.92  --prop_impl_unit                        []
% 0.99/0.92  --share_sel_clauses                     true
% 0.99/0.92  --reset_solvers                         false
% 0.99/0.92  --bc_imp_inh                            [conj_cone]
% 0.99/0.92  --conj_cone_tolerance                   3.
% 0.99/0.92  --extra_neg_conj                        none
% 0.99/0.92  --large_theory_mode                     true
% 0.99/0.92  --prolific_symb_bound                   200
% 0.99/0.92  --lt_threshold                          2000
% 0.99/0.92  --clause_weak_htbl                      true
% 0.99/0.92  --gc_record_bc_elim                     false
% 0.99/0.92  
% 0.99/0.92  ------ Preprocessing Options
% 0.99/0.92  
% 0.99/0.92  --preprocessing_flag                    true
% 0.99/0.92  --time_out_prep_mult                    0.1
% 0.99/0.92  --splitting_mode                        input
% 0.99/0.92  --splitting_grd                         true
% 0.99/0.92  --splitting_cvd                         false
% 0.99/0.92  --splitting_cvd_svl                     false
% 0.99/0.92  --splitting_nvd                         32
% 0.99/0.92  --sub_typing                            true
% 0.99/0.92  --prep_gs_sim                           true
% 0.99/0.92  --prep_unflatten                        true
% 0.99/0.92  --prep_res_sim                          true
% 0.99/0.92  --prep_upred                            true
% 0.99/0.92  --prep_sem_filter                       exhaustive
% 0.99/0.92  --prep_sem_filter_out                   false
% 0.99/0.92  --pred_elim                             true
% 0.99/0.92  --res_sim_input                         true
% 0.99/0.92  --eq_ax_congr_red                       true
% 0.99/0.92  --pure_diseq_elim                       true
% 0.99/0.92  --brand_transform                       false
% 0.99/0.92  --non_eq_to_eq                          false
% 0.99/0.92  --prep_def_merge                        true
% 0.99/0.92  --prep_def_merge_prop_impl              false
% 0.99/0.92  --prep_def_merge_mbd                    true
% 0.99/0.92  --prep_def_merge_tr_red                 false
% 0.99/0.92  --prep_def_merge_tr_cl                  false
% 0.99/0.92  --smt_preprocessing                     true
% 0.99/0.92  --smt_ac_axioms                         fast
% 0.99/0.92  --preprocessed_out                      false
% 0.99/0.92  --preprocessed_stats                    false
% 0.99/0.92  
% 0.99/0.92  ------ Abstraction refinement Options
% 0.99/0.92  
% 0.99/0.92  --abstr_ref                             []
% 0.99/0.92  --abstr_ref_prep                        false
% 0.99/0.92  --abstr_ref_until_sat                   false
% 0.99/0.92  --abstr_ref_sig_restrict                funpre
% 0.99/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/0.92  --abstr_ref_under                       []
% 0.99/0.92  
% 0.99/0.92  ------ SAT Options
% 0.99/0.92  
% 0.99/0.92  --sat_mode                              false
% 0.99/0.92  --sat_fm_restart_options                ""
% 0.99/0.93  --sat_gr_def                            false
% 0.99/0.93  --sat_epr_types                         true
% 0.99/0.93  --sat_non_cyclic_types                  false
% 0.99/0.93  --sat_finite_models                     false
% 0.99/0.93  --sat_fm_lemmas                         false
% 0.99/0.93  --sat_fm_prep                           false
% 0.99/0.93  --sat_fm_uc_incr                        true
% 0.99/0.93  --sat_out_model                         small
% 0.99/0.93  --sat_out_clauses                       false
% 0.99/0.93  
% 0.99/0.93  ------ QBF Options
% 0.99/0.93  
% 0.99/0.93  --qbf_mode                              false
% 0.99/0.93  --qbf_elim_univ                         false
% 0.99/0.93  --qbf_dom_inst                          none
% 0.99/0.93  --qbf_dom_pre_inst                      false
% 0.99/0.93  --qbf_sk_in                             false
% 0.99/0.93  --qbf_pred_elim                         true
% 0.99/0.93  --qbf_split                             512
% 0.99/0.93  
% 0.99/0.93  ------ BMC1 Options
% 0.99/0.93  
% 0.99/0.93  --bmc1_incremental                      false
% 0.99/0.93  --bmc1_axioms                           reachable_all
% 0.99/0.93  --bmc1_min_bound                        0
% 0.99/0.93  --bmc1_max_bound                        -1
% 0.99/0.93  --bmc1_max_bound_default                -1
% 0.99/0.93  --bmc1_symbol_reachability              true
% 0.99/0.93  --bmc1_property_lemmas                  false
% 0.99/0.93  --bmc1_k_induction                      false
% 0.99/0.93  --bmc1_non_equiv_states                 false
% 0.99/0.93  --bmc1_deadlock                         false
% 0.99/0.93  --bmc1_ucm                              false
% 0.99/0.93  --bmc1_add_unsat_core                   none
% 0.99/0.93  --bmc1_unsat_core_children              false
% 0.99/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/0.93  --bmc1_out_stat                         full
% 0.99/0.93  --bmc1_ground_init                      false
% 0.99/0.93  --bmc1_pre_inst_next_state              false
% 0.99/0.93  --bmc1_pre_inst_state                   false
% 0.99/0.93  --bmc1_pre_inst_reach_state             false
% 0.99/0.93  --bmc1_out_unsat_core                   false
% 0.99/0.93  --bmc1_aig_witness_out                  false
% 0.99/0.93  --bmc1_verbose                          false
% 0.99/0.93  --bmc1_dump_clauses_tptp                false
% 0.99/0.93  --bmc1_dump_unsat_core_tptp             false
% 0.99/0.93  --bmc1_dump_file                        -
% 0.99/0.93  --bmc1_ucm_expand_uc_limit              128
% 0.99/0.93  --bmc1_ucm_n_expand_iterations          6
% 0.99/0.93  --bmc1_ucm_extend_mode                  1
% 0.99/0.93  --bmc1_ucm_init_mode                    2
% 0.99/0.93  --bmc1_ucm_cone_mode                    none
% 0.99/0.93  --bmc1_ucm_reduced_relation_type        0
% 0.99/0.93  --bmc1_ucm_relax_model                  4
% 0.99/0.93  --bmc1_ucm_full_tr_after_sat            true
% 0.99/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/0.93  --bmc1_ucm_layered_model                none
% 0.99/0.93  --bmc1_ucm_max_lemma_size               10
% 0.99/0.93  
% 0.99/0.93  ------ AIG Options
% 0.99/0.93  
% 0.99/0.93  --aig_mode                              false
% 0.99/0.93  
% 0.99/0.93  ------ Instantiation Options
% 0.99/0.93  
% 0.99/0.93  --instantiation_flag                    true
% 0.99/0.93  --inst_sos_flag                         false
% 0.99/0.93  --inst_sos_phase                        true
% 0.99/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/0.93  --inst_lit_sel_side                     none
% 0.99/0.93  --inst_solver_per_active                1400
% 0.99/0.93  --inst_solver_calls_frac                1.
% 0.99/0.93  --inst_passive_queue_type               priority_queues
% 0.99/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/0.93  --inst_passive_queues_freq              [25;2]
% 0.99/0.93  --inst_dismatching                      true
% 0.99/0.93  --inst_eager_unprocessed_to_passive     true
% 0.99/0.93  --inst_prop_sim_given                   true
% 0.99/0.93  --inst_prop_sim_new                     false
% 0.99/0.93  --inst_subs_new                         false
% 0.99/0.93  --inst_eq_res_simp                      false
% 0.99/0.93  --inst_subs_given                       false
% 0.99/0.93  --inst_orphan_elimination               true
% 0.99/0.93  --inst_learning_loop_flag               true
% 0.99/0.93  --inst_learning_start                   3000
% 0.99/0.93  --inst_learning_factor                  2
% 0.99/0.93  --inst_start_prop_sim_after_learn       3
% 0.99/0.93  --inst_sel_renew                        solver
% 0.99/0.93  --inst_lit_activity_flag                true
% 0.99/0.93  --inst_restr_to_given                   false
% 0.99/0.93  --inst_activity_threshold               500
% 0.99/0.93  --inst_out_proof                        true
% 0.99/0.93  
% 0.99/0.93  ------ Resolution Options
% 0.99/0.93  
% 0.99/0.93  --resolution_flag                       false
% 0.99/0.93  --res_lit_sel                           adaptive
% 0.99/0.93  --res_lit_sel_side                      none
% 0.99/0.93  --res_ordering                          kbo
% 0.99/0.93  --res_to_prop_solver                    active
% 0.99/0.93  --res_prop_simpl_new                    false
% 0.99/0.93  --res_prop_simpl_given                  true
% 0.99/0.93  --res_passive_queue_type                priority_queues
% 0.99/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/0.93  --res_passive_queues_freq               [15;5]
% 0.99/0.93  --res_forward_subs                      full
% 0.99/0.93  --res_backward_subs                     full
% 0.99/0.93  --res_forward_subs_resolution           true
% 0.99/0.93  --res_backward_subs_resolution          true
% 0.99/0.93  --res_orphan_elimination                true
% 0.99/0.93  --res_time_limit                        2.
% 0.99/0.93  --res_out_proof                         true
% 0.99/0.93  
% 0.99/0.93  ------ Superposition Options
% 0.99/0.93  
% 0.99/0.93  --superposition_flag                    true
% 0.99/0.93  --sup_passive_queue_type                priority_queues
% 0.99/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/0.93  --sup_passive_queues_freq               [8;1;4]
% 0.99/0.93  --demod_completeness_check              fast
% 0.99/0.93  --demod_use_ground                      true
% 0.99/0.93  --sup_to_prop_solver                    passive
% 0.99/0.93  --sup_prop_simpl_new                    true
% 0.99/0.93  --sup_prop_simpl_given                  true
% 0.99/0.93  --sup_fun_splitting                     false
% 0.99/0.93  --sup_smt_interval                      50000
% 0.99/0.93  
% 0.99/0.93  ------ Superposition Simplification Setup
% 0.99/0.93  
% 0.99/0.93  --sup_indices_passive                   []
% 0.99/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.93  --sup_full_bw                           [BwDemod]
% 0.99/0.93  --sup_immed_triv                        [TrivRules]
% 0.99/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.93  --sup_immed_bw_main                     []
% 0.99/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/0.93  
% 0.99/0.93  ------ Combination Options
% 0.99/0.93  
% 0.99/0.93  --comb_res_mult                         3
% 0.99/0.93  --comb_sup_mult                         2
% 0.99/0.93  --comb_inst_mult                        10
% 0.99/0.93  
% 0.99/0.93  ------ Debug Options
% 0.99/0.93  
% 0.99/0.93  --dbg_backtrace                         false
% 0.99/0.93  --dbg_dump_prop_clauses                 false
% 0.99/0.93  --dbg_dump_prop_clauses_file            -
% 0.99/0.93  --dbg_out_stat                          false
% 0.99/0.93  
% 0.99/0.93  
% 0.99/0.93  
% 0.99/0.93  
% 0.99/0.93  ------ Proving...
% 0.99/0.93  
% 0.99/0.93  
% 0.99/0.93  % SZS status Theorem for theBenchmark.p
% 0.99/0.93  
% 0.99/0.93   Resolution empty clause
% 0.99/0.93  
% 0.99/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 0.99/0.93  
% 0.99/0.93  fof(f15,conjecture,(
% 0.99/0.93    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f16,negated_conjecture,(
% 0.99/0.93    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.99/0.93    inference(negated_conjecture,[],[f15])).
% 0.99/0.93  
% 0.99/0.93  fof(f26,plain,(
% 0.99/0.93    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.99/0.93    inference(ennf_transformation,[],[f16])).
% 0.99/0.93  
% 0.99/0.93  fof(f27,plain,(
% 0.99/0.93    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.99/0.93    inference(flattening,[],[f26])).
% 0.99/0.93  
% 0.99/0.93  fof(f29,plain,(
% 0.99/0.93    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK1),X0) & m1_subset_1(sK1,X0))) )),
% 0.99/0.93    introduced(choice_axiom,[])).
% 0.99/0.93  
% 0.99/0.93  fof(f28,plain,(
% 0.99/0.93    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.99/0.93    introduced(choice_axiom,[])).
% 0.99/0.93  
% 0.99/0.93  fof(f30,plain,(
% 0.99/0.93    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.99/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 0.99/0.93  
% 0.99/0.93  fof(f46,plain,(
% 0.99/0.93    m1_subset_1(sK1,sK0)),
% 0.99/0.93    inference(cnf_transformation,[],[f30])).
% 0.99/0.93  
% 0.99/0.93  fof(f13,axiom,(
% 0.99/0.93    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f22,plain,(
% 0.99/0.93    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.99/0.93    inference(ennf_transformation,[],[f13])).
% 0.99/0.93  
% 0.99/0.93  fof(f23,plain,(
% 0.99/0.93    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.99/0.93    inference(flattening,[],[f22])).
% 0.99/0.93  
% 0.99/0.93  fof(f43,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f23])).
% 0.99/0.93  
% 0.99/0.93  fof(f7,axiom,(
% 0.99/0.93    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f37,plain,(
% 0.99/0.93    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f7])).
% 0.99/0.93  
% 0.99/0.93  fof(f8,axiom,(
% 0.99/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f38,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f8])).
% 0.99/0.93  
% 0.99/0.93  fof(f52,plain,(
% 0.99/0.93    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.99/0.93    inference(definition_unfolding,[],[f37,f38])).
% 0.99/0.93  
% 0.99/0.93  fof(f55,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.99/0.93    inference(definition_unfolding,[],[f43,f52])).
% 0.99/0.93  
% 0.99/0.93  fof(f47,plain,(
% 0.99/0.93    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.99/0.93    inference(cnf_transformation,[],[f30])).
% 0.99/0.93  
% 0.99/0.93  fof(f14,axiom,(
% 0.99/0.93    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f24,plain,(
% 0.99/0.93    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.99/0.93    inference(ennf_transformation,[],[f14])).
% 0.99/0.93  
% 0.99/0.93  fof(f25,plain,(
% 0.99/0.93    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.99/0.93    inference(flattening,[],[f24])).
% 0.99/0.93  
% 0.99/0.93  fof(f44,plain,(
% 0.99/0.93    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f25])).
% 0.99/0.93  
% 0.99/0.93  fof(f10,axiom,(
% 0.99/0.93    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f19,plain,(
% 0.99/0.93    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.99/0.93    inference(ennf_transformation,[],[f10])).
% 0.99/0.93  
% 0.99/0.93  fof(f40,plain,(
% 0.99/0.93    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f19])).
% 0.99/0.93  
% 0.99/0.93  fof(f48,plain,(
% 0.99/0.93    v1_zfmisc_1(sK0)),
% 0.99/0.93    inference(cnf_transformation,[],[f30])).
% 0.99/0.93  
% 0.99/0.93  fof(f45,plain,(
% 0.99/0.93    ~v1_xboole_0(sK0)),
% 0.99/0.93    inference(cnf_transformation,[],[f30])).
% 0.99/0.93  
% 0.99/0.93  fof(f12,axiom,(
% 0.99/0.93    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f20,plain,(
% 0.99/0.93    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.99/0.93    inference(ennf_transformation,[],[f12])).
% 0.99/0.93  
% 0.99/0.93  fof(f21,plain,(
% 0.99/0.93    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.99/0.93    inference(flattening,[],[f20])).
% 0.99/0.93  
% 0.99/0.93  fof(f42,plain,(
% 0.99/0.93    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f21])).
% 0.99/0.93  
% 0.99/0.93  fof(f2,axiom,(
% 0.99/0.93    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f18,plain,(
% 0.99/0.93    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.99/0.93    inference(ennf_transformation,[],[f2])).
% 0.99/0.93  
% 0.99/0.93  fof(f32,plain,(
% 0.99/0.93    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f18])).
% 0.99/0.93  
% 0.99/0.93  fof(f1,axiom,(
% 0.99/0.93    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f17,plain,(
% 0.99/0.93    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.99/0.93    inference(rectify,[],[f1])).
% 0.99/0.93  
% 0.99/0.93  fof(f31,plain,(
% 0.99/0.93    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.99/0.93    inference(cnf_transformation,[],[f17])).
% 0.99/0.93  
% 0.99/0.93  fof(f11,axiom,(
% 0.99/0.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f41,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.99/0.93    inference(cnf_transformation,[],[f11])).
% 0.99/0.93  
% 0.99/0.93  fof(f49,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.99/0.93    inference(definition_unfolding,[],[f41,f38])).
% 0.99/0.93  
% 0.99/0.93  fof(f53,plain,(
% 0.99/0.93    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.99/0.93    inference(definition_unfolding,[],[f31,f49])).
% 0.99/0.93  
% 0.99/0.93  fof(f9,axiom,(
% 0.99/0.93    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f39,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f9])).
% 0.99/0.93  
% 0.99/0.93  fof(f6,axiom,(
% 0.99/0.93    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f36,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f6])).
% 0.99/0.93  
% 0.99/0.93  fof(f3,axiom,(
% 0.99/0.93    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f33,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.99/0.93    inference(cnf_transformation,[],[f3])).
% 0.99/0.93  
% 0.99/0.93  fof(f50,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.99/0.93    inference(definition_unfolding,[],[f33,f49])).
% 0.99/0.93  
% 0.99/0.93  fof(f51,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 0.99/0.93    inference(definition_unfolding,[],[f36,f50])).
% 0.99/0.93  
% 0.99/0.93  fof(f54,plain,(
% 0.99/0.93    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_enumset1(X0,X0,X0)))))) )),
% 0.99/0.93    inference(definition_unfolding,[],[f39,f51,f52])).
% 0.99/0.93  
% 0.99/0.93  fof(f4,axiom,(
% 0.99/0.93    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f34,plain,(
% 0.99/0.93    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.99/0.93    inference(cnf_transformation,[],[f4])).
% 0.99/0.93  
% 0.99/0.93  fof(f5,axiom,(
% 0.99/0.93    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.99/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.99/0.93  
% 0.99/0.93  fof(f35,plain,(
% 0.99/0.93    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.99/0.93    inference(cnf_transformation,[],[f5])).
% 0.99/0.93  
% 0.99/0.93  cnf(c_11,negated_conjecture,
% 0.99/0.93      ( m1_subset_1(sK1,sK0) ),
% 0.99/0.93      inference(cnf_transformation,[],[f46]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_494,plain,
% 0.99/0.93      ( m1_subset_1(sK1,sK0) = iProver_top ),
% 0.99/0.93      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_7,plain,
% 0.99/0.93      ( ~ m1_subset_1(X0,X1)
% 0.99/0.93      | v1_xboole_0(X1)
% 0.99/0.93      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 0.99/0.93      inference(cnf_transformation,[],[f55]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_495,plain,
% 0.99/0.93      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 0.99/0.93      | m1_subset_1(X0,X1) != iProver_top
% 0.99/0.93      | v1_xboole_0(X1) = iProver_top ),
% 0.99/0.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_786,plain,
% 0.99/0.93      ( k1_enumset1(sK1,sK1,sK1) = k6_domain_1(sK0,sK1)
% 0.99/0.93      | v1_xboole_0(sK0) = iProver_top ),
% 0.99/0.93      inference(superposition,[status(thm)],[c_494,c_495]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_10,negated_conjecture,
% 0.99/0.93      ( v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
% 0.99/0.93      inference(cnf_transformation,[],[f47]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_8,plain,
% 0.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.99/0.93      | ~ v1_subset_1(X0,X1)
% 0.99/0.93      | ~ v1_zfmisc_1(X1)
% 0.99/0.93      | v1_xboole_0(X1)
% 0.99/0.93      | v1_xboole_0(X0) ),
% 0.99/0.93      inference(cnf_transformation,[],[f44]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_5,plain,
% 0.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.99/0.93      | ~ v1_subset_1(X0,X1)
% 0.99/0.93      | ~ v1_xboole_0(X1) ),
% 0.99/0.93      inference(cnf_transformation,[],[f40]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_55,plain,
% 0.99/0.93      ( ~ v1_zfmisc_1(X1)
% 0.99/0.93      | ~ v1_subset_1(X0,X1)
% 0.99/0.93      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.99/0.93      | v1_xboole_0(X0) ),
% 0.99/0.93      inference(global_propositional_subsumption,[status(thm)],[c_8,c_5]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_56,plain,
% 0.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.99/0.93      | ~ v1_subset_1(X0,X1)
% 0.99/0.93      | ~ v1_zfmisc_1(X1)
% 0.99/0.93      | v1_xboole_0(X0) ),
% 0.99/0.93      inference(renaming,[status(thm)],[c_55]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_9,negated_conjecture,
% 0.99/0.93      ( v1_zfmisc_1(sK0) ),
% 0.99/0.93      inference(cnf_transformation,[],[f48]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_111,plain,
% 0.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.99/0.93      | ~ v1_subset_1(X0,X1)
% 0.99/0.93      | v1_xboole_0(X0)
% 0.99/0.93      | sK0 != X1 ),
% 0.99/0.93      inference(resolution_lifted,[status(thm)],[c_56,c_9]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_112,plain,
% 0.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
% 0.99/0.93      | ~ v1_subset_1(X0,sK0)
% 0.99/0.93      | v1_xboole_0(X0) ),
% 0.99/0.93      inference(unflattening,[status(thm)],[c_111]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_132,plain,
% 0.99/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
% 0.99/0.93      | v1_xboole_0(X0)
% 0.99/0.93      | k6_domain_1(sK0,sK1) != X0
% 0.99/0.93      | sK0 != sK0 ),
% 0.99/0.93      inference(resolution_lifted,[status(thm)],[c_10,c_112]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_133,plain,
% 0.99/0.93      ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
% 0.99/0.93      | v1_xboole_0(k6_domain_1(sK0,sK1)) ),
% 0.99/0.93      inference(unflattening,[status(thm)],[c_132]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_492,plain,
% 0.99/0.93      ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 0.99/0.93      | v1_xboole_0(k6_domain_1(sK0,sK1)) = iProver_top ),
% 0.99/0.93      inference(predicate_to_equality,[status(thm)],[c_133]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_12,negated_conjecture,
% 0.99/0.93      ( ~ v1_xboole_0(sK0) ),
% 0.99/0.93      inference(cnf_transformation,[],[f45]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_13,plain,
% 0.99/0.93      ( v1_xboole_0(sK0) != iProver_top ),
% 0.99/0.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_14,plain,
% 0.99/0.93      ( m1_subset_1(sK1,sK0) = iProver_top ),
% 0.99/0.93      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_134,plain,
% 0.99/0.93      ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) != iProver_top
% 0.99/0.93      | v1_xboole_0(k6_domain_1(sK0,sK1)) = iProver_top ),
% 0.99/0.93      inference(predicate_to_equality,[status(thm)],[c_133]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_6,plain,
% 0.99/0.93      ( ~ m1_subset_1(X0,X1)
% 0.99/0.93      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 0.99/0.93      | v1_xboole_0(X1) ),
% 0.99/0.93      inference(cnf_transformation,[],[f42]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_544,plain,
% 0.99/0.93      ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
% 0.99/0.93      | ~ m1_subset_1(sK1,sK0)
% 0.99/0.93      | v1_xboole_0(sK0) ),
% 0.99/0.93      inference(instantiation,[status(thm)],[c_6]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_545,plain,
% 0.99/0.93      ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) = iProver_top
% 0.99/0.93      | m1_subset_1(sK1,sK0) != iProver_top
% 0.99/0.93      | v1_xboole_0(sK0) = iProver_top ),
% 0.99/0.93      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_562,plain,
% 0.99/0.93      ( v1_xboole_0(k6_domain_1(sK0,sK1)) = iProver_top ),
% 0.99/0.93      inference(global_propositional_subsumption,
% 0.99/0.93                [status(thm)],
% 0.99/0.93                [c_492,c_13,c_14,c_134,c_545]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_1,plain,
% 0.99/0.93      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 0.99/0.93      inference(cnf_transformation,[],[f32]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_497,plain,
% 0.99/0.93      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 0.99/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_732,plain,
% 0.99/0.93      ( k6_domain_1(sK0,sK1) = k1_xboole_0 ),
% 0.99/0.93      inference(superposition,[status(thm)],[c_562,c_497]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_787,plain,
% 0.99/0.93      ( k1_enumset1(sK1,sK1,sK1) = k1_xboole_0
% 0.99/0.93      | v1_xboole_0(sK0) = iProver_top ),
% 0.99/0.93      inference(light_normalisation,[status(thm)],[c_786,c_732]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_1118,plain,
% 0.99/0.93      ( k1_enumset1(sK1,sK1,sK1) = k1_xboole_0 ),
% 0.99/0.93      inference(global_propositional_subsumption,[status(thm)],[c_787,c_13]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_0,plain,
% 0.99/0.93      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
% 0.99/0.93      inference(cnf_transformation,[],[f53]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_4,plain,
% 0.99/0.93      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_enumset1(X0,X0,X0))))) != k1_xboole_0 ),
% 0.99/0.93      inference(cnf_transformation,[],[f54]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_790,plain,
% 0.99/0.93      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) != k1_xboole_0 ),
% 0.99/0.93      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_2,plain,
% 0.99/0.93      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.99/0.93      inference(cnf_transformation,[],[f34]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_3,plain,
% 0.99/0.93      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 0.99/0.93      inference(cnf_transformation,[],[f35]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_791,plain,
% 0.99/0.93      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 0.99/0.93      inference(demodulation,[status(thm)],[c_790,c_2,c_3]) ).
% 0.99/0.93  
% 0.99/0.93  cnf(c_1121,plain,
% 0.99/0.93      ( $false ),
% 0.99/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_1118,c_791]) ).
% 0.99/0.93  
% 0.99/0.93  
% 0.99/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 0.99/0.93  
% 0.99/0.93  ------                               Statistics
% 0.99/0.93  
% 0.99/0.93  ------ General
% 0.99/0.93  
% 0.99/0.93  abstr_ref_over_cycles:                  0
% 0.99/0.93  abstr_ref_under_cycles:                 0
% 0.99/0.93  gc_basic_clause_elim:                   0
% 0.99/0.93  forced_gc_time:                         0
% 0.99/0.93  parsing_time:                           0.008
% 0.99/0.93  unif_index_cands_time:                  0.
% 0.99/0.93  unif_index_add_time:                    0.
% 0.99/0.93  orderings_time:                         0.
% 0.99/0.93  out_proof_time:                         0.011
% 0.99/0.93  total_time:                             0.071
% 0.99/0.93  num_of_symbols:                         43
% 0.99/0.93  num_of_terms:                           964
% 0.99/0.93  
% 0.99/0.93  ------ Preprocessing
% 0.99/0.93  
% 0.99/0.93  num_of_splits:                          0
% 0.99/0.93  num_of_split_atoms:                     0
% 0.99/0.93  num_of_reused_defs:                     0
% 0.99/0.93  num_eq_ax_congr_red:                    7
% 0.99/0.93  num_of_sem_filtered_clauses:            1
% 0.99/0.93  num_of_subtypes:                        0
% 0.99/0.93  monotx_restored_types:                  0
% 0.99/0.93  sat_num_of_epr_types:                   0
% 0.99/0.93  sat_num_of_non_cyclic_types:            0
% 0.99/0.93  sat_guarded_non_collapsed_types:        0
% 0.99/0.93  num_pure_diseq_elim:                    0
% 0.99/0.93  simp_replaced_by:                       0
% 0.99/0.93  res_preprocessed:                       62
% 0.99/0.93  prep_upred:                             0
% 0.99/0.93  prep_unflattend:                        14
% 0.99/0.93  smt_new_axioms:                         0
% 0.99/0.93  pred_elim_cands:                        2
% 0.99/0.93  pred_elim:                              2
% 0.99/0.93  pred_elim_cl:                           3
% 0.99/0.93  pred_elim_cycles:                       4
% 0.99/0.93  merged_defs:                            0
% 0.99/0.93  merged_defs_ncl:                        0
% 0.99/0.93  bin_hyper_res:                          0
% 0.99/0.93  prep_cycles:                            4
% 0.99/0.93  pred_elim_time:                         0.003
% 0.99/0.93  splitting_time:                         0.
% 0.99/0.93  sem_filter_time:                        0.
% 0.99/0.93  monotx_time:                            0.
% 0.99/0.93  subtype_inf_time:                       0.
% 0.99/0.93  
% 0.99/0.93  ------ Problem properties
% 0.99/0.93  
% 0.99/0.93  clauses:                                10
% 0.99/0.93  conjectures:                            2
% 0.99/0.93  epr:                                    3
% 0.99/0.93  horn:                                   8
% 0.99/0.93  ground:                                 3
% 0.99/0.93  unary:                                  6
% 0.99/0.93  binary:                                 2
% 0.99/0.93  lits:                                   16
% 0.99/0.93  lits_eq:                                6
% 0.99/0.93  fd_pure:                                0
% 0.99/0.93  fd_pseudo:                              0
% 0.99/0.93  fd_cond:                                1
% 0.99/0.93  fd_pseudo_cond:                         0
% 0.99/0.93  ac_symbols:                             0
% 0.99/0.93  
% 0.99/0.93  ------ Propositional Solver
% 0.99/0.93  
% 0.99/0.93  prop_solver_calls:                      27
% 0.99/0.93  prop_fast_solver_calls:                 301
% 0.99/0.93  smt_solver_calls:                       0
% 0.99/0.93  smt_fast_solver_calls:                  0
% 0.99/0.93  prop_num_of_clauses:                    414
% 0.99/0.93  prop_preprocess_simplified:             1763
% 0.99/0.93  prop_fo_subsumed:                       5
% 0.99/0.93  prop_solver_time:                       0.
% 0.99/0.93  smt_solver_time:                        0.
% 0.99/0.93  smt_fast_solver_time:                   0.
% 0.99/0.93  prop_fast_solver_time:                  0.
% 0.99/0.93  prop_unsat_core_time:                   0.
% 0.99/0.93  
% 0.99/0.93  ------ QBF
% 0.99/0.93  
% 0.99/0.93  qbf_q_res:                              0
% 0.99/0.93  qbf_num_tautologies:                    0
% 0.99/0.93  qbf_prep_cycles:                        0
% 0.99/0.93  
% 0.99/0.93  ------ BMC1
% 0.99/0.93  
% 0.99/0.93  bmc1_current_bound:                     -1
% 0.99/0.93  bmc1_last_solved_bound:                 -1
% 0.99/0.93  bmc1_unsat_core_size:                   -1
% 0.99/0.93  bmc1_unsat_core_parents_size:           -1
% 0.99/0.93  bmc1_merge_next_fun:                    0
% 0.99/0.93  bmc1_unsat_core_clauses_time:           0.
% 0.99/0.93  
% 0.99/0.93  ------ Instantiation
% 0.99/0.93  
% 0.99/0.93  inst_num_of_clauses:                    151
% 0.99/0.93  inst_num_in_passive:                    26
% 0.99/0.93  inst_num_in_active:                     73
% 0.99/0.93  inst_num_in_unprocessed:                52
% 0.99/0.93  inst_num_of_loops:                      80
% 0.99/0.93  inst_num_of_learning_restarts:          0
% 0.99/0.93  inst_num_moves_active_passive:          4
% 0.99/0.93  inst_lit_activity:                      0
% 0.99/0.93  inst_lit_activity_moves:                0
% 0.99/0.93  inst_num_tautologies:                   0
% 0.99/0.93  inst_num_prop_implied:                  0
% 0.99/0.93  inst_num_existing_simplified:           0
% 0.99/0.93  inst_num_eq_res_simplified:             0
% 0.99/0.93  inst_num_child_elim:                    0
% 0.99/0.93  inst_num_of_dismatching_blockings:      5
% 0.99/0.93  inst_num_of_non_proper_insts:           93
% 0.99/0.93  inst_num_of_duplicates:                 0
% 0.99/0.93  inst_inst_num_from_inst_to_res:         0
% 0.99/0.93  inst_dismatching_checking_time:         0.
% 0.99/0.93  
% 0.99/0.93  ------ Resolution
% 0.99/0.93  
% 0.99/0.93  res_num_of_clauses:                     0
% 0.99/0.93  res_num_in_passive:                     0
% 0.99/0.93  res_num_in_active:                      0
% 0.99/0.93  res_num_of_loops:                       66
% 0.99/0.93  res_forward_subset_subsumed:            5
% 0.99/0.93  res_backward_subset_subsumed:           0
% 0.99/0.93  res_forward_subsumed:                   0
% 0.99/0.93  res_backward_subsumed:                  0
% 0.99/0.93  res_forward_subsumption_resolution:     0
% 0.99/0.93  res_backward_subsumption_resolution:    0
% 0.99/0.93  res_clause_to_clause_subsumption:       18
% 0.99/0.93  res_orphan_elimination:                 0
% 0.99/0.93  res_tautology_del:                      11
% 0.99/0.93  res_num_eq_res_simplified:              0
% 0.99/0.93  res_num_sel_changes:                    0
% 0.99/0.93  res_moves_from_active_to_pass:          0
% 0.99/0.93  
% 0.99/0.93  ------ Superposition
% 0.99/0.93  
% 0.99/0.93  sup_time_total:                         0.
% 0.99/0.93  sup_time_generating:                    0.
% 0.99/0.93  sup_time_sim_full:                      0.
% 0.99/0.93  sup_time_sim_immed:                     0.
% 0.99/0.93  
% 0.99/0.93  sup_num_of_clauses:                     16
% 0.99/0.93  sup_num_in_active:                      13
% 0.99/0.93  sup_num_in_passive:                     3
% 0.99/0.93  sup_num_of_loops:                       14
% 0.99/0.93  sup_fw_superposition:                   4
% 0.99/0.93  sup_bw_superposition:                   3
% 0.99/0.93  sup_immediate_simplified:               2
% 0.99/0.93  sup_given_eliminated:                   0
% 0.99/0.93  comparisons_done:                       0
% 0.99/0.93  comparisons_avoided:                    0
% 0.99/0.93  
% 0.99/0.93  ------ Simplifications
% 0.99/0.93  
% 0.99/0.93  
% 0.99/0.93  sim_fw_subset_subsumed:                 0
% 0.99/0.93  sim_bw_subset_subsumed:                 0
% 0.99/0.93  sim_fw_subsumed:                        0
% 0.99/0.93  sim_bw_subsumed:                        0
% 0.99/0.93  sim_fw_subsumption_res:                 1
% 0.99/0.93  sim_bw_subsumption_res:                 0
% 0.99/0.93  sim_tautology_del:                      0
% 0.99/0.93  sim_eq_tautology_del:                   0
% 0.99/0.93  sim_eq_res_simp:                        0
% 0.99/0.93  sim_fw_demodulated:                     1
% 0.99/0.93  sim_bw_demodulated:                     1
% 0.99/0.93  sim_light_normalised:                   1
% 0.99/0.93  sim_joinable_taut:                      0
% 0.99/0.93  sim_joinable_simp:                      0
% 0.99/0.93  sim_ac_normalised:                      0
% 0.99/0.93  sim_smt_subsumption:                    0
% 0.99/0.93  
%------------------------------------------------------------------------------
