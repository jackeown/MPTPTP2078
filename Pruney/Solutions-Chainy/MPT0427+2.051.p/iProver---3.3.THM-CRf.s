%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:36 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  132 (1644 expanded)
%              Number of clauses        :   91 ( 662 expanded)
%              Number of leaves         :   15 ( 392 expanded)
%              Depth                    :   25
%              Number of atoms          :  308 (5213 expanded)
%              Number of equality atoms :  169 (1461 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f28])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f40,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_555,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_564,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1442,plain,
    ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_555,c_564])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_562,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1074,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(superposition,[status(thm)],[c_555,c_562])).

cnf(c_1445,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1442,c_1074])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_563,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_560,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1419,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_563,c_560])).

cnf(c_2201,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_1419])).

cnf(c_2557,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_2201])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_42,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_668,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_669,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_721,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_722,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_744,plain,
    ( ~ r1_xboole_0(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_757,plain,
    ( k1_xboole_0 = sK1
    | r1_xboole_0(sK1,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_198,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_684,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK1,sK2)
    | X0 != sK1
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_759,plain,
    ( r1_tarski(sK1,X0)
    | ~ r1_tarski(sK1,sK2)
    | X0 != sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_761,plain,
    ( X0 != sK2
    | sK1 != sK1
    | r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_763,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | r1_tarski(sK1,sK2) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_195,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_760,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_196,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_801,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_802,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_827,plain,
    ( ~ r1_tarski(sK1,X0)
    | ~ r1_xboole_0(X0,sK1)
    | r1_xboole_0(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_828,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_xboole_0(X0,sK1) != iProver_top
    | r1_xboole_0(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_830,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_xboole_0(sK1,sK1) = iProver_top
    | r1_xboole_0(k1_xboole_0,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_942,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_1523,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1524,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1523])).

cnf(c_556,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1441,plain,
    ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_556,c_564])).

cnf(c_1073,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_556,c_562])).

cnf(c_1450,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1441,c_1073])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_558,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1817,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_558])).

cnf(c_1936,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1450,c_1817])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_746,plain,
    ( r1_tarski(k1_setfam_1(X0),k1_setfam_1(sK1))
    | ~ r1_tarski(sK1,X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_847,plain,
    ( r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_746])).

cnf(c_848,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_2018,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1936,c_17,c_760,c_848,c_1524])).

cnf(c_2019,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2018])).

cnf(c_2028,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2019,c_555])).

cnf(c_1015,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK0)) = k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_689,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | X1 != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_1626,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | X0 != sK2
    | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1627,plain,
    ( X0 != sK2
    | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_1629,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
    | k1_xboole_0 != sK2
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_2101,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2028,c_16,c_3,c_42,c_802,c_1015,c_1629])).

cnf(c_4,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_565,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2106,plain,
    ( k8_setfam_1(sK0,k1_xboole_0) = sK0 ),
    inference(superposition,[status(thm)],[c_2101,c_565])).

cnf(c_2027,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2019,c_558])).

cnf(c_2227,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2106,c_2027])).

cnf(c_566,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2630,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2227,c_16,c_669,c_722])).

cnf(c_557,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_568,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1557,plain,
    ( r1_xboole_0(sK1,X0) = iProver_top
    | r1_xboole_0(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_568])).

cnf(c_2637,plain,
    ( r1_xboole_0(sK1,X0) = iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2630,c_1557])).

cnf(c_2988,plain,
    ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_2637])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_569,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3183,plain,
    ( r1_xboole_0(k1_xboole_0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2988,c_569])).

cnf(c_3542,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2557,c_16,c_17,c_3,c_42,c_669,c_722,c_757,c_763,c_760,c_802,c_830,c_1524,c_2227,c_3183])).

cnf(c_2640,plain,
    ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2630,c_558])).

cnf(c_2646,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2640,c_2106])).

cnf(c_3549,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3542,c_2646])).

cnf(c_3560,plain,
    ( r1_tarski(sK0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3549,c_2106])).

cnf(c_2202,plain,
    ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2101,c_1419])).

cnf(c_2624,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2202,c_2106])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3560,c_2624])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:32:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.05/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/0.99  
% 2.05/0.99  ------  iProver source info
% 2.05/0.99  
% 2.05/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.05/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/0.99  git: non_committed_changes: false
% 2.05/0.99  git: last_make_outside_of_git: false
% 2.05/0.99  
% 2.05/0.99  ------ 
% 2.05/0.99  
% 2.05/0.99  ------ Input Options
% 2.05/0.99  
% 2.05/0.99  --out_options                           all
% 2.05/0.99  --tptp_safe_out                         true
% 2.05/0.99  --problem_path                          ""
% 2.05/0.99  --include_path                          ""
% 2.05/0.99  --clausifier                            res/vclausify_rel
% 2.05/0.99  --clausifier_options                    --mode clausify
% 2.05/0.99  --stdin                                 false
% 2.05/0.99  --stats_out                             all
% 2.05/0.99  
% 2.05/0.99  ------ General Options
% 2.05/0.99  
% 2.05/0.99  --fof                                   false
% 2.05/0.99  --time_out_real                         305.
% 2.05/0.99  --time_out_virtual                      -1.
% 2.05/0.99  --symbol_type_check                     false
% 2.05/0.99  --clausify_out                          false
% 2.05/0.99  --sig_cnt_out                           false
% 2.05/0.99  --trig_cnt_out                          false
% 2.05/0.99  --trig_cnt_out_tolerance                1.
% 2.05/0.99  --trig_cnt_out_sk_spl                   false
% 2.05/0.99  --abstr_cl_out                          false
% 2.05/0.99  
% 2.05/0.99  ------ Global Options
% 2.05/0.99  
% 2.05/0.99  --schedule                              default
% 2.05/0.99  --add_important_lit                     false
% 2.05/0.99  --prop_solver_per_cl                    1000
% 2.05/0.99  --min_unsat_core                        false
% 2.05/0.99  --soft_assumptions                      false
% 2.05/0.99  --soft_lemma_size                       3
% 2.05/0.99  --prop_impl_unit_size                   0
% 2.05/0.99  --prop_impl_unit                        []
% 2.05/0.99  --share_sel_clauses                     true
% 2.05/0.99  --reset_solvers                         false
% 2.05/0.99  --bc_imp_inh                            [conj_cone]
% 2.05/0.99  --conj_cone_tolerance                   3.
% 2.05/0.99  --extra_neg_conj                        none
% 2.05/0.99  --large_theory_mode                     true
% 2.05/0.99  --prolific_symb_bound                   200
% 2.05/0.99  --lt_threshold                          2000
% 2.05/0.99  --clause_weak_htbl                      true
% 2.05/0.99  --gc_record_bc_elim                     false
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing Options
% 2.05/0.99  
% 2.05/0.99  --preprocessing_flag                    true
% 2.05/0.99  --time_out_prep_mult                    0.1
% 2.05/0.99  --splitting_mode                        input
% 2.05/0.99  --splitting_grd                         true
% 2.05/0.99  --splitting_cvd                         false
% 2.05/0.99  --splitting_cvd_svl                     false
% 2.05/0.99  --splitting_nvd                         32
% 2.05/0.99  --sub_typing                            true
% 2.05/0.99  --prep_gs_sim                           true
% 2.05/0.99  --prep_unflatten                        true
% 2.05/0.99  --prep_res_sim                          true
% 2.05/0.99  --prep_upred                            true
% 2.05/0.99  --prep_sem_filter                       exhaustive
% 2.05/0.99  --prep_sem_filter_out                   false
% 2.05/0.99  --pred_elim                             true
% 2.05/0.99  --res_sim_input                         true
% 2.05/0.99  --eq_ax_congr_red                       true
% 2.05/0.99  --pure_diseq_elim                       true
% 2.05/0.99  --brand_transform                       false
% 2.05/0.99  --non_eq_to_eq                          false
% 2.05/0.99  --prep_def_merge                        true
% 2.05/0.99  --prep_def_merge_prop_impl              false
% 2.05/0.99  --prep_def_merge_mbd                    true
% 2.05/0.99  --prep_def_merge_tr_red                 false
% 2.05/0.99  --prep_def_merge_tr_cl                  false
% 2.05/0.99  --smt_preprocessing                     true
% 2.05/0.99  --smt_ac_axioms                         fast
% 2.05/0.99  --preprocessed_out                      false
% 2.05/0.99  --preprocessed_stats                    false
% 2.05/0.99  
% 2.05/0.99  ------ Abstraction refinement Options
% 2.05/0.99  
% 2.05/0.99  --abstr_ref                             []
% 2.05/0.99  --abstr_ref_prep                        false
% 2.05/0.99  --abstr_ref_until_sat                   false
% 2.05/0.99  --abstr_ref_sig_restrict                funpre
% 2.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.99  --abstr_ref_under                       []
% 2.05/0.99  
% 2.05/0.99  ------ SAT Options
% 2.05/0.99  
% 2.05/0.99  --sat_mode                              false
% 2.05/0.99  --sat_fm_restart_options                ""
% 2.05/0.99  --sat_gr_def                            false
% 2.05/0.99  --sat_epr_types                         true
% 2.05/0.99  --sat_non_cyclic_types                  false
% 2.05/0.99  --sat_finite_models                     false
% 2.05/0.99  --sat_fm_lemmas                         false
% 2.05/0.99  --sat_fm_prep                           false
% 2.05/0.99  --sat_fm_uc_incr                        true
% 2.05/0.99  --sat_out_model                         small
% 2.05/0.99  --sat_out_clauses                       false
% 2.05/0.99  
% 2.05/0.99  ------ QBF Options
% 2.05/0.99  
% 2.05/0.99  --qbf_mode                              false
% 2.05/0.99  --qbf_elim_univ                         false
% 2.05/0.99  --qbf_dom_inst                          none
% 2.05/0.99  --qbf_dom_pre_inst                      false
% 2.05/0.99  --qbf_sk_in                             false
% 2.05/0.99  --qbf_pred_elim                         true
% 2.05/0.99  --qbf_split                             512
% 2.05/0.99  
% 2.05/0.99  ------ BMC1 Options
% 2.05/0.99  
% 2.05/0.99  --bmc1_incremental                      false
% 2.05/0.99  --bmc1_axioms                           reachable_all
% 2.05/0.99  --bmc1_min_bound                        0
% 2.05/0.99  --bmc1_max_bound                        -1
% 2.05/0.99  --bmc1_max_bound_default                -1
% 2.05/0.99  --bmc1_symbol_reachability              true
% 2.05/0.99  --bmc1_property_lemmas                  false
% 2.05/0.99  --bmc1_k_induction                      false
% 2.05/0.99  --bmc1_non_equiv_states                 false
% 2.05/0.99  --bmc1_deadlock                         false
% 2.05/0.99  --bmc1_ucm                              false
% 2.05/0.99  --bmc1_add_unsat_core                   none
% 2.05/0.99  --bmc1_unsat_core_children              false
% 2.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.99  --bmc1_out_stat                         full
% 2.05/0.99  --bmc1_ground_init                      false
% 2.05/0.99  --bmc1_pre_inst_next_state              false
% 2.05/0.99  --bmc1_pre_inst_state                   false
% 2.05/0.99  --bmc1_pre_inst_reach_state             false
% 2.05/0.99  --bmc1_out_unsat_core                   false
% 2.05/0.99  --bmc1_aig_witness_out                  false
% 2.05/0.99  --bmc1_verbose                          false
% 2.05/0.99  --bmc1_dump_clauses_tptp                false
% 2.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.99  --bmc1_dump_file                        -
% 2.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.99  --bmc1_ucm_extend_mode                  1
% 2.05/0.99  --bmc1_ucm_init_mode                    2
% 2.05/0.99  --bmc1_ucm_cone_mode                    none
% 2.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.99  --bmc1_ucm_relax_model                  4
% 2.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.99  --bmc1_ucm_layered_model                none
% 2.05/0.99  --bmc1_ucm_max_lemma_size               10
% 2.05/0.99  
% 2.05/0.99  ------ AIG Options
% 2.05/0.99  
% 2.05/0.99  --aig_mode                              false
% 2.05/0.99  
% 2.05/0.99  ------ Instantiation Options
% 2.05/0.99  
% 2.05/0.99  --instantiation_flag                    true
% 2.05/0.99  --inst_sos_flag                         false
% 2.05/0.99  --inst_sos_phase                        true
% 2.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.99  --inst_lit_sel_side                     num_symb
% 2.05/0.99  --inst_solver_per_active                1400
% 2.05/0.99  --inst_solver_calls_frac                1.
% 2.05/0.99  --inst_passive_queue_type               priority_queues
% 2.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.99  --inst_passive_queues_freq              [25;2]
% 2.05/0.99  --inst_dismatching                      true
% 2.05/0.99  --inst_eager_unprocessed_to_passive     true
% 2.05/0.99  --inst_prop_sim_given                   true
% 2.05/0.99  --inst_prop_sim_new                     false
% 2.05/0.99  --inst_subs_new                         false
% 2.05/0.99  --inst_eq_res_simp                      false
% 2.05/0.99  --inst_subs_given                       false
% 2.05/0.99  --inst_orphan_elimination               true
% 2.05/0.99  --inst_learning_loop_flag               true
% 2.05/0.99  --inst_learning_start                   3000
% 2.05/0.99  --inst_learning_factor                  2
% 2.05/0.99  --inst_start_prop_sim_after_learn       3
% 2.05/0.99  --inst_sel_renew                        solver
% 2.05/0.99  --inst_lit_activity_flag                true
% 2.05/0.99  --inst_restr_to_given                   false
% 2.05/0.99  --inst_activity_threshold               500
% 2.05/0.99  --inst_out_proof                        true
% 2.05/0.99  
% 2.05/0.99  ------ Resolution Options
% 2.05/0.99  
% 2.05/0.99  --resolution_flag                       true
% 2.05/0.99  --res_lit_sel                           adaptive
% 2.05/0.99  --res_lit_sel_side                      none
% 2.05/0.99  --res_ordering                          kbo
% 2.05/0.99  --res_to_prop_solver                    active
% 2.05/0.99  --res_prop_simpl_new                    false
% 2.05/0.99  --res_prop_simpl_given                  true
% 2.05/0.99  --res_passive_queue_type                priority_queues
% 2.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.99  --res_passive_queues_freq               [15;5]
% 2.05/0.99  --res_forward_subs                      full
% 2.05/0.99  --res_backward_subs                     full
% 2.05/0.99  --res_forward_subs_resolution           true
% 2.05/0.99  --res_backward_subs_resolution          true
% 2.05/0.99  --res_orphan_elimination                true
% 2.05/0.99  --res_time_limit                        2.
% 2.05/0.99  --res_out_proof                         true
% 2.05/0.99  
% 2.05/0.99  ------ Superposition Options
% 2.05/0.99  
% 2.05/0.99  --superposition_flag                    true
% 2.05/0.99  --sup_passive_queue_type                priority_queues
% 2.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.99  --demod_completeness_check              fast
% 2.05/0.99  --demod_use_ground                      true
% 2.05/0.99  --sup_to_prop_solver                    passive
% 2.05/0.99  --sup_prop_simpl_new                    true
% 2.05/0.99  --sup_prop_simpl_given                  true
% 2.05/0.99  --sup_fun_splitting                     false
% 2.05/0.99  --sup_smt_interval                      50000
% 2.05/0.99  
% 2.05/0.99  ------ Superposition Simplification Setup
% 2.05/0.99  
% 2.05/0.99  --sup_indices_passive                   []
% 2.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_full_bw                           [BwDemod]
% 2.05/0.99  --sup_immed_triv                        [TrivRules]
% 2.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_immed_bw_main                     []
% 2.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.99  
% 2.05/0.99  ------ Combination Options
% 2.05/0.99  
% 2.05/0.99  --comb_res_mult                         3
% 2.05/0.99  --comb_sup_mult                         2
% 2.05/0.99  --comb_inst_mult                        10
% 2.05/0.99  
% 2.05/0.99  ------ Debug Options
% 2.05/0.99  
% 2.05/0.99  --dbg_backtrace                         false
% 2.05/0.99  --dbg_dump_prop_clauses                 false
% 2.05/0.99  --dbg_dump_prop_clauses_file            -
% 2.05/0.99  --dbg_out_stat                          false
% 2.05/0.99  ------ Parsing...
% 2.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/0.99  ------ Proving...
% 2.05/0.99  ------ Problem Properties 
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  clauses                                 15
% 2.05/0.99  conjectures                             4
% 2.05/0.99  EPR                                     5
% 2.05/0.99  Horn                                    13
% 2.05/0.99  unary                                   5
% 2.05/0.99  binary                                  7
% 2.05/0.99  lits                                    28
% 2.05/0.99  lits eq                                 6
% 2.05/0.99  fd_pure                                 0
% 2.05/0.99  fd_pseudo                               0
% 2.05/0.99  fd_cond                                 3
% 2.05/0.99  fd_pseudo_cond                          0
% 2.05/0.99  AC symbols                              0
% 2.05/0.99  
% 2.05/0.99  ------ Schedule dynamic 5 is on 
% 2.05/0.99  
% 2.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  ------ 
% 2.05/0.99  Current options:
% 2.05/0.99  ------ 
% 2.05/0.99  
% 2.05/0.99  ------ Input Options
% 2.05/0.99  
% 2.05/0.99  --out_options                           all
% 2.05/0.99  --tptp_safe_out                         true
% 2.05/0.99  --problem_path                          ""
% 2.05/0.99  --include_path                          ""
% 2.05/0.99  --clausifier                            res/vclausify_rel
% 2.05/0.99  --clausifier_options                    --mode clausify
% 2.05/0.99  --stdin                                 false
% 2.05/0.99  --stats_out                             all
% 2.05/0.99  
% 2.05/0.99  ------ General Options
% 2.05/0.99  
% 2.05/0.99  --fof                                   false
% 2.05/0.99  --time_out_real                         305.
% 2.05/0.99  --time_out_virtual                      -1.
% 2.05/0.99  --symbol_type_check                     false
% 2.05/0.99  --clausify_out                          false
% 2.05/0.99  --sig_cnt_out                           false
% 2.05/0.99  --trig_cnt_out                          false
% 2.05/0.99  --trig_cnt_out_tolerance                1.
% 2.05/0.99  --trig_cnt_out_sk_spl                   false
% 2.05/0.99  --abstr_cl_out                          false
% 2.05/0.99  
% 2.05/0.99  ------ Global Options
% 2.05/0.99  
% 2.05/0.99  --schedule                              default
% 2.05/0.99  --add_important_lit                     false
% 2.05/0.99  --prop_solver_per_cl                    1000
% 2.05/0.99  --min_unsat_core                        false
% 2.05/0.99  --soft_assumptions                      false
% 2.05/0.99  --soft_lemma_size                       3
% 2.05/0.99  --prop_impl_unit_size                   0
% 2.05/0.99  --prop_impl_unit                        []
% 2.05/0.99  --share_sel_clauses                     true
% 2.05/0.99  --reset_solvers                         false
% 2.05/0.99  --bc_imp_inh                            [conj_cone]
% 2.05/0.99  --conj_cone_tolerance                   3.
% 2.05/0.99  --extra_neg_conj                        none
% 2.05/0.99  --large_theory_mode                     true
% 2.05/0.99  --prolific_symb_bound                   200
% 2.05/0.99  --lt_threshold                          2000
% 2.05/0.99  --clause_weak_htbl                      true
% 2.05/0.99  --gc_record_bc_elim                     false
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing Options
% 2.05/0.99  
% 2.05/0.99  --preprocessing_flag                    true
% 2.05/0.99  --time_out_prep_mult                    0.1
% 2.05/0.99  --splitting_mode                        input
% 2.05/0.99  --splitting_grd                         true
% 2.05/0.99  --splitting_cvd                         false
% 2.05/0.99  --splitting_cvd_svl                     false
% 2.05/0.99  --splitting_nvd                         32
% 2.05/0.99  --sub_typing                            true
% 2.05/0.99  --prep_gs_sim                           true
% 2.05/0.99  --prep_unflatten                        true
% 2.05/0.99  --prep_res_sim                          true
% 2.05/0.99  --prep_upred                            true
% 2.05/0.99  --prep_sem_filter                       exhaustive
% 2.05/0.99  --prep_sem_filter_out                   false
% 2.05/0.99  --pred_elim                             true
% 2.05/0.99  --res_sim_input                         true
% 2.05/0.99  --eq_ax_congr_red                       true
% 2.05/0.99  --pure_diseq_elim                       true
% 2.05/0.99  --brand_transform                       false
% 2.05/0.99  --non_eq_to_eq                          false
% 2.05/0.99  --prep_def_merge                        true
% 2.05/0.99  --prep_def_merge_prop_impl              false
% 2.05/0.99  --prep_def_merge_mbd                    true
% 2.05/0.99  --prep_def_merge_tr_red                 false
% 2.05/0.99  --prep_def_merge_tr_cl                  false
% 2.05/0.99  --smt_preprocessing                     true
% 2.05/0.99  --smt_ac_axioms                         fast
% 2.05/0.99  --preprocessed_out                      false
% 2.05/0.99  --preprocessed_stats                    false
% 2.05/0.99  
% 2.05/0.99  ------ Abstraction refinement Options
% 2.05/0.99  
% 2.05/0.99  --abstr_ref                             []
% 2.05/0.99  --abstr_ref_prep                        false
% 2.05/0.99  --abstr_ref_until_sat                   false
% 2.05/0.99  --abstr_ref_sig_restrict                funpre
% 2.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.99  --abstr_ref_under                       []
% 2.05/0.99  
% 2.05/0.99  ------ SAT Options
% 2.05/0.99  
% 2.05/0.99  --sat_mode                              false
% 2.05/0.99  --sat_fm_restart_options                ""
% 2.05/0.99  --sat_gr_def                            false
% 2.05/0.99  --sat_epr_types                         true
% 2.05/0.99  --sat_non_cyclic_types                  false
% 2.05/0.99  --sat_finite_models                     false
% 2.05/0.99  --sat_fm_lemmas                         false
% 2.05/0.99  --sat_fm_prep                           false
% 2.05/0.99  --sat_fm_uc_incr                        true
% 2.05/0.99  --sat_out_model                         small
% 2.05/0.99  --sat_out_clauses                       false
% 2.05/0.99  
% 2.05/0.99  ------ QBF Options
% 2.05/0.99  
% 2.05/0.99  --qbf_mode                              false
% 2.05/0.99  --qbf_elim_univ                         false
% 2.05/0.99  --qbf_dom_inst                          none
% 2.05/0.99  --qbf_dom_pre_inst                      false
% 2.05/0.99  --qbf_sk_in                             false
% 2.05/0.99  --qbf_pred_elim                         true
% 2.05/0.99  --qbf_split                             512
% 2.05/0.99  
% 2.05/0.99  ------ BMC1 Options
% 2.05/0.99  
% 2.05/0.99  --bmc1_incremental                      false
% 2.05/0.99  --bmc1_axioms                           reachable_all
% 2.05/0.99  --bmc1_min_bound                        0
% 2.05/0.99  --bmc1_max_bound                        -1
% 2.05/0.99  --bmc1_max_bound_default                -1
% 2.05/0.99  --bmc1_symbol_reachability              true
% 2.05/0.99  --bmc1_property_lemmas                  false
% 2.05/0.99  --bmc1_k_induction                      false
% 2.05/0.99  --bmc1_non_equiv_states                 false
% 2.05/0.99  --bmc1_deadlock                         false
% 2.05/0.99  --bmc1_ucm                              false
% 2.05/0.99  --bmc1_add_unsat_core                   none
% 2.05/0.99  --bmc1_unsat_core_children              false
% 2.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.99  --bmc1_out_stat                         full
% 2.05/0.99  --bmc1_ground_init                      false
% 2.05/0.99  --bmc1_pre_inst_next_state              false
% 2.05/0.99  --bmc1_pre_inst_state                   false
% 2.05/0.99  --bmc1_pre_inst_reach_state             false
% 2.05/0.99  --bmc1_out_unsat_core                   false
% 2.05/0.99  --bmc1_aig_witness_out                  false
% 2.05/0.99  --bmc1_verbose                          false
% 2.05/0.99  --bmc1_dump_clauses_tptp                false
% 2.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.99  --bmc1_dump_file                        -
% 2.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.99  --bmc1_ucm_extend_mode                  1
% 2.05/0.99  --bmc1_ucm_init_mode                    2
% 2.05/0.99  --bmc1_ucm_cone_mode                    none
% 2.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.99  --bmc1_ucm_relax_model                  4
% 2.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.99  --bmc1_ucm_layered_model                none
% 2.05/0.99  --bmc1_ucm_max_lemma_size               10
% 2.05/0.99  
% 2.05/0.99  ------ AIG Options
% 2.05/0.99  
% 2.05/0.99  --aig_mode                              false
% 2.05/0.99  
% 2.05/0.99  ------ Instantiation Options
% 2.05/0.99  
% 2.05/0.99  --instantiation_flag                    true
% 2.05/0.99  --inst_sos_flag                         false
% 2.05/0.99  --inst_sos_phase                        true
% 2.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.99  --inst_lit_sel_side                     none
% 2.05/0.99  --inst_solver_per_active                1400
% 2.05/0.99  --inst_solver_calls_frac                1.
% 2.05/0.99  --inst_passive_queue_type               priority_queues
% 2.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.99  --inst_passive_queues_freq              [25;2]
% 2.05/0.99  --inst_dismatching                      true
% 2.05/0.99  --inst_eager_unprocessed_to_passive     true
% 2.05/0.99  --inst_prop_sim_given                   true
% 2.05/0.99  --inst_prop_sim_new                     false
% 2.05/0.99  --inst_subs_new                         false
% 2.05/0.99  --inst_eq_res_simp                      false
% 2.05/0.99  --inst_subs_given                       false
% 2.05/0.99  --inst_orphan_elimination               true
% 2.05/0.99  --inst_learning_loop_flag               true
% 2.05/0.99  --inst_learning_start                   3000
% 2.05/0.99  --inst_learning_factor                  2
% 2.05/0.99  --inst_start_prop_sim_after_learn       3
% 2.05/0.99  --inst_sel_renew                        solver
% 2.05/0.99  --inst_lit_activity_flag                true
% 2.05/0.99  --inst_restr_to_given                   false
% 2.05/0.99  --inst_activity_threshold               500
% 2.05/0.99  --inst_out_proof                        true
% 2.05/0.99  
% 2.05/0.99  ------ Resolution Options
% 2.05/0.99  
% 2.05/0.99  --resolution_flag                       false
% 2.05/0.99  --res_lit_sel                           adaptive
% 2.05/0.99  --res_lit_sel_side                      none
% 2.05/0.99  --res_ordering                          kbo
% 2.05/0.99  --res_to_prop_solver                    active
% 2.05/0.99  --res_prop_simpl_new                    false
% 2.05/0.99  --res_prop_simpl_given                  true
% 2.05/0.99  --res_passive_queue_type                priority_queues
% 2.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.99  --res_passive_queues_freq               [15;5]
% 2.05/0.99  --res_forward_subs                      full
% 2.05/0.99  --res_backward_subs                     full
% 2.05/0.99  --res_forward_subs_resolution           true
% 2.05/0.99  --res_backward_subs_resolution          true
% 2.05/0.99  --res_orphan_elimination                true
% 2.05/0.99  --res_time_limit                        2.
% 2.05/0.99  --res_out_proof                         true
% 2.05/0.99  
% 2.05/0.99  ------ Superposition Options
% 2.05/0.99  
% 2.05/0.99  --superposition_flag                    true
% 2.05/0.99  --sup_passive_queue_type                priority_queues
% 2.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.99  --demod_completeness_check              fast
% 2.05/0.99  --demod_use_ground                      true
% 2.05/0.99  --sup_to_prop_solver                    passive
% 2.05/0.99  --sup_prop_simpl_new                    true
% 2.05/0.99  --sup_prop_simpl_given                  true
% 2.05/0.99  --sup_fun_splitting                     false
% 2.05/0.99  --sup_smt_interval                      50000
% 2.05/0.99  
% 2.05/0.99  ------ Superposition Simplification Setup
% 2.05/0.99  
% 2.05/0.99  --sup_indices_passive                   []
% 2.05/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_full_bw                           [BwDemod]
% 2.05/0.99  --sup_immed_triv                        [TrivRules]
% 2.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_immed_bw_main                     []
% 2.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.99  
% 2.05/0.99  ------ Combination Options
% 2.05/0.99  
% 2.05/0.99  --comb_res_mult                         3
% 2.05/0.99  --comb_sup_mult                         2
% 2.05/0.99  --comb_inst_mult                        10
% 2.05/0.99  
% 2.05/0.99  ------ Debug Options
% 2.05/0.99  
% 2.05/0.99  --dbg_backtrace                         false
% 2.05/0.99  --dbg_dump_prop_clauses                 false
% 2.05/0.99  --dbg_dump_prop_clauses_file            -
% 2.05/0.99  --dbg_out_stat                          false
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  ------ Proving...
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  % SZS status Theorem for theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  fof(f9,conjecture,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f10,negated_conjecture,(
% 2.05/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.05/0.99    inference(negated_conjecture,[],[f9])).
% 2.05/0.99  
% 2.05/0.99  fof(f20,plain,(
% 2.05/0.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.05/0.99    inference(ennf_transformation,[],[f10])).
% 2.05/0.99  
% 2.05/0.99  fof(f21,plain,(
% 2.05/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.05/0.99    inference(flattening,[],[f20])).
% 2.05/0.99  
% 2.05/0.99  fof(f24,plain,(
% 2.05/0.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f23,plain,(
% 2.05/0.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f25,plain,(
% 2.05/0.99    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23])).
% 2.05/0.99  
% 2.05/0.99  fof(f37,plain,(
% 2.05/0.99    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.05/0.99    inference(cnf_transformation,[],[f25])).
% 2.05/0.99  
% 2.05/0.99  fof(f4,axiom,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f15,plain,(
% 2.05/0.99    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.05/0.99    inference(ennf_transformation,[],[f4])).
% 2.05/0.99  
% 2.05/0.99  fof(f30,plain,(
% 2.05/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f15])).
% 2.05/0.99  
% 2.05/0.99  fof(f6,axiom,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f17,plain,(
% 2.05/0.99    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.05/0.99    inference(ennf_transformation,[],[f6])).
% 2.05/0.99  
% 2.05/0.99  fof(f33,plain,(
% 2.05/0.99    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f17])).
% 2.05/0.99  
% 2.05/0.99  fof(f5,axiom,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f16,plain,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.05/0.99    inference(ennf_transformation,[],[f5])).
% 2.05/0.99  
% 2.05/0.99  fof(f32,plain,(
% 2.05/0.99    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f16])).
% 2.05/0.99  
% 2.05/0.99  fof(f7,axiom,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f22,plain,(
% 2.05/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.05/0.99    inference(nnf_transformation,[],[f7])).
% 2.05/0.99  
% 2.05/0.99  fof(f34,plain,(
% 2.05/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f22])).
% 2.05/0.99  
% 2.05/0.99  fof(f38,plain,(
% 2.05/0.99    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.05/0.99    inference(cnf_transformation,[],[f25])).
% 2.05/0.99  
% 2.05/0.99  fof(f39,plain,(
% 2.05/0.99    r1_tarski(sK1,sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f25])).
% 2.05/0.99  
% 2.05/0.99  fof(f3,axiom,(
% 2.05/0.99    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f14,plain,(
% 2.05/0.99    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f3])).
% 2.05/0.99  
% 2.05/0.99  fof(f28,plain,(
% 2.05/0.99    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f14])).
% 2.05/0.99  
% 2.05/0.99  fof(f41,plain,(
% 2.05/0.99    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.05/0.99    inference(equality_resolution,[],[f28])).
% 2.05/0.99  
% 2.05/0.99  fof(f29,plain,(
% 2.05/0.99    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.05/0.99    inference(cnf_transformation,[],[f14])).
% 2.05/0.99  
% 2.05/0.99  fof(f2,axiom,(
% 2.05/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f12,plain,(
% 2.05/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.05/0.99    inference(ennf_transformation,[],[f2])).
% 2.05/0.99  
% 2.05/0.99  fof(f13,plain,(
% 2.05/0.99    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.05/0.99    inference(flattening,[],[f12])).
% 2.05/0.99  
% 2.05/0.99  fof(f27,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f13])).
% 2.05/0.99  
% 2.05/0.99  fof(f40,plain,(
% 2.05/0.99    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 2.05/0.99    inference(cnf_transformation,[],[f25])).
% 2.05/0.99  
% 2.05/0.99  fof(f8,axiom,(
% 2.05/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f18,plain,(
% 2.05/0.99    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.05/0.99    inference(ennf_transformation,[],[f8])).
% 2.05/0.99  
% 2.05/0.99  fof(f19,plain,(
% 2.05/0.99    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.05/0.99    inference(flattening,[],[f18])).
% 2.05/0.99  
% 2.05/0.99  fof(f36,plain,(
% 2.05/0.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f19])).
% 2.05/0.99  
% 2.05/0.99  fof(f31,plain,(
% 2.05/0.99    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f15])).
% 2.05/0.99  
% 2.05/0.99  fof(f42,plain,(
% 2.05/0.99    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.05/0.99    inference(equality_resolution,[],[f31])).
% 2.05/0.99  
% 2.05/0.99  fof(f1,axiom,(
% 2.05/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f11,plain,(
% 2.05/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.05/0.99    inference(ennf_transformation,[],[f1])).
% 2.05/0.99  
% 2.05/0.99  fof(f26,plain,(
% 2.05/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f11])).
% 2.05/0.99  
% 2.05/0.99  cnf(c_14,negated_conjecture,
% 2.05/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.05/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_555,plain,
% 2.05/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_5,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.05/0.99      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.05/0.99      | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_564,plain,
% 2.05/0.99      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.05/0.99      | k1_xboole_0 = X1
% 2.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1442,plain,
% 2.05/0.99      ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1) | sK1 = k1_xboole_0 ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_555,c_564]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_7,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.05/0.99      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_562,plain,
% 2.05/0.99      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1074,plain,
% 2.05/0.99      ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_555,c_562]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1445,plain,
% 2.05/0.99      ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | sK1 = k1_xboole_0 ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1442,c_1074]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_6,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.05/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_563,plain,
% 2.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.05/0.99      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_9,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_560,plain,
% 2.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.05/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1419,plain,
% 2.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.05/0.99      | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_563,c_560]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2201,plain,
% 2.05/0.99      ( r1_tarski(k8_setfam_1(sK0,sK1),sK0) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_555,c_1419]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2557,plain,
% 2.05/0.99      ( sK1 = k1_xboole_0
% 2.05/0.99      | r1_tarski(k1_setfam_1(sK1),sK0) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1445,c_2201]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_13,negated_conjecture,
% 2.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.05/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_16,plain,
% 2.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_12,negated_conjecture,
% 2.05/0.99      ( r1_tarski(sK1,sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_17,plain,
% 2.05/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3,plain,
% 2.05/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2,plain,
% 2.05/0.99      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_42,plain,
% 2.05/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.05/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_668,plain,
% 2.05/0.99      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_669,plain,
% 2.05/0.99      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_721,plain,
% 2.05/0.99      ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
% 2.05/0.99      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_722,plain,
% 2.05/0.99      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 2.05/0.99      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_744,plain,
% 2.05/0.99      ( ~ r1_xboole_0(sK1,sK1) | k1_xboole_0 = sK1 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_757,plain,
% 2.05/0.99      ( k1_xboole_0 = sK1 | r1_xboole_0(sK1,sK1) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_198,plain,
% 2.05/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.05/0.99      theory(equality) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_684,plain,
% 2.05/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(sK1,sK2) | X0 != sK1 | X1 != sK2 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_198]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_759,plain,
% 2.05/0.99      ( r1_tarski(sK1,X0)
% 2.05/0.99      | ~ r1_tarski(sK1,sK2)
% 2.05/0.99      | X0 != sK2
% 2.05/0.99      | sK1 != sK1 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_684]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_761,plain,
% 2.05/0.99      ( X0 != sK2
% 2.05/0.99      | sK1 != sK1
% 2.05/0.99      | r1_tarski(sK1,X0) = iProver_top
% 2.05/0.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_763,plain,
% 2.05/0.99      ( sK1 != sK1
% 2.05/0.99      | k1_xboole_0 != sK2
% 2.05/0.99      | r1_tarski(sK1,sK2) != iProver_top
% 2.05/0.99      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_761]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_195,plain,( X0 = X0 ),theory(equality) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_760,plain,
% 2.05/0.99      ( sK1 = sK1 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_195]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_196,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_801,plain,
% 2.05/0.99      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_196]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_802,plain,
% 2.05/0.99      ( sK2 != k1_xboole_0
% 2.05/0.99      | k1_xboole_0 = sK2
% 2.05/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_801]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1,plain,
% 2.05/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_827,plain,
% 2.05/0.99      ( ~ r1_tarski(sK1,X0)
% 2.05/0.99      | ~ r1_xboole_0(X0,sK1)
% 2.05/0.99      | r1_xboole_0(sK1,sK1) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_828,plain,
% 2.05/0.99      ( r1_tarski(sK1,X0) != iProver_top
% 2.05/0.99      | r1_xboole_0(X0,sK1) != iProver_top
% 2.05/0.99      | r1_xboole_0(sK1,sK1) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_830,plain,
% 2.05/0.99      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 2.05/0.99      | r1_xboole_0(sK1,sK1) = iProver_top
% 2.05/0.99      | r1_xboole_0(k1_xboole_0,sK1) != iProver_top ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_828]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_942,plain,
% 2.05/0.99      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_196]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1523,plain,
% 2.05/0.99      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_942]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1524,plain,
% 2.05/0.99      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_1523]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_556,plain,
% 2.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1441,plain,
% 2.05/0.99      ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2) | sK2 = k1_xboole_0 ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_556,c_564]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1073,plain,
% 2.05/0.99      ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_556,c_562]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1450,plain,
% 2.05/0.99      ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_1441,c_1073]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_11,negated_conjecture,
% 2.05/0.99      ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_558,plain,
% 2.05/0.99      ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1817,plain,
% 2.05/0.99      ( sK1 = k1_xboole_0
% 2.05/0.99      | r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1445,c_558]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1936,plain,
% 2.05/0.99      ( sK1 = k1_xboole_0
% 2.05/0.99      | sK2 = k1_xboole_0
% 2.05/0.99      | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_1450,c_1817]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_10,plain,
% 2.05/0.99      ( ~ r1_tarski(X0,X1)
% 2.05/0.99      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.05/0.99      | k1_xboole_0 = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_746,plain,
% 2.05/0.99      ( r1_tarski(k1_setfam_1(X0),k1_setfam_1(sK1))
% 2.05/0.99      | ~ r1_tarski(sK1,X0)
% 2.05/0.99      | k1_xboole_0 = sK1 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_847,plain,
% 2.05/0.99      ( r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
% 2.05/0.99      | ~ r1_tarski(sK1,sK2)
% 2.05/0.99      | k1_xboole_0 = sK1 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_746]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_848,plain,
% 2.05/0.99      ( k1_xboole_0 = sK1
% 2.05/0.99      | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) = iProver_top
% 2.05/0.99      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2018,plain,
% 2.05/0.99      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_1936,c_17,c_760,c_848,c_1524]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2019,plain,
% 2.05/0.99      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_2018]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2028,plain,
% 2.05/0.99      ( sK2 = k1_xboole_0
% 2.05/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_2019,c_555]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1015,plain,
% 2.05/0.99      ( k1_zfmisc_1(k1_zfmisc_1(sK0)) = k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_195]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_201,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.05/0.99      theory(equality) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_689,plain,
% 2.05/0.99      ( m1_subset_1(X0,X1)
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 2.05/0.99      | X1 != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 2.05/0.99      | X0 != sK2 ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_201]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1626,plain,
% 2.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 2.05/0.99      | X0 != sK2
% 2.05/0.99      | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0)) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_689]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1627,plain,
% 2.05/0.99      ( X0 != sK2
% 2.05/0.99      | k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 2.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1626]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1629,plain,
% 2.05/0.99      ( k1_zfmisc_1(k1_zfmisc_1(sK0)) != k1_zfmisc_1(k1_zfmisc_1(sK0))
% 2.05/0.99      | k1_xboole_0 != sK2
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top
% 2.05/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_1627]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2101,plain,
% 2.05/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2028,c_16,c_3,c_42,c_802,c_1015,c_1629]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4,plain,
% 2.05/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.05/0.99      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_565,plain,
% 2.05/0.99      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.05/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2106,plain,
% 2.05/0.99      ( k8_setfam_1(sK0,k1_xboole_0) = sK0 ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_2101,c_565]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2027,plain,
% 2.05/0.99      ( sK2 = k1_xboole_0
% 2.05/0.99      | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_2019,c_558]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2227,plain,
% 2.05/0.99      ( sK2 = k1_xboole_0
% 2.05/0.99      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_2106,c_2027]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_566,plain,
% 2.05/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2630,plain,
% 2.05/0.99      ( sK2 = k1_xboole_0 ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2227,c_16,c_669,c_722]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_557,plain,
% 2.05/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_568,plain,
% 2.05/0.99      ( r1_tarski(X0,X1) != iProver_top
% 2.05/0.99      | r1_xboole_0(X1,X2) != iProver_top
% 2.05/0.99      | r1_xboole_0(X0,X2) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1557,plain,
% 2.05/0.99      ( r1_xboole_0(sK1,X0) = iProver_top
% 2.05/0.99      | r1_xboole_0(sK2,X0) != iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_557,c_568]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2637,plain,
% 2.05/0.99      ( r1_xboole_0(sK1,X0) = iProver_top
% 2.05/0.99      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_2630,c_1557]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2988,plain,
% 2.05/0.99      ( r1_xboole_0(sK1,k1_xboole_0) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_566,c_2637]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_0,plain,
% 2.05/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_569,plain,
% 2.05/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 2.05/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3183,plain,
% 2.05/0.99      ( r1_xboole_0(k1_xboole_0,sK1) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_2988,c_569]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3542,plain,
% 2.05/0.99      ( sK1 = k1_xboole_0 ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_2557,c_16,c_17,c_3,c_42,c_669,c_722,c_757,c_763,c_760,
% 2.05/0.99                 c_802,c_830,c_1524,c_2227,c_3183]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2640,plain,
% 2.05/0.99      ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_2630,c_558]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2646,plain,
% 2.05/0.99      ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_2640,c_2106]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3549,plain,
% 2.05/0.99      ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_3542,c_2646]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3560,plain,
% 2.05/0.99      ( r1_tarski(sK0,sK0) != iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_3549,c_2106]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2202,plain,
% 2.05/0.99      ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) = iProver_top ),
% 2.05/0.99      inference(superposition,[status(thm)],[c_2101,c_1419]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2624,plain,
% 2.05/0.99      ( r1_tarski(sK0,sK0) = iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_2202,c_2106]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(contradiction,plain,
% 2.05/0.99      ( $false ),
% 2.05/0.99      inference(minisat,[status(thm)],[c_3560,c_2624]) ).
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  ------                               Statistics
% 2.05/0.99  
% 2.05/0.99  ------ General
% 2.05/0.99  
% 2.05/0.99  abstr_ref_over_cycles:                  0
% 2.05/0.99  abstr_ref_under_cycles:                 0
% 2.05/0.99  gc_basic_clause_elim:                   0
% 2.05/0.99  forced_gc_time:                         0
% 2.05/0.99  parsing_time:                           0.01
% 2.05/0.99  unif_index_cands_time:                  0.
% 2.05/0.99  unif_index_add_time:                    0.
% 2.05/0.99  orderings_time:                         0.
% 2.05/0.99  out_proof_time:                         0.009
% 2.05/0.99  total_time:                             0.131
% 2.05/0.99  num_of_symbols:                         42
% 2.05/0.99  num_of_terms:                           2152
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing
% 2.05/0.99  
% 2.05/0.99  num_of_splits:                          0
% 2.05/0.99  num_of_split_atoms:                     0
% 2.05/0.99  num_of_reused_defs:                     0
% 2.05/0.99  num_eq_ax_congr_red:                    6
% 2.05/0.99  num_of_sem_filtered_clauses:            1
% 2.05/0.99  num_of_subtypes:                        0
% 2.05/0.99  monotx_restored_types:                  0
% 2.05/0.99  sat_num_of_epr_types:                   0
% 2.05/0.99  sat_num_of_non_cyclic_types:            0
% 2.05/0.99  sat_guarded_non_collapsed_types:        0
% 2.05/0.99  num_pure_diseq_elim:                    0
% 2.05/0.99  simp_replaced_by:                       0
% 2.05/0.99  res_preprocessed:                       60
% 2.05/0.99  prep_upred:                             0
% 2.05/0.99  prep_unflattend:                        0
% 2.05/0.99  smt_new_axioms:                         0
% 2.05/0.99  pred_elim_cands:                        3
% 2.05/0.99  pred_elim:                              0
% 2.05/0.99  pred_elim_cl:                           0
% 2.05/0.99  pred_elim_cycles:                       1
% 2.05/0.99  merged_defs:                            6
% 2.05/0.99  merged_defs_ncl:                        0
% 2.05/0.99  bin_hyper_res:                          6
% 2.05/0.99  prep_cycles:                            3
% 2.05/0.99  pred_elim_time:                         0.
% 2.05/0.99  splitting_time:                         0.
% 2.05/0.99  sem_filter_time:                        0.
% 2.05/0.99  monotx_time:                            0.001
% 2.05/0.99  subtype_inf_time:                       0.
% 2.05/0.99  
% 2.05/0.99  ------ Problem properties
% 2.05/0.99  
% 2.05/0.99  clauses:                                15
% 2.05/0.99  conjectures:                            4
% 2.05/0.99  epr:                                    5
% 2.05/0.99  horn:                                   13
% 2.05/0.99  ground:                                 5
% 2.05/0.99  unary:                                  5
% 2.05/0.99  binary:                                 7
% 2.05/0.99  lits:                                   28
% 2.05/0.99  lits_eq:                                6
% 2.05/0.99  fd_pure:                                0
% 2.05/0.99  fd_pseudo:                              0
% 2.05/0.99  fd_cond:                                3
% 2.05/0.99  fd_pseudo_cond:                         0
% 2.05/0.99  ac_symbols:                             0
% 2.05/0.99  
% 2.05/0.99  ------ Propositional Solver
% 2.05/0.99  
% 2.05/0.99  prop_solver_calls:                      25
% 2.05/0.99  prop_fast_solver_calls:                 348
% 2.05/0.99  smt_solver_calls:                       0
% 2.05/0.99  smt_fast_solver_calls:                  0
% 2.05/0.99  prop_num_of_clauses:                    1364
% 2.05/0.99  prop_preprocess_simplified:             3902
% 2.05/0.99  prop_fo_subsumed:                       5
% 2.05/0.99  prop_solver_time:                       0.
% 2.05/0.99  smt_solver_time:                        0.
% 2.05/0.99  smt_fast_solver_time:                   0.
% 2.05/0.99  prop_fast_solver_time:                  0.
% 2.05/0.99  prop_unsat_core_time:                   0.
% 2.05/0.99  
% 2.05/0.99  ------ QBF
% 2.05/0.99  
% 2.05/0.99  qbf_q_res:                              0
% 2.05/0.99  qbf_num_tautologies:                    0
% 2.05/0.99  qbf_prep_cycles:                        0
% 2.05/0.99  
% 2.05/0.99  ------ BMC1
% 2.05/0.99  
% 2.05/0.99  bmc1_current_bound:                     -1
% 2.05/0.99  bmc1_last_solved_bound:                 -1
% 2.05/0.99  bmc1_unsat_core_size:                   -1
% 2.05/0.99  bmc1_unsat_core_parents_size:           -1
% 2.05/0.99  bmc1_merge_next_fun:                    0
% 2.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.05/0.99  
% 2.05/0.99  ------ Instantiation
% 2.05/0.99  
% 2.05/0.99  inst_num_of_clauses:                    447
% 2.05/0.99  inst_num_in_passive:                    206
% 2.05/0.99  inst_num_in_active:                     212
% 2.05/0.99  inst_num_in_unprocessed:                29
% 2.05/0.99  inst_num_of_loops:                      250
% 2.05/0.99  inst_num_of_learning_restarts:          0
% 2.05/0.99  inst_num_moves_active_passive:          35
% 2.05/0.99  inst_lit_activity:                      0
% 2.05/0.99  inst_lit_activity_moves:                0
% 2.05/0.99  inst_num_tautologies:                   0
% 2.05/0.99  inst_num_prop_implied:                  0
% 2.05/0.99  inst_num_existing_simplified:           0
% 2.05/0.99  inst_num_eq_res_simplified:             0
% 2.05/0.99  inst_num_child_elim:                    0
% 2.05/0.99  inst_num_of_dismatching_blockings:      99
% 2.05/0.99  inst_num_of_non_proper_insts:           361
% 2.05/0.99  inst_num_of_duplicates:                 0
% 2.05/0.99  inst_inst_num_from_inst_to_res:         0
% 2.05/0.99  inst_dismatching_checking_time:         0.
% 2.05/0.99  
% 2.05/0.99  ------ Resolution
% 2.05/0.99  
% 2.05/0.99  res_num_of_clauses:                     0
% 2.05/0.99  res_num_in_passive:                     0
% 2.05/0.99  res_num_in_active:                      0
% 2.05/0.99  res_num_of_loops:                       63
% 2.05/0.99  res_forward_subset_subsumed:            29
% 2.05/0.99  res_backward_subset_subsumed:           0
% 2.05/0.99  res_forward_subsumed:                   0
% 2.05/0.99  res_backward_subsumed:                  0
% 2.05/0.99  res_forward_subsumption_resolution:     0
% 2.05/0.99  res_backward_subsumption_resolution:    0
% 2.05/0.99  res_clause_to_clause_subsumption:       132
% 2.05/0.99  res_orphan_elimination:                 0
% 2.05/0.99  res_tautology_del:                      56
% 2.05/0.99  res_num_eq_res_simplified:              0
% 2.05/0.99  res_num_sel_changes:                    0
% 2.05/0.99  res_moves_from_active_to_pass:          0
% 2.05/0.99  
% 2.05/0.99  ------ Superposition
% 2.05/0.99  
% 2.05/0.99  sup_time_total:                         0.
% 2.05/0.99  sup_time_generating:                    0.
% 2.05/0.99  sup_time_sim_full:                      0.
% 2.05/0.99  sup_time_sim_immed:                     0.
% 2.05/0.99  
% 2.05/0.99  sup_num_of_clauses:                     40
% 2.05/0.99  sup_num_in_active:                      22
% 2.05/0.99  sup_num_in_passive:                     18
% 2.05/0.99  sup_num_of_loops:                       48
% 2.05/0.99  sup_fw_superposition:                   38
% 2.05/0.99  sup_bw_superposition:                   34
% 2.05/0.99  sup_immediate_simplified:               13
% 2.05/0.99  sup_given_eliminated:                   0
% 2.05/0.99  comparisons_done:                       0
% 2.05/0.99  comparisons_avoided:                    8
% 2.05/0.99  
% 2.05/0.99  ------ Simplifications
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  sim_fw_subset_subsumed:                 7
% 2.05/0.99  sim_bw_subset_subsumed:                 11
% 2.05/0.99  sim_fw_subsumed:                        0
% 2.05/0.99  sim_bw_subsumed:                        0
% 2.05/0.99  sim_fw_subsumption_res:                 0
% 2.05/0.99  sim_bw_subsumption_res:                 0
% 2.05/0.99  sim_tautology_del:                      5
% 2.05/0.99  sim_eq_tautology_del:                   4
% 2.05/0.99  sim_eq_res_simp:                        0
% 2.05/0.99  sim_fw_demodulated:                     0
% 2.05/0.99  sim_bw_demodulated:                     23
% 2.05/0.99  sim_light_normalised:                   8
% 2.05/0.99  sim_joinable_taut:                      0
% 2.05/0.99  sim_joinable_simp:                      0
% 2.05/0.99  sim_ac_normalised:                      0
% 2.05/0.99  sim_smt_subsumption:                    0
% 2.05/0.99  
%------------------------------------------------------------------------------
