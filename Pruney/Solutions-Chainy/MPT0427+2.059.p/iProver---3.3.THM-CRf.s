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
% DateTime   : Thu Dec  3 11:42:38 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 556 expanded)
%              Number of clauses        :   62 ( 206 expanded)
%              Number of leaves         :   13 ( 125 expanded)
%              Depth                    :   24
%              Number of atoms          :  227 (1694 expanded)
%              Number of equality atoms :  114 ( 455 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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

fof(f29,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28,f27])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f38])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_651,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_647,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_656,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1669,plain,
    ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_647,c_656])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_654,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1510,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(superposition,[status(thm)],[c_647,c_654])).

cnf(c_2029,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1669,c_1510])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_648,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1668,plain,
    ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_648,c_656])).

cnf(c_1509,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_648,c_654])).

cnf(c_1879,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1668,c_1509])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_650,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1883,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_650])).

cnf(c_2033,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2029,c_1883])).

cnf(c_3008,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_651,c_2033])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3009,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3008])).

cnf(c_3197,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3008,c_15,c_3009])).

cnf(c_3198,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3197])).

cnf(c_3210,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3198,c_650])).

cnf(c_7,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_657,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_658,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_700,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_657,c_658])).

cnf(c_3219,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3210,c_700])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_655,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_652,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1527,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_655,c_652])).

cnf(c_2539,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_1527])).

cnf(c_3419,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3219,c_2539])).

cnf(c_649,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_663,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1625,plain,
    ( r1_xboole_0(sK1,X0) = iProver_top
    | r1_xboole_0(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_663])).

cnf(c_3429,plain,
    ( r1_xboole_0(sK1,X0) = iProver_top
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3419,c_1625])).

cnf(c_0,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_660,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1063,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_660])).

cnf(c_3567,plain,
    ( r1_xboole_0(sK1,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3429,c_1063])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_662,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3576,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3567,c_662])).

cnf(c_3432,plain,
    ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3419,c_650])).

cnf(c_3439,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3432,c_700])).

cnf(c_3679,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3576,c_3439])).

cnf(c_3694,plain,
    ( r1_tarski(sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3679,c_700])).

cnf(c_1526,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_655])).

cnf(c_769,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_772,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_2291,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1526,c_772])).

cnf(c_2296,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2291,c_652])).

cnf(c_3844,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3694,c_2296])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:24:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.34/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/0.93  
% 2.34/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/0.93  
% 2.34/0.93  ------  iProver source info
% 2.34/0.93  
% 2.34/0.93  git: date: 2020-06-30 10:37:57 +0100
% 2.34/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/0.93  git: non_committed_changes: false
% 2.34/0.93  git: last_make_outside_of_git: false
% 2.34/0.93  
% 2.34/0.93  ------ 
% 2.34/0.93  
% 2.34/0.93  ------ Input Options
% 2.34/0.93  
% 2.34/0.93  --out_options                           all
% 2.34/0.93  --tptp_safe_out                         true
% 2.34/0.93  --problem_path                          ""
% 2.34/0.93  --include_path                          ""
% 2.34/0.93  --clausifier                            res/vclausify_rel
% 2.34/0.93  --clausifier_options                    --mode clausify
% 2.34/0.93  --stdin                                 false
% 2.34/0.93  --stats_out                             all
% 2.34/0.93  
% 2.34/0.93  ------ General Options
% 2.34/0.93  
% 2.34/0.93  --fof                                   false
% 2.34/0.93  --time_out_real                         305.
% 2.34/0.93  --time_out_virtual                      -1.
% 2.34/0.93  --symbol_type_check                     false
% 2.34/0.93  --clausify_out                          false
% 2.34/0.93  --sig_cnt_out                           false
% 2.34/0.93  --trig_cnt_out                          false
% 2.34/0.93  --trig_cnt_out_tolerance                1.
% 2.34/0.93  --trig_cnt_out_sk_spl                   false
% 2.34/0.93  --abstr_cl_out                          false
% 2.34/0.93  
% 2.34/0.93  ------ Global Options
% 2.34/0.93  
% 2.34/0.93  --schedule                              default
% 2.34/0.93  --add_important_lit                     false
% 2.34/0.93  --prop_solver_per_cl                    1000
% 2.34/0.93  --min_unsat_core                        false
% 2.34/0.93  --soft_assumptions                      false
% 2.34/0.93  --soft_lemma_size                       3
% 2.34/0.93  --prop_impl_unit_size                   0
% 2.34/0.93  --prop_impl_unit                        []
% 2.34/0.93  --share_sel_clauses                     true
% 2.34/0.93  --reset_solvers                         false
% 2.34/0.93  --bc_imp_inh                            [conj_cone]
% 2.34/0.93  --conj_cone_tolerance                   3.
% 2.34/0.93  --extra_neg_conj                        none
% 2.34/0.93  --large_theory_mode                     true
% 2.34/0.93  --prolific_symb_bound                   200
% 2.34/0.93  --lt_threshold                          2000
% 2.34/0.93  --clause_weak_htbl                      true
% 2.34/0.93  --gc_record_bc_elim                     false
% 2.34/0.93  
% 2.34/0.93  ------ Preprocessing Options
% 2.34/0.93  
% 2.34/0.93  --preprocessing_flag                    true
% 2.34/0.93  --time_out_prep_mult                    0.1
% 2.34/0.93  --splitting_mode                        input
% 2.34/0.93  --splitting_grd                         true
% 2.34/0.93  --splitting_cvd                         false
% 2.34/0.93  --splitting_cvd_svl                     false
% 2.34/0.93  --splitting_nvd                         32
% 2.34/0.93  --sub_typing                            true
% 2.34/0.93  --prep_gs_sim                           true
% 2.34/0.93  --prep_unflatten                        true
% 2.34/0.93  --prep_res_sim                          true
% 2.34/0.93  --prep_upred                            true
% 2.34/0.93  --prep_sem_filter                       exhaustive
% 2.34/0.93  --prep_sem_filter_out                   false
% 2.34/0.93  --pred_elim                             true
% 2.34/0.93  --res_sim_input                         true
% 2.34/0.93  --eq_ax_congr_red                       true
% 2.34/0.93  --pure_diseq_elim                       true
% 2.34/0.93  --brand_transform                       false
% 2.34/0.93  --non_eq_to_eq                          false
% 2.34/0.93  --prep_def_merge                        true
% 2.34/0.93  --prep_def_merge_prop_impl              false
% 2.34/0.93  --prep_def_merge_mbd                    true
% 2.34/0.93  --prep_def_merge_tr_red                 false
% 2.34/0.93  --prep_def_merge_tr_cl                  false
% 2.34/0.93  --smt_preprocessing                     true
% 2.34/0.93  --smt_ac_axioms                         fast
% 2.34/0.93  --preprocessed_out                      false
% 2.34/0.93  --preprocessed_stats                    false
% 2.34/0.93  
% 2.34/0.93  ------ Abstraction refinement Options
% 2.34/0.93  
% 2.34/0.93  --abstr_ref                             []
% 2.34/0.93  --abstr_ref_prep                        false
% 2.34/0.93  --abstr_ref_until_sat                   false
% 2.34/0.93  --abstr_ref_sig_restrict                funpre
% 2.34/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.93  --abstr_ref_under                       []
% 2.34/0.93  
% 2.34/0.93  ------ SAT Options
% 2.34/0.93  
% 2.34/0.93  --sat_mode                              false
% 2.34/0.93  --sat_fm_restart_options                ""
% 2.34/0.93  --sat_gr_def                            false
% 2.34/0.93  --sat_epr_types                         true
% 2.34/0.93  --sat_non_cyclic_types                  false
% 2.34/0.93  --sat_finite_models                     false
% 2.34/0.93  --sat_fm_lemmas                         false
% 2.34/0.93  --sat_fm_prep                           false
% 2.34/0.93  --sat_fm_uc_incr                        true
% 2.34/0.93  --sat_out_model                         small
% 2.34/0.93  --sat_out_clauses                       false
% 2.34/0.93  
% 2.34/0.93  ------ QBF Options
% 2.34/0.93  
% 2.34/0.93  --qbf_mode                              false
% 2.34/0.93  --qbf_elim_univ                         false
% 2.34/0.93  --qbf_dom_inst                          none
% 2.34/0.93  --qbf_dom_pre_inst                      false
% 2.34/0.93  --qbf_sk_in                             false
% 2.34/0.93  --qbf_pred_elim                         true
% 2.34/0.93  --qbf_split                             512
% 2.34/0.93  
% 2.34/0.93  ------ BMC1 Options
% 2.34/0.93  
% 2.34/0.93  --bmc1_incremental                      false
% 2.34/0.93  --bmc1_axioms                           reachable_all
% 2.34/0.93  --bmc1_min_bound                        0
% 2.34/0.93  --bmc1_max_bound                        -1
% 2.34/0.93  --bmc1_max_bound_default                -1
% 2.34/0.93  --bmc1_symbol_reachability              true
% 2.34/0.93  --bmc1_property_lemmas                  false
% 2.34/0.93  --bmc1_k_induction                      false
% 2.34/0.93  --bmc1_non_equiv_states                 false
% 2.34/0.93  --bmc1_deadlock                         false
% 2.34/0.93  --bmc1_ucm                              false
% 2.34/0.93  --bmc1_add_unsat_core                   none
% 2.34/0.93  --bmc1_unsat_core_children              false
% 2.34/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.93  --bmc1_out_stat                         full
% 2.34/0.93  --bmc1_ground_init                      false
% 2.34/0.93  --bmc1_pre_inst_next_state              false
% 2.34/0.93  --bmc1_pre_inst_state                   false
% 2.34/0.93  --bmc1_pre_inst_reach_state             false
% 2.34/0.93  --bmc1_out_unsat_core                   false
% 2.34/0.93  --bmc1_aig_witness_out                  false
% 2.34/0.93  --bmc1_verbose                          false
% 2.34/0.93  --bmc1_dump_clauses_tptp                false
% 2.34/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.93  --bmc1_dump_file                        -
% 2.34/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.93  --bmc1_ucm_extend_mode                  1
% 2.34/0.93  --bmc1_ucm_init_mode                    2
% 2.34/0.93  --bmc1_ucm_cone_mode                    none
% 2.34/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.93  --bmc1_ucm_relax_model                  4
% 2.34/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.93  --bmc1_ucm_layered_model                none
% 2.34/0.93  --bmc1_ucm_max_lemma_size               10
% 2.34/0.93  
% 2.34/0.93  ------ AIG Options
% 2.34/0.93  
% 2.34/0.93  --aig_mode                              false
% 2.34/0.93  
% 2.34/0.93  ------ Instantiation Options
% 2.34/0.93  
% 2.34/0.93  --instantiation_flag                    true
% 2.34/0.93  --inst_sos_flag                         false
% 2.34/0.93  --inst_sos_phase                        true
% 2.34/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.93  --inst_lit_sel_side                     num_symb
% 2.34/0.93  --inst_solver_per_active                1400
% 2.34/0.93  --inst_solver_calls_frac                1.
% 2.34/0.93  --inst_passive_queue_type               priority_queues
% 2.34/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.93  --inst_passive_queues_freq              [25;2]
% 2.34/0.93  --inst_dismatching                      true
% 2.34/0.93  --inst_eager_unprocessed_to_passive     true
% 2.34/0.93  --inst_prop_sim_given                   true
% 2.34/0.93  --inst_prop_sim_new                     false
% 2.34/0.93  --inst_subs_new                         false
% 2.34/0.93  --inst_eq_res_simp                      false
% 2.34/0.93  --inst_subs_given                       false
% 2.34/0.93  --inst_orphan_elimination               true
% 2.34/0.93  --inst_learning_loop_flag               true
% 2.34/0.93  --inst_learning_start                   3000
% 2.34/0.93  --inst_learning_factor                  2
% 2.34/0.93  --inst_start_prop_sim_after_learn       3
% 2.34/0.93  --inst_sel_renew                        solver
% 2.34/0.93  --inst_lit_activity_flag                true
% 2.34/0.93  --inst_restr_to_given                   false
% 2.34/0.93  --inst_activity_threshold               500
% 2.34/0.93  --inst_out_proof                        true
% 2.34/0.93  
% 2.34/0.93  ------ Resolution Options
% 2.34/0.93  
% 2.34/0.93  --resolution_flag                       true
% 2.34/0.93  --res_lit_sel                           adaptive
% 2.34/0.93  --res_lit_sel_side                      none
% 2.34/0.93  --res_ordering                          kbo
% 2.34/0.93  --res_to_prop_solver                    active
% 2.34/0.93  --res_prop_simpl_new                    false
% 2.34/0.93  --res_prop_simpl_given                  true
% 2.34/0.93  --res_passive_queue_type                priority_queues
% 2.34/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.93  --res_passive_queues_freq               [15;5]
% 2.34/0.93  --res_forward_subs                      full
% 2.34/0.93  --res_backward_subs                     full
% 2.34/0.93  --res_forward_subs_resolution           true
% 2.34/0.93  --res_backward_subs_resolution          true
% 2.34/0.93  --res_orphan_elimination                true
% 2.34/0.93  --res_time_limit                        2.
% 2.34/0.93  --res_out_proof                         true
% 2.34/0.93  
% 2.34/0.93  ------ Superposition Options
% 2.34/0.93  
% 2.34/0.93  --superposition_flag                    true
% 2.34/0.93  --sup_passive_queue_type                priority_queues
% 2.34/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.93  --demod_completeness_check              fast
% 2.34/0.93  --demod_use_ground                      true
% 2.34/0.93  --sup_to_prop_solver                    passive
% 2.34/0.93  --sup_prop_simpl_new                    true
% 2.34/0.93  --sup_prop_simpl_given                  true
% 2.34/0.93  --sup_fun_splitting                     false
% 2.34/0.93  --sup_smt_interval                      50000
% 2.34/0.93  
% 2.34/0.93  ------ Superposition Simplification Setup
% 2.34/0.93  
% 2.34/0.93  --sup_indices_passive                   []
% 2.34/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.93  --sup_full_bw                           [BwDemod]
% 2.34/0.93  --sup_immed_triv                        [TrivRules]
% 2.34/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.93  --sup_immed_bw_main                     []
% 2.34/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.93  
% 2.34/0.93  ------ Combination Options
% 2.34/0.93  
% 2.34/0.93  --comb_res_mult                         3
% 2.34/0.93  --comb_sup_mult                         2
% 2.34/0.93  --comb_inst_mult                        10
% 2.34/0.93  
% 2.34/0.93  ------ Debug Options
% 2.34/0.93  
% 2.34/0.93  --dbg_backtrace                         false
% 2.34/0.93  --dbg_dump_prop_clauses                 false
% 2.34/0.93  --dbg_dump_prop_clauses_file            -
% 2.34/0.93  --dbg_out_stat                          false
% 2.34/0.93  ------ Parsing...
% 2.34/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/0.93  
% 2.34/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.34/0.93  
% 2.34/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/0.93  
% 2.34/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/0.93  ------ Proving...
% 2.34/0.93  ------ Problem Properties 
% 2.34/0.93  
% 2.34/0.93  
% 2.34/0.93  clauses                                 18
% 2.34/0.93  conjectures                             4
% 2.34/0.93  EPR                                     4
% 2.34/0.93  Horn                                    16
% 2.34/0.93  unary                                   7
% 2.34/0.93  binary                                  8
% 2.34/0.93  lits                                    32
% 2.34/0.93  lits eq                                 9
% 2.34/0.93  fd_pure                                 0
% 2.34/0.93  fd_pseudo                               0
% 2.34/0.93  fd_cond                                 3
% 2.34/0.93  fd_pseudo_cond                          0
% 2.34/0.93  AC symbols                              0
% 2.34/0.93  
% 2.34/0.93  ------ Schedule dynamic 5 is on 
% 2.34/0.93  
% 2.34/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/0.93  
% 2.34/0.93  
% 2.34/0.93  ------ 
% 2.34/0.93  Current options:
% 2.34/0.93  ------ 
% 2.34/0.93  
% 2.34/0.93  ------ Input Options
% 2.34/0.93  
% 2.34/0.93  --out_options                           all
% 2.34/0.93  --tptp_safe_out                         true
% 2.34/0.93  --problem_path                          ""
% 2.34/0.93  --include_path                          ""
% 2.34/0.93  --clausifier                            res/vclausify_rel
% 2.34/0.93  --clausifier_options                    --mode clausify
% 2.34/0.93  --stdin                                 false
% 2.34/0.93  --stats_out                             all
% 2.34/0.93  
% 2.34/0.93  ------ General Options
% 2.34/0.93  
% 2.34/0.93  --fof                                   false
% 2.34/0.93  --time_out_real                         305.
% 2.34/0.93  --time_out_virtual                      -1.
% 2.34/0.93  --symbol_type_check                     false
% 2.34/0.93  --clausify_out                          false
% 2.34/0.93  --sig_cnt_out                           false
% 2.34/0.93  --trig_cnt_out                          false
% 2.34/0.93  --trig_cnt_out_tolerance                1.
% 2.34/0.93  --trig_cnt_out_sk_spl                   false
% 2.34/0.93  --abstr_cl_out                          false
% 2.34/0.93  
% 2.34/0.93  ------ Global Options
% 2.34/0.93  
% 2.34/0.93  --schedule                              default
% 2.34/0.93  --add_important_lit                     false
% 2.34/0.93  --prop_solver_per_cl                    1000
% 2.34/0.93  --min_unsat_core                        false
% 2.34/0.93  --soft_assumptions                      false
% 2.34/0.93  --soft_lemma_size                       3
% 2.34/0.93  --prop_impl_unit_size                   0
% 2.34/0.93  --prop_impl_unit                        []
% 2.34/0.93  --share_sel_clauses                     true
% 2.34/0.93  --reset_solvers                         false
% 2.34/0.93  --bc_imp_inh                            [conj_cone]
% 2.34/0.93  --conj_cone_tolerance                   3.
% 2.34/0.93  --extra_neg_conj                        none
% 2.34/0.93  --large_theory_mode                     true
% 2.34/0.93  --prolific_symb_bound                   200
% 2.34/0.93  --lt_threshold                          2000
% 2.34/0.93  --clause_weak_htbl                      true
% 2.34/0.93  --gc_record_bc_elim                     false
% 2.34/0.93  
% 2.34/0.93  ------ Preprocessing Options
% 2.34/0.93  
% 2.34/0.93  --preprocessing_flag                    true
% 2.34/0.93  --time_out_prep_mult                    0.1
% 2.34/0.93  --splitting_mode                        input
% 2.34/0.93  --splitting_grd                         true
% 2.34/0.93  --splitting_cvd                         false
% 2.34/0.93  --splitting_cvd_svl                     false
% 2.34/0.93  --splitting_nvd                         32
% 2.34/0.93  --sub_typing                            true
% 2.34/0.93  --prep_gs_sim                           true
% 2.34/0.93  --prep_unflatten                        true
% 2.34/0.93  --prep_res_sim                          true
% 2.34/0.93  --prep_upred                            true
% 2.34/0.93  --prep_sem_filter                       exhaustive
% 2.34/0.93  --prep_sem_filter_out                   false
% 2.34/0.93  --pred_elim                             true
% 2.34/0.93  --res_sim_input                         true
% 2.34/0.93  --eq_ax_congr_red                       true
% 2.34/0.93  --pure_diseq_elim                       true
% 2.34/0.93  --brand_transform                       false
% 2.34/0.93  --non_eq_to_eq                          false
% 2.34/0.93  --prep_def_merge                        true
% 2.34/0.93  --prep_def_merge_prop_impl              false
% 2.34/0.93  --prep_def_merge_mbd                    true
% 2.34/0.93  --prep_def_merge_tr_red                 false
% 2.34/0.93  --prep_def_merge_tr_cl                  false
% 2.34/0.93  --smt_preprocessing                     true
% 2.34/0.93  --smt_ac_axioms                         fast
% 2.34/0.93  --preprocessed_out                      false
% 2.34/0.93  --preprocessed_stats                    false
% 2.34/0.93  
% 2.34/0.93  ------ Abstraction refinement Options
% 2.34/0.93  
% 2.34/0.93  --abstr_ref                             []
% 2.34/0.93  --abstr_ref_prep                        false
% 2.34/0.93  --abstr_ref_until_sat                   false
% 2.34/0.93  --abstr_ref_sig_restrict                funpre
% 2.34/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.93  --abstr_ref_under                       []
% 2.34/0.93  
% 2.34/0.93  ------ SAT Options
% 2.34/0.93  
% 2.34/0.93  --sat_mode                              false
% 2.34/0.93  --sat_fm_restart_options                ""
% 2.34/0.93  --sat_gr_def                            false
% 2.34/0.93  --sat_epr_types                         true
% 2.34/0.93  --sat_non_cyclic_types                  false
% 2.34/0.93  --sat_finite_models                     false
% 2.34/0.93  --sat_fm_lemmas                         false
% 2.34/0.93  --sat_fm_prep                           false
% 2.34/0.93  --sat_fm_uc_incr                        true
% 2.34/0.93  --sat_out_model                         small
% 2.34/0.93  --sat_out_clauses                       false
% 2.34/0.93  
% 2.34/0.93  ------ QBF Options
% 2.34/0.93  
% 2.34/0.93  --qbf_mode                              false
% 2.34/0.93  --qbf_elim_univ                         false
% 2.34/0.93  --qbf_dom_inst                          none
% 2.34/0.93  --qbf_dom_pre_inst                      false
% 2.34/0.93  --qbf_sk_in                             false
% 2.34/0.93  --qbf_pred_elim                         true
% 2.34/0.93  --qbf_split                             512
% 2.34/0.93  
% 2.34/0.93  ------ BMC1 Options
% 2.34/0.93  
% 2.34/0.93  --bmc1_incremental                      false
% 2.34/0.93  --bmc1_axioms                           reachable_all
% 2.34/0.93  --bmc1_min_bound                        0
% 2.34/0.93  --bmc1_max_bound                        -1
% 2.34/0.93  --bmc1_max_bound_default                -1
% 2.34/0.93  --bmc1_symbol_reachability              true
% 2.34/0.93  --bmc1_property_lemmas                  false
% 2.34/0.93  --bmc1_k_induction                      false
% 2.34/0.93  --bmc1_non_equiv_states                 false
% 2.34/0.93  --bmc1_deadlock                         false
% 2.34/0.93  --bmc1_ucm                              false
% 2.34/0.93  --bmc1_add_unsat_core                   none
% 2.34/0.93  --bmc1_unsat_core_children              false
% 2.34/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.93  --bmc1_out_stat                         full
% 2.34/0.93  --bmc1_ground_init                      false
% 2.34/0.93  --bmc1_pre_inst_next_state              false
% 2.34/0.93  --bmc1_pre_inst_state                   false
% 2.34/0.93  --bmc1_pre_inst_reach_state             false
% 2.34/0.93  --bmc1_out_unsat_core                   false
% 2.34/0.93  --bmc1_aig_witness_out                  false
% 2.34/0.93  --bmc1_verbose                          false
% 2.34/0.93  --bmc1_dump_clauses_tptp                false
% 2.34/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.93  --bmc1_dump_file                        -
% 2.34/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.93  --bmc1_ucm_extend_mode                  1
% 2.34/0.93  --bmc1_ucm_init_mode                    2
% 2.34/0.93  --bmc1_ucm_cone_mode                    none
% 2.34/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.93  --bmc1_ucm_relax_model                  4
% 2.34/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.93  --bmc1_ucm_layered_model                none
% 2.34/0.93  --bmc1_ucm_max_lemma_size               10
% 2.34/0.93  
% 2.34/0.93  ------ AIG Options
% 2.34/0.93  
% 2.34/0.93  --aig_mode                              false
% 2.34/0.93  
% 2.34/0.93  ------ Instantiation Options
% 2.34/0.93  
% 2.34/0.93  --instantiation_flag                    true
% 2.34/0.93  --inst_sos_flag                         false
% 2.34/0.93  --inst_sos_phase                        true
% 2.34/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.93  --inst_lit_sel_side                     none
% 2.34/0.93  --inst_solver_per_active                1400
% 2.34/0.93  --inst_solver_calls_frac                1.
% 2.34/0.93  --inst_passive_queue_type               priority_queues
% 2.34/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.93  --inst_passive_queues_freq              [25;2]
% 2.34/0.93  --inst_dismatching                      true
% 2.34/0.93  --inst_eager_unprocessed_to_passive     true
% 2.34/0.93  --inst_prop_sim_given                   true
% 2.34/0.93  --inst_prop_sim_new                     false
% 2.34/0.93  --inst_subs_new                         false
% 2.34/0.93  --inst_eq_res_simp                      false
% 2.34/0.93  --inst_subs_given                       false
% 2.34/0.93  --inst_orphan_elimination               true
% 2.34/0.93  --inst_learning_loop_flag               true
% 2.34/0.93  --inst_learning_start                   3000
% 2.34/0.93  --inst_learning_factor                  2
% 2.34/0.93  --inst_start_prop_sim_after_learn       3
% 2.34/0.93  --inst_sel_renew                        solver
% 2.34/0.93  --inst_lit_activity_flag                true
% 2.34/0.93  --inst_restr_to_given                   false
% 2.34/0.93  --inst_activity_threshold               500
% 2.34/0.93  --inst_out_proof                        true
% 2.34/0.93  
% 2.34/0.93  ------ Resolution Options
% 2.34/0.93  
% 2.34/0.93  --resolution_flag                       false
% 2.34/0.93  --res_lit_sel                           adaptive
% 2.34/0.93  --res_lit_sel_side                      none
% 2.34/0.93  --res_ordering                          kbo
% 2.34/0.93  --res_to_prop_solver                    active
% 2.34/0.93  --res_prop_simpl_new                    false
% 2.34/0.93  --res_prop_simpl_given                  true
% 2.34/0.93  --res_passive_queue_type                priority_queues
% 2.34/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.93  --res_passive_queues_freq               [15;5]
% 2.34/0.93  --res_forward_subs                      full
% 2.34/0.93  --res_backward_subs                     full
% 2.34/0.93  --res_forward_subs_resolution           true
% 2.34/0.93  --res_backward_subs_resolution          true
% 2.34/0.93  --res_orphan_elimination                true
% 2.34/0.93  --res_time_limit                        2.
% 2.34/0.93  --res_out_proof                         true
% 2.34/0.93  
% 2.34/0.93  ------ Superposition Options
% 2.34/0.93  
% 2.34/0.93  --superposition_flag                    true
% 2.34/0.93  --sup_passive_queue_type                priority_queues
% 2.34/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.93  --demod_completeness_check              fast
% 2.34/0.93  --demod_use_ground                      true
% 2.34/0.93  --sup_to_prop_solver                    passive
% 2.34/0.93  --sup_prop_simpl_new                    true
% 2.34/0.93  --sup_prop_simpl_given                  true
% 2.34/0.93  --sup_fun_splitting                     false
% 2.34/0.93  --sup_smt_interval                      50000
% 2.34/0.93  
% 2.34/0.93  ------ Superposition Simplification Setup
% 2.34/0.93  
% 2.34/0.93  --sup_indices_passive                   []
% 2.34/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.93  --sup_full_bw                           [BwDemod]
% 2.34/0.93  --sup_immed_triv                        [TrivRules]
% 2.34/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.93  --sup_immed_bw_main                     []
% 2.34/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.93  
% 2.34/0.93  ------ Combination Options
% 2.34/0.93  
% 2.34/0.93  --comb_res_mult                         3
% 2.34/0.93  --comb_sup_mult                         2
% 2.34/0.93  --comb_inst_mult                        10
% 2.34/0.93  
% 2.34/0.93  ------ Debug Options
% 2.34/0.93  
% 2.34/0.93  --dbg_backtrace                         false
% 2.34/0.93  --dbg_dump_prop_clauses                 false
% 2.34/0.93  --dbg_dump_prop_clauses_file            -
% 2.34/0.93  --dbg_out_stat                          false
% 2.34/0.93  
% 2.34/0.93  
% 2.34/0.93  
% 2.34/0.93  
% 2.34/0.93  ------ Proving...
% 2.34/0.93  
% 2.34/0.93  
% 2.34/0.93  % SZS status Theorem for theBenchmark.p
% 2.34/0.93  
% 2.34/0.93   Resolution empty clause
% 2.34/0.93  
% 2.34/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/0.93  
% 2.34/0.93  fof(f11,axiom,(
% 2.34/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f21,plain,(
% 2.34/0.93    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.34/0.93    inference(ennf_transformation,[],[f11])).
% 2.34/0.93  
% 2.34/0.93  fof(f22,plain,(
% 2.34/0.93    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.34/0.93    inference(flattening,[],[f21])).
% 2.34/0.93  
% 2.34/0.93  fof(f43,plain,(
% 2.34/0.93    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.34/0.93    inference(cnf_transformation,[],[f22])).
% 2.34/0.93  
% 2.34/0.93  fof(f12,conjecture,(
% 2.34/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f13,negated_conjecture,(
% 2.34/0.93    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.34/0.93    inference(negated_conjecture,[],[f12])).
% 2.34/0.93  
% 2.34/0.93  fof(f23,plain,(
% 2.34/0.93    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.93    inference(ennf_transformation,[],[f13])).
% 2.34/0.93  
% 2.34/0.93  fof(f24,plain,(
% 2.34/0.93    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.93    inference(flattening,[],[f23])).
% 2.34/0.93  
% 2.34/0.93  fof(f28,plain,(
% 2.34/0.93    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.34/0.93    introduced(choice_axiom,[])).
% 2.34/0.93  
% 2.34/0.93  fof(f27,plain,(
% 2.34/0.93    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 2.34/0.93    introduced(choice_axiom,[])).
% 2.34/0.93  
% 2.34/0.93  fof(f29,plain,(
% 2.34/0.93    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.34/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28,f27])).
% 2.34/0.93  
% 2.34/0.93  fof(f44,plain,(
% 2.34/0.93    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.34/0.93    inference(cnf_transformation,[],[f29])).
% 2.34/0.93  
% 2.34/0.93  fof(f6,axiom,(
% 2.34/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f18,plain,(
% 2.34/0.93    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.93    inference(ennf_transformation,[],[f6])).
% 2.34/0.93  
% 2.34/0.93  fof(f37,plain,(
% 2.34/0.93    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.93    inference(cnf_transformation,[],[f18])).
% 2.34/0.93  
% 2.34/0.93  fof(f8,axiom,(
% 2.34/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f20,plain,(
% 2.34/0.93    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.93    inference(ennf_transformation,[],[f8])).
% 2.34/0.93  
% 2.34/0.93  fof(f40,plain,(
% 2.34/0.93    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.93    inference(cnf_transformation,[],[f20])).
% 2.34/0.93  
% 2.34/0.93  fof(f45,plain,(
% 2.34/0.93    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.34/0.93    inference(cnf_transformation,[],[f29])).
% 2.34/0.93  
% 2.34/0.93  fof(f47,plain,(
% 2.34/0.93    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 2.34/0.93    inference(cnf_transformation,[],[f29])).
% 2.34/0.93  
% 2.34/0.93  fof(f46,plain,(
% 2.34/0.93    r1_tarski(sK1,sK2)),
% 2.34/0.93    inference(cnf_transformation,[],[f29])).
% 2.34/0.93  
% 2.34/0.93  fof(f38,plain,(
% 2.34/0.93    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.93    inference(cnf_transformation,[],[f18])).
% 2.34/0.93  
% 2.34/0.93  fof(f49,plain,(
% 2.34/0.93    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.93    inference(equality_resolution,[],[f38])).
% 2.34/0.93  
% 2.34/0.93  fof(f5,axiom,(
% 2.34/0.93    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f36,plain,(
% 2.34/0.93    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.34/0.93    inference(cnf_transformation,[],[f5])).
% 2.34/0.93  
% 2.34/0.93  fof(f7,axiom,(
% 2.34/0.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f19,plain,(
% 2.34/0.93    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.93    inference(ennf_transformation,[],[f7])).
% 2.34/0.93  
% 2.34/0.93  fof(f39,plain,(
% 2.34/0.93    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.93    inference(cnf_transformation,[],[f19])).
% 2.34/0.93  
% 2.34/0.93  fof(f9,axiom,(
% 2.34/0.93    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f26,plain,(
% 2.34/0.93    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.34/0.93    inference(nnf_transformation,[],[f9])).
% 2.34/0.93  
% 2.34/0.93  fof(f41,plain,(
% 2.34/0.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.34/0.93    inference(cnf_transformation,[],[f26])).
% 2.34/0.93  
% 2.34/0.93  fof(f2,axiom,(
% 2.34/0.93    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f15,plain,(
% 2.34/0.93    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.34/0.93    inference(ennf_transformation,[],[f2])).
% 2.34/0.93  
% 2.34/0.93  fof(f16,plain,(
% 2.34/0.93    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.34/0.93    inference(flattening,[],[f15])).
% 2.34/0.93  
% 2.34/0.93  fof(f31,plain,(
% 2.34/0.93    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.34/0.93    inference(cnf_transformation,[],[f16])).
% 2.34/0.93  
% 2.34/0.93  fof(f1,axiom,(
% 2.34/0.93    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f30,plain,(
% 2.34/0.93    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.34/0.93    inference(cnf_transformation,[],[f1])).
% 2.34/0.93  
% 2.34/0.93  fof(f4,axiom,(
% 2.34/0.93    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f25,plain,(
% 2.34/0.93    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.34/0.93    inference(nnf_transformation,[],[f4])).
% 2.34/0.93  
% 2.34/0.93  fof(f35,plain,(
% 2.34/0.93    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.34/0.93    inference(cnf_transformation,[],[f25])).
% 2.34/0.93  
% 2.34/0.93  fof(f3,axiom,(
% 2.34/0.93    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.34/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.93  
% 2.34/0.93  fof(f17,plain,(
% 2.34/0.93    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.34/0.93    inference(ennf_transformation,[],[f3])).
% 2.34/0.93  
% 2.34/0.93  fof(f33,plain,(
% 2.34/0.93    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.34/0.93    inference(cnf_transformation,[],[f17])).
% 2.34/0.93  
% 2.34/0.93  cnf(c_13,plain,
% 2.34/0.93      ( ~ r1_tarski(X0,X1)
% 2.34/0.93      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.34/0.93      | k1_xboole_0 = X0 ),
% 2.34/0.93      inference(cnf_transformation,[],[f43]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_651,plain,
% 2.34/0.93      ( k1_xboole_0 = X0
% 2.34/0.93      | r1_tarski(X0,X1) != iProver_top
% 2.34/0.93      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_17,negated_conjecture,
% 2.34/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.34/0.93      inference(cnf_transformation,[],[f44]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_647,plain,
% 2.34/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_8,plain,
% 2.34/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.34/0.93      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.34/0.93      | k1_xboole_0 = X0 ),
% 2.34/0.93      inference(cnf_transformation,[],[f37]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_656,plain,
% 2.34/0.93      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.34/0.93      | k1_xboole_0 = X1
% 2.34/0.93      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1669,plain,
% 2.34/0.93      ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1) | sK1 = k1_xboole_0 ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_647,c_656]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_10,plain,
% 2.34/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.34/0.93      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.34/0.93      inference(cnf_transformation,[],[f40]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_654,plain,
% 2.34/0.93      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.34/0.93      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1510,plain,
% 2.34/0.93      ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_647,c_654]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_2029,plain,
% 2.34/0.93      ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | sK1 = k1_xboole_0 ),
% 2.34/0.93      inference(light_normalisation,[status(thm)],[c_1669,c_1510]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_16,negated_conjecture,
% 2.34/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.34/0.93      inference(cnf_transformation,[],[f45]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_648,plain,
% 2.34/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1668,plain,
% 2.34/0.93      ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2) | sK2 = k1_xboole_0 ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_648,c_656]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1509,plain,
% 2.34/0.93      ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_648,c_654]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1879,plain,
% 2.34/0.93      ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.34/0.93      inference(light_normalisation,[status(thm)],[c_1668,c_1509]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_14,negated_conjecture,
% 2.34/0.93      ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
% 2.34/0.93      inference(cnf_transformation,[],[f47]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_650,plain,
% 2.34/0.93      ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1883,plain,
% 2.34/0.93      ( sK2 = k1_xboole_0
% 2.34/0.93      | r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_1879,c_650]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_2033,plain,
% 2.34/0.93      ( sK1 = k1_xboole_0
% 2.34/0.93      | sK2 = k1_xboole_0
% 2.34/0.93      | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_2029,c_1883]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3008,plain,
% 2.34/0.93      ( sK1 = k1_xboole_0
% 2.34/0.93      | sK2 = k1_xboole_0
% 2.34/0.93      | r1_tarski(sK1,sK2) != iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_651,c_2033]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_15,negated_conjecture,
% 2.34/0.93      ( r1_tarski(sK1,sK2) ),
% 2.34/0.93      inference(cnf_transformation,[],[f46]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3009,plain,
% 2.34/0.93      ( ~ r1_tarski(sK1,sK2) | sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.34/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_3008]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3197,plain,
% 2.34/0.93      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.34/0.93      inference(global_propositional_subsumption,
% 2.34/0.93                [status(thm)],
% 2.34/0.93                [c_3008,c_15,c_3009]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3198,plain,
% 2.34/0.93      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.34/0.93      inference(renaming,[status(thm)],[c_3197]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3210,plain,
% 2.34/0.93      ( sK2 = k1_xboole_0
% 2.34/0.93      | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_3198,c_650]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_7,plain,
% 2.34/0.93      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.34/0.93      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.34/0.93      inference(cnf_transformation,[],[f49]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_657,plain,
% 2.34/0.93      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.34/0.93      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_6,plain,
% 2.34/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.34/0.93      inference(cnf_transformation,[],[f36]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_658,plain,
% 2.34/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_700,plain,
% 2.34/0.93      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.34/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_657,c_658]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3219,plain,
% 2.34/0.93      ( sK2 = k1_xboole_0
% 2.34/0.93      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
% 2.34/0.93      inference(demodulation,[status(thm)],[c_3210,c_700]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_9,plain,
% 2.34/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.34/0.93      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.34/0.93      inference(cnf_transformation,[],[f39]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_655,plain,
% 2.34/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.34/0.93      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_12,plain,
% 2.34/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.34/0.93      inference(cnf_transformation,[],[f41]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_652,plain,
% 2.34/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.34/0.93      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1527,plain,
% 2.34/0.93      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.34/0.93      | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_655,c_652]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_2539,plain,
% 2.34/0.93      ( r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_648,c_1527]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3419,plain,
% 2.34/0.93      ( sK2 = k1_xboole_0 ),
% 2.34/0.93      inference(global_propositional_subsumption,[status(thm)],[c_3219,c_2539]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_649,plain,
% 2.34/0.93      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1,plain,
% 2.34/0.93      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 2.34/0.93      inference(cnf_transformation,[],[f31]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_663,plain,
% 2.34/0.93      ( r1_tarski(X0,X1) != iProver_top
% 2.34/0.93      | r1_xboole_0(X1,X2) != iProver_top
% 2.34/0.93      | r1_xboole_0(X0,X2) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1625,plain,
% 2.34/0.93      ( r1_xboole_0(sK1,X0) = iProver_top
% 2.34/0.93      | r1_xboole_0(sK2,X0) != iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_649,c_663]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3429,plain,
% 2.34/0.93      ( r1_xboole_0(sK1,X0) = iProver_top
% 2.34/0.93      | r1_xboole_0(k1_xboole_0,X0) != iProver_top ),
% 2.34/0.93      inference(demodulation,[status(thm)],[c_3419,c_1625]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_0,plain,
% 2.34/0.93      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.34/0.93      inference(cnf_transformation,[],[f30]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_4,plain,
% 2.34/0.93      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.34/0.93      inference(cnf_transformation,[],[f35]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_660,plain,
% 2.34/0.93      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1063,plain,
% 2.34/0.93      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_0,c_660]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3567,plain,
% 2.34/0.93      ( r1_xboole_0(sK1,X0) = iProver_top ),
% 2.34/0.93      inference(global_propositional_subsumption,[status(thm)],[c_3429,c_1063]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_2,plain,
% 2.34/0.93      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 2.34/0.93      inference(cnf_transformation,[],[f33]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_662,plain,
% 2.34/0.93      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3576,plain,
% 2.34/0.93      ( sK1 = k1_xboole_0 ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_3567,c_662]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3432,plain,
% 2.34/0.93      ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.34/0.93      inference(demodulation,[status(thm)],[c_3419,c_650]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3439,plain,
% 2.34/0.93      ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.34/0.93      inference(demodulation,[status(thm)],[c_3432,c_700]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3679,plain,
% 2.34/0.93      ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 2.34/0.93      inference(demodulation,[status(thm)],[c_3576,c_3439]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3694,plain,
% 2.34/0.93      ( r1_tarski(sK0,sK0) != iProver_top ),
% 2.34/0.93      inference(demodulation,[status(thm)],[c_3679,c_700]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_1526,plain,
% 2.34/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 2.34/0.93      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_700,c_655]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_769,plain,
% 2.34/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 2.34/0.93      inference(instantiation,[status(thm)],[c_6]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_772,plain,
% 2.34/0.93      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 2.34/0.93      inference(predicate_to_equality,[status(thm)],[c_769]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_2291,plain,
% 2.34/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.34/0.93      inference(global_propositional_subsumption,[status(thm)],[c_1526,c_772]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_2296,plain,
% 2.34/0.93      ( r1_tarski(X0,X0) = iProver_top ),
% 2.34/0.93      inference(superposition,[status(thm)],[c_2291,c_652]) ).
% 2.34/0.93  
% 2.34/0.93  cnf(c_3844,plain,
% 2.34/0.93      ( $false ),
% 2.34/0.93      inference(forward_subsumption_resolution,[status(thm)],[c_3694,c_2296]) ).
% 2.34/0.93  
% 2.34/0.93  
% 2.34/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/0.93  
% 2.34/0.93  ------                               Statistics
% 2.34/0.93  
% 2.34/0.93  ------ General
% 2.34/0.93  
% 2.34/0.93  abstr_ref_over_cycles:                  0
% 2.34/0.93  abstr_ref_under_cycles:                 0
% 2.34/0.93  gc_basic_clause_elim:                   0
% 2.34/0.93  forced_gc_time:                         0
% 2.34/0.93  parsing_time:                           0.017
% 2.34/0.93  unif_index_cands_time:                  0.
% 2.34/0.93  unif_index_add_time:                    0.
% 2.34/0.93  orderings_time:                         0.
% 2.34/0.93  out_proof_time:                         0.019
% 2.34/0.93  total_time:                             0.173
% 2.34/0.93  num_of_symbols:                         43
% 2.34/0.93  num_of_terms:                           3035
% 2.34/0.93  
% 2.34/0.93  ------ Preprocessing
% 2.34/0.93  
% 2.34/0.93  num_of_splits:                          0
% 2.34/0.93  num_of_split_atoms:                     0
% 2.34/0.93  num_of_reused_defs:                     0
% 2.34/0.93  num_eq_ax_congr_red:                    8
% 2.34/0.93  num_of_sem_filtered_clauses:            1
% 2.34/0.93  num_of_subtypes:                        0
% 2.34/0.93  monotx_restored_types:                  0
% 2.34/0.93  sat_num_of_epr_types:                   0
% 2.34/0.93  sat_num_of_non_cyclic_types:            0
% 2.34/0.93  sat_guarded_non_collapsed_types:        0
% 2.34/0.93  num_pure_diseq_elim:                    0
% 2.34/0.93  simp_replaced_by:                       0
% 2.34/0.93  res_preprocessed:                       71
% 2.34/0.93  prep_upred:                             0
% 2.34/0.93  prep_unflattend:                        0
% 2.34/0.93  smt_new_axioms:                         0
% 2.34/0.93  pred_elim_cands:                        3
% 2.34/0.93  pred_elim:                              0
% 2.34/0.93  pred_elim_cl:                           0
% 2.34/0.93  pred_elim_cycles:                       1
% 2.34/0.93  merged_defs:                            12
% 2.34/0.93  merged_defs_ncl:                        0
% 2.34/0.93  bin_hyper_res:                          12
% 2.34/0.93  prep_cycles:                            3
% 2.34/0.93  pred_elim_time:                         0.
% 2.34/0.93  splitting_time:                         0.
% 2.34/0.93  sem_filter_time:                        0.
% 2.34/0.93  monotx_time:                            0.
% 2.34/0.93  subtype_inf_time:                       0.
% 2.34/0.93  
% 2.34/0.93  ------ Problem properties
% 2.34/0.93  
% 2.34/0.93  clauses:                                18
% 2.34/0.93  conjectures:                            4
% 2.34/0.93  epr:                                    4
% 2.34/0.93  horn:                                   16
% 2.34/0.93  ground:                                 5
% 2.34/0.93  unary:                                  7
% 2.34/0.93  binary:                                 8
% 2.34/0.93  lits:                                   32
% 2.34/0.93  lits_eq:                                9
% 2.34/0.93  fd_pure:                                0
% 2.34/0.93  fd_pseudo:                              0
% 2.34/0.93  fd_cond:                                3
% 2.34/0.93  fd_pseudo_cond:                         0
% 2.34/0.93  ac_symbols:                             0
% 2.34/0.93  
% 2.34/0.93  ------ Propositional Solver
% 2.34/0.93  
% 2.34/0.93  prop_solver_calls:                      26
% 2.34/0.93  prop_fast_solver_calls:                 407
% 2.34/0.93  smt_solver_calls:                       0
% 2.34/0.93  smt_fast_solver_calls:                  0
% 2.34/0.93  prop_num_of_clauses:                    1460
% 2.34/0.93  prop_preprocess_simplified:             3825
% 2.34/0.93  prop_fo_subsumed:                       8
% 2.34/0.93  prop_solver_time:                       0.
% 2.34/0.93  smt_solver_time:                        0.
% 2.34/0.93  smt_fast_solver_time:                   0.
% 2.34/0.93  prop_fast_solver_time:                  0.
% 2.34/0.93  prop_unsat_core_time:                   0.
% 2.34/0.93  
% 2.34/0.93  ------ QBF
% 2.34/0.93  
% 2.34/0.93  qbf_q_res:                              0
% 2.34/0.93  qbf_num_tautologies:                    0
% 2.34/0.93  qbf_prep_cycles:                        0
% 2.34/0.93  
% 2.34/0.93  ------ BMC1
% 2.34/0.93  
% 2.34/0.93  bmc1_current_bound:                     -1
% 2.34/0.93  bmc1_last_solved_bound:                 -1
% 2.34/0.93  bmc1_unsat_core_size:                   -1
% 2.34/0.93  bmc1_unsat_core_parents_size:           -1
% 2.34/0.93  bmc1_merge_next_fun:                    0
% 2.34/0.93  bmc1_unsat_core_clauses_time:           0.
% 2.34/0.93  
% 2.34/0.93  ------ Instantiation
% 2.34/0.93  
% 2.34/0.93  inst_num_of_clauses:                    487
% 2.34/0.93  inst_num_in_passive:                    203
% 2.34/0.93  inst_num_in_active:                     247
% 2.34/0.93  inst_num_in_unprocessed:                37
% 2.34/0.93  inst_num_of_loops:                      300
% 2.34/0.93  inst_num_of_learning_restarts:          0
% 2.34/0.93  inst_num_moves_active_passive:          49
% 2.34/0.93  inst_lit_activity:                      0
% 2.34/0.93  inst_lit_activity_moves:                0
% 2.34/0.93  inst_num_tautologies:                   0
% 2.34/0.93  inst_num_prop_implied:                  0
% 2.34/0.93  inst_num_existing_simplified:           0
% 2.34/0.93  inst_num_eq_res_simplified:             0
% 2.34/0.93  inst_num_child_elim:                    0
% 2.34/0.93  inst_num_of_dismatching_blockings:      149
% 2.34/0.93  inst_num_of_non_proper_insts:           492
% 2.34/0.93  inst_num_of_duplicates:                 0
% 2.34/0.93  inst_inst_num_from_inst_to_res:         0
% 2.34/0.93  inst_dismatching_checking_time:         0.
% 2.34/0.93  
% 2.34/0.93  ------ Resolution
% 2.34/0.93  
% 2.34/0.93  res_num_of_clauses:                     0
% 2.34/0.93  res_num_in_passive:                     0
% 2.34/0.93  res_num_in_active:                      0
% 2.34/0.93  res_num_of_loops:                       74
% 2.34/0.93  res_forward_subset_subsumed:            75
% 2.34/0.93  res_backward_subset_subsumed:           0
% 2.34/0.93  res_forward_subsumed:                   0
% 2.34/0.93  res_backward_subsumed:                  0
% 2.34/0.93  res_forward_subsumption_resolution:     0
% 2.34/0.93  res_backward_subsumption_resolution:    0
% 2.34/0.93  res_clause_to_clause_subsumption:       186
% 2.34/0.93  res_orphan_elimination:                 0
% 2.34/0.93  res_tautology_del:                      60
% 2.34/0.93  res_num_eq_res_simplified:              0
% 2.34/0.93  res_num_sel_changes:                    0
% 2.34/0.93  res_moves_from_active_to_pass:          0
% 2.34/0.93  
% 2.34/0.93  ------ Superposition
% 2.34/0.93  
% 2.34/0.93  sup_time_total:                         0.
% 2.34/0.93  sup_time_generating:                    0.
% 2.34/0.93  sup_time_sim_full:                      0.
% 2.34/0.93  sup_time_sim_immed:                     0.
% 2.34/0.93  
% 2.34/0.93  sup_num_of_clauses:                     43
% 2.34/0.93  sup_num_in_active:                      29
% 2.34/0.93  sup_num_in_passive:                     14
% 2.34/0.93  sup_num_of_loops:                       58
% 2.34/0.93  sup_fw_superposition:                   52
% 2.34/0.93  sup_bw_superposition:                   40
% 2.34/0.93  sup_immediate_simplified:               38
% 2.34/0.93  sup_given_eliminated:                   1
% 2.34/0.93  comparisons_done:                       0
% 2.34/0.93  comparisons_avoided:                    10
% 2.34/0.93  
% 2.34/0.93  ------ Simplifications
% 2.34/0.93  
% 2.34/0.93  
% 2.34/0.93  sim_fw_subset_subsumed:                 11
% 2.34/0.93  sim_bw_subset_subsumed:                 12
% 2.34/0.93  sim_fw_subsumed:                        12
% 2.34/0.93  sim_bw_subsumed:                        0
% 2.34/0.93  sim_fw_subsumption_res:                 2
% 2.34/0.93  sim_bw_subsumption_res:                 0
% 2.34/0.93  sim_tautology_del:                      4
% 2.34/0.93  sim_eq_tautology_del:                   7
% 2.34/0.93  sim_eq_res_simp:                        0
% 2.34/0.93  sim_fw_demodulated:                     15
% 2.34/0.93  sim_bw_demodulated:                     24
% 2.34/0.93  sim_light_normalised:                   6
% 2.34/0.93  sim_joinable_taut:                      0
% 2.34/0.93  sim_joinable_simp:                      0
% 2.34/0.93  sim_ac_normalised:                      0
% 2.34/0.93  sim_smt_subsumption:                    0
% 2.34/0.93  
%------------------------------------------------------------------------------
