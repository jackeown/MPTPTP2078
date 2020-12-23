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
% DateTime   : Thu Dec  3 11:42:36 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 448 expanded)
%              Number of clauses        :   75 ( 178 expanded)
%              Number of leaves         :   12 (  96 expanded)
%              Depth                    :   23
%              Number of atoms          :  247 (1282 expanded)
%              Number of equality atoms :  126 ( 357 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
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

fof(f31,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f40])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_671,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_680,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1873,plain,
    ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_671,c_680])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_678,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1748,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(superposition,[status(thm)],[c_671,c_678])).

cnf(c_2167,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | sK1 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1873,c_1748])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_672,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1872,plain,
    ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_672,c_680])).

cnf(c_1747,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_672,c_678])).

cnf(c_2054,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1872,c_1747])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_674,plain,
    ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2058,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_674])).

cnf(c_2171,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2167,c_2058])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_673,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_675,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_688,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1153,plain,
    ( k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_675,c_688])).

cnf(c_2471,plain,
    ( k4_xboole_0(k1_setfam_1(sK2),k1_setfam_1(sK1)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_673,c_1153])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_687,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2762,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_687])).

cnf(c_3113,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2171,c_2762])).

cnf(c_3114,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3113])).

cnf(c_3129,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3114,c_674])).

cnf(c_7,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_681,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_682,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_725,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_681,c_682])).

cnf(c_3138,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3129,c_725])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_818,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_819,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1221,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK0,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_1352,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_3172,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3138,c_19,c_819,c_1352])).

cnf(c_3190,plain,
    ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3172,c_673])).

cnf(c_676,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1167,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_682,c_676])).

cnf(c_2498,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1167,c_688])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_684,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2629,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2498,c_684])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_685,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X1) = iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2637,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_685])).

cnf(c_3340,plain,
    ( r1_xboole_0(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_2637])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_683,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3599,plain,
    ( k4_xboole_0(sK1,X0) = sK1 ),
    inference(superposition,[status(thm)],[c_3340,c_683])).

cnf(c_1169,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_676])).

cnf(c_1286,plain,
    ( k4_xboole_0(sK1,k1_zfmisc_1(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1169,c_688])).

cnf(c_3794,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3599,c_1286])).

cnf(c_3188,plain,
    ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3172,c_674])).

cnf(c_3195,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3188,c_725])).

cnf(c_3877,plain,
    ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3794,c_3195])).

cnf(c_3894,plain,
    ( r1_tarski(sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3877,c_725])).

cnf(c_679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_725,c_679])).

cnf(c_808,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_811,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_3902,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1611,c_811])).

cnf(c_3909,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3902,c_676])).

cnf(c_4811,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3894,c_3909])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.79/1.07  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.07  
% 2.79/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/1.07  
% 2.79/1.07  ------  iProver source info
% 2.79/1.07  
% 2.79/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.79/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/1.07  git: non_committed_changes: false
% 2.79/1.07  git: last_make_outside_of_git: false
% 2.79/1.07  
% 2.79/1.07  ------ 
% 2.79/1.07  
% 2.79/1.07  ------ Input Options
% 2.79/1.07  
% 2.79/1.07  --out_options                           all
% 2.79/1.07  --tptp_safe_out                         true
% 2.79/1.07  --problem_path                          ""
% 2.79/1.07  --include_path                          ""
% 2.79/1.07  --clausifier                            res/vclausify_rel
% 2.79/1.07  --clausifier_options                    --mode clausify
% 2.79/1.07  --stdin                                 false
% 2.79/1.07  --stats_out                             all
% 2.79/1.07  
% 2.79/1.07  ------ General Options
% 2.79/1.07  
% 2.79/1.07  --fof                                   false
% 2.79/1.07  --time_out_real                         305.
% 2.79/1.07  --time_out_virtual                      -1.
% 2.79/1.07  --symbol_type_check                     false
% 2.79/1.07  --clausify_out                          false
% 2.79/1.07  --sig_cnt_out                           false
% 2.79/1.07  --trig_cnt_out                          false
% 2.79/1.07  --trig_cnt_out_tolerance                1.
% 2.79/1.07  --trig_cnt_out_sk_spl                   false
% 2.79/1.07  --abstr_cl_out                          false
% 2.79/1.07  
% 2.79/1.07  ------ Global Options
% 2.79/1.07  
% 2.79/1.07  --schedule                              default
% 2.79/1.07  --add_important_lit                     false
% 2.79/1.07  --prop_solver_per_cl                    1000
% 2.79/1.07  --min_unsat_core                        false
% 2.79/1.07  --soft_assumptions                      false
% 2.79/1.07  --soft_lemma_size                       3
% 2.79/1.07  --prop_impl_unit_size                   0
% 2.79/1.07  --prop_impl_unit                        []
% 2.79/1.07  --share_sel_clauses                     true
% 2.79/1.07  --reset_solvers                         false
% 2.79/1.07  --bc_imp_inh                            [conj_cone]
% 2.79/1.07  --conj_cone_tolerance                   3.
% 2.79/1.07  --extra_neg_conj                        none
% 2.79/1.07  --large_theory_mode                     true
% 2.79/1.07  --prolific_symb_bound                   200
% 2.79/1.07  --lt_threshold                          2000
% 2.79/1.07  --clause_weak_htbl                      true
% 2.79/1.07  --gc_record_bc_elim                     false
% 2.79/1.07  
% 2.79/1.07  ------ Preprocessing Options
% 2.79/1.07  
% 2.79/1.07  --preprocessing_flag                    true
% 2.79/1.07  --time_out_prep_mult                    0.1
% 2.79/1.07  --splitting_mode                        input
% 2.79/1.07  --splitting_grd                         true
% 2.79/1.07  --splitting_cvd                         false
% 2.79/1.07  --splitting_cvd_svl                     false
% 2.79/1.07  --splitting_nvd                         32
% 2.79/1.07  --sub_typing                            true
% 2.79/1.07  --prep_gs_sim                           true
% 2.79/1.07  --prep_unflatten                        true
% 2.79/1.07  --prep_res_sim                          true
% 2.79/1.07  --prep_upred                            true
% 2.79/1.07  --prep_sem_filter                       exhaustive
% 2.79/1.07  --prep_sem_filter_out                   false
% 2.79/1.07  --pred_elim                             true
% 2.79/1.07  --res_sim_input                         true
% 2.79/1.07  --eq_ax_congr_red                       true
% 2.79/1.07  --pure_diseq_elim                       true
% 2.79/1.07  --brand_transform                       false
% 2.79/1.07  --non_eq_to_eq                          false
% 2.79/1.07  --prep_def_merge                        true
% 2.79/1.07  --prep_def_merge_prop_impl              false
% 2.79/1.07  --prep_def_merge_mbd                    true
% 2.79/1.07  --prep_def_merge_tr_red                 false
% 2.79/1.07  --prep_def_merge_tr_cl                  false
% 2.79/1.07  --smt_preprocessing                     true
% 2.79/1.07  --smt_ac_axioms                         fast
% 2.79/1.07  --preprocessed_out                      false
% 2.79/1.07  --preprocessed_stats                    false
% 2.79/1.07  
% 2.79/1.07  ------ Abstraction refinement Options
% 2.79/1.07  
% 2.79/1.07  --abstr_ref                             []
% 2.79/1.07  --abstr_ref_prep                        false
% 2.79/1.07  --abstr_ref_until_sat                   false
% 2.79/1.07  --abstr_ref_sig_restrict                funpre
% 2.79/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/1.07  --abstr_ref_under                       []
% 2.79/1.07  
% 2.79/1.07  ------ SAT Options
% 2.79/1.07  
% 2.79/1.07  --sat_mode                              false
% 2.79/1.07  --sat_fm_restart_options                ""
% 2.79/1.07  --sat_gr_def                            false
% 2.79/1.07  --sat_epr_types                         true
% 2.79/1.07  --sat_non_cyclic_types                  false
% 2.79/1.07  --sat_finite_models                     false
% 2.79/1.07  --sat_fm_lemmas                         false
% 2.79/1.07  --sat_fm_prep                           false
% 2.79/1.07  --sat_fm_uc_incr                        true
% 2.79/1.07  --sat_out_model                         small
% 2.79/1.07  --sat_out_clauses                       false
% 2.79/1.07  
% 2.79/1.07  ------ QBF Options
% 2.79/1.07  
% 2.79/1.07  --qbf_mode                              false
% 2.79/1.07  --qbf_elim_univ                         false
% 2.79/1.07  --qbf_dom_inst                          none
% 2.79/1.07  --qbf_dom_pre_inst                      false
% 2.79/1.07  --qbf_sk_in                             false
% 2.79/1.07  --qbf_pred_elim                         true
% 2.79/1.07  --qbf_split                             512
% 2.79/1.07  
% 2.79/1.07  ------ BMC1 Options
% 2.79/1.07  
% 2.79/1.07  --bmc1_incremental                      false
% 2.79/1.07  --bmc1_axioms                           reachable_all
% 2.79/1.07  --bmc1_min_bound                        0
% 2.79/1.07  --bmc1_max_bound                        -1
% 2.79/1.07  --bmc1_max_bound_default                -1
% 2.79/1.07  --bmc1_symbol_reachability              true
% 2.79/1.07  --bmc1_property_lemmas                  false
% 2.79/1.07  --bmc1_k_induction                      false
% 2.79/1.07  --bmc1_non_equiv_states                 false
% 2.79/1.07  --bmc1_deadlock                         false
% 2.79/1.07  --bmc1_ucm                              false
% 2.79/1.07  --bmc1_add_unsat_core                   none
% 2.79/1.07  --bmc1_unsat_core_children              false
% 2.79/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/1.07  --bmc1_out_stat                         full
% 2.79/1.07  --bmc1_ground_init                      false
% 2.79/1.07  --bmc1_pre_inst_next_state              false
% 2.79/1.07  --bmc1_pre_inst_state                   false
% 2.79/1.07  --bmc1_pre_inst_reach_state             false
% 2.79/1.07  --bmc1_out_unsat_core                   false
% 2.79/1.07  --bmc1_aig_witness_out                  false
% 2.79/1.07  --bmc1_verbose                          false
% 2.79/1.07  --bmc1_dump_clauses_tptp                false
% 2.79/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.79/1.07  --bmc1_dump_file                        -
% 2.79/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.79/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.79/1.07  --bmc1_ucm_extend_mode                  1
% 2.79/1.07  --bmc1_ucm_init_mode                    2
% 2.79/1.07  --bmc1_ucm_cone_mode                    none
% 2.79/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.79/1.07  --bmc1_ucm_relax_model                  4
% 2.79/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.79/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/1.07  --bmc1_ucm_layered_model                none
% 2.79/1.07  --bmc1_ucm_max_lemma_size               10
% 2.79/1.07  
% 2.79/1.07  ------ AIG Options
% 2.79/1.07  
% 2.79/1.07  --aig_mode                              false
% 2.79/1.07  
% 2.79/1.07  ------ Instantiation Options
% 2.79/1.07  
% 2.79/1.07  --instantiation_flag                    true
% 2.79/1.07  --inst_sos_flag                         false
% 2.79/1.07  --inst_sos_phase                        true
% 2.79/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/1.07  --inst_lit_sel_side                     num_symb
% 2.79/1.07  --inst_solver_per_active                1400
% 2.79/1.07  --inst_solver_calls_frac                1.
% 2.79/1.07  --inst_passive_queue_type               priority_queues
% 2.79/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/1.07  --inst_passive_queues_freq              [25;2]
% 2.79/1.07  --inst_dismatching                      true
% 2.79/1.07  --inst_eager_unprocessed_to_passive     true
% 2.79/1.07  --inst_prop_sim_given                   true
% 2.79/1.07  --inst_prop_sim_new                     false
% 2.79/1.07  --inst_subs_new                         false
% 2.79/1.07  --inst_eq_res_simp                      false
% 2.79/1.07  --inst_subs_given                       false
% 2.79/1.07  --inst_orphan_elimination               true
% 2.79/1.07  --inst_learning_loop_flag               true
% 2.79/1.07  --inst_learning_start                   3000
% 2.79/1.07  --inst_learning_factor                  2
% 2.79/1.07  --inst_start_prop_sim_after_learn       3
% 2.79/1.07  --inst_sel_renew                        solver
% 2.79/1.07  --inst_lit_activity_flag                true
% 2.79/1.07  --inst_restr_to_given                   false
% 2.79/1.07  --inst_activity_threshold               500
% 2.79/1.07  --inst_out_proof                        true
% 2.79/1.07  
% 2.79/1.07  ------ Resolution Options
% 2.79/1.07  
% 2.79/1.07  --resolution_flag                       true
% 2.79/1.07  --res_lit_sel                           adaptive
% 2.79/1.07  --res_lit_sel_side                      none
% 2.79/1.07  --res_ordering                          kbo
% 2.79/1.07  --res_to_prop_solver                    active
% 2.79/1.07  --res_prop_simpl_new                    false
% 2.79/1.07  --res_prop_simpl_given                  true
% 2.79/1.07  --res_passive_queue_type                priority_queues
% 2.79/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/1.07  --res_passive_queues_freq               [15;5]
% 2.79/1.07  --res_forward_subs                      full
% 2.79/1.07  --res_backward_subs                     full
% 2.79/1.07  --res_forward_subs_resolution           true
% 2.79/1.07  --res_backward_subs_resolution          true
% 2.79/1.07  --res_orphan_elimination                true
% 2.79/1.07  --res_time_limit                        2.
% 2.79/1.07  --res_out_proof                         true
% 2.79/1.07  
% 2.79/1.07  ------ Superposition Options
% 2.79/1.07  
% 2.79/1.07  --superposition_flag                    true
% 2.79/1.07  --sup_passive_queue_type                priority_queues
% 2.79/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.79/1.07  --demod_completeness_check              fast
% 2.79/1.07  --demod_use_ground                      true
% 2.79/1.07  --sup_to_prop_solver                    passive
% 2.79/1.07  --sup_prop_simpl_new                    true
% 2.79/1.07  --sup_prop_simpl_given                  true
% 2.79/1.07  --sup_fun_splitting                     false
% 2.79/1.07  --sup_smt_interval                      50000
% 2.79/1.07  
% 2.79/1.07  ------ Superposition Simplification Setup
% 2.79/1.07  
% 2.79/1.07  --sup_indices_passive                   []
% 2.79/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.07  --sup_full_bw                           [BwDemod]
% 2.79/1.07  --sup_immed_triv                        [TrivRules]
% 2.79/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.07  --sup_immed_bw_main                     []
% 2.79/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.07  
% 2.79/1.07  ------ Combination Options
% 2.79/1.07  
% 2.79/1.07  --comb_res_mult                         3
% 2.79/1.07  --comb_sup_mult                         2
% 2.79/1.07  --comb_inst_mult                        10
% 2.79/1.07  
% 2.79/1.07  ------ Debug Options
% 2.79/1.07  
% 2.79/1.07  --dbg_backtrace                         false
% 2.79/1.07  --dbg_dump_prop_clauses                 false
% 2.79/1.07  --dbg_dump_prop_clauses_file            -
% 2.79/1.07  --dbg_out_stat                          false
% 2.79/1.07  ------ Parsing...
% 2.79/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/1.07  
% 2.79/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.79/1.07  
% 2.79/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/1.07  
% 2.79/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.79/1.07  ------ Proving...
% 2.79/1.07  ------ Problem Properties 
% 2.79/1.07  
% 2.79/1.07  
% 2.79/1.07  clauses                                 18
% 2.79/1.07  conjectures                             4
% 2.79/1.07  EPR                                     3
% 2.79/1.07  Horn                                    16
% 2.79/1.07  unary                                   5
% 2.79/1.07  binary                                  9
% 2.79/1.07  lits                                    35
% 2.79/1.07  lits eq                                 9
% 2.79/1.07  fd_pure                                 0
% 2.79/1.07  fd_pseudo                               0
% 2.79/1.07  fd_cond                                 2
% 2.79/1.07  fd_pseudo_cond                          0
% 2.79/1.07  AC symbols                              0
% 2.79/1.07  
% 2.79/1.07  ------ Schedule dynamic 5 is on 
% 2.79/1.07  
% 2.79/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.79/1.07  
% 2.79/1.07  
% 2.79/1.07  ------ 
% 2.79/1.07  Current options:
% 2.79/1.07  ------ 
% 2.79/1.07  
% 2.79/1.07  ------ Input Options
% 2.79/1.07  
% 2.79/1.07  --out_options                           all
% 2.79/1.07  --tptp_safe_out                         true
% 2.79/1.07  --problem_path                          ""
% 2.79/1.07  --include_path                          ""
% 2.79/1.07  --clausifier                            res/vclausify_rel
% 2.79/1.07  --clausifier_options                    --mode clausify
% 2.79/1.07  --stdin                                 false
% 2.79/1.07  --stats_out                             all
% 2.79/1.07  
% 2.79/1.07  ------ General Options
% 2.79/1.07  
% 2.79/1.07  --fof                                   false
% 2.79/1.07  --time_out_real                         305.
% 2.79/1.07  --time_out_virtual                      -1.
% 2.79/1.07  --symbol_type_check                     false
% 2.79/1.07  --clausify_out                          false
% 2.79/1.07  --sig_cnt_out                           false
% 2.79/1.07  --trig_cnt_out                          false
% 2.79/1.07  --trig_cnt_out_tolerance                1.
% 2.79/1.07  --trig_cnt_out_sk_spl                   false
% 2.79/1.07  --abstr_cl_out                          false
% 2.79/1.07  
% 2.79/1.07  ------ Global Options
% 2.79/1.07  
% 2.79/1.07  --schedule                              default
% 2.79/1.07  --add_important_lit                     false
% 2.79/1.07  --prop_solver_per_cl                    1000
% 2.79/1.07  --min_unsat_core                        false
% 2.79/1.07  --soft_assumptions                      false
% 2.79/1.07  --soft_lemma_size                       3
% 2.79/1.07  --prop_impl_unit_size                   0
% 2.79/1.07  --prop_impl_unit                        []
% 2.79/1.07  --share_sel_clauses                     true
% 2.79/1.07  --reset_solvers                         false
% 2.79/1.07  --bc_imp_inh                            [conj_cone]
% 2.79/1.07  --conj_cone_tolerance                   3.
% 2.79/1.07  --extra_neg_conj                        none
% 2.79/1.07  --large_theory_mode                     true
% 2.79/1.07  --prolific_symb_bound                   200
% 2.79/1.07  --lt_threshold                          2000
% 2.79/1.07  --clause_weak_htbl                      true
% 2.79/1.07  --gc_record_bc_elim                     false
% 2.79/1.07  
% 2.79/1.07  ------ Preprocessing Options
% 2.79/1.07  
% 2.79/1.07  --preprocessing_flag                    true
% 2.79/1.07  --time_out_prep_mult                    0.1
% 2.79/1.07  --splitting_mode                        input
% 2.79/1.07  --splitting_grd                         true
% 2.79/1.07  --splitting_cvd                         false
% 2.79/1.07  --splitting_cvd_svl                     false
% 2.79/1.07  --splitting_nvd                         32
% 2.79/1.07  --sub_typing                            true
% 2.79/1.07  --prep_gs_sim                           true
% 2.79/1.07  --prep_unflatten                        true
% 2.79/1.07  --prep_res_sim                          true
% 2.79/1.07  --prep_upred                            true
% 2.79/1.07  --prep_sem_filter                       exhaustive
% 2.79/1.07  --prep_sem_filter_out                   false
% 2.79/1.07  --pred_elim                             true
% 2.79/1.07  --res_sim_input                         true
% 2.79/1.07  --eq_ax_congr_red                       true
% 2.79/1.07  --pure_diseq_elim                       true
% 2.79/1.07  --brand_transform                       false
% 2.79/1.07  --non_eq_to_eq                          false
% 2.79/1.07  --prep_def_merge                        true
% 2.79/1.07  --prep_def_merge_prop_impl              false
% 2.79/1.07  --prep_def_merge_mbd                    true
% 2.79/1.07  --prep_def_merge_tr_red                 false
% 2.79/1.07  --prep_def_merge_tr_cl                  false
% 2.79/1.07  --smt_preprocessing                     true
% 2.79/1.07  --smt_ac_axioms                         fast
% 2.79/1.07  --preprocessed_out                      false
% 2.79/1.07  --preprocessed_stats                    false
% 2.79/1.07  
% 2.79/1.07  ------ Abstraction refinement Options
% 2.79/1.07  
% 2.79/1.07  --abstr_ref                             []
% 2.79/1.07  --abstr_ref_prep                        false
% 2.79/1.07  --abstr_ref_until_sat                   false
% 2.79/1.07  --abstr_ref_sig_restrict                funpre
% 2.79/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/1.07  --abstr_ref_under                       []
% 2.79/1.07  
% 2.79/1.07  ------ SAT Options
% 2.79/1.07  
% 2.79/1.07  --sat_mode                              false
% 2.79/1.07  --sat_fm_restart_options                ""
% 2.79/1.07  --sat_gr_def                            false
% 2.79/1.07  --sat_epr_types                         true
% 2.79/1.07  --sat_non_cyclic_types                  false
% 2.79/1.07  --sat_finite_models                     false
% 2.79/1.07  --sat_fm_lemmas                         false
% 2.79/1.07  --sat_fm_prep                           false
% 2.79/1.07  --sat_fm_uc_incr                        true
% 2.79/1.07  --sat_out_model                         small
% 2.79/1.07  --sat_out_clauses                       false
% 2.79/1.07  
% 2.79/1.07  ------ QBF Options
% 2.79/1.07  
% 2.79/1.07  --qbf_mode                              false
% 2.79/1.07  --qbf_elim_univ                         false
% 2.79/1.07  --qbf_dom_inst                          none
% 2.79/1.07  --qbf_dom_pre_inst                      false
% 2.79/1.07  --qbf_sk_in                             false
% 2.79/1.07  --qbf_pred_elim                         true
% 2.79/1.07  --qbf_split                             512
% 2.79/1.07  
% 2.79/1.07  ------ BMC1 Options
% 2.79/1.07  
% 2.79/1.07  --bmc1_incremental                      false
% 2.79/1.07  --bmc1_axioms                           reachable_all
% 2.79/1.07  --bmc1_min_bound                        0
% 2.79/1.07  --bmc1_max_bound                        -1
% 2.79/1.07  --bmc1_max_bound_default                -1
% 2.79/1.07  --bmc1_symbol_reachability              true
% 2.79/1.07  --bmc1_property_lemmas                  false
% 2.79/1.07  --bmc1_k_induction                      false
% 2.79/1.07  --bmc1_non_equiv_states                 false
% 2.79/1.07  --bmc1_deadlock                         false
% 2.79/1.07  --bmc1_ucm                              false
% 2.79/1.07  --bmc1_add_unsat_core                   none
% 2.79/1.07  --bmc1_unsat_core_children              false
% 2.79/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/1.07  --bmc1_out_stat                         full
% 2.79/1.07  --bmc1_ground_init                      false
% 2.79/1.07  --bmc1_pre_inst_next_state              false
% 2.79/1.07  --bmc1_pre_inst_state                   false
% 2.79/1.07  --bmc1_pre_inst_reach_state             false
% 2.79/1.07  --bmc1_out_unsat_core                   false
% 2.79/1.07  --bmc1_aig_witness_out                  false
% 2.79/1.07  --bmc1_verbose                          false
% 2.79/1.07  --bmc1_dump_clauses_tptp                false
% 2.79/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.79/1.07  --bmc1_dump_file                        -
% 2.79/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.79/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.79/1.07  --bmc1_ucm_extend_mode                  1
% 2.79/1.07  --bmc1_ucm_init_mode                    2
% 2.79/1.07  --bmc1_ucm_cone_mode                    none
% 2.79/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.79/1.07  --bmc1_ucm_relax_model                  4
% 2.79/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.79/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/1.07  --bmc1_ucm_layered_model                none
% 2.79/1.07  --bmc1_ucm_max_lemma_size               10
% 2.79/1.07  
% 2.79/1.07  ------ AIG Options
% 2.79/1.07  
% 2.79/1.07  --aig_mode                              false
% 2.79/1.07  
% 2.79/1.07  ------ Instantiation Options
% 2.79/1.07  
% 2.79/1.07  --instantiation_flag                    true
% 2.79/1.07  --inst_sos_flag                         false
% 2.79/1.07  --inst_sos_phase                        true
% 2.79/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/1.07  --inst_lit_sel_side                     none
% 2.79/1.07  --inst_solver_per_active                1400
% 2.79/1.07  --inst_solver_calls_frac                1.
% 2.79/1.07  --inst_passive_queue_type               priority_queues
% 2.79/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/1.07  --inst_passive_queues_freq              [25;2]
% 2.79/1.07  --inst_dismatching                      true
% 2.79/1.07  --inst_eager_unprocessed_to_passive     true
% 2.79/1.07  --inst_prop_sim_given                   true
% 2.79/1.07  --inst_prop_sim_new                     false
% 2.79/1.07  --inst_subs_new                         false
% 2.79/1.07  --inst_eq_res_simp                      false
% 2.79/1.07  --inst_subs_given                       false
% 2.79/1.07  --inst_orphan_elimination               true
% 2.79/1.07  --inst_learning_loop_flag               true
% 2.79/1.07  --inst_learning_start                   3000
% 2.79/1.07  --inst_learning_factor                  2
% 2.79/1.07  --inst_start_prop_sim_after_learn       3
% 2.79/1.07  --inst_sel_renew                        solver
% 2.79/1.07  --inst_lit_activity_flag                true
% 2.79/1.07  --inst_restr_to_given                   false
% 2.79/1.07  --inst_activity_threshold               500
% 2.79/1.07  --inst_out_proof                        true
% 2.79/1.07  
% 2.79/1.07  ------ Resolution Options
% 2.79/1.07  
% 2.79/1.07  --resolution_flag                       false
% 2.79/1.07  --res_lit_sel                           adaptive
% 2.79/1.07  --res_lit_sel_side                      none
% 2.79/1.07  --res_ordering                          kbo
% 2.79/1.07  --res_to_prop_solver                    active
% 2.79/1.07  --res_prop_simpl_new                    false
% 2.79/1.07  --res_prop_simpl_given                  true
% 2.79/1.07  --res_passive_queue_type                priority_queues
% 2.79/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/1.07  --res_passive_queues_freq               [15;5]
% 2.79/1.07  --res_forward_subs                      full
% 2.79/1.07  --res_backward_subs                     full
% 2.79/1.07  --res_forward_subs_resolution           true
% 2.79/1.07  --res_backward_subs_resolution          true
% 2.79/1.07  --res_orphan_elimination                true
% 2.79/1.07  --res_time_limit                        2.
% 2.79/1.07  --res_out_proof                         true
% 2.79/1.07  
% 2.79/1.07  ------ Superposition Options
% 2.79/1.07  
% 2.79/1.07  --superposition_flag                    true
% 2.79/1.07  --sup_passive_queue_type                priority_queues
% 2.79/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.79/1.07  --demod_completeness_check              fast
% 2.79/1.07  --demod_use_ground                      true
% 2.79/1.07  --sup_to_prop_solver                    passive
% 2.79/1.07  --sup_prop_simpl_new                    true
% 2.79/1.07  --sup_prop_simpl_given                  true
% 2.79/1.07  --sup_fun_splitting                     false
% 2.79/1.07  --sup_smt_interval                      50000
% 2.79/1.07  
% 2.79/1.07  ------ Superposition Simplification Setup
% 2.79/1.07  
% 2.79/1.07  --sup_indices_passive                   []
% 2.79/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.07  --sup_full_bw                           [BwDemod]
% 2.79/1.07  --sup_immed_triv                        [TrivRules]
% 2.79/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.07  --sup_immed_bw_main                     []
% 2.79/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/1.07  
% 2.79/1.07  ------ Combination Options
% 2.79/1.07  
% 2.79/1.07  --comb_res_mult                         3
% 2.79/1.07  --comb_sup_mult                         2
% 2.79/1.07  --comb_inst_mult                        10
% 2.79/1.07  
% 2.79/1.07  ------ Debug Options
% 2.79/1.07  
% 2.79/1.07  --dbg_backtrace                         false
% 2.79/1.07  --dbg_dump_prop_clauses                 false
% 2.79/1.07  --dbg_dump_prop_clauses_file            -
% 2.79/1.07  --dbg_out_stat                          false
% 2.79/1.07  
% 2.79/1.07  
% 2.79/1.07  
% 2.79/1.07  
% 2.79/1.07  ------ Proving...
% 2.79/1.07  
% 2.79/1.07  
% 2.79/1.07  % SZS status Theorem for theBenchmark.p
% 2.79/1.07  
% 2.79/1.07   Resolution empty clause
% 2.79/1.07  
% 2.79/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/1.07  
% 2.79/1.07  fof(f12,conjecture,(
% 2.79/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f13,negated_conjecture,(
% 2.79/1.07    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.79/1.07    inference(negated_conjecture,[],[f12])).
% 2.79/1.07  
% 2.79/1.07  fof(f24,plain,(
% 2.79/1.07    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.79/1.07    inference(ennf_transformation,[],[f13])).
% 2.79/1.07  
% 2.79/1.07  fof(f25,plain,(
% 2.79/1.07    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.79/1.07    inference(flattening,[],[f24])).
% 2.79/1.07  
% 2.79/1.07  fof(f30,plain,(
% 2.79/1.07    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK2),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.79/1.07    introduced(choice_axiom,[])).
% 2.79/1.07  
% 2.79/1.07  fof(f29,plain,(
% 2.79/1.07    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 2.79/1.07    introduced(choice_axiom,[])).
% 2.79/1.07  
% 2.79/1.07  fof(f31,plain,(
% 2.79/1.07    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.79/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f30,f29])).
% 2.79/1.07  
% 2.79/1.07  fof(f46,plain,(
% 2.79/1.07    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.79/1.07    inference(cnf_transformation,[],[f31])).
% 2.79/1.07  
% 2.79/1.07  fof(f6,axiom,(
% 2.79/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f19,plain,(
% 2.79/1.07    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.79/1.07    inference(ennf_transformation,[],[f6])).
% 2.79/1.07  
% 2.79/1.07  fof(f39,plain,(
% 2.79/1.07    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.79/1.07    inference(cnf_transformation,[],[f19])).
% 2.79/1.07  
% 2.79/1.07  fof(f8,axiom,(
% 2.79/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f21,plain,(
% 2.79/1.07    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.79/1.07    inference(ennf_transformation,[],[f8])).
% 2.79/1.07  
% 2.79/1.07  fof(f42,plain,(
% 2.79/1.07    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.79/1.07    inference(cnf_transformation,[],[f21])).
% 2.79/1.07  
% 2.79/1.07  fof(f47,plain,(
% 2.79/1.07    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 2.79/1.07    inference(cnf_transformation,[],[f31])).
% 2.79/1.07  
% 2.79/1.07  fof(f49,plain,(
% 2.79/1.07    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 2.79/1.07    inference(cnf_transformation,[],[f31])).
% 2.79/1.07  
% 2.79/1.07  fof(f48,plain,(
% 2.79/1.07    r1_tarski(sK1,sK2)),
% 2.79/1.07    inference(cnf_transformation,[],[f31])).
% 2.79/1.07  
% 2.79/1.07  fof(f11,axiom,(
% 2.79/1.07    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f22,plain,(
% 2.79/1.07    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.79/1.07    inference(ennf_transformation,[],[f11])).
% 2.79/1.07  
% 2.79/1.07  fof(f23,plain,(
% 2.79/1.07    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.79/1.07    inference(flattening,[],[f22])).
% 2.79/1.07  
% 2.79/1.07  fof(f45,plain,(
% 2.79/1.07    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.79/1.07    inference(cnf_transformation,[],[f23])).
% 2.79/1.07  
% 2.79/1.07  fof(f1,axiom,(
% 2.79/1.07    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f26,plain,(
% 2.79/1.07    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.79/1.07    inference(nnf_transformation,[],[f1])).
% 2.79/1.07  
% 2.79/1.07  fof(f33,plain,(
% 2.79/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.79/1.07    inference(cnf_transformation,[],[f26])).
% 2.79/1.07  
% 2.79/1.07  fof(f32,plain,(
% 2.79/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.79/1.07    inference(cnf_transformation,[],[f26])).
% 2.79/1.07  
% 2.79/1.07  fof(f40,plain,(
% 2.79/1.07    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.79/1.07    inference(cnf_transformation,[],[f19])).
% 2.79/1.07  
% 2.79/1.07  fof(f50,plain,(
% 2.79/1.07    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.79/1.07    inference(equality_resolution,[],[f40])).
% 2.79/1.07  
% 2.79/1.07  fof(f5,axiom,(
% 2.79/1.07    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f38,plain,(
% 2.79/1.07    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.79/1.07    inference(cnf_transformation,[],[f5])).
% 2.79/1.07  
% 2.79/1.07  fof(f7,axiom,(
% 2.79/1.07    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f20,plain,(
% 2.79/1.07    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.79/1.07    inference(ennf_transformation,[],[f7])).
% 2.79/1.07  
% 2.79/1.07  fof(f41,plain,(
% 2.79/1.07    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.79/1.07    inference(cnf_transformation,[],[f20])).
% 2.79/1.07  
% 2.79/1.07  fof(f9,axiom,(
% 2.79/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f28,plain,(
% 2.79/1.07    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.79/1.07    inference(nnf_transformation,[],[f9])).
% 2.79/1.07  
% 2.79/1.07  fof(f43,plain,(
% 2.79/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.79/1.07    inference(cnf_transformation,[],[f28])).
% 2.79/1.07  
% 2.79/1.07  fof(f4,axiom,(
% 2.79/1.07    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f27,plain,(
% 2.79/1.07    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.79/1.07    inference(nnf_transformation,[],[f4])).
% 2.79/1.07  
% 2.79/1.07  fof(f37,plain,(
% 2.79/1.07    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.79/1.07    inference(cnf_transformation,[],[f27])).
% 2.79/1.07  
% 2.79/1.07  fof(f3,axiom,(
% 2.79/1.07    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.79/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.79/1.07  
% 2.79/1.07  fof(f17,plain,(
% 2.79/1.07    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.79/1.07    inference(ennf_transformation,[],[f3])).
% 2.79/1.07  
% 2.79/1.07  fof(f18,plain,(
% 2.79/1.07    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.79/1.07    inference(flattening,[],[f17])).
% 2.79/1.07  
% 2.79/1.07  fof(f35,plain,(
% 2.79/1.07    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.79/1.07    inference(cnf_transformation,[],[f18])).
% 2.79/1.07  
% 2.79/1.07  fof(f36,plain,(
% 2.79/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.79/1.07    inference(cnf_transformation,[],[f27])).
% 2.79/1.07  
% 2.79/1.07  cnf(c_17,negated_conjecture,
% 2.79/1.07      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.79/1.07      inference(cnf_transformation,[],[f46]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_671,plain,
% 2.79/1.07      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_8,plain,
% 2.79/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.79/1.07      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.79/1.07      | k1_xboole_0 = X0 ),
% 2.79/1.07      inference(cnf_transformation,[],[f39]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_680,plain,
% 2.79/1.07      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.79/1.07      | k1_xboole_0 = X1
% 2.79/1.07      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1873,plain,
% 2.79/1.07      ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1) | sK1 = k1_xboole_0 ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_671,c_680]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_10,plain,
% 2.79/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.79/1.07      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.79/1.07      inference(cnf_transformation,[],[f42]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_678,plain,
% 2.79/1.07      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.79/1.07      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1748,plain,
% 2.79/1.07      ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_671,c_678]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2167,plain,
% 2.79/1.07      ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | sK1 = k1_xboole_0 ),
% 2.79/1.07      inference(light_normalisation,[status(thm)],[c_1873,c_1748]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_16,negated_conjecture,
% 2.79/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.79/1.07      inference(cnf_transformation,[],[f47]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_672,plain,
% 2.79/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1872,plain,
% 2.79/1.07      ( k6_setfam_1(sK0,sK2) = k8_setfam_1(sK0,sK2) | sK2 = k1_xboole_0 ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_672,c_680]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1747,plain,
% 2.79/1.07      ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_672,c_678]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2054,plain,
% 2.79/1.07      ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.79/1.07      inference(light_normalisation,[status(thm)],[c_1872,c_1747]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_14,negated_conjecture,
% 2.79/1.07      ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
% 2.79/1.07      inference(cnf_transformation,[],[f49]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_674,plain,
% 2.79/1.07      ( r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2058,plain,
% 2.79/1.07      ( sK2 = k1_xboole_0
% 2.79/1.07      | r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_2054,c_674]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2171,plain,
% 2.79/1.07      ( sK1 = k1_xboole_0
% 2.79/1.07      | sK2 = k1_xboole_0
% 2.79/1.07      | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) != iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_2167,c_2058]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_15,negated_conjecture,
% 2.79/1.07      ( r1_tarski(sK1,sK2) ),
% 2.79/1.07      inference(cnf_transformation,[],[f48]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_673,plain,
% 2.79/1.07      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_13,plain,
% 2.79/1.07      ( ~ r1_tarski(X0,X1)
% 2.79/1.07      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.79/1.07      | k1_xboole_0 = X0 ),
% 2.79/1.07      inference(cnf_transformation,[],[f45]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_675,plain,
% 2.79/1.07      ( k1_xboole_0 = X0
% 2.79/1.07      | r1_tarski(X0,X1) != iProver_top
% 2.79/1.07      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_0,plain,
% 2.79/1.07      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.79/1.07      inference(cnf_transformation,[],[f33]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_688,plain,
% 2.79/1.07      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1153,plain,
% 2.79/1.07      ( k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_xboole_0
% 2.79/1.07      | k1_xboole_0 = X1
% 2.79/1.07      | r1_tarski(X1,X0) != iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_675,c_688]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2471,plain,
% 2.79/1.07      ( k4_xboole_0(k1_setfam_1(sK2),k1_setfam_1(sK1)) = k1_xboole_0
% 2.79/1.07      | sK1 = k1_xboole_0 ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_673,c_1153]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1,plain,
% 2.79/1.07      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.79/1.07      inference(cnf_transformation,[],[f32]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_687,plain,
% 2.79/1.07      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2762,plain,
% 2.79/1.07      ( sK1 = k1_xboole_0
% 2.79/1.07      | r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) = iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_2471,c_687]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3113,plain,
% 2.79/1.07      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.79/1.07      inference(global_propositional_subsumption,[status(thm)],[c_2171,c_2762]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3114,plain,
% 2.79/1.07      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.79/1.07      inference(renaming,[status(thm)],[c_3113]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3129,plain,
% 2.79/1.07      ( sK2 = k1_xboole_0
% 2.79/1.07      | r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_3114,c_674]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_7,plain,
% 2.79/1.07      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.79/1.07      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.79/1.07      inference(cnf_transformation,[],[f50]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_681,plain,
% 2.79/1.07      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.79/1.07      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_6,plain,
% 2.79/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.79/1.07      inference(cnf_transformation,[],[f38]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_682,plain,
% 2.79/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_725,plain,
% 2.79/1.07      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.79/1.07      inference(forward_subsumption_resolution,[status(thm)],[c_681,c_682]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3138,plain,
% 2.79/1.07      ( sK2 = k1_xboole_0
% 2.79/1.07      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) != iProver_top ),
% 2.79/1.07      inference(demodulation,[status(thm)],[c_3129,c_725]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_19,plain,
% 2.79/1.07      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_9,plain,
% 2.79/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.79/1.07      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.79/1.07      inference(cnf_transformation,[],[f41]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_818,plain,
% 2.79/1.07      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
% 2.79/1.07      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 2.79/1.07      inference(instantiation,[status(thm)],[c_9]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_819,plain,
% 2.79/1.07      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) = iProver_top
% 2.79/1.07      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) != iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_12,plain,
% 2.79/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.79/1.07      inference(cnf_transformation,[],[f43]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1221,plain,
% 2.79/1.07      ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(X0))
% 2.79/1.07      | r1_tarski(k8_setfam_1(sK0,sK2),X0) ),
% 2.79/1.07      inference(instantiation,[status(thm)],[c_12]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1351,plain,
% 2.79/1.07      ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
% 2.79/1.07      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
% 2.79/1.07      inference(instantiation,[status(thm)],[c_1221]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1352,plain,
% 2.79/1.07      ( m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) != iProver_top
% 2.79/1.07      | r1_tarski(k8_setfam_1(sK0,sK2),sK0) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_1351]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3172,plain,
% 2.79/1.07      ( sK2 = k1_xboole_0 ),
% 2.79/1.07      inference(global_propositional_subsumption,
% 2.79/1.07                [status(thm)],
% 2.79/1.07                [c_3138,c_19,c_819,c_1352]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3190,plain,
% 2.79/1.07      ( r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 2.79/1.07      inference(demodulation,[status(thm)],[c_3172,c_673]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_676,plain,
% 2.79/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.79/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1167,plain,
% 2.79/1.07      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_682,c_676]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2498,plain,
% 2.79/1.07      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_1167,c_688]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_4,plain,
% 2.79/1.07      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.79/1.07      inference(cnf_transformation,[],[f37]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_684,plain,
% 2.79/1.07      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2629,plain,
% 2.79/1.07      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_2498,c_684]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3,plain,
% 2.79/1.07      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | ~ r1_tarski(X2,X0) ),
% 2.79/1.07      inference(cnf_transformation,[],[f35]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_685,plain,
% 2.79/1.07      ( r1_xboole_0(X0,X1) != iProver_top
% 2.79/1.07      | r1_xboole_0(X2,X1) = iProver_top
% 2.79/1.07      | r1_tarski(X2,X0) != iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_2637,plain,
% 2.79/1.07      ( r1_xboole_0(X0,X1) = iProver_top
% 2.79/1.07      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_2629,c_685]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3340,plain,
% 2.79/1.07      ( r1_xboole_0(sK1,X0) = iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_3190,c_2637]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_5,plain,
% 2.79/1.07      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.79/1.07      inference(cnf_transformation,[],[f36]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_683,plain,
% 2.79/1.07      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3599,plain,
% 2.79/1.07      ( k4_xboole_0(sK1,X0) = sK1 ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_3340,c_683]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1169,plain,
% 2.79/1.07      ( r1_tarski(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_671,c_676]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1286,plain,
% 2.79/1.07      ( k4_xboole_0(sK1,k1_zfmisc_1(sK0)) = k1_xboole_0 ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_1169,c_688]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3794,plain,
% 2.79/1.07      ( sK1 = k1_xboole_0 ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_3599,c_1286]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3188,plain,
% 2.79/1.07      ( r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.79/1.07      inference(demodulation,[status(thm)],[c_3172,c_674]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3195,plain,
% 2.79/1.07      ( r1_tarski(sK0,k8_setfam_1(sK0,sK1)) != iProver_top ),
% 2.79/1.07      inference(demodulation,[status(thm)],[c_3188,c_725]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3877,plain,
% 2.79/1.07      ( r1_tarski(sK0,k8_setfam_1(sK0,k1_xboole_0)) != iProver_top ),
% 2.79/1.07      inference(demodulation,[status(thm)],[c_3794,c_3195]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3894,plain,
% 2.79/1.07      ( r1_tarski(sK0,sK0) != iProver_top ),
% 2.79/1.07      inference(demodulation,[status(thm)],[c_3877,c_725]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_679,plain,
% 2.79/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.79/1.07      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_1611,plain,
% 2.79/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 2.79/1.07      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_725,c_679]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_808,plain,
% 2.79/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 2.79/1.07      inference(instantiation,[status(thm)],[c_6]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_811,plain,
% 2.79/1.07      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 2.79/1.07      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3902,plain,
% 2.79/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.79/1.07      inference(global_propositional_subsumption,[status(thm)],[c_1611,c_811]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_3909,plain,
% 2.79/1.07      ( r1_tarski(X0,X0) = iProver_top ),
% 2.79/1.07      inference(superposition,[status(thm)],[c_3902,c_676]) ).
% 2.79/1.07  
% 2.79/1.07  cnf(c_4811,plain,
% 2.79/1.07      ( $false ),
% 2.79/1.07      inference(forward_subsumption_resolution,[status(thm)],[c_3894,c_3909]) ).
% 2.79/1.07  
% 2.79/1.07  
% 2.79/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/1.07  
% 2.79/1.07  ------                               Statistics
% 2.79/1.07  
% 2.79/1.07  ------ General
% 2.79/1.07  
% 2.79/1.07  abstr_ref_over_cycles:                  0
% 2.79/1.07  abstr_ref_under_cycles:                 0
% 2.79/1.07  gc_basic_clause_elim:                   0
% 2.79/1.07  forced_gc_time:                         0
% 2.79/1.07  parsing_time:                           0.012
% 2.79/1.07  unif_index_cands_time:                  0.
% 2.79/1.07  unif_index_add_time:                    0.
% 2.79/1.07  orderings_time:                         0.
% 2.79/1.07  out_proof_time:                         0.007
% 2.79/1.07  total_time:                             0.161
% 2.79/1.07  num_of_symbols:                         43
% 2.79/1.07  num_of_terms:                           3640
% 2.79/1.07  
% 2.79/1.07  ------ Preprocessing
% 2.79/1.07  
% 2.79/1.07  num_of_splits:                          0
% 2.79/1.07  num_of_split_atoms:                     0
% 2.79/1.07  num_of_reused_defs:                     0
% 2.79/1.07  num_eq_ax_congr_red:                    14
% 2.79/1.07  num_of_sem_filtered_clauses:            1
% 2.79/1.07  num_of_subtypes:                        0
% 2.79/1.07  monotx_restored_types:                  0
% 2.79/1.07  sat_num_of_epr_types:                   0
% 2.79/1.07  sat_num_of_non_cyclic_types:            0
% 2.79/1.07  sat_guarded_non_collapsed_types:        0
% 2.79/1.07  num_pure_diseq_elim:                    0
% 2.79/1.07  simp_replaced_by:                       0
% 2.79/1.07  res_preprocessed:                       67
% 2.79/1.07  prep_upred:                             0
% 2.79/1.07  prep_unflattend:                        0
% 2.79/1.07  smt_new_axioms:                         0
% 2.79/1.07  pred_elim_cands:                        3
% 2.79/1.07  pred_elim:                              0
% 2.79/1.07  pred_elim_cl:                           0
% 2.79/1.07  pred_elim_cycles:                       1
% 2.79/1.07  merged_defs:                            18
% 2.79/1.07  merged_defs_ncl:                        0
% 2.79/1.07  bin_hyper_res:                          18
% 2.79/1.07  prep_cycles:                            3
% 2.79/1.07  pred_elim_time:                         0.
% 2.79/1.07  splitting_time:                         0.
% 2.79/1.07  sem_filter_time:                        0.
% 2.79/1.07  monotx_time:                            0.001
% 2.79/1.07  subtype_inf_time:                       0.
% 2.79/1.07  
% 2.79/1.07  ------ Problem properties
% 2.79/1.07  
% 2.79/1.07  clauses:                                18
% 2.79/1.07  conjectures:                            4
% 2.79/1.07  epr:                                    3
% 2.79/1.07  horn:                                   16
% 2.79/1.07  ground:                                 4
% 2.79/1.07  unary:                                  5
% 2.79/1.07  binary:                                 9
% 2.79/1.07  lits:                                   35
% 2.79/1.07  lits_eq:                                9
% 2.79/1.07  fd_pure:                                0
% 2.79/1.07  fd_pseudo:                              0
% 2.79/1.07  fd_cond:                                2
% 2.79/1.07  fd_pseudo_cond:                         0
% 2.79/1.07  ac_symbols:                             0
% 2.79/1.07  
% 2.79/1.07  ------ Propositional Solver
% 2.79/1.07  
% 2.79/1.07  prop_solver_calls:                      26
% 2.79/1.07  prop_fast_solver_calls:                 441
% 2.79/1.07  smt_solver_calls:                       0
% 2.79/1.07  smt_fast_solver_calls:                  0
% 2.79/1.07  prop_num_of_clauses:                    1648
% 2.79/1.07  prop_preprocess_simplified:             4345
% 2.79/1.07  prop_fo_subsumed:                       15
% 2.79/1.07  prop_solver_time:                       0.
% 2.79/1.07  smt_solver_time:                        0.
% 2.79/1.07  smt_fast_solver_time:                   0.
% 2.79/1.07  prop_fast_solver_time:                  0.
% 2.79/1.07  prop_unsat_core_time:                   0.
% 2.79/1.07  
% 2.79/1.07  ------ QBF
% 2.79/1.07  
% 2.79/1.07  qbf_q_res:                              0
% 2.79/1.07  qbf_num_tautologies:                    0
% 2.79/1.07  qbf_prep_cycles:                        0
% 2.79/1.07  
% 2.79/1.07  ------ BMC1
% 2.79/1.07  
% 2.79/1.07  bmc1_current_bound:                     -1
% 2.79/1.07  bmc1_last_solved_bound:                 -1
% 2.79/1.07  bmc1_unsat_core_size:                   -1
% 2.79/1.07  bmc1_unsat_core_parents_size:           -1
% 2.79/1.07  bmc1_merge_next_fun:                    0
% 2.79/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.79/1.07  
% 2.79/1.07  ------ Instantiation
% 2.79/1.07  
% 2.79/1.07  inst_num_of_clauses:                    543
% 2.79/1.07  inst_num_in_passive:                    175
% 2.79/1.07  inst_num_in_active:                     321
% 2.79/1.07  inst_num_in_unprocessed:                47
% 2.79/1.07  inst_num_of_loops:                      350
% 2.79/1.07  inst_num_of_learning_restarts:          0
% 2.79/1.07  inst_num_moves_active_passive:          25
% 2.79/1.07  inst_lit_activity:                      0
% 2.79/1.07  inst_lit_activity_moves:                0
% 2.79/1.07  inst_num_tautologies:                   0
% 2.79/1.07  inst_num_prop_implied:                  0
% 2.79/1.07  inst_num_existing_simplified:           0
% 2.79/1.07  inst_num_eq_res_simplified:             0
% 2.79/1.07  inst_num_child_elim:                    0
% 2.79/1.07  inst_num_of_dismatching_blockings:      268
% 2.79/1.07  inst_num_of_non_proper_insts:           695
% 2.79/1.07  inst_num_of_duplicates:                 0
% 2.79/1.07  inst_inst_num_from_inst_to_res:         0
% 2.79/1.07  inst_dismatching_checking_time:         0.
% 2.79/1.07  
% 2.79/1.07  ------ Resolution
% 2.79/1.07  
% 2.79/1.07  res_num_of_clauses:                     0
% 2.79/1.07  res_num_in_passive:                     0
% 2.79/1.07  res_num_in_active:                      0
% 2.79/1.07  res_num_of_loops:                       70
% 2.79/1.07  res_forward_subset_subsumed:            93
% 2.79/1.07  res_backward_subset_subsumed:           0
% 2.79/1.07  res_forward_subsumed:                   0
% 2.79/1.07  res_backward_subsumed:                  0
% 2.79/1.07  res_forward_subsumption_resolution:     0
% 2.79/1.07  res_backward_subsumption_resolution:    0
% 2.79/1.07  res_clause_to_clause_subsumption:       244
% 2.79/1.07  res_orphan_elimination:                 0
% 2.79/1.07  res_tautology_del:                      108
% 2.79/1.07  res_num_eq_res_simplified:              0
% 2.79/1.07  res_num_sel_changes:                    0
% 2.79/1.07  res_moves_from_active_to_pass:          0
% 2.79/1.07  
% 2.79/1.07  ------ Superposition
% 2.79/1.07  
% 2.79/1.07  sup_time_total:                         0.
% 2.79/1.07  sup_time_generating:                    0.
% 2.79/1.07  sup_time_sim_full:                      0.
% 2.79/1.07  sup_time_sim_immed:                     0.
% 2.79/1.07  
% 2.79/1.07  sup_num_of_clauses:                     62
% 2.79/1.07  sup_num_in_active:                      35
% 2.79/1.07  sup_num_in_passive:                     27
% 2.79/1.07  sup_num_of_loops:                       69
% 2.79/1.07  sup_fw_superposition:                   61
% 2.79/1.07  sup_bw_superposition:                   89
% 2.79/1.07  sup_immediate_simplified:               45
% 2.79/1.07  sup_given_eliminated:                   1
% 2.79/1.07  comparisons_done:                       0
% 2.79/1.07  comparisons_avoided:                    10
% 2.79/1.07  
% 2.79/1.07  ------ Simplifications
% 2.79/1.07  
% 2.79/1.07  
% 2.79/1.07  sim_fw_subset_subsumed:                 16
% 2.79/1.07  sim_bw_subset_subsumed:                 13
% 2.79/1.07  sim_fw_subsumed:                        15
% 2.79/1.07  sim_bw_subsumed:                        1
% 2.79/1.07  sim_fw_subsumption_res:                 2
% 2.79/1.07  sim_bw_subsumption_res:                 0
% 2.79/1.07  sim_tautology_del:                      1
% 2.79/1.07  sim_eq_tautology_del:                   14
% 2.79/1.07  sim_eq_res_simp:                        3
% 2.79/1.07  sim_fw_demodulated:                     10
% 2.79/1.07  sim_bw_demodulated:                     31
% 2.79/1.07  sim_light_normalised:                   11
% 2.79/1.07  sim_joinable_taut:                      0
% 2.79/1.07  sim_joinable_simp:                      0
% 2.79/1.07  sim_ac_normalised:                      0
% 2.79/1.07  sim_smt_subsumption:                    0
% 2.79/1.07  
%------------------------------------------------------------------------------
