%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:33 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 556 expanded)
%              Number of clauses        :   64 ( 206 expanded)
%              Number of leaves         :   13 ( 125 expanded)
%              Depth                    :   24
%              Number of atoms          :  222 (1687 expanded)
%              Number of equality atoms :  106 ( 439 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2))
          & r1_tarski(sK2,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f39,f38])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f64,plain,(
    ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f53])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ) ),
    inference(definition_unfolding,[],[f44,f41])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1452,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1449,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1458,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2641,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1449,c_1458])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1456,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2186,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_1449,c_1456])).

cnf(c_2650,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2641,c_2186])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1448,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2642,plain,
    ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1448,c_1458])).

cnf(c_2187,plain,
    ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_1448,c_1456])).

cnf(c_2645,plain,
    ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2642,c_2187])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1451,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3503,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2645,c_1451])).

cnf(c_3677,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2650,c_3503])).

cnf(c_3832,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_3677])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3833,plain,
    ( ~ r1_tarski(sK2,sK3)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3832])).

cnf(c_4149,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3832,c_20,c_3833])).

cnf(c_4150,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4149])).

cnf(c_4162,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4150,c_1451])).

cnf(c_10,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1459,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1460,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1499,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1459,c_1460])).

cnf(c_4171,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4162,c_1499])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1619,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1620,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1619])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1820,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK1,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2081,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_1820])).

cnf(c_2082,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2081])).

cnf(c_4413,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4171,c_24,c_1620,c_2082])).

cnf(c_1450,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4428,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4413,c_1450])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1467,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1468,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2474,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_1468])).

cnf(c_4482,plain,
    ( r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4428,c_2474])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1466,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4558,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4482,c_1466])).

cnf(c_4426,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4413,c_1451])).

cnf(c_4433,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4426,c_1499])).

cnf(c_4651,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4558,c_4433])).

cnf(c_4666,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4651,c_1499])).

cnf(c_1457,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2438,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_1457])).

cnf(c_1609,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1612,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1609])).

cnf(c_4221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2438,c_1612])).

cnf(c_1454,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4226,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4221,c_1454])).

cnf(c_7421,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4666,c_4226])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.78/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.00  
% 2.78/1.00  ------  iProver source info
% 2.78/1.00  
% 2.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.00  git: non_committed_changes: false
% 2.78/1.00  git: last_make_outside_of_git: false
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     num_symb
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       true
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  ------ Parsing...
% 2.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.00  ------ Proving...
% 2.78/1.00  ------ Problem Properties 
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  clauses                                 21
% 2.78/1.00  conjectures                             4
% 2.78/1.00  EPR                                     3
% 2.78/1.00  Horn                                    18
% 2.78/1.00  unary                                   6
% 2.78/1.00  binary                                  9
% 2.78/1.00  lits                                    42
% 2.78/1.00  lits eq                                 8
% 2.78/1.00  fd_pure                                 0
% 2.78/1.00  fd_pseudo                               0
% 2.78/1.00  fd_cond                                 3
% 2.78/1.00  fd_pseudo_cond                          2
% 2.78/1.00  AC symbols                              0
% 2.78/1.00  
% 2.78/1.00  ------ Schedule dynamic 5 is on 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  Current options:
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.01  --sat_fm_restart_options                ""
% 2.78/1.01  --sat_gr_def                            false
% 2.78/1.01  --sat_epr_types                         true
% 2.78/1.01  --sat_non_cyclic_types                  false
% 2.78/1.01  --sat_finite_models                     false
% 2.78/1.01  --sat_fm_lemmas                         false
% 2.78/1.01  --sat_fm_prep                           false
% 2.78/1.01  --sat_fm_uc_incr                        true
% 2.78/1.01  --sat_out_model                         small
% 2.78/1.01  --sat_out_clauses                       false
% 2.78/1.01  
% 2.78/1.01  ------ QBF Options
% 2.78/1.01  
% 2.78/1.01  --qbf_mode                              false
% 2.78/1.01  --qbf_elim_univ                         false
% 2.78/1.01  --qbf_dom_inst                          none
% 2.78/1.01  --qbf_dom_pre_inst                      false
% 2.78/1.01  --qbf_sk_in                             false
% 2.78/1.01  --qbf_pred_elim                         true
% 2.78/1.01  --qbf_split                             512
% 2.78/1.01  
% 2.78/1.01  ------ BMC1 Options
% 2.78/1.01  
% 2.78/1.01  --bmc1_incremental                      false
% 2.78/1.01  --bmc1_axioms                           reachable_all
% 2.78/1.01  --bmc1_min_bound                        0
% 2.78/1.01  --bmc1_max_bound                        -1
% 2.78/1.01  --bmc1_max_bound_default                -1
% 2.78/1.01  --bmc1_symbol_reachability              true
% 2.78/1.01  --bmc1_property_lemmas                  false
% 2.78/1.01  --bmc1_k_induction                      false
% 2.78/1.01  --bmc1_non_equiv_states                 false
% 2.78/1.01  --bmc1_deadlock                         false
% 2.78/1.01  --bmc1_ucm                              false
% 2.78/1.01  --bmc1_add_unsat_core                   none
% 2.78/1.01  --bmc1_unsat_core_children              false
% 2.78/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.01  --bmc1_out_stat                         full
% 2.78/1.01  --bmc1_ground_init                      false
% 2.78/1.01  --bmc1_pre_inst_next_state              false
% 2.78/1.01  --bmc1_pre_inst_state                   false
% 2.78/1.01  --bmc1_pre_inst_reach_state             false
% 2.78/1.01  --bmc1_out_unsat_core                   false
% 2.78/1.01  --bmc1_aig_witness_out                  false
% 2.78/1.01  --bmc1_verbose                          false
% 2.78/1.01  --bmc1_dump_clauses_tptp                false
% 2.78/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.01  --bmc1_dump_file                        -
% 2.78/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.01  --bmc1_ucm_extend_mode                  1
% 2.78/1.01  --bmc1_ucm_init_mode                    2
% 2.78/1.01  --bmc1_ucm_cone_mode                    none
% 2.78/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.01  --bmc1_ucm_relax_model                  4
% 2.78/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.01  --bmc1_ucm_layered_model                none
% 2.78/1.01  --bmc1_ucm_max_lemma_size               10
% 2.78/1.01  
% 2.78/1.01  ------ AIG Options
% 2.78/1.01  
% 2.78/1.01  --aig_mode                              false
% 2.78/1.01  
% 2.78/1.01  ------ Instantiation Options
% 2.78/1.01  
% 2.78/1.01  --instantiation_flag                    true
% 2.78/1.01  --inst_sos_flag                         false
% 2.78/1.01  --inst_sos_phase                        true
% 2.78/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.01  --inst_lit_sel_side                     none
% 2.78/1.01  --inst_solver_per_active                1400
% 2.78/1.01  --inst_solver_calls_frac                1.
% 2.78/1.01  --inst_passive_queue_type               priority_queues
% 2.78/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.01  --inst_passive_queues_freq              [25;2]
% 2.78/1.01  --inst_dismatching                      true
% 2.78/1.01  --inst_eager_unprocessed_to_passive     true
% 2.78/1.01  --inst_prop_sim_given                   true
% 2.78/1.01  --inst_prop_sim_new                     false
% 2.78/1.01  --inst_subs_new                         false
% 2.78/1.01  --inst_eq_res_simp                      false
% 2.78/1.01  --inst_subs_given                       false
% 2.78/1.01  --inst_orphan_elimination               true
% 2.78/1.01  --inst_learning_loop_flag               true
% 2.78/1.01  --inst_learning_start                   3000
% 2.78/1.01  --inst_learning_factor                  2
% 2.78/1.01  --inst_start_prop_sim_after_learn       3
% 2.78/1.01  --inst_sel_renew                        solver
% 2.78/1.01  --inst_lit_activity_flag                true
% 2.78/1.01  --inst_restr_to_given                   false
% 2.78/1.01  --inst_activity_threshold               500
% 2.78/1.01  --inst_out_proof                        true
% 2.78/1.01  
% 2.78/1.01  ------ Resolution Options
% 2.78/1.01  
% 2.78/1.01  --resolution_flag                       false
% 2.78/1.01  --res_lit_sel                           adaptive
% 2.78/1.01  --res_lit_sel_side                      none
% 2.78/1.01  --res_ordering                          kbo
% 2.78/1.01  --res_to_prop_solver                    active
% 2.78/1.01  --res_prop_simpl_new                    false
% 2.78/1.01  --res_prop_simpl_given                  true
% 2.78/1.01  --res_passive_queue_type                priority_queues
% 2.78/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.01  --res_passive_queues_freq               [15;5]
% 2.78/1.01  --res_forward_subs                      full
% 2.78/1.01  --res_backward_subs                     full
% 2.78/1.01  --res_forward_subs_resolution           true
% 2.78/1.01  --res_backward_subs_resolution          true
% 2.78/1.01  --res_orphan_elimination                true
% 2.78/1.01  --res_time_limit                        2.
% 2.78/1.01  --res_out_proof                         true
% 2.78/1.01  
% 2.78/1.01  ------ Superposition Options
% 2.78/1.01  
% 2.78/1.01  --superposition_flag                    true
% 2.78/1.01  --sup_passive_queue_type                priority_queues
% 2.78/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.01  --demod_completeness_check              fast
% 2.78/1.01  --demod_use_ground                      true
% 2.78/1.01  --sup_to_prop_solver                    passive
% 2.78/1.01  --sup_prop_simpl_new                    true
% 2.78/1.01  --sup_prop_simpl_given                  true
% 2.78/1.01  --sup_fun_splitting                     false
% 2.78/1.01  --sup_smt_interval                      50000
% 2.78/1.01  
% 2.78/1.01  ------ Superposition Simplification Setup
% 2.78/1.01  
% 2.78/1.01  --sup_indices_passive                   []
% 2.78/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_full_bw                           [BwDemod]
% 2.78/1.01  --sup_immed_triv                        [TrivRules]
% 2.78/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_immed_bw_main                     []
% 2.78/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.01  
% 2.78/1.01  ------ Combination Options
% 2.78/1.01  
% 2.78/1.01  --comb_res_mult                         3
% 2.78/1.01  --comb_sup_mult                         2
% 2.78/1.01  --comb_inst_mult                        10
% 2.78/1.01  
% 2.78/1.01  ------ Debug Options
% 2.78/1.01  
% 2.78/1.01  --dbg_backtrace                         false
% 2.78/1.01  --dbg_dump_prop_clauses                 false
% 2.78/1.01  --dbg_dump_prop_clauses_file            -
% 2.78/1.01  --dbg_out_stat                          false
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  ------ Proving...
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  % SZS status Theorem for theBenchmark.p
% 2.78/1.01  
% 2.78/1.01   Resolution empty clause
% 2.78/1.01  
% 2.78/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.01  
% 2.78/1.01  fof(f15,axiom,(
% 2.78/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f29,plain,(
% 2.78/1.01    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.78/1.01    inference(ennf_transformation,[],[f15])).
% 2.78/1.01  
% 2.78/1.01  fof(f30,plain,(
% 2.78/1.01    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.78/1.01    inference(flattening,[],[f29])).
% 2.78/1.01  
% 2.78/1.01  fof(f60,plain,(
% 2.78/1.01    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f30])).
% 2.78/1.01  
% 2.78/1.01  fof(f16,conjecture,(
% 2.78/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f17,negated_conjecture,(
% 2.78/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.78/1.01    inference(negated_conjecture,[],[f16])).
% 2.78/1.01  
% 2.78/1.01  fof(f31,plain,(
% 2.78/1.01    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/1.01    inference(ennf_transformation,[],[f17])).
% 2.78/1.01  
% 2.78/1.01  fof(f32,plain,(
% 2.78/1.01    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/1.01    inference(flattening,[],[f31])).
% 2.78/1.01  
% 2.78/1.01  fof(f39,plain,(
% 2.78/1.01    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.78/1.01    introduced(choice_axiom,[])).
% 2.78/1.01  
% 2.78/1.01  fof(f38,plain,(
% 2.78/1.01    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 2.78/1.01    introduced(choice_axiom,[])).
% 2.78/1.01  
% 2.78/1.01  fof(f40,plain,(
% 2.78/1.01    (~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.78/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f39,f38])).
% 2.78/1.01  
% 2.78/1.01  fof(f62,plain,(
% 2.78/1.01    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f9,axiom,(
% 2.78/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f22,plain,(
% 2.78/1.01    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/1.01    inference(ennf_transformation,[],[f9])).
% 2.78/1.01  
% 2.78/1.01  fof(f52,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f22])).
% 2.78/1.01  
% 2.78/1.01  fof(f11,axiom,(
% 2.78/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f24,plain,(
% 2.78/1.01    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/1.01    inference(ennf_transformation,[],[f11])).
% 2.78/1.01  
% 2.78/1.01  fof(f55,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f24])).
% 2.78/1.01  
% 2.78/1.01  fof(f61,plain,(
% 2.78/1.01    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f64,plain,(
% 2.78/1.01    ~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f63,plain,(
% 2.78/1.01    r1_tarski(sK2,sK3)),
% 2.78/1.01    inference(cnf_transformation,[],[f40])).
% 2.78/1.01  
% 2.78/1.01  fof(f53,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f22])).
% 2.78/1.01  
% 2.78/1.01  fof(f68,plain,(
% 2.78/1.01    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/1.01    inference(equality_resolution,[],[f53])).
% 2.78/1.01  
% 2.78/1.01  fof(f8,axiom,(
% 2.78/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f51,plain,(
% 2.78/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f8])).
% 2.78/1.01  
% 2.78/1.01  fof(f10,axiom,(
% 2.78/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f23,plain,(
% 2.78/1.01    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.78/1.01    inference(ennf_transformation,[],[f10])).
% 2.78/1.01  
% 2.78/1.01  fof(f54,plain,(
% 2.78/1.01    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f23])).
% 2.78/1.01  
% 2.78/1.01  fof(f13,axiom,(
% 2.78/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f37,plain,(
% 2.78/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.78/1.01    inference(nnf_transformation,[],[f13])).
% 2.78/1.01  
% 2.78/1.01  fof(f57,plain,(
% 2.78/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f37])).
% 2.78/1.01  
% 2.78/1.01  fof(f3,axiom,(
% 2.78/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f43,plain,(
% 2.78/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f3])).
% 2.78/1.01  
% 2.78/1.01  fof(f2,axiom,(
% 2.78/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f18,plain,(
% 2.78/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.78/1.01    inference(ennf_transformation,[],[f2])).
% 2.78/1.01  
% 2.78/1.01  fof(f19,plain,(
% 2.78/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.78/1.01    inference(flattening,[],[f18])).
% 2.78/1.01  
% 2.78/1.01  fof(f42,plain,(
% 2.78/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.78/1.01    inference(cnf_transformation,[],[f19])).
% 2.78/1.01  
% 2.78/1.01  fof(f4,axiom,(
% 2.78/1.01    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f20,plain,(
% 2.78/1.01    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 2.78/1.01    inference(ennf_transformation,[],[f4])).
% 2.78/1.01  
% 2.78/1.01  fof(f44,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f20])).
% 2.78/1.01  
% 2.78/1.01  fof(f1,axiom,(
% 2.78/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.78/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.01  
% 2.78/1.01  fof(f41,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.78/1.01    inference(cnf_transformation,[],[f1])).
% 2.78/1.01  
% 2.78/1.01  fof(f65,plain,(
% 2.78/1.01    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.78/1.01    inference(definition_unfolding,[],[f44,f41])).
% 2.78/1.01  
% 2.78/1.01  cnf(c_18,plain,
% 2.78/1.01      ( ~ r1_tarski(X0,X1)
% 2.78/1.01      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.78/1.01      | k1_xboole_0 = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1452,plain,
% 2.78/1.01      ( k1_xboole_0 = X0
% 2.78/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.78/1.01      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_21,negated_conjecture,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.78/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1449,plain,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_11,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.78/1.01      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.78/1.01      | k1_xboole_0 = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1458,plain,
% 2.78/1.01      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.78/1.01      | k1_xboole_0 = X1
% 2.78/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2641,plain,
% 2.78/1.01      ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3) | sK3 = k1_xboole_0 ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1449,c_1458]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_13,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.78/1.01      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1456,plain,
% 2.78/1.01      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.78/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2186,plain,
% 2.78/1.01      ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1449,c_1456]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2650,plain,
% 2.78/1.01      ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.78/1.01      inference(light_normalisation,[status(thm)],[c_2641,c_2186]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_22,negated_conjecture,
% 2.78/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.78/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1448,plain,
% 2.78/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2642,plain,
% 2.78/1.01      ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) | sK2 = k1_xboole_0 ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1448,c_1458]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2187,plain,
% 2.78/1.01      ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1448,c_1456]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2645,plain,
% 2.78/1.01      ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.78/1.01      inference(light_normalisation,[status(thm)],[c_2642,c_2187]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_19,negated_conjecture,
% 2.78/1.01      ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1451,plain,
% 2.78/1.01      ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3503,plain,
% 2.78/1.01      ( sK2 = k1_xboole_0
% 2.78/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_2645,c_1451]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3677,plain,
% 2.78/1.01      ( sK2 = k1_xboole_0
% 2.78/1.01      | sK3 = k1_xboole_0
% 2.78/1.01      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_2650,c_3503]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3832,plain,
% 2.78/1.01      ( sK2 = k1_xboole_0
% 2.78/1.01      | sK3 = k1_xboole_0
% 2.78/1.01      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1452,c_3677]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_20,negated_conjecture,
% 2.78/1.01      ( r1_tarski(sK2,sK3) ),
% 2.78/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3833,plain,
% 2.78/1.01      ( ~ r1_tarski(sK2,sK3) | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.78/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3832]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4149,plain,
% 2.78/1.01      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_3832,c_20,c_3833]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4150,plain,
% 2.78/1.01      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.78/1.01      inference(renaming,[status(thm)],[c_4149]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4162,plain,
% 2.78/1.01      ( sK3 = k1_xboole_0
% 2.78/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4150,c_1451]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_10,plain,
% 2.78/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.78/1.01      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1459,plain,
% 2.78/1.01      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.78/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_9,plain,
% 2.78/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1460,plain,
% 2.78/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1499,plain,
% 2.78/1.01      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.78/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_1459,c_1460]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4171,plain,
% 2.78/1.01      ( sK3 = k1_xboole_0
% 2.78/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_4162,c_1499]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_24,plain,
% 2.78/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_12,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.78/1.01      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1619,plain,
% 2.78/1.01      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
% 2.78/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1620,plain,
% 2.78/1.01      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 2.78/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_1619]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_16,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.78/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1820,plain,
% 2.78/1.01      ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(X0))
% 2.78/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),X0) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2081,plain,
% 2.78/1.01      ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
% 2.78/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_1820]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2082,plain,
% 2.78/1.01      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 2.78/1.01      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2081]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4413,plain,
% 2.78/1.01      ( sK3 = k1_xboole_0 ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_4171,c_24,c_1620,c_2082]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1450,plain,
% 2.78/1.01      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4428,plain,
% 2.78/1.01      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_4413,c_1450]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1,plain,
% 2.78/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1467,plain,
% 2.78/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_0,plain,
% 2.78/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 2.78/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1468,plain,
% 2.78/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.78/1.01      | r1_tarski(X2,X0) != iProver_top
% 2.78/1.01      | r1_tarski(X2,X1) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2474,plain,
% 2.78/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.78/1.01      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1467,c_1468]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4482,plain,
% 2.78/1.01      ( r1_tarski(sK2,X0) = iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4428,c_2474]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2,plain,
% 2.78/1.01      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) | k1_xboole_0 = X0 ),
% 2.78/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1466,plain,
% 2.78/1.01      ( k1_xboole_0 = X0
% 2.78/1.01      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4558,plain,
% 2.78/1.01      ( sK2 = k1_xboole_0 ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4482,c_1466]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4426,plain,
% 2.78/1.01      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_4413,c_1451]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4433,plain,
% 2.78/1.01      ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_4426,c_1499]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4651,plain,
% 2.78/1.01      ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_4558,c_4433]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4666,plain,
% 2.78/1.01      ( r1_tarski(sK1,sK1) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_4651,c_1499]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1457,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.78/1.01      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2438,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 2.78/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1499,c_1457]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1609,plain,
% 2.78/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1612,plain,
% 2.78/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_1609]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4221,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.78/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2438,c_1612]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1454,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.78/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4226,plain,
% 2.78/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4221,c_1454]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_7421,plain,
% 2.78/1.01      ( $false ),
% 2.78/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4666,c_4226]) ).
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.01  
% 2.78/1.01  ------                               Statistics
% 2.78/1.01  
% 2.78/1.01  ------ General
% 2.78/1.01  
% 2.78/1.01  abstr_ref_over_cycles:                  0
% 2.78/1.01  abstr_ref_under_cycles:                 0
% 2.78/1.01  gc_basic_clause_elim:                   0
% 2.78/1.01  forced_gc_time:                         0
% 2.78/1.01  parsing_time:                           0.008
% 2.78/1.01  unif_index_cands_time:                  0.
% 2.78/1.01  unif_index_add_time:                    0.
% 2.78/1.01  orderings_time:                         0.
% 2.78/1.01  out_proof_time:                         0.009
% 2.78/1.01  total_time:                             0.2
% 2.78/1.01  num_of_symbols:                         46
% 2.78/1.01  num_of_terms:                           4866
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing
% 2.78/1.01  
% 2.78/1.01  num_of_splits:                          0
% 2.78/1.01  num_of_split_atoms:                     0
% 2.78/1.01  num_of_reused_defs:                     0
% 2.78/1.01  num_eq_ax_congr_red:                    32
% 2.78/1.01  num_of_sem_filtered_clauses:            1
% 2.78/1.01  num_of_subtypes:                        0
% 2.78/1.01  monotx_restored_types:                  0
% 2.78/1.01  sat_num_of_epr_types:                   0
% 2.78/1.01  sat_num_of_non_cyclic_types:            0
% 2.78/1.01  sat_guarded_non_collapsed_types:        0
% 2.78/1.01  num_pure_diseq_elim:                    0
% 2.78/1.01  simp_replaced_by:                       0
% 2.78/1.01  res_preprocessed:                       124
% 2.78/1.01  prep_upred:                             0
% 2.78/1.01  prep_unflattend:                        29
% 2.78/1.01  smt_new_axioms:                         0
% 2.78/1.01  pred_elim_cands:                        3
% 2.78/1.01  pred_elim:                              1
% 2.78/1.01  pred_elim_cl:                           1
% 2.78/1.01  pred_elim_cycles:                       4
% 2.78/1.01  merged_defs:                            20
% 2.78/1.01  merged_defs_ncl:                        0
% 2.78/1.01  bin_hyper_res:                          21
% 2.78/1.01  prep_cycles:                            5
% 2.78/1.01  pred_elim_time:                         0.005
% 2.78/1.01  splitting_time:                         0.
% 2.78/1.01  sem_filter_time:                        0.
% 2.78/1.01  monotx_time:                            0.
% 2.78/1.01  subtype_inf_time:                       0.
% 2.78/1.01  
% 2.78/1.01  ------ Problem properties
% 2.78/1.01  
% 2.78/1.01  clauses:                                21
% 2.78/1.01  conjectures:                            4
% 2.78/1.01  epr:                                    3
% 2.78/1.01  horn:                                   18
% 2.78/1.01  ground:                                 4
% 2.78/1.01  unary:                                  6
% 2.78/1.01  binary:                                 9
% 2.78/1.01  lits:                                   42
% 2.78/1.01  lits_eq:                                8
% 2.78/1.01  fd_pure:                                0
% 2.78/1.01  fd_pseudo:                              0
% 2.78/1.01  fd_cond:                                3
% 2.78/1.01  fd_pseudo_cond:                         2
% 2.78/1.01  ac_symbols:                             0
% 2.78/1.01  
% 2.78/1.01  ------ Propositional Solver
% 2.78/1.01  
% 2.78/1.01  prop_solver_calls:                      34
% 2.78/1.01  prop_fast_solver_calls:                 817
% 2.78/1.01  smt_solver_calls:                       0
% 2.78/1.01  smt_fast_solver_calls:                  0
% 2.78/1.01  prop_num_of_clauses:                    2299
% 2.78/1.01  prop_preprocess_simplified:             6592
% 2.78/1.01  prop_fo_subsumed:                       7
% 2.78/1.01  prop_solver_time:                       0.
% 2.78/1.01  smt_solver_time:                        0.
% 2.78/1.01  smt_fast_solver_time:                   0.
% 2.78/1.01  prop_fast_solver_time:                  0.
% 2.78/1.01  prop_unsat_core_time:                   0.
% 2.78/1.01  
% 2.78/1.01  ------ QBF
% 2.78/1.01  
% 2.78/1.01  qbf_q_res:                              0
% 2.78/1.01  qbf_num_tautologies:                    0
% 2.78/1.01  qbf_prep_cycles:                        0
% 2.78/1.01  
% 2.78/1.01  ------ BMC1
% 2.78/1.01  
% 2.78/1.01  bmc1_current_bound:                     -1
% 2.78/1.01  bmc1_last_solved_bound:                 -1
% 2.78/1.01  bmc1_unsat_core_size:                   -1
% 2.78/1.01  bmc1_unsat_core_parents_size:           -1
% 2.78/1.01  bmc1_merge_next_fun:                    0
% 2.78/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.01  
% 2.78/1.01  ------ Instantiation
% 2.78/1.01  
% 2.78/1.01  inst_num_of_clauses:                    608
% 2.78/1.01  inst_num_in_passive:                    260
% 2.78/1.01  inst_num_in_active:                     330
% 2.78/1.01  inst_num_in_unprocessed:                18
% 2.78/1.01  inst_num_of_loops:                      420
% 2.78/1.01  inst_num_of_learning_restarts:          0
% 2.78/1.01  inst_num_moves_active_passive:          86
% 2.78/1.01  inst_lit_activity:                      0
% 2.78/1.01  inst_lit_activity_moves:                0
% 2.78/1.01  inst_num_tautologies:                   0
% 2.78/1.01  inst_num_prop_implied:                  0
% 2.78/1.01  inst_num_existing_simplified:           0
% 2.78/1.01  inst_num_eq_res_simplified:             0
% 2.78/1.01  inst_num_child_elim:                    0
% 2.78/1.01  inst_num_of_dismatching_blockings:      260
% 2.78/1.01  inst_num_of_non_proper_insts:           768
% 2.78/1.01  inst_num_of_duplicates:                 0
% 2.78/1.01  inst_inst_num_from_inst_to_res:         0
% 2.78/1.01  inst_dismatching_checking_time:         0.
% 2.78/1.01  
% 2.78/1.01  ------ Resolution
% 2.78/1.01  
% 2.78/1.01  res_num_of_clauses:                     0
% 2.78/1.01  res_num_in_passive:                     0
% 2.78/1.01  res_num_in_active:                      0
% 2.78/1.01  res_num_of_loops:                       129
% 2.78/1.01  res_forward_subset_subsumed:            111
% 2.78/1.01  res_backward_subset_subsumed:           0
% 2.78/1.01  res_forward_subsumed:                   0
% 2.78/1.01  res_backward_subsumed:                  0
% 2.78/1.01  res_forward_subsumption_resolution:     0
% 2.78/1.01  res_backward_subsumption_resolution:    0
% 2.78/1.01  res_clause_to_clause_subsumption:       870
% 2.78/1.01  res_orphan_elimination:                 0
% 2.78/1.01  res_tautology_del:                      105
% 2.78/1.01  res_num_eq_res_simplified:              0
% 2.78/1.01  res_num_sel_changes:                    0
% 2.78/1.01  res_moves_from_active_to_pass:          0
% 2.78/1.01  
% 2.78/1.01  ------ Superposition
% 2.78/1.01  
% 2.78/1.01  sup_time_total:                         0.
% 2.78/1.01  sup_time_generating:                    0.
% 2.78/1.01  sup_time_sim_full:                      0.
% 2.78/1.01  sup_time_sim_immed:                     0.
% 2.78/1.01  
% 2.78/1.01  sup_num_of_clauses:                     189
% 2.78/1.01  sup_num_in_active:                      54
% 2.78/1.01  sup_num_in_passive:                     135
% 2.78/1.01  sup_num_of_loops:                       83
% 2.78/1.01  sup_fw_superposition:                   116
% 2.78/1.01  sup_bw_superposition:                   147
% 2.78/1.01  sup_immediate_simplified:               41
% 2.78/1.01  sup_given_eliminated:                   2
% 2.78/1.01  comparisons_done:                       0
% 2.78/1.01  comparisons_avoided:                    11
% 2.78/1.01  
% 2.78/1.01  ------ Simplifications
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  sim_fw_subset_subsumed:                 7
% 2.78/1.01  sim_bw_subset_subsumed:                 8
% 2.78/1.01  sim_fw_subsumed:                        23
% 2.78/1.01  sim_bw_subsumed:                        2
% 2.78/1.01  sim_fw_subsumption_res:                 4
% 2.78/1.01  sim_bw_subsumption_res:                 0
% 2.78/1.01  sim_tautology_del:                      3
% 2.78/1.01  sim_eq_tautology_del:                   9
% 2.78/1.01  sim_eq_res_simp:                        0
% 2.78/1.01  sim_fw_demodulated:                     8
% 2.78/1.01  sim_bw_demodulated:                     26
% 2.78/1.01  sim_light_normalised:                   23
% 2.78/1.01  sim_joinable_taut:                      0
% 2.78/1.01  sim_joinable_simp:                      0
% 2.78/1.01  sim_ac_normalised:                      0
% 2.78/1.01  sim_smt_subsumption:                    0
% 2.78/1.01  
%------------------------------------------------------------------------------
