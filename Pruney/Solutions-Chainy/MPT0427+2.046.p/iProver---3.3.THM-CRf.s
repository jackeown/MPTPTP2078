%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:35 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  131 (1847 expanded)
%              Number of clauses        :   77 ( 675 expanded)
%              Number of leaves         :   19 ( 443 expanded)
%              Depth                    :   26
%              Number of atoms          :  287 (5966 expanded)
%              Number of equality atoms :  155 (1563 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
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

fof(f33,plain,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f32,f31])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f38,f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f40,f52])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_692,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_689,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_697,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2090,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_689,c_697])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_695,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1246,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_689,c_695])).

cnf(c_2099,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2090,c_1246])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_688,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2091,plain,
    ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_688,c_697])).

cnf(c_1247,plain,
    ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
    inference(superposition,[status(thm)],[c_688,c_695])).

cnf(c_2094,plain,
    ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2091,c_1247])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_691,plain,
    ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2356,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2094,c_691])).

cnf(c_2468,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2099,c_2356])).

cnf(c_2591,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_2468])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2592,plain,
    ( ~ r1_tarski(sK2,sK3)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2591])).

cnf(c_2681,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_13,c_2592])).

cnf(c_2682,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2681])).

cnf(c_2694,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_691])).

cnf(c_2695,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_688])).

cnf(c_17,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_348,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_365,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_349,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_981,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_982,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_825,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | X1 != k1_zfmisc_1(k1_zfmisc_1(sK1))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_1220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | X0 != sK3
    | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_825])).

cnf(c_1222,plain,
    ( X0 != sK3
    | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1220])).

cnf(c_1224,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
    | k1_xboole_0 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1222])).

cnf(c_1221,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(sK1)) = k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_2794,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2695,c_17,c_365,c_982,c_1224,c_1221])).

cnf(c_5,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_698,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2799,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_2794,c_698])).

cnf(c_3020,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2694,c_2799])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_796,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_797,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_874,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_875,plain,
    ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_874])).

cnf(c_3024,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3020,c_17,c_797,c_875])).

cnf(c_690,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3036,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3024,c_690])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_204,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | X1 != X2
    | sK0(X2) != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_205,plain,
    ( r1_tarski(k1_tarski(sK0(X0)),X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_687,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(k1_tarski(sK0(X0)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_699,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2046,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tarski(sK0(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_687,c_699])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_700,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4482,plain,
    ( k5_xboole_0(k1_tarski(sK0(X0)),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(sK0(X0))))) = X1
    | k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2046,c_700])).

cnf(c_9323,plain,
    ( k5_xboole_0(k1_tarski(sK0(sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_tarski(sK0(sK2))))) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3036,c_4482])).

cnf(c_4,plain,
    ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X0)))) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10130,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9323,c_4])).

cnf(c_3034,plain,
    ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3024,c_691])).

cnf(c_3040,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3034,c_2799])).

cnf(c_10164,plain,
    ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10130,c_3040])).

cnf(c_10175,plain,
    ( r1_tarski(sK1,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10164,c_2799])).

cnf(c_696,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2882,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2799,c_696])).

cnf(c_3416,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2882,c_17,c_365,c_982,c_1224,c_1221,c_2695])).

cnf(c_693,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3421,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3416,c_693])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10175,c_3421])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.43/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/0.97  
% 2.43/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/0.97  
% 2.43/0.97  ------  iProver source info
% 2.43/0.97  
% 2.43/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.43/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/0.97  git: non_committed_changes: false
% 2.43/0.97  git: last_make_outside_of_git: false
% 2.43/0.97  
% 2.43/0.97  ------ 
% 2.43/0.97  
% 2.43/0.97  ------ Input Options
% 2.43/0.97  
% 2.43/0.97  --out_options                           all
% 2.43/0.97  --tptp_safe_out                         true
% 2.43/0.97  --problem_path                          ""
% 2.43/0.97  --include_path                          ""
% 2.43/0.97  --clausifier                            res/vclausify_rel
% 2.43/0.97  --clausifier_options                    --mode clausify
% 2.43/0.97  --stdin                                 false
% 2.43/0.97  --stats_out                             all
% 2.43/0.97  
% 2.43/0.97  ------ General Options
% 2.43/0.97  
% 2.43/0.97  --fof                                   false
% 2.43/0.97  --time_out_real                         305.
% 2.43/0.97  --time_out_virtual                      -1.
% 2.43/0.97  --symbol_type_check                     false
% 2.43/0.97  --clausify_out                          false
% 2.43/0.97  --sig_cnt_out                           false
% 2.43/0.97  --trig_cnt_out                          false
% 2.43/0.97  --trig_cnt_out_tolerance                1.
% 2.43/0.97  --trig_cnt_out_sk_spl                   false
% 2.43/0.97  --abstr_cl_out                          false
% 2.43/0.97  
% 2.43/0.97  ------ Global Options
% 2.43/0.97  
% 2.43/0.97  --schedule                              default
% 2.43/0.97  --add_important_lit                     false
% 2.43/0.97  --prop_solver_per_cl                    1000
% 2.43/0.97  --min_unsat_core                        false
% 2.43/0.97  --soft_assumptions                      false
% 2.43/0.97  --soft_lemma_size                       3
% 2.43/0.97  --prop_impl_unit_size                   0
% 2.43/0.97  --prop_impl_unit                        []
% 2.43/0.97  --share_sel_clauses                     true
% 2.43/0.97  --reset_solvers                         false
% 2.43/0.97  --bc_imp_inh                            [conj_cone]
% 2.43/0.97  --conj_cone_tolerance                   3.
% 2.43/0.97  --extra_neg_conj                        none
% 2.43/0.97  --large_theory_mode                     true
% 2.43/0.97  --prolific_symb_bound                   200
% 2.43/0.97  --lt_threshold                          2000
% 2.43/0.97  --clause_weak_htbl                      true
% 2.43/0.97  --gc_record_bc_elim                     false
% 2.43/0.97  
% 2.43/0.97  ------ Preprocessing Options
% 2.43/0.97  
% 2.43/0.97  --preprocessing_flag                    true
% 2.43/0.97  --time_out_prep_mult                    0.1
% 2.43/0.97  --splitting_mode                        input
% 2.43/0.97  --splitting_grd                         true
% 2.43/0.97  --splitting_cvd                         false
% 2.43/0.97  --splitting_cvd_svl                     false
% 2.43/0.97  --splitting_nvd                         32
% 2.43/0.97  --sub_typing                            true
% 2.43/0.97  --prep_gs_sim                           true
% 2.43/0.97  --prep_unflatten                        true
% 2.43/0.97  --prep_res_sim                          true
% 2.43/0.97  --prep_upred                            true
% 2.43/0.97  --prep_sem_filter                       exhaustive
% 2.43/0.97  --prep_sem_filter_out                   false
% 2.43/0.97  --pred_elim                             true
% 2.43/0.97  --res_sim_input                         true
% 2.43/0.97  --eq_ax_congr_red                       true
% 2.43/0.97  --pure_diseq_elim                       true
% 2.43/0.97  --brand_transform                       false
% 2.43/0.97  --non_eq_to_eq                          false
% 2.43/0.97  --prep_def_merge                        true
% 2.43/0.97  --prep_def_merge_prop_impl              false
% 2.43/0.98  --prep_def_merge_mbd                    true
% 2.43/0.98  --prep_def_merge_tr_red                 false
% 2.43/0.98  --prep_def_merge_tr_cl                  false
% 2.43/0.98  --smt_preprocessing                     true
% 2.43/0.98  --smt_ac_axioms                         fast
% 2.43/0.98  --preprocessed_out                      false
% 2.43/0.98  --preprocessed_stats                    false
% 2.43/0.98  
% 2.43/0.98  ------ Abstraction refinement Options
% 2.43/0.98  
% 2.43/0.98  --abstr_ref                             []
% 2.43/0.98  --abstr_ref_prep                        false
% 2.43/0.98  --abstr_ref_until_sat                   false
% 2.43/0.98  --abstr_ref_sig_restrict                funpre
% 2.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.98  --abstr_ref_under                       []
% 2.43/0.98  
% 2.43/0.98  ------ SAT Options
% 2.43/0.98  
% 2.43/0.98  --sat_mode                              false
% 2.43/0.98  --sat_fm_restart_options                ""
% 2.43/0.98  --sat_gr_def                            false
% 2.43/0.98  --sat_epr_types                         true
% 2.43/0.98  --sat_non_cyclic_types                  false
% 2.43/0.98  --sat_finite_models                     false
% 2.43/0.98  --sat_fm_lemmas                         false
% 2.43/0.98  --sat_fm_prep                           false
% 2.43/0.98  --sat_fm_uc_incr                        true
% 2.43/0.98  --sat_out_model                         small
% 2.43/0.98  --sat_out_clauses                       false
% 2.43/0.98  
% 2.43/0.98  ------ QBF Options
% 2.43/0.98  
% 2.43/0.98  --qbf_mode                              false
% 2.43/0.98  --qbf_elim_univ                         false
% 2.43/0.98  --qbf_dom_inst                          none
% 2.43/0.98  --qbf_dom_pre_inst                      false
% 2.43/0.98  --qbf_sk_in                             false
% 2.43/0.98  --qbf_pred_elim                         true
% 2.43/0.98  --qbf_split                             512
% 2.43/0.98  
% 2.43/0.98  ------ BMC1 Options
% 2.43/0.98  
% 2.43/0.98  --bmc1_incremental                      false
% 2.43/0.98  --bmc1_axioms                           reachable_all
% 2.43/0.98  --bmc1_min_bound                        0
% 2.43/0.98  --bmc1_max_bound                        -1
% 2.43/0.98  --bmc1_max_bound_default                -1
% 2.43/0.98  --bmc1_symbol_reachability              true
% 2.43/0.98  --bmc1_property_lemmas                  false
% 2.43/0.98  --bmc1_k_induction                      false
% 2.43/0.98  --bmc1_non_equiv_states                 false
% 2.43/0.98  --bmc1_deadlock                         false
% 2.43/0.98  --bmc1_ucm                              false
% 2.43/0.98  --bmc1_add_unsat_core                   none
% 2.43/0.98  --bmc1_unsat_core_children              false
% 2.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.98  --bmc1_out_stat                         full
% 2.43/0.98  --bmc1_ground_init                      false
% 2.43/0.98  --bmc1_pre_inst_next_state              false
% 2.43/0.98  --bmc1_pre_inst_state                   false
% 2.43/0.98  --bmc1_pre_inst_reach_state             false
% 2.43/0.98  --bmc1_out_unsat_core                   false
% 2.43/0.98  --bmc1_aig_witness_out                  false
% 2.43/0.98  --bmc1_verbose                          false
% 2.43/0.98  --bmc1_dump_clauses_tptp                false
% 2.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.98  --bmc1_dump_file                        -
% 2.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.98  --bmc1_ucm_extend_mode                  1
% 2.43/0.98  --bmc1_ucm_init_mode                    2
% 2.43/0.98  --bmc1_ucm_cone_mode                    none
% 2.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.98  --bmc1_ucm_relax_model                  4
% 2.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.98  --bmc1_ucm_layered_model                none
% 2.43/0.98  --bmc1_ucm_max_lemma_size               10
% 2.43/0.98  
% 2.43/0.98  ------ AIG Options
% 2.43/0.98  
% 2.43/0.98  --aig_mode                              false
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation Options
% 2.43/0.98  
% 2.43/0.98  --instantiation_flag                    true
% 2.43/0.98  --inst_sos_flag                         false
% 2.43/0.98  --inst_sos_phase                        true
% 2.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel_side                     num_symb
% 2.43/0.98  --inst_solver_per_active                1400
% 2.43/0.98  --inst_solver_calls_frac                1.
% 2.43/0.98  --inst_passive_queue_type               priority_queues
% 2.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.98  --inst_passive_queues_freq              [25;2]
% 2.43/0.98  --inst_dismatching                      true
% 2.43/0.98  --inst_eager_unprocessed_to_passive     true
% 2.43/0.98  --inst_prop_sim_given                   true
% 2.43/0.98  --inst_prop_sim_new                     false
% 2.43/0.98  --inst_subs_new                         false
% 2.43/0.98  --inst_eq_res_simp                      false
% 2.43/0.98  --inst_subs_given                       false
% 2.43/0.98  --inst_orphan_elimination               true
% 2.43/0.98  --inst_learning_loop_flag               true
% 2.43/0.98  --inst_learning_start                   3000
% 2.43/0.98  --inst_learning_factor                  2
% 2.43/0.98  --inst_start_prop_sim_after_learn       3
% 2.43/0.98  --inst_sel_renew                        solver
% 2.43/0.98  --inst_lit_activity_flag                true
% 2.43/0.98  --inst_restr_to_given                   false
% 2.43/0.98  --inst_activity_threshold               500
% 2.43/0.98  --inst_out_proof                        true
% 2.43/0.98  
% 2.43/0.98  ------ Resolution Options
% 2.43/0.98  
% 2.43/0.98  --resolution_flag                       true
% 2.43/0.98  --res_lit_sel                           adaptive
% 2.43/0.98  --res_lit_sel_side                      none
% 2.43/0.98  --res_ordering                          kbo
% 2.43/0.98  --res_to_prop_solver                    active
% 2.43/0.98  --res_prop_simpl_new                    false
% 2.43/0.98  --res_prop_simpl_given                  true
% 2.43/0.98  --res_passive_queue_type                priority_queues
% 2.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.98  --res_passive_queues_freq               [15;5]
% 2.43/0.98  --res_forward_subs                      full
% 2.43/0.98  --res_backward_subs                     full
% 2.43/0.98  --res_forward_subs_resolution           true
% 2.43/0.98  --res_backward_subs_resolution          true
% 2.43/0.98  --res_orphan_elimination                true
% 2.43/0.98  --res_time_limit                        2.
% 2.43/0.98  --res_out_proof                         true
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Options
% 2.43/0.98  
% 2.43/0.98  --superposition_flag                    true
% 2.43/0.98  --sup_passive_queue_type                priority_queues
% 2.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.98  --demod_completeness_check              fast
% 2.43/0.98  --demod_use_ground                      true
% 2.43/0.98  --sup_to_prop_solver                    passive
% 2.43/0.98  --sup_prop_simpl_new                    true
% 2.43/0.98  --sup_prop_simpl_given                  true
% 2.43/0.98  --sup_fun_splitting                     false
% 2.43/0.98  --sup_smt_interval                      50000
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Simplification Setup
% 2.43/0.98  
% 2.43/0.98  --sup_indices_passive                   []
% 2.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_full_bw                           [BwDemod]
% 2.43/0.98  --sup_immed_triv                        [TrivRules]
% 2.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_immed_bw_main                     []
% 2.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  
% 2.43/0.98  ------ Combination Options
% 2.43/0.98  
% 2.43/0.98  --comb_res_mult                         3
% 2.43/0.98  --comb_sup_mult                         2
% 2.43/0.98  --comb_inst_mult                        10
% 2.43/0.98  
% 2.43/0.98  ------ Debug Options
% 2.43/0.98  
% 2.43/0.98  --dbg_backtrace                         false
% 2.43/0.98  --dbg_dump_prop_clauses                 false
% 2.43/0.98  --dbg_dump_prop_clauses_file            -
% 2.43/0.98  --dbg_out_stat                          false
% 2.43/0.98  ------ Parsing...
% 2.43/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/0.98  ------ Proving...
% 2.43/0.98  ------ Problem Properties 
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  clauses                                 15
% 2.43/0.98  conjectures                             4
% 2.43/0.98  EPR                                     2
% 2.43/0.98  Horn                                    12
% 2.43/0.98  unary                                   5
% 2.43/0.98  binary                                  7
% 2.43/0.98  lits                                    28
% 2.43/0.98  lits eq                                 8
% 2.43/0.98  fd_pure                                 0
% 2.43/0.98  fd_pseudo                               0
% 2.43/0.98  fd_cond                                 3
% 2.43/0.98  fd_pseudo_cond                          0
% 2.43/0.98  AC symbols                              0
% 2.43/0.98  
% 2.43/0.98  ------ Schedule dynamic 5 is on 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  ------ 
% 2.43/0.98  Current options:
% 2.43/0.98  ------ 
% 2.43/0.98  
% 2.43/0.98  ------ Input Options
% 2.43/0.98  
% 2.43/0.98  --out_options                           all
% 2.43/0.98  --tptp_safe_out                         true
% 2.43/0.98  --problem_path                          ""
% 2.43/0.98  --include_path                          ""
% 2.43/0.98  --clausifier                            res/vclausify_rel
% 2.43/0.98  --clausifier_options                    --mode clausify
% 2.43/0.98  --stdin                                 false
% 2.43/0.98  --stats_out                             all
% 2.43/0.98  
% 2.43/0.98  ------ General Options
% 2.43/0.98  
% 2.43/0.98  --fof                                   false
% 2.43/0.98  --time_out_real                         305.
% 2.43/0.98  --time_out_virtual                      -1.
% 2.43/0.98  --symbol_type_check                     false
% 2.43/0.98  --clausify_out                          false
% 2.43/0.98  --sig_cnt_out                           false
% 2.43/0.98  --trig_cnt_out                          false
% 2.43/0.98  --trig_cnt_out_tolerance                1.
% 2.43/0.98  --trig_cnt_out_sk_spl                   false
% 2.43/0.98  --abstr_cl_out                          false
% 2.43/0.98  
% 2.43/0.98  ------ Global Options
% 2.43/0.98  
% 2.43/0.98  --schedule                              default
% 2.43/0.98  --add_important_lit                     false
% 2.43/0.98  --prop_solver_per_cl                    1000
% 2.43/0.98  --min_unsat_core                        false
% 2.43/0.98  --soft_assumptions                      false
% 2.43/0.98  --soft_lemma_size                       3
% 2.43/0.98  --prop_impl_unit_size                   0
% 2.43/0.98  --prop_impl_unit                        []
% 2.43/0.98  --share_sel_clauses                     true
% 2.43/0.98  --reset_solvers                         false
% 2.43/0.98  --bc_imp_inh                            [conj_cone]
% 2.43/0.98  --conj_cone_tolerance                   3.
% 2.43/0.98  --extra_neg_conj                        none
% 2.43/0.98  --large_theory_mode                     true
% 2.43/0.98  --prolific_symb_bound                   200
% 2.43/0.98  --lt_threshold                          2000
% 2.43/0.98  --clause_weak_htbl                      true
% 2.43/0.98  --gc_record_bc_elim                     false
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing Options
% 2.43/0.98  
% 2.43/0.98  --preprocessing_flag                    true
% 2.43/0.98  --time_out_prep_mult                    0.1
% 2.43/0.98  --splitting_mode                        input
% 2.43/0.98  --splitting_grd                         true
% 2.43/0.98  --splitting_cvd                         false
% 2.43/0.98  --splitting_cvd_svl                     false
% 2.43/0.98  --splitting_nvd                         32
% 2.43/0.98  --sub_typing                            true
% 2.43/0.98  --prep_gs_sim                           true
% 2.43/0.98  --prep_unflatten                        true
% 2.43/0.98  --prep_res_sim                          true
% 2.43/0.98  --prep_upred                            true
% 2.43/0.98  --prep_sem_filter                       exhaustive
% 2.43/0.98  --prep_sem_filter_out                   false
% 2.43/0.98  --pred_elim                             true
% 2.43/0.98  --res_sim_input                         true
% 2.43/0.98  --eq_ax_congr_red                       true
% 2.43/0.98  --pure_diseq_elim                       true
% 2.43/0.98  --brand_transform                       false
% 2.43/0.98  --non_eq_to_eq                          false
% 2.43/0.98  --prep_def_merge                        true
% 2.43/0.98  --prep_def_merge_prop_impl              false
% 2.43/0.98  --prep_def_merge_mbd                    true
% 2.43/0.98  --prep_def_merge_tr_red                 false
% 2.43/0.98  --prep_def_merge_tr_cl                  false
% 2.43/0.98  --smt_preprocessing                     true
% 2.43/0.98  --smt_ac_axioms                         fast
% 2.43/0.98  --preprocessed_out                      false
% 2.43/0.98  --preprocessed_stats                    false
% 2.43/0.98  
% 2.43/0.98  ------ Abstraction refinement Options
% 2.43/0.98  
% 2.43/0.98  --abstr_ref                             []
% 2.43/0.98  --abstr_ref_prep                        false
% 2.43/0.98  --abstr_ref_until_sat                   false
% 2.43/0.98  --abstr_ref_sig_restrict                funpre
% 2.43/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/0.98  --abstr_ref_under                       []
% 2.43/0.98  
% 2.43/0.98  ------ SAT Options
% 2.43/0.98  
% 2.43/0.98  --sat_mode                              false
% 2.43/0.98  --sat_fm_restart_options                ""
% 2.43/0.98  --sat_gr_def                            false
% 2.43/0.98  --sat_epr_types                         true
% 2.43/0.98  --sat_non_cyclic_types                  false
% 2.43/0.98  --sat_finite_models                     false
% 2.43/0.98  --sat_fm_lemmas                         false
% 2.43/0.98  --sat_fm_prep                           false
% 2.43/0.98  --sat_fm_uc_incr                        true
% 2.43/0.98  --sat_out_model                         small
% 2.43/0.98  --sat_out_clauses                       false
% 2.43/0.98  
% 2.43/0.98  ------ QBF Options
% 2.43/0.98  
% 2.43/0.98  --qbf_mode                              false
% 2.43/0.98  --qbf_elim_univ                         false
% 2.43/0.98  --qbf_dom_inst                          none
% 2.43/0.98  --qbf_dom_pre_inst                      false
% 2.43/0.98  --qbf_sk_in                             false
% 2.43/0.98  --qbf_pred_elim                         true
% 2.43/0.98  --qbf_split                             512
% 2.43/0.98  
% 2.43/0.98  ------ BMC1 Options
% 2.43/0.98  
% 2.43/0.98  --bmc1_incremental                      false
% 2.43/0.98  --bmc1_axioms                           reachable_all
% 2.43/0.98  --bmc1_min_bound                        0
% 2.43/0.98  --bmc1_max_bound                        -1
% 2.43/0.98  --bmc1_max_bound_default                -1
% 2.43/0.98  --bmc1_symbol_reachability              true
% 2.43/0.98  --bmc1_property_lemmas                  false
% 2.43/0.98  --bmc1_k_induction                      false
% 2.43/0.98  --bmc1_non_equiv_states                 false
% 2.43/0.98  --bmc1_deadlock                         false
% 2.43/0.98  --bmc1_ucm                              false
% 2.43/0.98  --bmc1_add_unsat_core                   none
% 2.43/0.98  --bmc1_unsat_core_children              false
% 2.43/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/0.98  --bmc1_out_stat                         full
% 2.43/0.98  --bmc1_ground_init                      false
% 2.43/0.98  --bmc1_pre_inst_next_state              false
% 2.43/0.98  --bmc1_pre_inst_state                   false
% 2.43/0.98  --bmc1_pre_inst_reach_state             false
% 2.43/0.98  --bmc1_out_unsat_core                   false
% 2.43/0.98  --bmc1_aig_witness_out                  false
% 2.43/0.98  --bmc1_verbose                          false
% 2.43/0.98  --bmc1_dump_clauses_tptp                false
% 2.43/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.43/0.98  --bmc1_dump_file                        -
% 2.43/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.43/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.43/0.98  --bmc1_ucm_extend_mode                  1
% 2.43/0.98  --bmc1_ucm_init_mode                    2
% 2.43/0.98  --bmc1_ucm_cone_mode                    none
% 2.43/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.43/0.98  --bmc1_ucm_relax_model                  4
% 2.43/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.43/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/0.98  --bmc1_ucm_layered_model                none
% 2.43/0.98  --bmc1_ucm_max_lemma_size               10
% 2.43/0.98  
% 2.43/0.98  ------ AIG Options
% 2.43/0.98  
% 2.43/0.98  --aig_mode                              false
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation Options
% 2.43/0.98  
% 2.43/0.98  --instantiation_flag                    true
% 2.43/0.98  --inst_sos_flag                         false
% 2.43/0.98  --inst_sos_phase                        true
% 2.43/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/0.98  --inst_lit_sel_side                     none
% 2.43/0.98  --inst_solver_per_active                1400
% 2.43/0.98  --inst_solver_calls_frac                1.
% 2.43/0.98  --inst_passive_queue_type               priority_queues
% 2.43/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/0.98  --inst_passive_queues_freq              [25;2]
% 2.43/0.98  --inst_dismatching                      true
% 2.43/0.98  --inst_eager_unprocessed_to_passive     true
% 2.43/0.98  --inst_prop_sim_given                   true
% 2.43/0.98  --inst_prop_sim_new                     false
% 2.43/0.98  --inst_subs_new                         false
% 2.43/0.98  --inst_eq_res_simp                      false
% 2.43/0.98  --inst_subs_given                       false
% 2.43/0.98  --inst_orphan_elimination               true
% 2.43/0.98  --inst_learning_loop_flag               true
% 2.43/0.98  --inst_learning_start                   3000
% 2.43/0.98  --inst_learning_factor                  2
% 2.43/0.98  --inst_start_prop_sim_after_learn       3
% 2.43/0.98  --inst_sel_renew                        solver
% 2.43/0.98  --inst_lit_activity_flag                true
% 2.43/0.98  --inst_restr_to_given                   false
% 2.43/0.98  --inst_activity_threshold               500
% 2.43/0.98  --inst_out_proof                        true
% 2.43/0.98  
% 2.43/0.98  ------ Resolution Options
% 2.43/0.98  
% 2.43/0.98  --resolution_flag                       false
% 2.43/0.98  --res_lit_sel                           adaptive
% 2.43/0.98  --res_lit_sel_side                      none
% 2.43/0.98  --res_ordering                          kbo
% 2.43/0.98  --res_to_prop_solver                    active
% 2.43/0.98  --res_prop_simpl_new                    false
% 2.43/0.98  --res_prop_simpl_given                  true
% 2.43/0.98  --res_passive_queue_type                priority_queues
% 2.43/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/0.98  --res_passive_queues_freq               [15;5]
% 2.43/0.98  --res_forward_subs                      full
% 2.43/0.98  --res_backward_subs                     full
% 2.43/0.98  --res_forward_subs_resolution           true
% 2.43/0.98  --res_backward_subs_resolution          true
% 2.43/0.98  --res_orphan_elimination                true
% 2.43/0.98  --res_time_limit                        2.
% 2.43/0.98  --res_out_proof                         true
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Options
% 2.43/0.98  
% 2.43/0.98  --superposition_flag                    true
% 2.43/0.98  --sup_passive_queue_type                priority_queues
% 2.43/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.43/0.98  --demod_completeness_check              fast
% 2.43/0.98  --demod_use_ground                      true
% 2.43/0.98  --sup_to_prop_solver                    passive
% 2.43/0.98  --sup_prop_simpl_new                    true
% 2.43/0.98  --sup_prop_simpl_given                  true
% 2.43/0.98  --sup_fun_splitting                     false
% 2.43/0.98  --sup_smt_interval                      50000
% 2.43/0.98  
% 2.43/0.98  ------ Superposition Simplification Setup
% 2.43/0.98  
% 2.43/0.98  --sup_indices_passive                   []
% 2.43/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_full_bw                           [BwDemod]
% 2.43/0.98  --sup_immed_triv                        [TrivRules]
% 2.43/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_immed_bw_main                     []
% 2.43/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/0.98  
% 2.43/0.98  ------ Combination Options
% 2.43/0.98  
% 2.43/0.98  --comb_res_mult                         3
% 2.43/0.98  --comb_sup_mult                         2
% 2.43/0.98  --comb_inst_mult                        10
% 2.43/0.98  
% 2.43/0.98  ------ Debug Options
% 2.43/0.98  
% 2.43/0.98  --dbg_backtrace                         false
% 2.43/0.98  --dbg_dump_prop_clauses                 false
% 2.43/0.98  --dbg_dump_prop_clauses_file            -
% 2.43/0.98  --dbg_out_stat                          false
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  ------ Proving...
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  % SZS status Theorem for theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  fof(f12,axiom,(
% 2.43/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f24,plain,(
% 2.43/0.98    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.43/0.98    inference(ennf_transformation,[],[f12])).
% 2.43/0.98  
% 2.43/0.98  fof(f25,plain,(
% 2.43/0.98    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.43/0.98    inference(flattening,[],[f24])).
% 2.43/0.98  
% 2.43/0.98  fof(f47,plain,(
% 2.43/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f25])).
% 2.43/0.98  
% 2.43/0.98  fof(f13,conjecture,(
% 2.43/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f14,negated_conjecture,(
% 2.43/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.43/0.98    inference(negated_conjecture,[],[f13])).
% 2.43/0.98  
% 2.43/0.98  fof(f26,plain,(
% 2.43/0.98    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.43/0.98    inference(ennf_transformation,[],[f14])).
% 2.43/0.98  
% 2.43/0.98  fof(f27,plain,(
% 2.43/0.98    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.43/0.98    inference(flattening,[],[f26])).
% 2.43/0.98  
% 2.43/0.98  fof(f32,plain,(
% 2.43/0.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK3),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.43/0.98    introduced(choice_axiom,[])).
% 2.43/0.98  
% 2.43/0.98  fof(f31,plain,(
% 2.43/0.98    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK1,X2),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 2.43/0.98    introduced(choice_axiom,[])).
% 2.43/0.98  
% 2.43/0.98  fof(f33,plain,(
% 2.43/0.98    (~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) & r1_tarski(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f32,f31])).
% 2.43/0.98  
% 2.43/0.98  fof(f49,plain,(
% 2.43/0.98    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.43/0.98    inference(cnf_transformation,[],[f33])).
% 2.43/0.98  
% 2.43/0.98  fof(f8,axiom,(
% 2.43/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f21,plain,(
% 2.43/0.98    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.43/0.98    inference(ennf_transformation,[],[f8])).
% 2.43/0.98  
% 2.43/0.98  fof(f41,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f21])).
% 2.43/0.98  
% 2.43/0.98  fof(f10,axiom,(
% 2.43/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f23,plain,(
% 2.43/0.98    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.43/0.98    inference(ennf_transformation,[],[f10])).
% 2.43/0.98  
% 2.43/0.98  fof(f44,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f23])).
% 2.43/0.98  
% 2.43/0.98  fof(f48,plain,(
% 2.43/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 2.43/0.98    inference(cnf_transformation,[],[f33])).
% 2.43/0.98  
% 2.43/0.98  fof(f51,plain,(
% 2.43/0.98    ~r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2))),
% 2.43/0.98    inference(cnf_transformation,[],[f33])).
% 2.43/0.98  
% 2.43/0.98  fof(f50,plain,(
% 2.43/0.98    r1_tarski(sK2,sK3)),
% 2.43/0.98    inference(cnf_transformation,[],[f33])).
% 2.43/0.98  
% 2.43/0.98  fof(f42,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f21])).
% 2.43/0.98  
% 2.43/0.98  fof(f55,plain,(
% 2.43/0.98    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.43/0.98    inference(equality_resolution,[],[f42])).
% 2.43/0.98  
% 2.43/0.98  fof(f9,axiom,(
% 2.43/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f22,plain,(
% 2.43/0.98    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.43/0.98    inference(ennf_transformation,[],[f9])).
% 2.43/0.98  
% 2.43/0.98  fof(f43,plain,(
% 2.43/0.98    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f22])).
% 2.43/0.98  
% 2.43/0.98  fof(f11,axiom,(
% 2.43/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f30,plain,(
% 2.43/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.43/0.98    inference(nnf_transformation,[],[f11])).
% 2.43/0.98  
% 2.43/0.98  fof(f45,plain,(
% 2.43/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f30])).
% 2.43/0.98  
% 2.43/0.98  fof(f1,axiom,(
% 2.43/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f16,plain,(
% 2.43/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.43/0.98    inference(ennf_transformation,[],[f1])).
% 2.43/0.98  
% 2.43/0.98  fof(f28,plain,(
% 2.43/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.43/0.98    introduced(choice_axiom,[])).
% 2.43/0.98  
% 2.43/0.98  fof(f29,plain,(
% 2.43/0.98    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.43/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).
% 2.43/0.98  
% 2.43/0.98  fof(f34,plain,(
% 2.43/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.43/0.98    inference(cnf_transformation,[],[f29])).
% 2.43/0.98  
% 2.43/0.98  fof(f6,axiom,(
% 2.43/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f15,plain,(
% 2.43/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 2.43/0.98    inference(unused_predicate_definition_removal,[],[f6])).
% 2.43/0.98  
% 2.43/0.98  fof(f20,plain,(
% 2.43/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 2.43/0.98    inference(ennf_transformation,[],[f15])).
% 2.43/0.98  
% 2.43/0.98  fof(f39,plain,(
% 2.43/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f20])).
% 2.43/0.98  
% 2.43/0.98  fof(f4,axiom,(
% 2.43/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f18,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.43/0.98    inference(ennf_transformation,[],[f4])).
% 2.43/0.98  
% 2.43/0.98  fof(f19,plain,(
% 2.43/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.43/0.98    inference(flattening,[],[f18])).
% 2.43/0.98  
% 2.43/0.98  fof(f37,plain,(
% 2.43/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f19])).
% 2.43/0.98  
% 2.43/0.98  fof(f3,axiom,(
% 2.43/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f17,plain,(
% 2.43/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.43/0.98    inference(ennf_transformation,[],[f3])).
% 2.43/0.98  
% 2.43/0.98  fof(f36,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f17])).
% 2.43/0.98  
% 2.43/0.98  fof(f5,axiom,(
% 2.43/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f38,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f5])).
% 2.43/0.98  
% 2.43/0.98  fof(f2,axiom,(
% 2.43/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f35,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.43/0.98    inference(cnf_transformation,[],[f2])).
% 2.43/0.98  
% 2.43/0.98  fof(f52,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.43/0.98    inference(definition_unfolding,[],[f38,f35])).
% 2.43/0.98  
% 2.43/0.98  fof(f53,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 2.43/0.98    inference(definition_unfolding,[],[f36,f52])).
% 2.43/0.98  
% 2.43/0.98  fof(f7,axiom,(
% 2.43/0.98    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.43/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.43/0.98  
% 2.43/0.98  fof(f40,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.43/0.98    inference(cnf_transformation,[],[f7])).
% 2.43/0.98  
% 2.43/0.98  fof(f54,plain,(
% 2.43/0.98    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X0))))) )),
% 2.43/0.98    inference(definition_unfolding,[],[f40,f52])).
% 2.43/0.98  
% 2.43/0.98  cnf(c_11,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1)
% 2.43/0.98      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.43/0.98      | k1_xboole_0 = X0 ),
% 2.43/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_692,plain,
% 2.43/0.98      ( k1_xboole_0 = X0
% 2.43/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.43/0.98      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_14,negated_conjecture,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.43/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_689,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_6,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.43/0.98      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.43/0.98      | k1_xboole_0 = X0 ),
% 2.43/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_697,plain,
% 2.43/0.98      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.43/0.98      | k1_xboole_0 = X1
% 2.43/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2090,plain,
% 2.43/0.98      ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3) | sK3 = k1_xboole_0 ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_689,c_697]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_8,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.43/0.98      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.43/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_695,plain,
% 2.43/0.98      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.43/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1246,plain,
% 2.43/0.98      ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_689,c_695]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2099,plain,
% 2.43/0.98      ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.43/0.98      inference(light_normalisation,[status(thm)],[c_2090,c_1246]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_15,negated_conjecture,
% 2.43/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.43/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_688,plain,
% 2.43/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2091,plain,
% 2.43/0.98      ( k6_setfam_1(sK1,sK2) = k8_setfam_1(sK1,sK2) | sK2 = k1_xboole_0 ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_688,c_697]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1247,plain,
% 2.43/0.98      ( k6_setfam_1(sK1,sK2) = k1_setfam_1(sK2) ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_688,c_695]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2094,plain,
% 2.43/0.98      ( k8_setfam_1(sK1,sK2) = k1_setfam_1(sK2) | sK2 = k1_xboole_0 ),
% 2.43/0.98      inference(light_normalisation,[status(thm)],[c_2091,c_1247]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_12,negated_conjecture,
% 2.43/0.98      ( ~ r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) ),
% 2.43/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_691,plain,
% 2.43/0.98      ( r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2356,plain,
% 2.43/0.98      ( sK2 = k1_xboole_0
% 2.43/0.98      | r1_tarski(k8_setfam_1(sK1,sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_2094,c_691]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2468,plain,
% 2.43/0.98      ( sK2 = k1_xboole_0
% 2.43/0.98      | sK3 = k1_xboole_0
% 2.43/0.98      | r1_tarski(k1_setfam_1(sK3),k1_setfam_1(sK2)) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_2099,c_2356]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2591,plain,
% 2.43/0.98      ( sK2 = k1_xboole_0
% 2.43/0.98      | sK3 = k1_xboole_0
% 2.43/0.98      | r1_tarski(sK2,sK3) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_692,c_2468]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_13,negated_conjecture,
% 2.43/0.98      ( r1_tarski(sK2,sK3) ),
% 2.43/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2592,plain,
% 2.43/0.98      ( ~ r1_tarski(sK2,sK3) | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.43/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2591]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2681,plain,
% 2.43/0.98      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_2591,c_13,c_2592]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2682,plain,
% 2.43/0.98      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.43/0.98      inference(renaming,[status(thm)],[c_2681]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2694,plain,
% 2.43/0.98      ( sK3 = k1_xboole_0
% 2.43/0.98      | r1_tarski(k8_setfam_1(sK1,sK3),k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_2682,c_691]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2695,plain,
% 2.43/0.98      ( sK3 = k1_xboole_0
% 2.43/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_2682,c_688]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_17,plain,
% 2.43/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_348,plain,( X0 = X0 ),theory(equality) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_365,plain,
% 2.43/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_348]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_349,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_981,plain,
% 2.43/0.98      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_349]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_982,plain,
% 2.43/0.98      ( sK3 != k1_xboole_0
% 2.43/0.98      | k1_xboole_0 = sK3
% 2.43/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_981]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_356,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.43/0.98      theory(equality) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_825,plain,
% 2.43/0.98      ( m1_subset_1(X0,X1)
% 2.43/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 2.43/0.98      | X1 != k1_zfmisc_1(k1_zfmisc_1(sK1))
% 2.43/0.98      | X0 != sK3 ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_356]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1220,plain,
% 2.43/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 2.43/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 2.43/0.98      | X0 != sK3
% 2.43/0.98      | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_825]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1222,plain,
% 2.43/0.98      ( X0 != sK3
% 2.43/0.98      | k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
% 2.43/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
% 2.43/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1220]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1224,plain,
% 2.43/0.98      ( k1_zfmisc_1(k1_zfmisc_1(sK1)) != k1_zfmisc_1(k1_zfmisc_1(sK1))
% 2.43/0.98      | k1_xboole_0 != sK3
% 2.43/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 2.43/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_1222]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1221,plain,
% 2.43/0.98      ( k1_zfmisc_1(k1_zfmisc_1(sK1)) = k1_zfmisc_1(k1_zfmisc_1(sK1)) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_348]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2794,plain,
% 2.43/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_2695,c_17,c_365,c_982,c_1224,c_1221]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_5,plain,
% 2.43/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.43/0.98      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.43/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_698,plain,
% 2.43/0.98      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.43/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2799,plain,
% 2.43/0.98      ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_2794,c_698]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3020,plain,
% 2.43/0.98      ( sK3 = k1_xboole_0
% 2.43/0.98      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) != iProver_top ),
% 2.43/0.98      inference(light_normalisation,[status(thm)],[c_2694,c_2799]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_7,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.43/0.98      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.43/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_796,plain,
% 2.43/0.98      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
% 2.43/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_797,plain,
% 2.43/0.98      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 2.43/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_10,plain,
% 2.43/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.43/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_874,plain,
% 2.43/0.98      ( ~ m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1))
% 2.43/0.98      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) ),
% 2.43/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_875,plain,
% 2.43/0.98      ( m1_subset_1(k8_setfam_1(sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 2.43/0.98      | r1_tarski(k8_setfam_1(sK1,sK3),sK1) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_874]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3024,plain,
% 2.43/0.98      ( sK3 = k1_xboole_0 ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_3020,c_17,c_797,c_875]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_690,plain,
% 2.43/0.98      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3036,plain,
% 2.43/0.98      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.43/0.98      inference(demodulation,[status(thm)],[c_3024,c_690]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_0,plain,
% 2.43/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.43/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3,plain,
% 2.43/0.98      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.43/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_204,plain,
% 2.43/0.98      ( r1_tarski(k1_tarski(X0),X1)
% 2.43/0.98      | X1 != X2
% 2.43/0.98      | sK0(X2) != X0
% 2.43/0.98      | k1_xboole_0 = X2 ),
% 2.43/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_205,plain,
% 2.43/0.98      ( r1_tarski(k1_tarski(sK0(X0)),X0) | k1_xboole_0 = X0 ),
% 2.43/0.98      inference(unflattening,[status(thm)],[c_204]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_687,plain,
% 2.43/0.98      ( k1_xboole_0 = X0
% 2.43/0.98      | r1_tarski(k1_tarski(sK0(X0)),X0) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_205]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 2.43/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_699,plain,
% 2.43/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.43/0.98      | r1_tarski(X1,X2) != iProver_top
% 2.43/0.98      | r1_tarski(X0,X2) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2046,plain,
% 2.43/0.98      ( k1_xboole_0 = X0
% 2.43/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.43/0.98      | r1_tarski(k1_tarski(sK0(X0)),X1) = iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_687,c_699]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_1,plain,
% 2.43/0.98      ( ~ r1_tarski(X0,X1)
% 2.43/0.98      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 2.43/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_700,plain,
% 2.43/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
% 2.43/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_4482,plain,
% 2.43/0.98      ( k5_xboole_0(k1_tarski(sK0(X0)),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(sK0(X0))))) = X1
% 2.43/0.98      | k1_xboole_0 = X0
% 2.43/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_2046,c_700]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_9323,plain,
% 2.43/0.98      ( k5_xboole_0(k1_tarski(sK0(sK2)),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_tarski(sK0(sK2))))) = k1_xboole_0
% 2.43/0.98      | sK2 = k1_xboole_0 ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_3036,c_4482]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_4,plain,
% 2.43/0.98      ( k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X0)))) != k1_xboole_0 ),
% 2.43/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_10130,plain,
% 2.43/0.98      ( sK2 = k1_xboole_0 ),
% 2.43/0.98      inference(forward_subsumption_resolution,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_9323,c_4]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3034,plain,
% 2.43/0.98      ( r1_tarski(k8_setfam_1(sK1,k1_xboole_0),k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.43/0.98      inference(demodulation,[status(thm)],[c_3024,c_691]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3040,plain,
% 2.43/0.98      ( r1_tarski(sK1,k8_setfam_1(sK1,sK2)) != iProver_top ),
% 2.43/0.98      inference(light_normalisation,[status(thm)],[c_3034,c_2799]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_10164,plain,
% 2.43/0.98      ( r1_tarski(sK1,k8_setfam_1(sK1,k1_xboole_0)) != iProver_top ),
% 2.43/0.98      inference(demodulation,[status(thm)],[c_10130,c_3040]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_10175,plain,
% 2.43/0.98      ( r1_tarski(sK1,sK1) != iProver_top ),
% 2.43/0.98      inference(light_normalisation,[status(thm)],[c_10164,c_2799]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_696,plain,
% 2.43/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.43/0.98      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_2882,plain,
% 2.43/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top
% 2.43/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_2799,c_696]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3416,plain,
% 2.43/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.43/0.98      inference(global_propositional_subsumption,
% 2.43/0.98                [status(thm)],
% 2.43/0.98                [c_2882,c_17,c_365,c_982,c_1224,c_1221,c_2695]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_693,plain,
% 2.43/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.43/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.43/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(c_3421,plain,
% 2.43/0.98      ( r1_tarski(sK1,sK1) = iProver_top ),
% 2.43/0.98      inference(superposition,[status(thm)],[c_3416,c_693]) ).
% 2.43/0.98  
% 2.43/0.98  cnf(contradiction,plain,
% 2.43/0.98      ( $false ),
% 2.43/0.98      inference(minisat,[status(thm)],[c_10175,c_3421]) ).
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/0.98  
% 2.43/0.98  ------                               Statistics
% 2.43/0.98  
% 2.43/0.98  ------ General
% 2.43/0.98  
% 2.43/0.98  abstr_ref_over_cycles:                  0
% 2.43/0.98  abstr_ref_under_cycles:                 0
% 2.43/0.98  gc_basic_clause_elim:                   0
% 2.43/0.98  forced_gc_time:                         0
% 2.43/0.98  parsing_time:                           0.01
% 2.43/0.98  unif_index_cands_time:                  0.
% 2.43/0.98  unif_index_add_time:                    0.
% 2.43/0.98  orderings_time:                         0.
% 2.43/0.98  out_proof_time:                         0.008
% 2.43/0.98  total_time:                             0.257
% 2.43/0.98  num_of_symbols:                         46
% 2.43/0.98  num_of_terms:                           5337
% 2.43/0.98  
% 2.43/0.98  ------ Preprocessing
% 2.43/0.98  
% 2.43/0.98  num_of_splits:                          0
% 2.43/0.98  num_of_split_atoms:                     0
% 2.43/0.98  num_of_reused_defs:                     0
% 2.43/0.98  num_eq_ax_congr_red:                    17
% 2.43/0.98  num_of_sem_filtered_clauses:            1
% 2.43/0.98  num_of_subtypes:                        0
% 2.43/0.98  monotx_restored_types:                  0
% 2.43/0.98  sat_num_of_epr_types:                   0
% 2.43/0.98  sat_num_of_non_cyclic_types:            0
% 2.43/0.98  sat_guarded_non_collapsed_types:        0
% 2.43/0.98  num_pure_diseq_elim:                    0
% 2.43/0.98  simp_replaced_by:                       0
% 2.43/0.98  res_preprocessed:                       80
% 2.43/0.98  prep_upred:                             0
% 2.43/0.98  prep_unflattend:                        2
% 2.43/0.98  smt_new_axioms:                         0
% 2.43/0.98  pred_elim_cands:                        2
% 2.43/0.98  pred_elim:                              1
% 2.43/0.98  pred_elim_cl:                           1
% 2.43/0.98  pred_elim_cycles:                       3
% 2.43/0.98  merged_defs:                            8
% 2.43/0.98  merged_defs_ncl:                        0
% 2.43/0.98  bin_hyper_res:                          8
% 2.43/0.98  prep_cycles:                            4
% 2.43/0.98  pred_elim_time:                         0.
% 2.43/0.98  splitting_time:                         0.
% 2.43/0.98  sem_filter_time:                        0.
% 2.43/0.98  monotx_time:                            0.001
% 2.43/0.98  subtype_inf_time:                       0.
% 2.43/0.98  
% 2.43/0.98  ------ Problem properties
% 2.43/0.98  
% 2.43/0.98  clauses:                                15
% 2.43/0.98  conjectures:                            4
% 2.43/0.98  epr:                                    2
% 2.43/0.98  horn:                                   12
% 2.43/0.98  ground:                                 4
% 2.43/0.98  unary:                                  5
% 2.43/0.98  binary:                                 7
% 2.43/0.98  lits:                                   28
% 2.43/0.98  lits_eq:                                8
% 2.43/0.98  fd_pure:                                0
% 2.43/0.98  fd_pseudo:                              0
% 2.43/0.98  fd_cond:                                3
% 2.43/0.98  fd_pseudo_cond:                         0
% 2.43/0.98  ac_symbols:                             0
% 2.43/0.98  
% 2.43/0.98  ------ Propositional Solver
% 2.43/0.98  
% 2.43/0.98  prop_solver_calls:                      27
% 2.43/0.98  prop_fast_solver_calls:                 576
% 2.43/0.98  smt_solver_calls:                       0
% 2.43/0.98  smt_fast_solver_calls:                  0
% 2.43/0.98  prop_num_of_clauses:                    3453
% 2.43/0.98  prop_preprocess_simplified:             7996
% 2.43/0.98  prop_fo_subsumed:                       7
% 2.43/0.98  prop_solver_time:                       0.
% 2.43/0.98  smt_solver_time:                        0.
% 2.43/0.98  smt_fast_solver_time:                   0.
% 2.43/0.98  prop_fast_solver_time:                  0.
% 2.43/0.98  prop_unsat_core_time:                   0.
% 2.43/0.98  
% 2.43/0.98  ------ QBF
% 2.43/0.98  
% 2.43/0.98  qbf_q_res:                              0
% 2.43/0.98  qbf_num_tautologies:                    0
% 2.43/0.98  qbf_prep_cycles:                        0
% 2.43/0.98  
% 2.43/0.98  ------ BMC1
% 2.43/0.98  
% 2.43/0.98  bmc1_current_bound:                     -1
% 2.43/0.98  bmc1_last_solved_bound:                 -1
% 2.43/0.98  bmc1_unsat_core_size:                   -1
% 2.43/0.98  bmc1_unsat_core_parents_size:           -1
% 2.43/0.98  bmc1_merge_next_fun:                    0
% 2.43/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.43/0.98  
% 2.43/0.98  ------ Instantiation
% 2.43/0.98  
% 2.43/0.98  inst_num_of_clauses:                    1027
% 2.43/0.98  inst_num_in_passive:                    545
% 2.43/0.98  inst_num_in_active:                     367
% 2.43/0.98  inst_num_in_unprocessed:                115
% 2.43/0.98  inst_num_of_loops:                      550
% 2.43/0.98  inst_num_of_learning_restarts:          0
% 2.43/0.98  inst_num_moves_active_passive:          181
% 2.43/0.98  inst_lit_activity:                      0
% 2.43/0.98  inst_lit_activity_moves:                0
% 2.43/0.98  inst_num_tautologies:                   0
% 2.43/0.98  inst_num_prop_implied:                  0
% 2.43/0.98  inst_num_existing_simplified:           0
% 2.43/0.98  inst_num_eq_res_simplified:             0
% 2.43/0.98  inst_num_child_elim:                    0
% 2.43/0.98  inst_num_of_dismatching_blockings:      623
% 2.43/0.98  inst_num_of_non_proper_insts:           1000
% 2.43/0.98  inst_num_of_duplicates:                 0
% 2.43/0.98  inst_inst_num_from_inst_to_res:         0
% 2.43/0.98  inst_dismatching_checking_time:         0.
% 2.43/0.98  
% 2.43/0.98  ------ Resolution
% 2.43/0.98  
% 2.43/0.98  res_num_of_clauses:                     0
% 2.43/0.98  res_num_in_passive:                     0
% 2.43/0.98  res_num_in_active:                      0
% 2.43/0.98  res_num_of_loops:                       84
% 2.43/0.98  res_forward_subset_subsumed:            46
% 2.43/0.98  res_backward_subset_subsumed:           0
% 2.43/0.98  res_forward_subsumed:                   0
% 2.43/0.98  res_backward_subsumed:                  0
% 2.43/0.98  res_forward_subsumption_resolution:     0
% 2.43/0.98  res_backward_subsumption_resolution:    0
% 2.43/0.98  res_clause_to_clause_subsumption:       1220
% 2.43/0.98  res_orphan_elimination:                 0
% 2.43/0.98  res_tautology_del:                      98
% 2.43/0.98  res_num_eq_res_simplified:              0
% 2.43/0.98  res_num_sel_changes:                    0
% 2.43/0.98  res_moves_from_active_to_pass:          0
% 2.43/0.98  
% 2.43/0.98  ------ Superposition
% 2.43/0.98  
% 2.43/0.98  sup_time_total:                         0.
% 2.43/0.98  sup_time_generating:                    0.
% 2.43/0.98  sup_time_sim_full:                      0.
% 2.43/0.98  sup_time_sim_immed:                     0.
% 2.43/0.98  
% 2.43/0.98  sup_num_of_clauses:                     194
% 2.43/0.98  sup_num_in_active:                      43
% 2.43/0.98  sup_num_in_passive:                     151
% 2.43/0.98  sup_num_of_loops:                       108
% 2.43/0.98  sup_fw_superposition:                   236
% 2.43/0.98  sup_bw_superposition:                   145
% 2.43/0.98  sup_immediate_simplified:               92
% 2.43/0.98  sup_given_eliminated:                   0
% 2.43/0.98  comparisons_done:                       0
% 2.43/0.98  comparisons_avoided:                    74
% 2.43/0.98  
% 2.43/0.98  ------ Simplifications
% 2.43/0.98  
% 2.43/0.98  
% 2.43/0.98  sim_fw_subset_subsumed:                 62
% 2.43/0.98  sim_bw_subset_subsumed:                 35
% 2.43/0.98  sim_fw_subsumed:                        13
% 2.43/0.98  sim_bw_subsumed:                        0
% 2.43/0.98  sim_fw_subsumption_res:                 1
% 2.43/0.98  sim_bw_subsumption_res:                 0
% 2.43/0.98  sim_tautology_del:                      7
% 2.43/0.98  sim_eq_tautology_del:                   18
% 2.43/0.98  sim_eq_res_simp:                        0
% 2.43/0.98  sim_fw_demodulated:                     3
% 2.43/0.98  sim_bw_demodulated:                     52
% 2.43/0.98  sim_light_normalised:                   25
% 2.43/0.98  sim_joinable_taut:                      0
% 2.43/0.98  sim_joinable_simp:                      0
% 2.43/0.98  sim_ac_normalised:                      0
% 2.43/0.98  sim_smt_subsumption:                    0
% 2.43/0.98  
%------------------------------------------------------------------------------
