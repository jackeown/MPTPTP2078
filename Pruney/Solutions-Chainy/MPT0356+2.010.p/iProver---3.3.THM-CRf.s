%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:43 EST 2020

% Result     : Theorem 23.42s
% Output     : CNFRefutation 23.42s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 195 expanded)
%              Number of clauses        :   67 (  75 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 ( 514 expanded)
%              Number of equality atoms :  108 ( 156 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(sK2,k3_subset_1(X0,X1))
        & r1_tarski(X1,k3_subset_1(X0,sK2))
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK0,sK1))
          & r1_tarski(sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24])).

fof(f42,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f33,f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_598,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_588,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_587,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_592,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2071,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_subset_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_587,c_592])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_597,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2374,plain,
    ( r1_xboole_0(X0,sK2) = iProver_top
    | r1_tarski(X0,k3_subset_1(sK0,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2071,c_597])).

cnf(c_3636,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_588,c_2374])).

cnf(c_6,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_595,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_593,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_599,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2187,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r1_xboole_0(X2,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_599])).

cnf(c_23536,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_2187])).

cnf(c_44,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_84260,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23536,c_44])).

cnf(c_84261,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_84260])).

cnf(c_84278,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_3636,c_84261])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_594,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_85148,plain,
    ( r1_xboole_0(X0,sK1) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_84278,c_594])).

cnf(c_91993,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_598,c_85148])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_704,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5549,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2)))) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_5550,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5549])).

cnf(c_5552,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))) != iProver_top
    | r1_tarski(sK2,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5550])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_586,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2072,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_586,c_592])).

cnf(c_2401,plain,
    ( r1_xboole_0(X0,sK1) != iProver_top
    | r1_tarski(X0,k3_subset_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2072,c_593])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_589,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4731,plain,
    ( r1_xboole_0(sK2,sK1) != iProver_top
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2401,c_589])).

cnf(c_2343,plain,
    ( r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2344,plain,
    ( r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2343])).

cnf(c_2346,plain,
    ( r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2285,plain,
    ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2287,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2285])).

cnf(c_338,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_717,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_1048,plain,
    ( ~ r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != k3_subset_1(X0,k3_subset_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_1181,plain,
    ( ~ r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2)))
    | r1_tarski(sK2,X1)
    | X1 != k3_subset_1(X0,k3_subset_1(X0,sK2))
    | sK2 != k3_subset_1(X0,k3_subset_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_1658,plain,
    ( ~ r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2)))
    | r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2))))
    | k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2))) != k3_subset_1(X0,k3_subset_1(X0,sK2))
    | sK2 != k3_subset_1(X0,k3_subset_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1181])).

cnf(c_1659,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2))) != k3_subset_1(X0,k3_subset_1(X0,sK2))
    | sK2 != k3_subset_1(X0,k3_subset_1(X0,sK2))
    | r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2))) != iProver_top
    | r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1658])).

cnf(c_1661,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) != k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | sK2 != k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) != iProver_top
    | r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_1367,plain,
    ( ~ m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))
    | k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2))) = k3_subset_1(X0,k3_subset_1(X0,sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_836,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_838,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_335,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_649,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_691,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_649])).

cnf(c_737,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,sK2)) != sK2
    | sK2 = k3_subset_1(X0,k3_subset_1(X0,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_738,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) != sK2
    | sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_334,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_655,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91993,c_5552,c_4731,c_2346,c_2287,c_1661,c_1369,c_838,c_738,c_655,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 13:41:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 23.42/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.42/3.49  
% 23.42/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.42/3.49  
% 23.42/3.49  ------  iProver source info
% 23.42/3.49  
% 23.42/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.42/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.42/3.49  git: non_committed_changes: false
% 23.42/3.49  git: last_make_outside_of_git: false
% 23.42/3.49  
% 23.42/3.49  ------ 
% 23.42/3.49  
% 23.42/3.49  ------ Input Options
% 23.42/3.49  
% 23.42/3.49  --out_options                           all
% 23.42/3.49  --tptp_safe_out                         true
% 23.42/3.49  --problem_path                          ""
% 23.42/3.49  --include_path                          ""
% 23.42/3.49  --clausifier                            res/vclausify_rel
% 23.42/3.49  --clausifier_options                    ""
% 23.42/3.49  --stdin                                 false
% 23.42/3.49  --stats_out                             all
% 23.42/3.49  
% 23.42/3.49  ------ General Options
% 23.42/3.49  
% 23.42/3.49  --fof                                   false
% 23.42/3.49  --time_out_real                         305.
% 23.42/3.49  --time_out_virtual                      -1.
% 23.42/3.49  --symbol_type_check                     false
% 23.42/3.49  --clausify_out                          false
% 23.42/3.49  --sig_cnt_out                           false
% 23.42/3.49  --trig_cnt_out                          false
% 23.42/3.49  --trig_cnt_out_tolerance                1.
% 23.42/3.49  --trig_cnt_out_sk_spl                   false
% 23.42/3.49  --abstr_cl_out                          false
% 23.42/3.49  
% 23.42/3.49  ------ Global Options
% 23.42/3.49  
% 23.42/3.49  --schedule                              default
% 23.42/3.49  --add_important_lit                     false
% 23.42/3.49  --prop_solver_per_cl                    1000
% 23.42/3.49  --min_unsat_core                        false
% 23.42/3.49  --soft_assumptions                      false
% 23.42/3.49  --soft_lemma_size                       3
% 23.42/3.49  --prop_impl_unit_size                   0
% 23.42/3.49  --prop_impl_unit                        []
% 23.42/3.49  --share_sel_clauses                     true
% 23.42/3.49  --reset_solvers                         false
% 23.42/3.49  --bc_imp_inh                            [conj_cone]
% 23.42/3.49  --conj_cone_tolerance                   3.
% 23.42/3.49  --extra_neg_conj                        none
% 23.42/3.49  --large_theory_mode                     true
% 23.42/3.49  --prolific_symb_bound                   200
% 23.42/3.49  --lt_threshold                          2000
% 23.42/3.49  --clause_weak_htbl                      true
% 23.42/3.49  --gc_record_bc_elim                     false
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing Options
% 23.42/3.49  
% 23.42/3.49  --preprocessing_flag                    true
% 23.42/3.49  --time_out_prep_mult                    0.1
% 23.42/3.49  --splitting_mode                        input
% 23.42/3.49  --splitting_grd                         true
% 23.42/3.49  --splitting_cvd                         false
% 23.42/3.49  --splitting_cvd_svl                     false
% 23.42/3.49  --splitting_nvd                         32
% 23.42/3.49  --sub_typing                            true
% 23.42/3.49  --prep_gs_sim                           true
% 23.42/3.49  --prep_unflatten                        true
% 23.42/3.49  --prep_res_sim                          true
% 23.42/3.49  --prep_upred                            true
% 23.42/3.49  --prep_sem_filter                       exhaustive
% 23.42/3.49  --prep_sem_filter_out                   false
% 23.42/3.49  --pred_elim                             true
% 23.42/3.49  --res_sim_input                         true
% 23.42/3.49  --eq_ax_congr_red                       true
% 23.42/3.49  --pure_diseq_elim                       true
% 23.42/3.49  --brand_transform                       false
% 23.42/3.49  --non_eq_to_eq                          false
% 23.42/3.49  --prep_def_merge                        true
% 23.42/3.49  --prep_def_merge_prop_impl              false
% 23.42/3.49  --prep_def_merge_mbd                    true
% 23.42/3.49  --prep_def_merge_tr_red                 false
% 23.42/3.49  --prep_def_merge_tr_cl                  false
% 23.42/3.49  --smt_preprocessing                     true
% 23.42/3.49  --smt_ac_axioms                         fast
% 23.42/3.49  --preprocessed_out                      false
% 23.42/3.49  --preprocessed_stats                    false
% 23.42/3.49  
% 23.42/3.49  ------ Abstraction refinement Options
% 23.42/3.49  
% 23.42/3.49  --abstr_ref                             []
% 23.42/3.49  --abstr_ref_prep                        false
% 23.42/3.49  --abstr_ref_until_sat                   false
% 23.42/3.49  --abstr_ref_sig_restrict                funpre
% 23.42/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.42/3.49  --abstr_ref_under                       []
% 23.42/3.49  
% 23.42/3.49  ------ SAT Options
% 23.42/3.49  
% 23.42/3.49  --sat_mode                              false
% 23.42/3.49  --sat_fm_restart_options                ""
% 23.42/3.49  --sat_gr_def                            false
% 23.42/3.49  --sat_epr_types                         true
% 23.42/3.49  --sat_non_cyclic_types                  false
% 23.42/3.49  --sat_finite_models                     false
% 23.42/3.49  --sat_fm_lemmas                         false
% 23.42/3.49  --sat_fm_prep                           false
% 23.42/3.49  --sat_fm_uc_incr                        true
% 23.42/3.49  --sat_out_model                         small
% 23.42/3.49  --sat_out_clauses                       false
% 23.42/3.49  
% 23.42/3.49  ------ QBF Options
% 23.42/3.49  
% 23.42/3.49  --qbf_mode                              false
% 23.42/3.49  --qbf_elim_univ                         false
% 23.42/3.49  --qbf_dom_inst                          none
% 23.42/3.49  --qbf_dom_pre_inst                      false
% 23.42/3.49  --qbf_sk_in                             false
% 23.42/3.49  --qbf_pred_elim                         true
% 23.42/3.49  --qbf_split                             512
% 23.42/3.49  
% 23.42/3.49  ------ BMC1 Options
% 23.42/3.49  
% 23.42/3.49  --bmc1_incremental                      false
% 23.42/3.49  --bmc1_axioms                           reachable_all
% 23.42/3.49  --bmc1_min_bound                        0
% 23.42/3.49  --bmc1_max_bound                        -1
% 23.42/3.49  --bmc1_max_bound_default                -1
% 23.42/3.49  --bmc1_symbol_reachability              true
% 23.42/3.49  --bmc1_property_lemmas                  false
% 23.42/3.49  --bmc1_k_induction                      false
% 23.42/3.49  --bmc1_non_equiv_states                 false
% 23.42/3.49  --bmc1_deadlock                         false
% 23.42/3.49  --bmc1_ucm                              false
% 23.42/3.49  --bmc1_add_unsat_core                   none
% 23.42/3.49  --bmc1_unsat_core_children              false
% 23.42/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.42/3.49  --bmc1_out_stat                         full
% 23.42/3.49  --bmc1_ground_init                      false
% 23.42/3.49  --bmc1_pre_inst_next_state              false
% 23.42/3.49  --bmc1_pre_inst_state                   false
% 23.42/3.49  --bmc1_pre_inst_reach_state             false
% 23.42/3.49  --bmc1_out_unsat_core                   false
% 23.42/3.49  --bmc1_aig_witness_out                  false
% 23.42/3.49  --bmc1_verbose                          false
% 23.42/3.49  --bmc1_dump_clauses_tptp                false
% 23.42/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.42/3.49  --bmc1_dump_file                        -
% 23.42/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.42/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.42/3.49  --bmc1_ucm_extend_mode                  1
% 23.42/3.49  --bmc1_ucm_init_mode                    2
% 23.42/3.49  --bmc1_ucm_cone_mode                    none
% 23.42/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.42/3.49  --bmc1_ucm_relax_model                  4
% 23.42/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.42/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.42/3.49  --bmc1_ucm_layered_model                none
% 23.42/3.49  --bmc1_ucm_max_lemma_size               10
% 23.42/3.49  
% 23.42/3.49  ------ AIG Options
% 23.42/3.49  
% 23.42/3.49  --aig_mode                              false
% 23.42/3.49  
% 23.42/3.49  ------ Instantiation Options
% 23.42/3.49  
% 23.42/3.49  --instantiation_flag                    true
% 23.42/3.49  --inst_sos_flag                         true
% 23.42/3.49  --inst_sos_phase                        true
% 23.42/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.42/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.42/3.49  --inst_lit_sel_side                     num_symb
% 23.42/3.49  --inst_solver_per_active                1400
% 23.42/3.49  --inst_solver_calls_frac                1.
% 23.42/3.49  --inst_passive_queue_type               priority_queues
% 23.42/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.42/3.49  --inst_passive_queues_freq              [25;2]
% 23.42/3.49  --inst_dismatching                      true
% 23.42/3.49  --inst_eager_unprocessed_to_passive     true
% 23.42/3.49  --inst_prop_sim_given                   true
% 23.42/3.49  --inst_prop_sim_new                     false
% 23.42/3.49  --inst_subs_new                         false
% 23.42/3.49  --inst_eq_res_simp                      false
% 23.42/3.49  --inst_subs_given                       false
% 23.42/3.49  --inst_orphan_elimination               true
% 23.42/3.49  --inst_learning_loop_flag               true
% 23.42/3.49  --inst_learning_start                   3000
% 23.42/3.49  --inst_learning_factor                  2
% 23.42/3.49  --inst_start_prop_sim_after_learn       3
% 23.42/3.49  --inst_sel_renew                        solver
% 23.42/3.49  --inst_lit_activity_flag                true
% 23.42/3.49  --inst_restr_to_given                   false
% 23.42/3.49  --inst_activity_threshold               500
% 23.42/3.49  --inst_out_proof                        true
% 23.42/3.49  
% 23.42/3.49  ------ Resolution Options
% 23.42/3.49  
% 23.42/3.49  --resolution_flag                       true
% 23.42/3.49  --res_lit_sel                           adaptive
% 23.42/3.49  --res_lit_sel_side                      none
% 23.42/3.49  --res_ordering                          kbo
% 23.42/3.49  --res_to_prop_solver                    active
% 23.42/3.49  --res_prop_simpl_new                    false
% 23.42/3.49  --res_prop_simpl_given                  true
% 23.42/3.49  --res_passive_queue_type                priority_queues
% 23.42/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.42/3.49  --res_passive_queues_freq               [15;5]
% 23.42/3.49  --res_forward_subs                      full
% 23.42/3.49  --res_backward_subs                     full
% 23.42/3.49  --res_forward_subs_resolution           true
% 23.42/3.49  --res_backward_subs_resolution          true
% 23.42/3.49  --res_orphan_elimination                true
% 23.42/3.49  --res_time_limit                        2.
% 23.42/3.49  --res_out_proof                         true
% 23.42/3.49  
% 23.42/3.49  ------ Superposition Options
% 23.42/3.49  
% 23.42/3.49  --superposition_flag                    true
% 23.42/3.49  --sup_passive_queue_type                priority_queues
% 23.42/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.42/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.42/3.49  --demod_completeness_check              fast
% 23.42/3.49  --demod_use_ground                      true
% 23.42/3.49  --sup_to_prop_solver                    passive
% 23.42/3.49  --sup_prop_simpl_new                    true
% 23.42/3.49  --sup_prop_simpl_given                  true
% 23.42/3.49  --sup_fun_splitting                     true
% 23.42/3.49  --sup_smt_interval                      50000
% 23.42/3.49  
% 23.42/3.49  ------ Superposition Simplification Setup
% 23.42/3.49  
% 23.42/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.42/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.42/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.42/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.42/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.42/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.42/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.42/3.49  --sup_immed_triv                        [TrivRules]
% 23.42/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.42/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.42/3.49  --sup_immed_bw_main                     []
% 23.42/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.42/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.42/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.42/3.49  --sup_input_bw                          []
% 23.42/3.49  
% 23.42/3.49  ------ Combination Options
% 23.42/3.49  
% 23.42/3.49  --comb_res_mult                         3
% 23.42/3.49  --comb_sup_mult                         2
% 23.42/3.49  --comb_inst_mult                        10
% 23.42/3.49  
% 23.42/3.49  ------ Debug Options
% 23.42/3.49  
% 23.42/3.49  --dbg_backtrace                         false
% 23.42/3.49  --dbg_dump_prop_clauses                 false
% 23.42/3.49  --dbg_dump_prop_clauses_file            -
% 23.42/3.49  --dbg_out_stat                          false
% 23.42/3.49  ------ Parsing...
% 23.42/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.42/3.49  ------ Proving...
% 23.42/3.49  ------ Problem Properties 
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  clauses                                 15
% 23.42/3.49  conjectures                             4
% 23.42/3.49  EPR                                     2
% 23.42/3.49  Horn                                    15
% 23.42/3.49  unary                                   7
% 23.42/3.49  binary                                  6
% 23.42/3.49  lits                                    25
% 23.42/3.49  lits eq                                 4
% 23.42/3.49  fd_pure                                 0
% 23.42/3.49  fd_pseudo                               0
% 23.42/3.49  fd_cond                                 0
% 23.42/3.49  fd_pseudo_cond                          1
% 23.42/3.49  AC symbols                              0
% 23.42/3.49  
% 23.42/3.49  ------ Schedule dynamic 5 is on 
% 23.42/3.49  
% 23.42/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  ------ 
% 23.42/3.49  Current options:
% 23.42/3.49  ------ 
% 23.42/3.49  
% 23.42/3.49  ------ Input Options
% 23.42/3.49  
% 23.42/3.49  --out_options                           all
% 23.42/3.49  --tptp_safe_out                         true
% 23.42/3.49  --problem_path                          ""
% 23.42/3.49  --include_path                          ""
% 23.42/3.49  --clausifier                            res/vclausify_rel
% 23.42/3.49  --clausifier_options                    ""
% 23.42/3.49  --stdin                                 false
% 23.42/3.49  --stats_out                             all
% 23.42/3.49  
% 23.42/3.49  ------ General Options
% 23.42/3.49  
% 23.42/3.49  --fof                                   false
% 23.42/3.49  --time_out_real                         305.
% 23.42/3.49  --time_out_virtual                      -1.
% 23.42/3.49  --symbol_type_check                     false
% 23.42/3.49  --clausify_out                          false
% 23.42/3.49  --sig_cnt_out                           false
% 23.42/3.49  --trig_cnt_out                          false
% 23.42/3.49  --trig_cnt_out_tolerance                1.
% 23.42/3.49  --trig_cnt_out_sk_spl                   false
% 23.42/3.49  --abstr_cl_out                          false
% 23.42/3.49  
% 23.42/3.49  ------ Global Options
% 23.42/3.49  
% 23.42/3.49  --schedule                              default
% 23.42/3.49  --add_important_lit                     false
% 23.42/3.49  --prop_solver_per_cl                    1000
% 23.42/3.49  --min_unsat_core                        false
% 23.42/3.49  --soft_assumptions                      false
% 23.42/3.49  --soft_lemma_size                       3
% 23.42/3.49  --prop_impl_unit_size                   0
% 23.42/3.49  --prop_impl_unit                        []
% 23.42/3.49  --share_sel_clauses                     true
% 23.42/3.49  --reset_solvers                         false
% 23.42/3.49  --bc_imp_inh                            [conj_cone]
% 23.42/3.49  --conj_cone_tolerance                   3.
% 23.42/3.49  --extra_neg_conj                        none
% 23.42/3.49  --large_theory_mode                     true
% 23.42/3.49  --prolific_symb_bound                   200
% 23.42/3.49  --lt_threshold                          2000
% 23.42/3.49  --clause_weak_htbl                      true
% 23.42/3.49  --gc_record_bc_elim                     false
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing Options
% 23.42/3.49  
% 23.42/3.49  --preprocessing_flag                    true
% 23.42/3.49  --time_out_prep_mult                    0.1
% 23.42/3.49  --splitting_mode                        input
% 23.42/3.49  --splitting_grd                         true
% 23.42/3.49  --splitting_cvd                         false
% 23.42/3.49  --splitting_cvd_svl                     false
% 23.42/3.49  --splitting_nvd                         32
% 23.42/3.49  --sub_typing                            true
% 23.42/3.49  --prep_gs_sim                           true
% 23.42/3.49  --prep_unflatten                        true
% 23.42/3.49  --prep_res_sim                          true
% 23.42/3.49  --prep_upred                            true
% 23.42/3.49  --prep_sem_filter                       exhaustive
% 23.42/3.49  --prep_sem_filter_out                   false
% 23.42/3.49  --pred_elim                             true
% 23.42/3.49  --res_sim_input                         true
% 23.42/3.49  --eq_ax_congr_red                       true
% 23.42/3.49  --pure_diseq_elim                       true
% 23.42/3.49  --brand_transform                       false
% 23.42/3.49  --non_eq_to_eq                          false
% 23.42/3.49  --prep_def_merge                        true
% 23.42/3.49  --prep_def_merge_prop_impl              false
% 23.42/3.49  --prep_def_merge_mbd                    true
% 23.42/3.49  --prep_def_merge_tr_red                 false
% 23.42/3.49  --prep_def_merge_tr_cl                  false
% 23.42/3.49  --smt_preprocessing                     true
% 23.42/3.49  --smt_ac_axioms                         fast
% 23.42/3.49  --preprocessed_out                      false
% 23.42/3.49  --preprocessed_stats                    false
% 23.42/3.49  
% 23.42/3.49  ------ Abstraction refinement Options
% 23.42/3.49  
% 23.42/3.49  --abstr_ref                             []
% 23.42/3.49  --abstr_ref_prep                        false
% 23.42/3.49  --abstr_ref_until_sat                   false
% 23.42/3.49  --abstr_ref_sig_restrict                funpre
% 23.42/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.42/3.49  --abstr_ref_under                       []
% 23.42/3.49  
% 23.42/3.49  ------ SAT Options
% 23.42/3.49  
% 23.42/3.49  --sat_mode                              false
% 23.42/3.49  --sat_fm_restart_options                ""
% 23.42/3.49  --sat_gr_def                            false
% 23.42/3.49  --sat_epr_types                         true
% 23.42/3.49  --sat_non_cyclic_types                  false
% 23.42/3.49  --sat_finite_models                     false
% 23.42/3.49  --sat_fm_lemmas                         false
% 23.42/3.49  --sat_fm_prep                           false
% 23.42/3.49  --sat_fm_uc_incr                        true
% 23.42/3.49  --sat_out_model                         small
% 23.42/3.49  --sat_out_clauses                       false
% 23.42/3.49  
% 23.42/3.49  ------ QBF Options
% 23.42/3.49  
% 23.42/3.49  --qbf_mode                              false
% 23.42/3.49  --qbf_elim_univ                         false
% 23.42/3.49  --qbf_dom_inst                          none
% 23.42/3.49  --qbf_dom_pre_inst                      false
% 23.42/3.49  --qbf_sk_in                             false
% 23.42/3.49  --qbf_pred_elim                         true
% 23.42/3.49  --qbf_split                             512
% 23.42/3.49  
% 23.42/3.49  ------ BMC1 Options
% 23.42/3.49  
% 23.42/3.49  --bmc1_incremental                      false
% 23.42/3.49  --bmc1_axioms                           reachable_all
% 23.42/3.49  --bmc1_min_bound                        0
% 23.42/3.49  --bmc1_max_bound                        -1
% 23.42/3.49  --bmc1_max_bound_default                -1
% 23.42/3.49  --bmc1_symbol_reachability              true
% 23.42/3.49  --bmc1_property_lemmas                  false
% 23.42/3.49  --bmc1_k_induction                      false
% 23.42/3.49  --bmc1_non_equiv_states                 false
% 23.42/3.49  --bmc1_deadlock                         false
% 23.42/3.49  --bmc1_ucm                              false
% 23.42/3.49  --bmc1_add_unsat_core                   none
% 23.42/3.49  --bmc1_unsat_core_children              false
% 23.42/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.42/3.49  --bmc1_out_stat                         full
% 23.42/3.49  --bmc1_ground_init                      false
% 23.42/3.49  --bmc1_pre_inst_next_state              false
% 23.42/3.49  --bmc1_pre_inst_state                   false
% 23.42/3.49  --bmc1_pre_inst_reach_state             false
% 23.42/3.49  --bmc1_out_unsat_core                   false
% 23.42/3.49  --bmc1_aig_witness_out                  false
% 23.42/3.49  --bmc1_verbose                          false
% 23.42/3.49  --bmc1_dump_clauses_tptp                false
% 23.42/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.42/3.49  --bmc1_dump_file                        -
% 23.42/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.42/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.42/3.49  --bmc1_ucm_extend_mode                  1
% 23.42/3.49  --bmc1_ucm_init_mode                    2
% 23.42/3.49  --bmc1_ucm_cone_mode                    none
% 23.42/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.42/3.49  --bmc1_ucm_relax_model                  4
% 23.42/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.42/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.42/3.49  --bmc1_ucm_layered_model                none
% 23.42/3.49  --bmc1_ucm_max_lemma_size               10
% 23.42/3.49  
% 23.42/3.49  ------ AIG Options
% 23.42/3.49  
% 23.42/3.49  --aig_mode                              false
% 23.42/3.49  
% 23.42/3.49  ------ Instantiation Options
% 23.42/3.49  
% 23.42/3.49  --instantiation_flag                    true
% 23.42/3.49  --inst_sos_flag                         true
% 23.42/3.49  --inst_sos_phase                        true
% 23.42/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.42/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.42/3.49  --inst_lit_sel_side                     none
% 23.42/3.49  --inst_solver_per_active                1400
% 23.42/3.49  --inst_solver_calls_frac                1.
% 23.42/3.49  --inst_passive_queue_type               priority_queues
% 23.42/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.42/3.49  --inst_passive_queues_freq              [25;2]
% 23.42/3.49  --inst_dismatching                      true
% 23.42/3.49  --inst_eager_unprocessed_to_passive     true
% 23.42/3.49  --inst_prop_sim_given                   true
% 23.42/3.49  --inst_prop_sim_new                     false
% 23.42/3.49  --inst_subs_new                         false
% 23.42/3.49  --inst_eq_res_simp                      false
% 23.42/3.49  --inst_subs_given                       false
% 23.42/3.49  --inst_orphan_elimination               true
% 23.42/3.49  --inst_learning_loop_flag               true
% 23.42/3.49  --inst_learning_start                   3000
% 23.42/3.49  --inst_learning_factor                  2
% 23.42/3.49  --inst_start_prop_sim_after_learn       3
% 23.42/3.49  --inst_sel_renew                        solver
% 23.42/3.49  --inst_lit_activity_flag                true
% 23.42/3.49  --inst_restr_to_given                   false
% 23.42/3.49  --inst_activity_threshold               500
% 23.42/3.49  --inst_out_proof                        true
% 23.42/3.49  
% 23.42/3.49  ------ Resolution Options
% 23.42/3.49  
% 23.42/3.49  --resolution_flag                       false
% 23.42/3.49  --res_lit_sel                           adaptive
% 23.42/3.49  --res_lit_sel_side                      none
% 23.42/3.49  --res_ordering                          kbo
% 23.42/3.49  --res_to_prop_solver                    active
% 23.42/3.49  --res_prop_simpl_new                    false
% 23.42/3.49  --res_prop_simpl_given                  true
% 23.42/3.49  --res_passive_queue_type                priority_queues
% 23.42/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.42/3.49  --res_passive_queues_freq               [15;5]
% 23.42/3.49  --res_forward_subs                      full
% 23.42/3.49  --res_backward_subs                     full
% 23.42/3.49  --res_forward_subs_resolution           true
% 23.42/3.49  --res_backward_subs_resolution          true
% 23.42/3.49  --res_orphan_elimination                true
% 23.42/3.49  --res_time_limit                        2.
% 23.42/3.49  --res_out_proof                         true
% 23.42/3.49  
% 23.42/3.49  ------ Superposition Options
% 23.42/3.49  
% 23.42/3.49  --superposition_flag                    true
% 23.42/3.49  --sup_passive_queue_type                priority_queues
% 23.42/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.42/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.42/3.49  --demod_completeness_check              fast
% 23.42/3.49  --demod_use_ground                      true
% 23.42/3.49  --sup_to_prop_solver                    passive
% 23.42/3.49  --sup_prop_simpl_new                    true
% 23.42/3.49  --sup_prop_simpl_given                  true
% 23.42/3.49  --sup_fun_splitting                     true
% 23.42/3.49  --sup_smt_interval                      50000
% 23.42/3.49  
% 23.42/3.49  ------ Superposition Simplification Setup
% 23.42/3.49  
% 23.42/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.42/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.42/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.42/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.42/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.42/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.42/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.42/3.49  --sup_immed_triv                        [TrivRules]
% 23.42/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.42/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.42/3.49  --sup_immed_bw_main                     []
% 23.42/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.42/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.42/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.42/3.49  --sup_input_bw                          []
% 23.42/3.49  
% 23.42/3.49  ------ Combination Options
% 23.42/3.49  
% 23.42/3.49  --comb_res_mult                         3
% 23.42/3.49  --comb_sup_mult                         2
% 23.42/3.49  --comb_inst_mult                        10
% 23.42/3.49  
% 23.42/3.49  ------ Debug Options
% 23.42/3.49  
% 23.42/3.49  --dbg_backtrace                         false
% 23.42/3.49  --dbg_dump_prop_clauses                 false
% 23.42/3.49  --dbg_dump_prop_clauses_file            -
% 23.42/3.49  --dbg_out_stat                          false
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  ------ Proving...
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  % SZS status Theorem for theBenchmark.p
% 23.42/3.49  
% 23.42/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.42/3.49  
% 23.42/3.49  fof(f1,axiom,(
% 23.42/3.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f22,plain,(
% 23.42/3.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.42/3.49    inference(nnf_transformation,[],[f1])).
% 23.42/3.49  
% 23.42/3.49  fof(f23,plain,(
% 23.42/3.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.42/3.49    inference(flattening,[],[f22])).
% 23.42/3.49  
% 23.42/3.49  fof(f27,plain,(
% 23.42/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.42/3.49    inference(cnf_transformation,[],[f23])).
% 23.42/3.49  
% 23.42/3.49  fof(f52,plain,(
% 23.42/3.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.42/3.49    inference(equality_resolution,[],[f27])).
% 23.42/3.49  
% 23.42/3.49  fof(f11,conjecture,(
% 23.42/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f12,negated_conjecture,(
% 23.42/3.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 23.42/3.49    inference(negated_conjecture,[],[f11])).
% 23.42/3.49  
% 23.42/3.49  fof(f20,plain,(
% 23.42/3.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.42/3.49    inference(ennf_transformation,[],[f12])).
% 23.42/3.49  
% 23.42/3.49  fof(f21,plain,(
% 23.42/3.49    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.42/3.49    inference(flattening,[],[f20])).
% 23.42/3.49  
% 23.42/3.49  fof(f25,plain,(
% 23.42/3.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(sK2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(X0)))) )),
% 23.42/3.49    introduced(choice_axiom,[])).
% 23.42/3.49  
% 23.42/3.49  fof(f24,plain,(
% 23.42/3.49    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k3_subset_1(X0,X1)) & r1_tarski(X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(X2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 23.42/3.49    introduced(choice_axiom,[])).
% 23.42/3.49  
% 23.42/3.49  fof(f26,plain,(
% 23.42/3.49    (~r1_tarski(sK2,k3_subset_1(sK0,sK1)) & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 23.42/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25,f24])).
% 23.42/3.49  
% 23.42/3.49  fof(f42,plain,(
% 23.42/3.49    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 23.42/3.49    inference(cnf_transformation,[],[f26])).
% 23.42/3.49  
% 23.42/3.49  fof(f41,plain,(
% 23.42/3.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 23.42/3.49    inference(cnf_transformation,[],[f26])).
% 23.42/3.49  
% 23.42/3.49  fof(f8,axiom,(
% 23.42/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f17,plain,(
% 23.42/3.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.42/3.49    inference(ennf_transformation,[],[f8])).
% 23.42/3.49  
% 23.42/3.49  fof(f37,plain,(
% 23.42/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f17])).
% 23.42/3.49  
% 23.42/3.49  fof(f2,axiom,(
% 23.42/3.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f30,plain,(
% 23.42/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f2])).
% 23.42/3.49  
% 23.42/3.49  fof(f50,plain,(
% 23.42/3.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.42/3.49    inference(definition_unfolding,[],[f37,f30])).
% 23.42/3.49  
% 23.42/3.49  fof(f3,axiom,(
% 23.42/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f13,plain,(
% 23.42/3.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 23.42/3.49    inference(ennf_transformation,[],[f3])).
% 23.42/3.49  
% 23.42/3.49  fof(f32,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f13])).
% 23.42/3.49  
% 23.42/3.49  fof(f45,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 23.42/3.49    inference(definition_unfolding,[],[f32,f30])).
% 23.42/3.49  
% 23.42/3.49  fof(f4,axiom,(
% 23.42/3.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f33,plain,(
% 23.42/3.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f4])).
% 23.42/3.49  
% 23.42/3.49  fof(f47,plain,(
% 23.42/3.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 23.42/3.49    inference(definition_unfolding,[],[f33,f30])).
% 23.42/3.49  
% 23.42/3.49  fof(f7,axiom,(
% 23.42/3.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f15,plain,(
% 23.42/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 23.42/3.49    inference(ennf_transformation,[],[f7])).
% 23.42/3.49  
% 23.42/3.49  fof(f16,plain,(
% 23.42/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 23.42/3.49    inference(flattening,[],[f15])).
% 23.42/3.49  
% 23.42/3.49  fof(f36,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f16])).
% 23.42/3.49  
% 23.42/3.49  fof(f49,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 23.42/3.49    inference(definition_unfolding,[],[f36,f30])).
% 23.42/3.49  
% 23.42/3.49  fof(f29,plain,(
% 23.42/3.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f23])).
% 23.42/3.49  
% 23.42/3.49  fof(f6,axiom,(
% 23.42/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f14,plain,(
% 23.42/3.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 23.42/3.49    inference(ennf_transformation,[],[f6])).
% 23.42/3.49  
% 23.42/3.49  fof(f35,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f14])).
% 23.42/3.49  
% 23.42/3.49  fof(f48,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 23.42/3.49    inference(definition_unfolding,[],[f35,f30])).
% 23.42/3.49  
% 23.42/3.49  fof(f31,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f13])).
% 23.42/3.49  
% 23.42/3.49  fof(f46,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 23.42/3.49    inference(definition_unfolding,[],[f31,f30])).
% 23.42/3.49  
% 23.42/3.49  fof(f40,plain,(
% 23.42/3.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 23.42/3.49    inference(cnf_transformation,[],[f26])).
% 23.42/3.49  
% 23.42/3.49  fof(f43,plain,(
% 23.42/3.49    ~r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 23.42/3.49    inference(cnf_transformation,[],[f26])).
% 23.42/3.49  
% 23.42/3.49  fof(f9,axiom,(
% 23.42/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f18,plain,(
% 23.42/3.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.42/3.49    inference(ennf_transformation,[],[f9])).
% 23.42/3.49  
% 23.42/3.49  fof(f38,plain,(
% 23.42/3.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f18])).
% 23.42/3.49  
% 23.42/3.49  fof(f10,axiom,(
% 23.42/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 23.42/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f19,plain,(
% 23.42/3.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.42/3.49    inference(ennf_transformation,[],[f10])).
% 23.42/3.49  
% 23.42/3.49  fof(f39,plain,(
% 23.42/3.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f19])).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3,plain,
% 23.42/3.49      ( r1_tarski(X0,X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f52]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_598,plain,
% 23.42/3.49      ( r1_tarski(X0,X0) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_13,negated_conjecture,
% 23.42/3.49      ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
% 23.42/3.49      inference(cnf_transformation,[],[f42]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_588,plain,
% 23.42/3.49      ( r1_tarski(sK1,k3_subset_1(sK0,sK2)) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_14,negated_conjecture,
% 23.42/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 23.42/3.49      inference(cnf_transformation,[],[f41]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_587,plain,
% 23.42/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_9,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.42/3.49      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f50]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_592,plain,
% 23.42/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 23.42/3.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2071,plain,
% 23.42/3.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_subset_1(sK0,sK2) ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_587,c_592]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4,plain,
% 23.42/3.49      ( r1_xboole_0(X0,X1)
% 23.42/3.49      | ~ r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 23.42/3.49      inference(cnf_transformation,[],[f45]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_597,plain,
% 23.42/3.49      ( r1_xboole_0(X0,X1) = iProver_top
% 23.42/3.49      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2374,plain,
% 23.42/3.49      ( r1_xboole_0(X0,sK2) = iProver_top
% 23.42/3.49      | r1_tarski(X0,k3_subset_1(sK0,sK2)) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2071,c_597]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3636,plain,
% 23.42/3.49      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_588,c_2374]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_6,plain,
% 23.42/3.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f47]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_595,plain,
% 23.42/3.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8,plain,
% 23.42/3.49      ( ~ r1_xboole_0(X0,X1)
% 23.42/3.49      | ~ r1_tarski(X0,X2)
% 23.42/3.49      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 23.42/3.49      inference(cnf_transformation,[],[f49]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_593,plain,
% 23.42/3.49      ( r1_xboole_0(X0,X1) != iProver_top
% 23.42/3.49      | r1_tarski(X0,X2) != iProver_top
% 23.42/3.49      | r1_tarski(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.42/3.49      inference(cnf_transformation,[],[f29]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_599,plain,
% 23.42/3.49      ( X0 = X1
% 23.42/3.49      | r1_tarski(X0,X1) != iProver_top
% 23.42/3.49      | r1_tarski(X1,X0) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2187,plain,
% 23.42/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 23.42/3.49      | r1_xboole_0(X2,X1) != iProver_top
% 23.42/3.49      | r1_tarski(X2,X0) != iProver_top
% 23.42/3.49      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_593,c_599]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_23536,plain,
% 23.42/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 23.42/3.49      | r1_xboole_0(X0,X1) != iProver_top
% 23.42/3.49      | r1_tarski(X0,X0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_595,c_2187]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_44,plain,
% 23.42/3.49      ( r1_tarski(X0,X0) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_84260,plain,
% 23.42/3.49      ( r1_xboole_0(X0,X1) != iProver_top
% 23.42/3.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_23536,c_44]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_84261,plain,
% 23.42/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 23.42/3.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 23.42/3.49      inference(renaming,[status(thm)],[c_84260]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_84278,plain,
% 23.42/3.49      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = sK1 ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_3636,c_84261]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_7,plain,
% 23.42/3.49      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 23.42/3.49      | ~ r1_tarski(X0,X2) ),
% 23.42/3.49      inference(cnf_transformation,[],[f48]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_594,plain,
% 23.42/3.49      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top
% 23.42/3.49      | r1_tarski(X0,X2) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_85148,plain,
% 23.42/3.49      ( r1_xboole_0(X0,sK1) = iProver_top
% 23.42/3.49      | r1_tarski(X0,sK2) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_84278,c_594]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_91993,plain,
% 23.42/3.49      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_598,c_85148]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5,plain,
% 23.42/3.49      ( r1_tarski(X0,X1)
% 23.42/3.49      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 23.42/3.49      inference(cnf_transformation,[],[f46]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_704,plain,
% 23.42/3.49      ( r1_tarski(sK2,X0)
% 23.42/3.49      | ~ r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_5]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5549,plain,
% 23.42/3.49      ( r1_tarski(sK2,X0)
% 23.42/3.49      | ~ r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2)))) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_704]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5550,plain,
% 23.42/3.49      ( r1_tarski(sK2,X0) = iProver_top
% 23.42/3.49      | r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2)))) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_5549]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5552,plain,
% 23.42/3.49      ( r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))) != iProver_top
% 23.42/3.49      | r1_tarski(sK2,sK0) = iProver_top ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_5550]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_15,negated_conjecture,
% 23.42/3.49      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 23.42/3.49      inference(cnf_transformation,[],[f40]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_586,plain,
% 23.42/3.49      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2072,plain,
% 23.42/3.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_586,c_592]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2401,plain,
% 23.42/3.49      ( r1_xboole_0(X0,sK1) != iProver_top
% 23.42/3.49      | r1_tarski(X0,k3_subset_1(sK0,sK1)) = iProver_top
% 23.42/3.49      | r1_tarski(X0,sK0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2072,c_593]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_12,negated_conjecture,
% 23.42/3.49      ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
% 23.42/3.49      inference(cnf_transformation,[],[f43]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_589,plain,
% 23.42/3.49      ( r1_tarski(sK2,k3_subset_1(sK0,sK1)) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4731,plain,
% 23.42/3.49      ( r1_xboole_0(sK2,sK1) != iProver_top
% 23.42/3.49      | r1_tarski(sK2,sK0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2401,c_589]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2343,plain,
% 23.42/3.49      ( r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2))) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_3]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2344,plain,
% 23.42/3.49      ( r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2))) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_2343]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2346,plain,
% 23.42/3.49      ( r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) = iProver_top ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_2344]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_10,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.42/3.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 23.42/3.49      inference(cnf_transformation,[],[f38]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2285,plain,
% 23.42/3.49      ( m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))
% 23.42/3.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_10]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2287,plain,
% 23.42/3.49      ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
% 23.42/3.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_2285]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_338,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.42/3.49      theory(equality) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_717,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_338]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1048,plain,
% 23.42/3.49      ( ~ r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),X1)
% 23.42/3.49      | r1_tarski(sK2,X2)
% 23.42/3.49      | X2 != X1
% 23.42/3.49      | sK2 != k3_subset_1(X0,k3_subset_1(X0,sK2)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_717]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1181,plain,
% 23.42/3.49      ( ~ r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2)))
% 23.42/3.49      | r1_tarski(sK2,X1)
% 23.42/3.49      | X1 != k3_subset_1(X0,k3_subset_1(X0,sK2))
% 23.42/3.49      | sK2 != k3_subset_1(X0,k3_subset_1(X0,sK2)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_1048]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1658,plain,
% 23.42/3.49      ( ~ r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2)))
% 23.42/3.49      | r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2))))
% 23.42/3.49      | k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2))) != k3_subset_1(X0,k3_subset_1(X0,sK2))
% 23.42/3.49      | sK2 != k3_subset_1(X0,k3_subset_1(X0,sK2)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_1181]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1659,plain,
% 23.42/3.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2))) != k3_subset_1(X0,k3_subset_1(X0,sK2))
% 23.42/3.49      | sK2 != k3_subset_1(X0,k3_subset_1(X0,sK2))
% 23.42/3.49      | r1_tarski(k3_subset_1(X0,k3_subset_1(X0,sK2)),k3_subset_1(X0,k3_subset_1(X0,sK2))) != iProver_top
% 23.42/3.49      | r1_tarski(sK2,k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2)))) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_1658]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1661,plain,
% 23.42/3.49      ( k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) != k3_subset_1(sK0,k3_subset_1(sK0,sK2))
% 23.42/3.49      | sK2 != k3_subset_1(sK0,k3_subset_1(sK0,sK2))
% 23.42/3.49      | r1_tarski(k3_subset_1(sK0,k3_subset_1(sK0,sK2)),k3_subset_1(sK0,k3_subset_1(sK0,sK2))) != iProver_top
% 23.42/3.49      | r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2)))) = iProver_top ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_1659]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1367,plain,
% 23.42/3.49      ( ~ m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))
% 23.42/3.49      | k5_xboole_0(X0,k3_xboole_0(X0,k3_subset_1(X0,sK2))) = k3_subset_1(X0,k3_subset_1(X0,sK2)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_9]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1369,plain,
% 23.42/3.49      ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
% 23.42/3.49      | k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK2))) = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_1367]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_11,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.42/3.49      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 23.42/3.49      inference(cnf_transformation,[],[f39]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_836,plain,
% 23.42/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 23.42/3.49      | k3_subset_1(X0,k3_subset_1(X0,sK2)) = sK2 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_11]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_838,plain,
% 23.42/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 23.42/3.49      | k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_836]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_335,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_649,plain,
% 23.42/3.49      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_335]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_691,plain,
% 23.42/3.49      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_649]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_737,plain,
% 23.42/3.49      ( k3_subset_1(X0,k3_subset_1(X0,sK2)) != sK2
% 23.42/3.49      | sK2 = k3_subset_1(X0,k3_subset_1(X0,sK2))
% 23.42/3.49      | sK2 != sK2 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_691]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_738,plain,
% 23.42/3.49      ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) != sK2
% 23.42/3.49      | sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
% 23.42/3.49      | sK2 != sK2 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_737]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_334,plain,( X0 = X0 ),theory(equality) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_655,plain,
% 23.42/3.49      ( sK2 = sK2 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_334]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(contradiction,plain,
% 23.42/3.49      ( $false ),
% 23.42/3.49      inference(minisat,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_91993,c_5552,c_4731,c_2346,c_2287,c_1661,c_1369,c_838,
% 23.42/3.49                 c_738,c_655,c_14]) ).
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.42/3.49  
% 23.42/3.49  ------                               Statistics
% 23.42/3.49  
% 23.42/3.49  ------ General
% 23.42/3.49  
% 23.42/3.49  abstr_ref_over_cycles:                  0
% 23.42/3.49  abstr_ref_under_cycles:                 0
% 23.42/3.49  gc_basic_clause_elim:                   0
% 23.42/3.49  forced_gc_time:                         0
% 23.42/3.49  parsing_time:                           0.026
% 23.42/3.49  unif_index_cands_time:                  0.
% 23.42/3.49  unif_index_add_time:                    0.
% 23.42/3.49  orderings_time:                         0.
% 23.42/3.49  out_proof_time:                         0.015
% 23.42/3.49  total_time:                             2.848
% 23.42/3.49  num_of_symbols:                         41
% 23.42/3.49  num_of_terms:                           87011
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing
% 23.42/3.49  
% 23.42/3.49  num_of_splits:                          0
% 23.42/3.49  num_of_split_atoms:                     0
% 23.42/3.49  num_of_reused_defs:                     0
% 23.42/3.49  num_eq_ax_congr_red:                    9
% 23.42/3.49  num_of_sem_filtered_clauses:            1
% 23.42/3.49  num_of_subtypes:                        0
% 23.42/3.49  monotx_restored_types:                  0
% 23.42/3.49  sat_num_of_epr_types:                   0
% 23.42/3.49  sat_num_of_non_cyclic_types:            0
% 23.42/3.49  sat_guarded_non_collapsed_types:        0
% 23.42/3.49  num_pure_diseq_elim:                    0
% 23.42/3.49  simp_replaced_by:                       0
% 23.42/3.49  res_preprocessed:                       79
% 23.42/3.49  prep_upred:                             0
% 23.42/3.49  prep_unflattend:                        4
% 23.42/3.49  smt_new_axioms:                         0
% 23.42/3.49  pred_elim_cands:                        3
% 23.42/3.49  pred_elim:                              0
% 23.42/3.49  pred_elim_cl:                           0
% 23.42/3.49  pred_elim_cycles:                       2
% 23.42/3.49  merged_defs:                            0
% 23.42/3.49  merged_defs_ncl:                        0
% 23.42/3.49  bin_hyper_res:                          0
% 23.42/3.49  prep_cycles:                            4
% 23.42/3.49  pred_elim_time:                         0.001
% 23.42/3.49  splitting_time:                         0.
% 23.42/3.49  sem_filter_time:                        0.
% 23.42/3.49  monotx_time:                            0.
% 23.42/3.49  subtype_inf_time:                       0.
% 23.42/3.49  
% 23.42/3.49  ------ Problem properties
% 23.42/3.49  
% 23.42/3.49  clauses:                                15
% 23.42/3.49  conjectures:                            4
% 23.42/3.49  epr:                                    2
% 23.42/3.49  horn:                                   15
% 23.42/3.49  ground:                                 4
% 23.42/3.49  unary:                                  7
% 23.42/3.49  binary:                                 6
% 23.42/3.49  lits:                                   25
% 23.42/3.49  lits_eq:                                4
% 23.42/3.49  fd_pure:                                0
% 23.42/3.49  fd_pseudo:                              0
% 23.42/3.49  fd_cond:                                0
% 23.42/3.49  fd_pseudo_cond:                         1
% 23.42/3.49  ac_symbols:                             0
% 23.42/3.49  
% 23.42/3.49  ------ Propositional Solver
% 23.42/3.49  
% 23.42/3.49  prop_solver_calls:                      36
% 23.42/3.49  prop_fast_solver_calls:                 1092
% 23.42/3.49  smt_solver_calls:                       0
% 23.42/3.49  smt_fast_solver_calls:                  0
% 23.42/3.49  prop_num_of_clauses:                    33617
% 23.42/3.49  prop_preprocess_simplified:             60239
% 23.42/3.49  prop_fo_subsumed:                       10
% 23.42/3.49  prop_solver_time:                       0.
% 23.42/3.49  smt_solver_time:                        0.
% 23.42/3.49  smt_fast_solver_time:                   0.
% 23.42/3.49  prop_fast_solver_time:                  0.
% 23.42/3.49  prop_unsat_core_time:                   0.003
% 23.42/3.49  
% 23.42/3.49  ------ QBF
% 23.42/3.49  
% 23.42/3.49  qbf_q_res:                              0
% 23.42/3.49  qbf_num_tautologies:                    0
% 23.42/3.49  qbf_prep_cycles:                        0
% 23.42/3.49  
% 23.42/3.49  ------ BMC1
% 23.42/3.49  
% 23.42/3.49  bmc1_current_bound:                     -1
% 23.42/3.49  bmc1_last_solved_bound:                 -1
% 23.42/3.49  bmc1_unsat_core_size:                   -1
% 23.42/3.49  bmc1_unsat_core_parents_size:           -1
% 23.42/3.49  bmc1_merge_next_fun:                    0
% 23.42/3.49  bmc1_unsat_core_clauses_time:           0.
% 23.42/3.49  
% 23.42/3.49  ------ Instantiation
% 23.42/3.49  
% 23.42/3.49  inst_num_of_clauses:                    8024
% 23.42/3.49  inst_num_in_passive:                    4173
% 23.42/3.49  inst_num_in_active:                     2730
% 23.42/3.49  inst_num_in_unprocessed:                1123
% 23.42/3.49  inst_num_of_loops:                      2860
% 23.42/3.49  inst_num_of_learning_restarts:          0
% 23.42/3.49  inst_num_moves_active_passive:          123
% 23.42/3.49  inst_lit_activity:                      0
% 23.42/3.49  inst_lit_activity_moves:                0
% 23.42/3.49  inst_num_tautologies:                   0
% 23.42/3.49  inst_num_prop_implied:                  0
% 23.42/3.49  inst_num_existing_simplified:           0
% 23.42/3.49  inst_num_eq_res_simplified:             0
% 23.42/3.49  inst_num_child_elim:                    0
% 23.42/3.49  inst_num_of_dismatching_blockings:      11859
% 23.42/3.49  inst_num_of_non_proper_insts:           14276
% 23.42/3.49  inst_num_of_duplicates:                 0
% 23.42/3.49  inst_inst_num_from_inst_to_res:         0
% 23.42/3.49  inst_dismatching_checking_time:         0.
% 23.42/3.49  
% 23.42/3.49  ------ Resolution
% 23.42/3.49  
% 23.42/3.49  res_num_of_clauses:                     0
% 23.42/3.49  res_num_in_passive:                     0
% 23.42/3.49  res_num_in_active:                      0
% 23.42/3.49  res_num_of_loops:                       83
% 23.42/3.49  res_forward_subset_subsumed:            1307
% 23.42/3.49  res_backward_subset_subsumed:           16
% 23.42/3.49  res_forward_subsumed:                   0
% 23.42/3.49  res_backward_subsumed:                  0
% 23.42/3.49  res_forward_subsumption_resolution:     0
% 23.42/3.49  res_backward_subsumption_resolution:    0
% 23.42/3.49  res_clause_to_clause_subsumption:       20739
% 23.42/3.49  res_orphan_elimination:                 0
% 23.42/3.49  res_tautology_del:                      1117
% 23.42/3.49  res_num_eq_res_simplified:              0
% 23.42/3.49  res_num_sel_changes:                    0
% 23.42/3.49  res_moves_from_active_to_pass:          0
% 23.42/3.49  
% 23.42/3.49  ------ Superposition
% 23.42/3.49  
% 23.42/3.49  sup_time_total:                         0.
% 23.42/3.49  sup_time_generating:                    0.
% 23.42/3.49  sup_time_sim_full:                      0.
% 23.42/3.49  sup_time_sim_immed:                     0.
% 23.42/3.49  
% 23.42/3.49  sup_num_of_clauses:                     2124
% 23.42/3.49  sup_num_in_active:                      304
% 23.42/3.49  sup_num_in_passive:                     1820
% 23.42/3.49  sup_num_of_loops:                       570
% 23.42/3.49  sup_fw_superposition:                   3544
% 23.42/3.49  sup_bw_superposition:                   3706
% 23.42/3.49  sup_immediate_simplified:               2374
% 23.42/3.49  sup_given_eliminated:                   1
% 23.42/3.49  comparisons_done:                       0
% 23.42/3.49  comparisons_avoided:                    0
% 23.42/3.49  
% 23.42/3.49  ------ Simplifications
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  sim_fw_subset_subsumed:                 32
% 23.42/3.49  sim_bw_subset_subsumed:                 4
% 23.42/3.49  sim_fw_subsumed:                        1235
% 23.42/3.49  sim_bw_subsumed:                        46
% 23.42/3.49  sim_fw_subsumption_res:                 0
% 23.42/3.49  sim_bw_subsumption_res:                 0
% 23.42/3.49  sim_tautology_del:                      61
% 23.42/3.49  sim_eq_tautology_del:                   111
% 23.42/3.49  sim_eq_res_simp:                        0
% 23.42/3.49  sim_fw_demodulated:                     518
% 23.42/3.49  sim_bw_demodulated:                     270
% 23.42/3.49  sim_light_normalised:                   711
% 23.42/3.49  sim_joinable_taut:                      0
% 23.42/3.49  sim_joinable_simp:                      0
% 23.42/3.49  sim_ac_normalised:                      0
% 23.42/3.49  sim_smt_subsumption:                    0
% 23.42/3.49  
%------------------------------------------------------------------------------
