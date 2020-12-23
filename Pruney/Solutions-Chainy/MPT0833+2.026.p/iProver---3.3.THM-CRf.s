%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:57 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 204 expanded)
%              Number of clauses        :   60 (  79 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   22
%              Number of atoms          :  244 ( 544 expanded)
%              Number of equality atoms :   85 ( 105 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4)
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4)
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f32])).

fof(f48,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_626,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_637,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_625,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_628,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1146,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_625,c_628])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_629,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1500,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_629])).

cnf(c_16,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1982,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1500,c_16])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1987,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1982,c_633])).

cnf(c_2112,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),X0),sK2) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_1987])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_638,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3473,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2112,c_638])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_634,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3629,plain,
    ( k2_xboole_0(k2_relat_1(sK4),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_3473,c_634])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_635,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4313,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3629,c_635])).

cnf(c_5653,plain,
    ( k2_xboole_0(k2_relat_1(sK4),X0) = X0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4313,c_634])).

cnf(c_5670,plain,
    ( k2_xboole_0(k2_relat_1(sK4),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_626,c_5653])).

cnf(c_1080,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_638])).

cnf(c_1343,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1080,c_635])).

cnf(c_5848,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5670,c_1343])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_630,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5878,plain,
    ( k8_relat_1(sK3,sK4) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5848,c_630])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_787,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_788,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_857,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_858,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_857])).

cnf(c_6218,plain,
    ( k8_relat_1(sK3,sK4) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5878,c_16,c_788,c_858])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_627,plain,
    ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_988,plain,
    ( k6_relset_1(sK1,sK2,X0,sK4) = k8_relat_1(X0,sK4) ),
    inference(superposition,[status(thm)],[c_625,c_627])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_182,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(sK1,sK2,sK3,sK4) != X3
    | sK4 != X3
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_13])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_182])).

cnf(c_309,plain,
    ( ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sP0_iProver_split
    | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_183])).

cnf(c_623,plain,
    ( sK4 != k6_relset_1(sK1,sK2,sK3,sK4)
    | m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_183])).

cnf(c_624,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_704,plain,
    ( k6_relset_1(sK1,sK2,sK3,sK4) != sK4
    | m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_623,c_624])).

cnf(c_1230,plain,
    ( k8_relat_1(sK3,sK4) != sK4
    | m1_subset_1(k8_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_988,c_704])).

cnf(c_6221,plain,
    ( sK4 != sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6218,c_1230])).

cnf(c_311,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_811,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6221,c_811,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:36:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.52/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.99  
% 2.52/0.99  ------  iProver source info
% 2.52/0.99  
% 2.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.99  git: non_committed_changes: false
% 2.52/0.99  git: last_make_outside_of_git: false
% 2.52/0.99  
% 2.52/0.99  ------ 
% 2.52/0.99  
% 2.52/0.99  ------ Input Options
% 2.52/0.99  
% 2.52/0.99  --out_options                           all
% 2.52/0.99  --tptp_safe_out                         true
% 2.52/0.99  --problem_path                          ""
% 2.52/0.99  --include_path                          ""
% 2.52/0.99  --clausifier                            res/vclausify_rel
% 2.52/0.99  --clausifier_options                    --mode clausify
% 2.52/0.99  --stdin                                 false
% 2.52/0.99  --stats_out                             all
% 2.52/0.99  
% 2.52/0.99  ------ General Options
% 2.52/0.99  
% 2.52/0.99  --fof                                   false
% 2.52/0.99  --time_out_real                         305.
% 2.52/0.99  --time_out_virtual                      -1.
% 2.52/0.99  --symbol_type_check                     false
% 2.52/0.99  --clausify_out                          false
% 2.52/0.99  --sig_cnt_out                           false
% 2.52/0.99  --trig_cnt_out                          false
% 2.52/0.99  --trig_cnt_out_tolerance                1.
% 2.52/0.99  --trig_cnt_out_sk_spl                   false
% 2.52/0.99  --abstr_cl_out                          false
% 2.52/0.99  
% 2.52/0.99  ------ Global Options
% 2.52/0.99  
% 2.52/0.99  --schedule                              default
% 2.52/0.99  --add_important_lit                     false
% 2.52/0.99  --prop_solver_per_cl                    1000
% 2.52/0.99  --min_unsat_core                        false
% 2.52/0.99  --soft_assumptions                      false
% 2.52/0.99  --soft_lemma_size                       3
% 2.52/0.99  --prop_impl_unit_size                   0
% 2.52/0.99  --prop_impl_unit                        []
% 2.52/0.99  --share_sel_clauses                     true
% 2.52/0.99  --reset_solvers                         false
% 2.52/0.99  --bc_imp_inh                            [conj_cone]
% 2.52/0.99  --conj_cone_tolerance                   3.
% 2.52/0.99  --extra_neg_conj                        none
% 2.52/0.99  --large_theory_mode                     true
% 2.52/0.99  --prolific_symb_bound                   200
% 2.52/0.99  --lt_threshold                          2000
% 2.52/0.99  --clause_weak_htbl                      true
% 2.52/0.99  --gc_record_bc_elim                     false
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing Options
% 2.52/0.99  
% 2.52/0.99  --preprocessing_flag                    true
% 2.52/0.99  --time_out_prep_mult                    0.1
% 2.52/0.99  --splitting_mode                        input
% 2.52/0.99  --splitting_grd                         true
% 2.52/0.99  --splitting_cvd                         false
% 2.52/0.99  --splitting_cvd_svl                     false
% 2.52/0.99  --splitting_nvd                         32
% 2.52/0.99  --sub_typing                            true
% 2.52/0.99  --prep_gs_sim                           true
% 2.52/0.99  --prep_unflatten                        true
% 2.52/0.99  --prep_res_sim                          true
% 2.52/0.99  --prep_upred                            true
% 2.52/0.99  --prep_sem_filter                       exhaustive
% 2.52/0.99  --prep_sem_filter_out                   false
% 2.52/0.99  --pred_elim                             true
% 2.52/0.99  --res_sim_input                         true
% 2.52/0.99  --eq_ax_congr_red                       true
% 2.52/0.99  --pure_diseq_elim                       true
% 2.52/0.99  --brand_transform                       false
% 2.52/0.99  --non_eq_to_eq                          false
% 2.52/0.99  --prep_def_merge                        true
% 2.52/0.99  --prep_def_merge_prop_impl              false
% 2.52/0.99  --prep_def_merge_mbd                    true
% 2.52/0.99  --prep_def_merge_tr_red                 false
% 2.52/0.99  --prep_def_merge_tr_cl                  false
% 2.52/0.99  --smt_preprocessing                     true
% 2.52/0.99  --smt_ac_axioms                         fast
% 2.52/0.99  --preprocessed_out                      false
% 2.52/0.99  --preprocessed_stats                    false
% 2.52/0.99  
% 2.52/0.99  ------ Abstraction refinement Options
% 2.52/0.99  
% 2.52/0.99  --abstr_ref                             []
% 2.52/0.99  --abstr_ref_prep                        false
% 2.52/0.99  --abstr_ref_until_sat                   false
% 2.52/0.99  --abstr_ref_sig_restrict                funpre
% 2.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.99  --abstr_ref_under                       []
% 2.52/0.99  
% 2.52/0.99  ------ SAT Options
% 2.52/0.99  
% 2.52/0.99  --sat_mode                              false
% 2.52/0.99  --sat_fm_restart_options                ""
% 2.52/0.99  --sat_gr_def                            false
% 2.52/0.99  --sat_epr_types                         true
% 2.52/0.99  --sat_non_cyclic_types                  false
% 2.52/0.99  --sat_finite_models                     false
% 2.52/0.99  --sat_fm_lemmas                         false
% 2.52/0.99  --sat_fm_prep                           false
% 2.52/0.99  --sat_fm_uc_incr                        true
% 2.52/0.99  --sat_out_model                         small
% 2.52/0.99  --sat_out_clauses                       false
% 2.52/0.99  
% 2.52/0.99  ------ QBF Options
% 2.52/0.99  
% 2.52/0.99  --qbf_mode                              false
% 2.52/0.99  --qbf_elim_univ                         false
% 2.52/0.99  --qbf_dom_inst                          none
% 2.52/0.99  --qbf_dom_pre_inst                      false
% 2.52/0.99  --qbf_sk_in                             false
% 2.52/0.99  --qbf_pred_elim                         true
% 2.52/0.99  --qbf_split                             512
% 2.52/0.99  
% 2.52/0.99  ------ BMC1 Options
% 2.52/0.99  
% 2.52/0.99  --bmc1_incremental                      false
% 2.52/0.99  --bmc1_axioms                           reachable_all
% 2.52/0.99  --bmc1_min_bound                        0
% 2.52/0.99  --bmc1_max_bound                        -1
% 2.52/0.99  --bmc1_max_bound_default                -1
% 2.52/0.99  --bmc1_symbol_reachability              true
% 2.52/0.99  --bmc1_property_lemmas                  false
% 2.52/0.99  --bmc1_k_induction                      false
% 2.52/0.99  --bmc1_non_equiv_states                 false
% 2.52/0.99  --bmc1_deadlock                         false
% 2.52/0.99  --bmc1_ucm                              false
% 2.52/0.99  --bmc1_add_unsat_core                   none
% 2.52/0.99  --bmc1_unsat_core_children              false
% 2.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.99  --bmc1_out_stat                         full
% 2.52/0.99  --bmc1_ground_init                      false
% 2.52/0.99  --bmc1_pre_inst_next_state              false
% 2.52/0.99  --bmc1_pre_inst_state                   false
% 2.52/0.99  --bmc1_pre_inst_reach_state             false
% 2.52/0.99  --bmc1_out_unsat_core                   false
% 2.52/0.99  --bmc1_aig_witness_out                  false
% 2.52/0.99  --bmc1_verbose                          false
% 2.52/0.99  --bmc1_dump_clauses_tptp                false
% 2.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.99  --bmc1_dump_file                        -
% 2.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.99  --bmc1_ucm_extend_mode                  1
% 2.52/0.99  --bmc1_ucm_init_mode                    2
% 2.52/0.99  --bmc1_ucm_cone_mode                    none
% 2.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.99  --bmc1_ucm_relax_model                  4
% 2.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.99  --bmc1_ucm_layered_model                none
% 2.52/0.99  --bmc1_ucm_max_lemma_size               10
% 2.52/0.99  
% 2.52/0.99  ------ AIG Options
% 2.52/0.99  
% 2.52/0.99  --aig_mode                              false
% 2.52/0.99  
% 2.52/0.99  ------ Instantiation Options
% 2.52/0.99  
% 2.52/0.99  --instantiation_flag                    true
% 2.52/0.99  --inst_sos_flag                         false
% 2.52/0.99  --inst_sos_phase                        true
% 2.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel_side                     num_symb
% 2.52/0.99  --inst_solver_per_active                1400
% 2.52/0.99  --inst_solver_calls_frac                1.
% 2.52/0.99  --inst_passive_queue_type               priority_queues
% 2.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.99  --inst_passive_queues_freq              [25;2]
% 2.52/0.99  --inst_dismatching                      true
% 2.52/0.99  --inst_eager_unprocessed_to_passive     true
% 2.52/0.99  --inst_prop_sim_given                   true
% 2.52/0.99  --inst_prop_sim_new                     false
% 2.52/0.99  --inst_subs_new                         false
% 2.52/0.99  --inst_eq_res_simp                      false
% 2.52/0.99  --inst_subs_given                       false
% 2.52/0.99  --inst_orphan_elimination               true
% 2.52/0.99  --inst_learning_loop_flag               true
% 2.52/0.99  --inst_learning_start                   3000
% 2.52/0.99  --inst_learning_factor                  2
% 2.52/0.99  --inst_start_prop_sim_after_learn       3
% 2.52/0.99  --inst_sel_renew                        solver
% 2.52/0.99  --inst_lit_activity_flag                true
% 2.52/0.99  --inst_restr_to_given                   false
% 2.52/0.99  --inst_activity_threshold               500
% 2.52/0.99  --inst_out_proof                        true
% 2.52/0.99  
% 2.52/0.99  ------ Resolution Options
% 2.52/0.99  
% 2.52/0.99  --resolution_flag                       true
% 2.52/0.99  --res_lit_sel                           adaptive
% 2.52/0.99  --res_lit_sel_side                      none
% 2.52/0.99  --res_ordering                          kbo
% 2.52/0.99  --res_to_prop_solver                    active
% 2.52/0.99  --res_prop_simpl_new                    false
% 2.52/0.99  --res_prop_simpl_given                  true
% 2.52/0.99  --res_passive_queue_type                priority_queues
% 2.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.99  --res_passive_queues_freq               [15;5]
% 2.52/0.99  --res_forward_subs                      full
% 2.52/0.99  --res_backward_subs                     full
% 2.52/0.99  --res_forward_subs_resolution           true
% 2.52/0.99  --res_backward_subs_resolution          true
% 2.52/0.99  --res_orphan_elimination                true
% 2.52/0.99  --res_time_limit                        2.
% 2.52/0.99  --res_out_proof                         true
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Options
% 2.52/0.99  
% 2.52/0.99  --superposition_flag                    true
% 2.52/0.99  --sup_passive_queue_type                priority_queues
% 2.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.99  --demod_completeness_check              fast
% 2.52/0.99  --demod_use_ground                      true
% 2.52/0.99  --sup_to_prop_solver                    passive
% 2.52/0.99  --sup_prop_simpl_new                    true
% 2.52/0.99  --sup_prop_simpl_given                  true
% 2.52/0.99  --sup_fun_splitting                     false
% 2.52/0.99  --sup_smt_interval                      50000
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Simplification Setup
% 2.52/0.99  
% 2.52/0.99  --sup_indices_passive                   []
% 2.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_full_bw                           [BwDemod]
% 2.52/0.99  --sup_immed_triv                        [TrivRules]
% 2.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_immed_bw_main                     []
% 2.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  
% 2.52/0.99  ------ Combination Options
% 2.52/0.99  
% 2.52/0.99  --comb_res_mult                         3
% 2.52/0.99  --comb_sup_mult                         2
% 2.52/0.99  --comb_inst_mult                        10
% 2.52/0.99  
% 2.52/0.99  ------ Debug Options
% 2.52/0.99  
% 2.52/0.99  --dbg_backtrace                         false
% 2.52/0.99  --dbg_dump_prop_clauses                 false
% 2.52/0.99  --dbg_dump_prop_clauses_file            -
% 2.52/0.99  --dbg_out_stat                          false
% 2.52/0.99  ------ Parsing...
% 2.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/0.99  ------ Proving...
% 2.52/0.99  ------ Problem Properties 
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  clauses                                 16
% 2.52/0.99  conjectures                             2
% 2.52/0.99  EPR                                     2
% 2.52/0.99  Horn                                    15
% 2.52/0.99  unary                                   3
% 2.52/0.99  binary                                  8
% 2.52/0.99  lits                                    34
% 2.52/0.99  lits eq                                 5
% 2.52/0.99  fd_pure                                 0
% 2.52/0.99  fd_pseudo                               0
% 2.52/0.99  fd_cond                                 0
% 2.52/0.99  fd_pseudo_cond                          0
% 2.52/0.99  AC symbols                              0
% 2.52/0.99  
% 2.52/0.99  ------ Schedule dynamic 5 is on 
% 2.52/0.99  
% 2.52/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ 
% 2.52/0.99  Current options:
% 2.52/0.99  ------ 
% 2.52/0.99  
% 2.52/0.99  ------ Input Options
% 2.52/0.99  
% 2.52/0.99  --out_options                           all
% 2.52/0.99  --tptp_safe_out                         true
% 2.52/0.99  --problem_path                          ""
% 2.52/0.99  --include_path                          ""
% 2.52/0.99  --clausifier                            res/vclausify_rel
% 2.52/0.99  --clausifier_options                    --mode clausify
% 2.52/0.99  --stdin                                 false
% 2.52/0.99  --stats_out                             all
% 2.52/0.99  
% 2.52/0.99  ------ General Options
% 2.52/0.99  
% 2.52/0.99  --fof                                   false
% 2.52/0.99  --time_out_real                         305.
% 2.52/0.99  --time_out_virtual                      -1.
% 2.52/0.99  --symbol_type_check                     false
% 2.52/0.99  --clausify_out                          false
% 2.52/0.99  --sig_cnt_out                           false
% 2.52/0.99  --trig_cnt_out                          false
% 2.52/0.99  --trig_cnt_out_tolerance                1.
% 2.52/0.99  --trig_cnt_out_sk_spl                   false
% 2.52/0.99  --abstr_cl_out                          false
% 2.52/0.99  
% 2.52/0.99  ------ Global Options
% 2.52/0.99  
% 2.52/0.99  --schedule                              default
% 2.52/0.99  --add_important_lit                     false
% 2.52/0.99  --prop_solver_per_cl                    1000
% 2.52/0.99  --min_unsat_core                        false
% 2.52/0.99  --soft_assumptions                      false
% 2.52/0.99  --soft_lemma_size                       3
% 2.52/0.99  --prop_impl_unit_size                   0
% 2.52/0.99  --prop_impl_unit                        []
% 2.52/0.99  --share_sel_clauses                     true
% 2.52/0.99  --reset_solvers                         false
% 2.52/0.99  --bc_imp_inh                            [conj_cone]
% 2.52/0.99  --conj_cone_tolerance                   3.
% 2.52/0.99  --extra_neg_conj                        none
% 2.52/0.99  --large_theory_mode                     true
% 2.52/0.99  --prolific_symb_bound                   200
% 2.52/0.99  --lt_threshold                          2000
% 2.52/0.99  --clause_weak_htbl                      true
% 2.52/0.99  --gc_record_bc_elim                     false
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing Options
% 2.52/0.99  
% 2.52/0.99  --preprocessing_flag                    true
% 2.52/0.99  --time_out_prep_mult                    0.1
% 2.52/0.99  --splitting_mode                        input
% 2.52/0.99  --splitting_grd                         true
% 2.52/0.99  --splitting_cvd                         false
% 2.52/0.99  --splitting_cvd_svl                     false
% 2.52/0.99  --splitting_nvd                         32
% 2.52/0.99  --sub_typing                            true
% 2.52/0.99  --prep_gs_sim                           true
% 2.52/0.99  --prep_unflatten                        true
% 2.52/0.99  --prep_res_sim                          true
% 2.52/0.99  --prep_upred                            true
% 2.52/0.99  --prep_sem_filter                       exhaustive
% 2.52/0.99  --prep_sem_filter_out                   false
% 2.52/0.99  --pred_elim                             true
% 2.52/0.99  --res_sim_input                         true
% 2.52/0.99  --eq_ax_congr_red                       true
% 2.52/0.99  --pure_diseq_elim                       true
% 2.52/0.99  --brand_transform                       false
% 2.52/0.99  --non_eq_to_eq                          false
% 2.52/0.99  --prep_def_merge                        true
% 2.52/0.99  --prep_def_merge_prop_impl              false
% 2.52/0.99  --prep_def_merge_mbd                    true
% 2.52/0.99  --prep_def_merge_tr_red                 false
% 2.52/0.99  --prep_def_merge_tr_cl                  false
% 2.52/0.99  --smt_preprocessing                     true
% 2.52/0.99  --smt_ac_axioms                         fast
% 2.52/0.99  --preprocessed_out                      false
% 2.52/0.99  --preprocessed_stats                    false
% 2.52/0.99  
% 2.52/0.99  ------ Abstraction refinement Options
% 2.52/0.99  
% 2.52/0.99  --abstr_ref                             []
% 2.52/0.99  --abstr_ref_prep                        false
% 2.52/0.99  --abstr_ref_until_sat                   false
% 2.52/0.99  --abstr_ref_sig_restrict                funpre
% 2.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.99  --abstr_ref_under                       []
% 2.52/0.99  
% 2.52/0.99  ------ SAT Options
% 2.52/0.99  
% 2.52/0.99  --sat_mode                              false
% 2.52/0.99  --sat_fm_restart_options                ""
% 2.52/0.99  --sat_gr_def                            false
% 2.52/0.99  --sat_epr_types                         true
% 2.52/0.99  --sat_non_cyclic_types                  false
% 2.52/0.99  --sat_finite_models                     false
% 2.52/0.99  --sat_fm_lemmas                         false
% 2.52/0.99  --sat_fm_prep                           false
% 2.52/0.99  --sat_fm_uc_incr                        true
% 2.52/0.99  --sat_out_model                         small
% 2.52/0.99  --sat_out_clauses                       false
% 2.52/0.99  
% 2.52/0.99  ------ QBF Options
% 2.52/0.99  
% 2.52/0.99  --qbf_mode                              false
% 2.52/0.99  --qbf_elim_univ                         false
% 2.52/0.99  --qbf_dom_inst                          none
% 2.52/0.99  --qbf_dom_pre_inst                      false
% 2.52/0.99  --qbf_sk_in                             false
% 2.52/0.99  --qbf_pred_elim                         true
% 2.52/0.99  --qbf_split                             512
% 2.52/0.99  
% 2.52/0.99  ------ BMC1 Options
% 2.52/0.99  
% 2.52/0.99  --bmc1_incremental                      false
% 2.52/0.99  --bmc1_axioms                           reachable_all
% 2.52/0.99  --bmc1_min_bound                        0
% 2.52/0.99  --bmc1_max_bound                        -1
% 2.52/0.99  --bmc1_max_bound_default                -1
% 2.52/0.99  --bmc1_symbol_reachability              true
% 2.52/0.99  --bmc1_property_lemmas                  false
% 2.52/0.99  --bmc1_k_induction                      false
% 2.52/0.99  --bmc1_non_equiv_states                 false
% 2.52/0.99  --bmc1_deadlock                         false
% 2.52/0.99  --bmc1_ucm                              false
% 2.52/0.99  --bmc1_add_unsat_core                   none
% 2.52/0.99  --bmc1_unsat_core_children              false
% 2.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.99  --bmc1_out_stat                         full
% 2.52/0.99  --bmc1_ground_init                      false
% 2.52/0.99  --bmc1_pre_inst_next_state              false
% 2.52/0.99  --bmc1_pre_inst_state                   false
% 2.52/0.99  --bmc1_pre_inst_reach_state             false
% 2.52/0.99  --bmc1_out_unsat_core                   false
% 2.52/0.99  --bmc1_aig_witness_out                  false
% 2.52/0.99  --bmc1_verbose                          false
% 2.52/0.99  --bmc1_dump_clauses_tptp                false
% 2.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.99  --bmc1_dump_file                        -
% 2.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.99  --bmc1_ucm_extend_mode                  1
% 2.52/0.99  --bmc1_ucm_init_mode                    2
% 2.52/0.99  --bmc1_ucm_cone_mode                    none
% 2.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.99  --bmc1_ucm_relax_model                  4
% 2.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.99  --bmc1_ucm_layered_model                none
% 2.52/0.99  --bmc1_ucm_max_lemma_size               10
% 2.52/0.99  
% 2.52/0.99  ------ AIG Options
% 2.52/0.99  
% 2.52/0.99  --aig_mode                              false
% 2.52/0.99  
% 2.52/0.99  ------ Instantiation Options
% 2.52/0.99  
% 2.52/0.99  --instantiation_flag                    true
% 2.52/0.99  --inst_sos_flag                         false
% 2.52/0.99  --inst_sos_phase                        true
% 2.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel_side                     none
% 2.52/0.99  --inst_solver_per_active                1400
% 2.52/0.99  --inst_solver_calls_frac                1.
% 2.52/0.99  --inst_passive_queue_type               priority_queues
% 2.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.99  --inst_passive_queues_freq              [25;2]
% 2.52/0.99  --inst_dismatching                      true
% 2.52/0.99  --inst_eager_unprocessed_to_passive     true
% 2.52/0.99  --inst_prop_sim_given                   true
% 2.52/0.99  --inst_prop_sim_new                     false
% 2.52/0.99  --inst_subs_new                         false
% 2.52/0.99  --inst_eq_res_simp                      false
% 2.52/0.99  --inst_subs_given                       false
% 2.52/0.99  --inst_orphan_elimination               true
% 2.52/0.99  --inst_learning_loop_flag               true
% 2.52/0.99  --inst_learning_start                   3000
% 2.52/0.99  --inst_learning_factor                  2
% 2.52/0.99  --inst_start_prop_sim_after_learn       3
% 2.52/0.99  --inst_sel_renew                        solver
% 2.52/0.99  --inst_lit_activity_flag                true
% 2.52/0.99  --inst_restr_to_given                   false
% 2.52/0.99  --inst_activity_threshold               500
% 2.52/0.99  --inst_out_proof                        true
% 2.52/0.99  
% 2.52/0.99  ------ Resolution Options
% 2.52/0.99  
% 2.52/0.99  --resolution_flag                       false
% 2.52/0.99  --res_lit_sel                           adaptive
% 2.52/0.99  --res_lit_sel_side                      none
% 2.52/0.99  --res_ordering                          kbo
% 2.52/0.99  --res_to_prop_solver                    active
% 2.52/0.99  --res_prop_simpl_new                    false
% 2.52/0.99  --res_prop_simpl_given                  true
% 2.52/0.99  --res_passive_queue_type                priority_queues
% 2.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.99  --res_passive_queues_freq               [15;5]
% 2.52/0.99  --res_forward_subs                      full
% 2.52/0.99  --res_backward_subs                     full
% 2.52/0.99  --res_forward_subs_resolution           true
% 2.52/0.99  --res_backward_subs_resolution          true
% 2.52/0.99  --res_orphan_elimination                true
% 2.52/0.99  --res_time_limit                        2.
% 2.52/0.99  --res_out_proof                         true
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Options
% 2.52/0.99  
% 2.52/0.99  --superposition_flag                    true
% 2.52/0.99  --sup_passive_queue_type                priority_queues
% 2.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.99  --demod_completeness_check              fast
% 2.52/0.99  --demod_use_ground                      true
% 2.52/0.99  --sup_to_prop_solver                    passive
% 2.52/0.99  --sup_prop_simpl_new                    true
% 2.52/0.99  --sup_prop_simpl_given                  true
% 2.52/0.99  --sup_fun_splitting                     false
% 2.52/0.99  --sup_smt_interval                      50000
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Simplification Setup
% 2.52/0.99  
% 2.52/0.99  --sup_indices_passive                   []
% 2.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_full_bw                           [BwDemod]
% 2.52/0.99  --sup_immed_triv                        [TrivRules]
% 2.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_immed_bw_main                     []
% 2.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  
% 2.52/0.99  ------ Combination Options
% 2.52/0.99  
% 2.52/0.99  --comb_res_mult                         3
% 2.52/0.99  --comb_sup_mult                         2
% 2.52/0.99  --comb_inst_mult                        10
% 2.52/0.99  
% 2.52/0.99  ------ Debug Options
% 2.52/0.99  
% 2.52/0.99  --dbg_backtrace                         false
% 2.52/0.99  --dbg_dump_prop_clauses                 false
% 2.52/0.99  --dbg_dump_prop_clauses_file            -
% 2.52/0.99  --dbg_out_stat                          false
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ Proving...
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS status Theorem for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  fof(f12,conjecture,(
% 2.52/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f13,negated_conjecture,(
% 2.52/1.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 2.52/1.00    inference(negated_conjecture,[],[f12])).
% 2.52/1.00  
% 2.52/1.00  fof(f26,plain,(
% 2.52/1.00    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.00    inference(ennf_transformation,[],[f13])).
% 2.52/1.00  
% 2.52/1.00  fof(f27,plain,(
% 2.52/1.00    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.00    inference(flattening,[],[f26])).
% 2.52/1.00  
% 2.52/1.00  fof(f32,plain,(
% 2.52/1.00    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 2.52/1.00    introduced(choice_axiom,[])).
% 2.52/1.00  
% 2.52/1.00  fof(f33,plain,(
% 2.52/1.00    ~r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f27,f32])).
% 2.52/1.00  
% 2.52/1.00  fof(f48,plain,(
% 2.52/1.00    r1_tarski(sK2,sK3)),
% 2.52/1.00    inference(cnf_transformation,[],[f33])).
% 2.52/1.00  
% 2.52/1.00  fof(f1,axiom,(
% 2.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f14,plain,(
% 2.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f1])).
% 2.52/1.00  
% 2.52/1.00  fof(f28,plain,(
% 2.52/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.52/1.00    inference(nnf_transformation,[],[f14])).
% 2.52/1.00  
% 2.52/1.00  fof(f29,plain,(
% 2.52/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.52/1.00    inference(rectify,[],[f28])).
% 2.52/1.00  
% 2.52/1.00  fof(f30,plain,(
% 2.52/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.52/1.00    introduced(choice_axiom,[])).
% 2.52/1.00  
% 2.52/1.00  fof(f31,plain,(
% 2.52/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.52/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.52/1.00  
% 2.52/1.00  fof(f35,plain,(
% 2.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f31])).
% 2.52/1.00  
% 2.52/1.00  fof(f47,plain,(
% 2.52/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.52/1.00    inference(cnf_transformation,[],[f33])).
% 2.52/1.00  
% 2.52/1.00  fof(f9,axiom,(
% 2.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f22,plain,(
% 2.52/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.00    inference(ennf_transformation,[],[f9])).
% 2.52/1.00  
% 2.52/1.00  fof(f44,plain,(
% 2.52/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.00    inference(cnf_transformation,[],[f22])).
% 2.52/1.00  
% 2.52/1.00  fof(f8,axiom,(
% 2.52/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f21,plain,(
% 2.52/1.00    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.00    inference(ennf_transformation,[],[f8])).
% 2.52/1.00  
% 2.52/1.00  fof(f43,plain,(
% 2.52/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.00    inference(cnf_transformation,[],[f21])).
% 2.52/1.00  
% 2.52/1.00  fof(f4,axiom,(
% 2.52/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f17,plain,(
% 2.52/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.52/1.00    inference(ennf_transformation,[],[f4])).
% 2.52/1.00  
% 2.52/1.00  fof(f39,plain,(
% 2.52/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.52/1.00    inference(cnf_transformation,[],[f17])).
% 2.52/1.00  
% 2.52/1.00  fof(f36,plain,(
% 2.52/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f31])).
% 2.52/1.00  
% 2.52/1.00  fof(f3,axiom,(
% 2.52/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f16,plain,(
% 2.52/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.52/1.00    inference(ennf_transformation,[],[f3])).
% 2.52/1.00  
% 2.52/1.00  fof(f38,plain,(
% 2.52/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f16])).
% 2.52/1.00  
% 2.52/1.00  fof(f2,axiom,(
% 2.52/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f15,plain,(
% 2.52/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.52/1.00    inference(ennf_transformation,[],[f2])).
% 2.52/1.00  
% 2.52/1.00  fof(f37,plain,(
% 2.52/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f15])).
% 2.52/1.00  
% 2.52/1.00  fof(f7,axiom,(
% 2.52/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f19,plain,(
% 2.52/1.00    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.52/1.00    inference(ennf_transformation,[],[f7])).
% 2.52/1.00  
% 2.52/1.00  fof(f20,plain,(
% 2.52/1.00    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.52/1.00    inference(flattening,[],[f19])).
% 2.52/1.00  
% 2.52/1.00  fof(f42,plain,(
% 2.52/1.00    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f20])).
% 2.52/1.00  
% 2.52/1.00  fof(f5,axiom,(
% 2.52/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f18,plain,(
% 2.52/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.52/1.00    inference(ennf_transformation,[],[f5])).
% 2.52/1.00  
% 2.52/1.00  fof(f40,plain,(
% 2.52/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.52/1.00    inference(cnf_transformation,[],[f18])).
% 2.52/1.00  
% 2.52/1.00  fof(f6,axiom,(
% 2.52/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f41,plain,(
% 2.52/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.52/1.00    inference(cnf_transformation,[],[f6])).
% 2.52/1.00  
% 2.52/1.00  fof(f10,axiom,(
% 2.52/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f23,plain,(
% 2.52/1.00    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.00    inference(ennf_transformation,[],[f10])).
% 2.52/1.00  
% 2.52/1.00  fof(f45,plain,(
% 2.52/1.00    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.00    inference(cnf_transformation,[],[f23])).
% 2.52/1.00  
% 2.52/1.00  fof(f11,axiom,(
% 2.52/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.52/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/1.00  
% 2.52/1.00  fof(f24,plain,(
% 2.52/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.52/1.00    inference(ennf_transformation,[],[f11])).
% 2.52/1.00  
% 2.52/1.00  fof(f25,plain,(
% 2.52/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/1.00    inference(flattening,[],[f24])).
% 2.52/1.00  
% 2.52/1.00  fof(f46,plain,(
% 2.52/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/1.00    inference(cnf_transformation,[],[f25])).
% 2.52/1.00  
% 2.52/1.00  fof(f49,plain,(
% 2.52/1.00    ~r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4)),
% 2.52/1.00    inference(cnf_transformation,[],[f33])).
% 2.52/1.00  
% 2.52/1.00  cnf(c_14,negated_conjecture,
% 2.52/1.00      ( r1_tarski(sK2,sK3) ),
% 2.52/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_626,plain,
% 2.52/1.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_1,plain,
% 2.52/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_637,plain,
% 2.52/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.52/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_15,negated_conjecture,
% 2.52/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.52/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_625,plain,
% 2.52/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_10,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.52/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_628,plain,
% 2.52/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.52/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_1146,plain,
% 2.52/1.00      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_625,c_628]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_9,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.52/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_629,plain,
% 2.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.52/1.00      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_1500,plain,
% 2.52/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 2.52/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_1146,c_629]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_16,plain,
% 2.52/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_1982,plain,
% 2.52/1.00      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_1500,c_16]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_5,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/1.00      | ~ r2_hidden(X2,X0)
% 2.52/1.00      | r2_hidden(X2,X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_633,plain,
% 2.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.52/1.00      | r2_hidden(X2,X0) != iProver_top
% 2.52/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_1987,plain,
% 2.52/1.00      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 2.52/1.00      | r2_hidden(X0,sK2) = iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_1982,c_633]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_2112,plain,
% 2.52/1.00      ( r2_hidden(sK0(k2_relat_1(sK4),X0),sK2) = iProver_top
% 2.52/1.00      | r1_tarski(k2_relat_1(sK4),X0) = iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_637,c_1987]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_0,plain,
% 2.52/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_638,plain,
% 2.52/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.52/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3473,plain,
% 2.52/1.00      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_2112,c_638]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4,plain,
% 2.52/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 2.52/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_634,plain,
% 2.52/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3629,plain,
% 2.52/1.00      ( k2_xboole_0(k2_relat_1(sK4),sK2) = sK2 ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3473,c_634]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_3,plain,
% 2.52/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 2.52/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_635,plain,
% 2.52/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.52/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_4313,plain,
% 2.52/1.00      ( r1_tarski(k2_relat_1(sK4),X0) = iProver_top
% 2.52/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_3629,c_635]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_5653,plain,
% 2.52/1.00      ( k2_xboole_0(k2_relat_1(sK4),X0) = X0
% 2.52/1.00      | r1_tarski(sK2,X0) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_4313,c_634]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_5670,plain,
% 2.52/1.00      ( k2_xboole_0(k2_relat_1(sK4),sK3) = sK3 ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_626,c_5653]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_1080,plain,
% 2.52/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_637,c_638]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_1343,plain,
% 2.52/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_1080,c_635]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_5848,plain,
% 2.52/1.00      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_5670,c_1343]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_8,plain,
% 2.52/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.52/1.00      | ~ v1_relat_1(X0)
% 2.52/1.00      | k8_relat_1(X1,X0) = X0 ),
% 2.52/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_630,plain,
% 2.52/1.00      ( k8_relat_1(X0,X1) = X1
% 2.52/1.00      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 2.52/1.00      | v1_relat_1(X1) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_5878,plain,
% 2.52/1.00      ( k8_relat_1(sK3,sK4) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_5848,c_630]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_6,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/1.00      | ~ v1_relat_1(X1)
% 2.52/1.00      | v1_relat_1(X0) ),
% 2.52/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_743,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.00      | v1_relat_1(X0)
% 2.52/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_787,plain,
% 2.52/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.52/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 2.52/1.00      | v1_relat_1(sK4) ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_743]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_788,plain,
% 2.52/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.52/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 2.52/1.00      | v1_relat_1(sK4) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_7,plain,
% 2.52/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.52/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_857,plain,
% 2.52/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_858,plain,
% 2.52/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_857]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_6218,plain,
% 2.52/1.00      ( k8_relat_1(sK3,sK4) = sK4 ),
% 2.52/1.00      inference(global_propositional_subsumption,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_5878,c_16,c_788,c_858]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_11,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.00      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 2.52/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_627,plain,
% 2.52/1.00      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
% 2.52/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_988,plain,
% 2.52/1.00      ( k6_relset_1(sK1,sK2,X0,sK4) = k8_relat_1(X0,sK4) ),
% 2.52/1.00      inference(superposition,[status(thm)],[c_625,c_627]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_12,plain,
% 2.52/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.52/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.52/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.52/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_13,negated_conjecture,
% 2.52/1.00      ( ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) ),
% 2.52/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_182,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/1.00      | k6_relset_1(sK1,sK2,sK3,sK4) != X3
% 2.52/1.00      | sK4 != X3
% 2.52/1.00      | sK2 != X2
% 2.52/1.00      | sK1 != X1 ),
% 2.52/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_13]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_183,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.52/1.00      | ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.52/1.00      | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
% 2.52/1.00      inference(unflattening,[status(thm)],[c_182]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_309,plain,
% 2.52/1.00      ( ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.52/1.00      | sP0_iProver_split
% 2.52/1.00      | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
% 2.52/1.00      inference(splitting,
% 2.52/1.00                [splitting(split),new_symbols(definition,[])],
% 2.52/1.00                [c_183]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_623,plain,
% 2.52/1.00      ( sK4 != k6_relset_1(sK1,sK2,sK3,sK4)
% 2.52/1.00      | m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.52/1.00      | sP0_iProver_split = iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_308,plain,
% 2.52/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.52/1.00      | ~ sP0_iProver_split ),
% 2.52/1.00      inference(splitting,
% 2.52/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.52/1.00                [c_183]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_624,plain,
% 2.52/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 2.52/1.00      | sP0_iProver_split != iProver_top ),
% 2.52/1.00      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_704,plain,
% 2.52/1.00      ( k6_relset_1(sK1,sK2,sK3,sK4) != sK4
% 2.52/1.00      | m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.52/1.00      inference(forward_subsumption_resolution,
% 2.52/1.00                [status(thm)],
% 2.52/1.00                [c_623,c_624]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_1230,plain,
% 2.52/1.00      ( k8_relat_1(sK3,sK4) != sK4
% 2.52/1.00      | m1_subset_1(k8_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.52/1.00      inference(demodulation,[status(thm)],[c_988,c_704]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_6221,plain,
% 2.52/1.00      ( sK4 != sK4
% 2.52/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.52/1.00      inference(demodulation,[status(thm)],[c_6218,c_1230]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_311,plain,( X0 = X0 ),theory(equality) ).
% 2.52/1.00  
% 2.52/1.00  cnf(c_811,plain,
% 2.52/1.00      ( sK4 = sK4 ),
% 2.52/1.00      inference(instantiation,[status(thm)],[c_311]) ).
% 2.52/1.00  
% 2.52/1.00  cnf(contradiction,plain,
% 2.52/1.00      ( $false ),
% 2.52/1.00      inference(minisat,[status(thm)],[c_6221,c_811,c_16]) ).
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/1.00  
% 2.52/1.00  ------                               Statistics
% 2.52/1.00  
% 2.52/1.00  ------ General
% 2.52/1.00  
% 2.52/1.00  abstr_ref_over_cycles:                  0
% 2.52/1.00  abstr_ref_under_cycles:                 0
% 2.52/1.00  gc_basic_clause_elim:                   0
% 2.52/1.00  forced_gc_time:                         0
% 2.52/1.00  parsing_time:                           0.01
% 2.52/1.00  unif_index_cands_time:                  0.
% 2.52/1.00  unif_index_add_time:                    0.
% 2.52/1.00  orderings_time:                         0.
% 2.52/1.00  out_proof_time:                         0.01
% 2.52/1.00  total_time:                             0.254
% 2.52/1.00  num_of_symbols:                         49
% 2.52/1.00  num_of_terms:                           6720
% 2.52/1.00  
% 2.52/1.00  ------ Preprocessing
% 2.52/1.00  
% 2.52/1.00  num_of_splits:                          1
% 2.52/1.00  num_of_split_atoms:                     1
% 2.52/1.00  num_of_reused_defs:                     0
% 2.52/1.00  num_eq_ax_congr_red:                    33
% 2.52/1.00  num_of_sem_filtered_clauses:            1
% 2.52/1.00  num_of_subtypes:                        0
% 2.52/1.00  monotx_restored_types:                  0
% 2.52/1.00  sat_num_of_epr_types:                   0
% 2.52/1.00  sat_num_of_non_cyclic_types:            0
% 2.52/1.00  sat_guarded_non_collapsed_types:        0
% 2.52/1.00  num_pure_diseq_elim:                    0
% 2.52/1.00  simp_replaced_by:                       0
% 2.52/1.00  res_preprocessed:                       82
% 2.52/1.00  prep_upred:                             0
% 2.52/1.00  prep_unflattend:                        3
% 2.52/1.00  smt_new_axioms:                         0
% 2.52/1.00  pred_elim_cands:                        4
% 2.52/1.00  pred_elim:                              1
% 2.52/1.00  pred_elim_cl:                           1
% 2.52/1.00  pred_elim_cycles:                       3
% 2.52/1.00  merged_defs:                            0
% 2.52/1.00  merged_defs_ncl:                        0
% 2.52/1.00  bin_hyper_res:                          0
% 2.52/1.00  prep_cycles:                            4
% 2.52/1.00  pred_elim_time:                         0.001
% 2.52/1.00  splitting_time:                         0.
% 2.52/1.00  sem_filter_time:                        0.
% 2.52/1.00  monotx_time:                            0.001
% 2.52/1.00  subtype_inf_time:                       0.
% 2.52/1.00  
% 2.52/1.00  ------ Problem properties
% 2.52/1.00  
% 2.52/1.00  clauses:                                16
% 2.52/1.00  conjectures:                            2
% 2.52/1.00  epr:                                    2
% 2.52/1.00  horn:                                   15
% 2.52/1.00  ground:                                 3
% 2.52/1.00  unary:                                  3
% 2.52/1.00  binary:                                 8
% 2.52/1.00  lits:                                   34
% 2.52/1.00  lits_eq:                                5
% 2.52/1.00  fd_pure:                                0
% 2.52/1.00  fd_pseudo:                              0
% 2.52/1.00  fd_cond:                                0
% 2.52/1.00  fd_pseudo_cond:                         0
% 2.52/1.00  ac_symbols:                             0
% 2.52/1.00  
% 2.52/1.00  ------ Propositional Solver
% 2.52/1.00  
% 2.52/1.00  prop_solver_calls:                      29
% 2.52/1.00  prop_fast_solver_calls:                 528
% 2.52/1.00  smt_solver_calls:                       0
% 2.52/1.00  smt_fast_solver_calls:                  0
% 2.52/1.00  prop_num_of_clauses:                    2662
% 2.52/1.00  prop_preprocess_simplified:             6009
% 2.52/1.00  prop_fo_subsumed:                       4
% 2.52/1.00  prop_solver_time:                       0.
% 2.52/1.00  smt_solver_time:                        0.
% 2.52/1.00  smt_fast_solver_time:                   0.
% 2.52/1.00  prop_fast_solver_time:                  0.
% 2.52/1.00  prop_unsat_core_time:                   0.
% 2.52/1.00  
% 2.52/1.00  ------ QBF
% 2.52/1.00  
% 2.52/1.00  qbf_q_res:                              0
% 2.52/1.00  qbf_num_tautologies:                    0
% 2.52/1.00  qbf_prep_cycles:                        0
% 2.52/1.00  
% 2.52/1.00  ------ BMC1
% 2.52/1.00  
% 2.52/1.00  bmc1_current_bound:                     -1
% 2.52/1.00  bmc1_last_solved_bound:                 -1
% 2.52/1.00  bmc1_unsat_core_size:                   -1
% 2.52/1.00  bmc1_unsat_core_parents_size:           -1
% 2.52/1.00  bmc1_merge_next_fun:                    0
% 2.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.52/1.00  
% 2.52/1.00  ------ Instantiation
% 2.52/1.00  
% 2.52/1.00  inst_num_of_clauses:                    711
% 2.52/1.00  inst_num_in_passive:                    155
% 2.52/1.00  inst_num_in_active:                     321
% 2.52/1.00  inst_num_in_unprocessed:                235
% 2.52/1.00  inst_num_of_loops:                      420
% 2.52/1.00  inst_num_of_learning_restarts:          0
% 2.52/1.00  inst_num_moves_active_passive:          95
% 2.52/1.00  inst_lit_activity:                      0
% 2.52/1.00  inst_lit_activity_moves:                0
% 2.52/1.00  inst_num_tautologies:                   0
% 2.52/1.00  inst_num_prop_implied:                  0
% 2.52/1.00  inst_num_existing_simplified:           0
% 2.52/1.00  inst_num_eq_res_simplified:             0
% 2.52/1.00  inst_num_child_elim:                    0
% 2.52/1.00  inst_num_of_dismatching_blockings:      237
% 2.52/1.00  inst_num_of_non_proper_insts:           643
% 2.52/1.00  inst_num_of_duplicates:                 0
% 2.52/1.00  inst_inst_num_from_inst_to_res:         0
% 2.52/1.00  inst_dismatching_checking_time:         0.
% 2.52/1.00  
% 2.52/1.00  ------ Resolution
% 2.52/1.00  
% 2.52/1.00  res_num_of_clauses:                     0
% 2.52/1.00  res_num_in_passive:                     0
% 2.52/1.00  res_num_in_active:                      0
% 2.52/1.00  res_num_of_loops:                       86
% 2.52/1.00  res_forward_subset_subsumed:            34
% 2.52/1.00  res_backward_subset_subsumed:           0
% 2.52/1.00  res_forward_subsumed:                   0
% 2.52/1.00  res_backward_subsumed:                  0
% 2.52/1.00  res_forward_subsumption_resolution:     0
% 2.52/1.00  res_backward_subsumption_resolution:    0
% 2.52/1.00  res_clause_to_clause_subsumption:       538
% 2.52/1.00  res_orphan_elimination:                 0
% 2.52/1.00  res_tautology_del:                      51
% 2.52/1.00  res_num_eq_res_simplified:              0
% 2.52/1.00  res_num_sel_changes:                    0
% 2.52/1.00  res_moves_from_active_to_pass:          0
% 2.52/1.00  
% 2.52/1.00  ------ Superposition
% 2.52/1.00  
% 2.52/1.00  sup_time_total:                         0.
% 2.52/1.00  sup_time_generating:                    0.
% 2.52/1.00  sup_time_sim_full:                      0.
% 2.52/1.00  sup_time_sim_immed:                     0.
% 2.52/1.00  
% 2.52/1.00  sup_num_of_clauses:                     135
% 2.52/1.00  sup_num_in_active:                      80
% 2.52/1.00  sup_num_in_passive:                     55
% 2.52/1.00  sup_num_of_loops:                       82
% 2.52/1.00  sup_fw_superposition:                   248
% 2.52/1.00  sup_bw_superposition:                   138
% 2.52/1.00  sup_immediate_simplified:               45
% 2.52/1.00  sup_given_eliminated:                   0
% 2.52/1.00  comparisons_done:                       0
% 2.52/1.00  comparisons_avoided:                    0
% 2.52/1.00  
% 2.52/1.00  ------ Simplifications
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  sim_fw_subset_subsumed:                 2
% 2.52/1.00  sim_bw_subset_subsumed:                 0
% 2.52/1.00  sim_fw_subsumed:                        10
% 2.52/1.00  sim_bw_subsumed:                        0
% 2.52/1.00  sim_fw_subsumption_res:                 1
% 2.52/1.00  sim_bw_subsumption_res:                 0
% 2.52/1.00  sim_tautology_del:                      1
% 2.52/1.00  sim_eq_tautology_del:                   6
% 2.52/1.00  sim_eq_res_simp:                        0
% 2.52/1.00  sim_fw_demodulated:                     16
% 2.52/1.00  sim_bw_demodulated:                     2
% 2.52/1.00  sim_light_normalised:                   22
% 2.52/1.00  sim_joinable_taut:                      0
% 2.52/1.00  sim_joinable_simp:                      0
% 2.52/1.00  sim_ac_normalised:                      0
% 2.52/1.00  sim_smt_subsumption:                    0
% 2.52/1.00  
%------------------------------------------------------------------------------
