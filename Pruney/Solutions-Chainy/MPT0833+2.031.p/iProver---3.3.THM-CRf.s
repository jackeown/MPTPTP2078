%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:58 EST 2020

% Result     : Theorem 6.34s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 228 expanded)
%              Number of clauses        :   52 (  94 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :  225 ( 586 expanded)
%              Number of equality atoms :   73 ( 114 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f28])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f46,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_898,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1207,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_898,c_904])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_102,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_5,c_3])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_102])).

cnf(c_896,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_8,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_901,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_899,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_908,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2436,plain,
    ( r1_tarski(X0,sK2) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_899,c_908])).

cnf(c_2587,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,sK1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_2436])).

cnf(c_2593,plain,
    ( r1_tarski(X0,k2_relat_1(k2_zfmisc_1(X1,sK1))) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2587,c_908])).

cnf(c_3159,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,sK1)) != iProver_top
    | r1_tarski(k2_relat_1(X0),sK2) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_2593])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_903,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_20970,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,sK1)) != iProver_top
    | r1_tarski(k2_relat_1(X0),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3159,c_903])).

cnf(c_20977,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_20970])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_902,plain,
    ( k8_relat_1(X0,X1) = X1
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_21573,plain,
    ( k8_relat_1(sK2,sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_20977,c_902])).

cnf(c_140,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_171,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_141])).

cnf(c_895,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_1479,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_895])).

cnf(c_1867,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1479,c_903])).

cnf(c_7439,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k8_relat_1(X0,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_16094,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | k8_relat_1(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_7439])).

cnf(c_16099,plain,
    ( k8_relat_1(sK2,sK3) = sK3
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16094])).

cnf(c_22430,plain,
    ( k8_relat_1(sK2,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21573,c_1867,c_16099,c_20977])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_900,plain,
    ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1638,plain,
    ( k6_relset_1(sK0,sK1,X0,sK3) = k8_relat_1(X0,sK3) ),
    inference(superposition,[status(thm)],[c_898,c_900])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(sK0,sK1,sK2,sK3) != X0
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_237,plain,
    ( ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_894,plain,
    ( sK3 != k6_relset_1(sK0,sK1,sK2,sK3)
    | m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_1789,plain,
    ( k8_relat_1(sK2,sK3) != sK3
    | m1_subset_1(k8_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1638,c_894])).

cnf(c_22433,plain,
    ( sK3 != sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22430,c_1789])).

cnf(c_520,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1216,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_17,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22433,c_1216,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.34/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/1.52  
% 6.34/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.34/1.52  
% 6.34/1.52  ------  iProver source info
% 6.34/1.52  
% 6.34/1.52  git: date: 2020-06-30 10:37:57 +0100
% 6.34/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.34/1.52  git: non_committed_changes: false
% 6.34/1.52  git: last_make_outside_of_git: false
% 6.34/1.52  
% 6.34/1.52  ------ 
% 6.34/1.52  
% 6.34/1.52  ------ Input Options
% 6.34/1.52  
% 6.34/1.52  --out_options                           all
% 6.34/1.52  --tptp_safe_out                         true
% 6.34/1.52  --problem_path                          ""
% 6.34/1.52  --include_path                          ""
% 6.34/1.52  --clausifier                            res/vclausify_rel
% 6.34/1.52  --clausifier_options                    --mode clausify
% 6.34/1.52  --stdin                                 false
% 6.34/1.52  --stats_out                             all
% 6.34/1.52  
% 6.34/1.52  ------ General Options
% 6.34/1.52  
% 6.34/1.52  --fof                                   false
% 6.34/1.52  --time_out_real                         305.
% 6.34/1.52  --time_out_virtual                      -1.
% 6.34/1.52  --symbol_type_check                     false
% 6.34/1.52  --clausify_out                          false
% 6.34/1.52  --sig_cnt_out                           false
% 6.34/1.52  --trig_cnt_out                          false
% 6.34/1.52  --trig_cnt_out_tolerance                1.
% 6.34/1.52  --trig_cnt_out_sk_spl                   false
% 6.34/1.52  --abstr_cl_out                          false
% 6.34/1.52  
% 6.34/1.52  ------ Global Options
% 6.34/1.52  
% 6.34/1.52  --schedule                              default
% 6.34/1.52  --add_important_lit                     false
% 6.34/1.52  --prop_solver_per_cl                    1000
% 6.34/1.52  --min_unsat_core                        false
% 6.34/1.52  --soft_assumptions                      false
% 6.34/1.52  --soft_lemma_size                       3
% 6.34/1.52  --prop_impl_unit_size                   0
% 6.34/1.52  --prop_impl_unit                        []
% 6.34/1.52  --share_sel_clauses                     true
% 6.34/1.52  --reset_solvers                         false
% 6.34/1.52  --bc_imp_inh                            [conj_cone]
% 6.34/1.52  --conj_cone_tolerance                   3.
% 6.34/1.52  --extra_neg_conj                        none
% 6.34/1.52  --large_theory_mode                     true
% 6.34/1.52  --prolific_symb_bound                   200
% 6.34/1.52  --lt_threshold                          2000
% 6.34/1.52  --clause_weak_htbl                      true
% 6.34/1.52  --gc_record_bc_elim                     false
% 6.34/1.52  
% 6.34/1.52  ------ Preprocessing Options
% 6.34/1.52  
% 6.34/1.52  --preprocessing_flag                    true
% 6.34/1.52  --time_out_prep_mult                    0.1
% 6.34/1.52  --splitting_mode                        input
% 6.34/1.52  --splitting_grd                         true
% 6.34/1.52  --splitting_cvd                         false
% 6.34/1.52  --splitting_cvd_svl                     false
% 6.34/1.52  --splitting_nvd                         32
% 6.34/1.52  --sub_typing                            true
% 6.34/1.52  --prep_gs_sim                           true
% 6.34/1.52  --prep_unflatten                        true
% 6.34/1.52  --prep_res_sim                          true
% 6.34/1.52  --prep_upred                            true
% 6.34/1.52  --prep_sem_filter                       exhaustive
% 6.34/1.52  --prep_sem_filter_out                   false
% 6.34/1.52  --pred_elim                             true
% 6.34/1.52  --res_sim_input                         true
% 6.34/1.52  --eq_ax_congr_red                       true
% 6.34/1.52  --pure_diseq_elim                       true
% 6.34/1.52  --brand_transform                       false
% 6.34/1.52  --non_eq_to_eq                          false
% 6.34/1.52  --prep_def_merge                        true
% 6.34/1.52  --prep_def_merge_prop_impl              false
% 6.34/1.52  --prep_def_merge_mbd                    true
% 6.34/1.52  --prep_def_merge_tr_red                 false
% 6.34/1.52  --prep_def_merge_tr_cl                  false
% 6.34/1.52  --smt_preprocessing                     true
% 6.34/1.52  --smt_ac_axioms                         fast
% 6.34/1.52  --preprocessed_out                      false
% 6.34/1.52  --preprocessed_stats                    false
% 6.34/1.52  
% 6.34/1.52  ------ Abstraction refinement Options
% 6.34/1.52  
% 6.34/1.52  --abstr_ref                             []
% 6.34/1.52  --abstr_ref_prep                        false
% 6.34/1.52  --abstr_ref_until_sat                   false
% 6.34/1.52  --abstr_ref_sig_restrict                funpre
% 6.34/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 6.34/1.52  --abstr_ref_under                       []
% 6.34/1.52  
% 6.34/1.52  ------ SAT Options
% 6.34/1.52  
% 6.34/1.52  --sat_mode                              false
% 6.34/1.52  --sat_fm_restart_options                ""
% 6.34/1.52  --sat_gr_def                            false
% 6.34/1.52  --sat_epr_types                         true
% 6.34/1.52  --sat_non_cyclic_types                  false
% 6.34/1.52  --sat_finite_models                     false
% 6.34/1.52  --sat_fm_lemmas                         false
% 6.34/1.52  --sat_fm_prep                           false
% 6.34/1.52  --sat_fm_uc_incr                        true
% 6.34/1.52  --sat_out_model                         small
% 6.34/1.52  --sat_out_clauses                       false
% 6.34/1.52  
% 6.34/1.52  ------ QBF Options
% 6.34/1.52  
% 6.34/1.52  --qbf_mode                              false
% 6.34/1.52  --qbf_elim_univ                         false
% 6.34/1.52  --qbf_dom_inst                          none
% 6.34/1.52  --qbf_dom_pre_inst                      false
% 6.34/1.52  --qbf_sk_in                             false
% 6.34/1.52  --qbf_pred_elim                         true
% 6.34/1.52  --qbf_split                             512
% 6.34/1.52  
% 6.34/1.52  ------ BMC1 Options
% 6.34/1.52  
% 6.34/1.52  --bmc1_incremental                      false
% 6.34/1.52  --bmc1_axioms                           reachable_all
% 6.34/1.52  --bmc1_min_bound                        0
% 6.34/1.52  --bmc1_max_bound                        -1
% 6.34/1.52  --bmc1_max_bound_default                -1
% 6.34/1.52  --bmc1_symbol_reachability              true
% 6.34/1.52  --bmc1_property_lemmas                  false
% 6.34/1.52  --bmc1_k_induction                      false
% 6.34/1.52  --bmc1_non_equiv_states                 false
% 6.34/1.52  --bmc1_deadlock                         false
% 6.34/1.52  --bmc1_ucm                              false
% 6.34/1.52  --bmc1_add_unsat_core                   none
% 6.34/1.52  --bmc1_unsat_core_children              false
% 6.34/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.34/1.52  --bmc1_out_stat                         full
% 6.34/1.52  --bmc1_ground_init                      false
% 6.34/1.52  --bmc1_pre_inst_next_state              false
% 6.34/1.52  --bmc1_pre_inst_state                   false
% 6.34/1.52  --bmc1_pre_inst_reach_state             false
% 6.34/1.52  --bmc1_out_unsat_core                   false
% 6.34/1.52  --bmc1_aig_witness_out                  false
% 6.34/1.52  --bmc1_verbose                          false
% 6.34/1.52  --bmc1_dump_clauses_tptp                false
% 6.34/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.34/1.52  --bmc1_dump_file                        -
% 6.34/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.34/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.34/1.52  --bmc1_ucm_extend_mode                  1
% 6.34/1.52  --bmc1_ucm_init_mode                    2
% 6.34/1.52  --bmc1_ucm_cone_mode                    none
% 6.34/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.34/1.52  --bmc1_ucm_relax_model                  4
% 6.34/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.34/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.34/1.52  --bmc1_ucm_layered_model                none
% 6.34/1.52  --bmc1_ucm_max_lemma_size               10
% 6.34/1.52  
% 6.34/1.52  ------ AIG Options
% 6.34/1.52  
% 6.34/1.52  --aig_mode                              false
% 6.34/1.52  
% 6.34/1.52  ------ Instantiation Options
% 6.34/1.52  
% 6.34/1.52  --instantiation_flag                    true
% 6.34/1.52  --inst_sos_flag                         false
% 6.34/1.52  --inst_sos_phase                        true
% 6.34/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.34/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.34/1.52  --inst_lit_sel_side                     num_symb
% 6.34/1.52  --inst_solver_per_active                1400
% 6.34/1.52  --inst_solver_calls_frac                1.
% 6.34/1.52  --inst_passive_queue_type               priority_queues
% 6.34/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.34/1.52  --inst_passive_queues_freq              [25;2]
% 6.34/1.52  --inst_dismatching                      true
% 6.34/1.52  --inst_eager_unprocessed_to_passive     true
% 6.34/1.52  --inst_prop_sim_given                   true
% 6.34/1.52  --inst_prop_sim_new                     false
% 6.34/1.52  --inst_subs_new                         false
% 6.34/1.52  --inst_eq_res_simp                      false
% 6.34/1.52  --inst_subs_given                       false
% 6.34/1.52  --inst_orphan_elimination               true
% 6.34/1.52  --inst_learning_loop_flag               true
% 6.34/1.52  --inst_learning_start                   3000
% 6.34/1.52  --inst_learning_factor                  2
% 6.34/1.52  --inst_start_prop_sim_after_learn       3
% 6.34/1.52  --inst_sel_renew                        solver
% 6.34/1.52  --inst_lit_activity_flag                true
% 6.34/1.52  --inst_restr_to_given                   false
% 6.34/1.52  --inst_activity_threshold               500
% 6.34/1.52  --inst_out_proof                        true
% 6.34/1.52  
% 6.34/1.52  ------ Resolution Options
% 6.34/1.52  
% 6.34/1.52  --resolution_flag                       true
% 6.34/1.52  --res_lit_sel                           adaptive
% 6.34/1.52  --res_lit_sel_side                      none
% 6.34/1.52  --res_ordering                          kbo
% 6.34/1.52  --res_to_prop_solver                    active
% 6.34/1.52  --res_prop_simpl_new                    false
% 6.34/1.52  --res_prop_simpl_given                  true
% 6.34/1.52  --res_passive_queue_type                priority_queues
% 6.34/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.34/1.52  --res_passive_queues_freq               [15;5]
% 6.34/1.52  --res_forward_subs                      full
% 6.34/1.52  --res_backward_subs                     full
% 6.34/1.52  --res_forward_subs_resolution           true
% 6.34/1.52  --res_backward_subs_resolution          true
% 6.34/1.52  --res_orphan_elimination                true
% 6.34/1.52  --res_time_limit                        2.
% 6.34/1.52  --res_out_proof                         true
% 6.34/1.52  
% 6.34/1.52  ------ Superposition Options
% 6.34/1.52  
% 6.34/1.52  --superposition_flag                    true
% 6.34/1.52  --sup_passive_queue_type                priority_queues
% 6.34/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.34/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.34/1.52  --demod_completeness_check              fast
% 6.34/1.52  --demod_use_ground                      true
% 6.34/1.52  --sup_to_prop_solver                    passive
% 6.34/1.52  --sup_prop_simpl_new                    true
% 6.34/1.52  --sup_prop_simpl_given                  true
% 6.34/1.52  --sup_fun_splitting                     false
% 6.34/1.52  --sup_smt_interval                      50000
% 6.34/1.52  
% 6.34/1.52  ------ Superposition Simplification Setup
% 6.34/1.52  
% 6.34/1.52  --sup_indices_passive                   []
% 6.34/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.34/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.52  --sup_full_bw                           [BwDemod]
% 6.34/1.52  --sup_immed_triv                        [TrivRules]
% 6.34/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.34/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.52  --sup_immed_bw_main                     []
% 6.34/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.34/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.34/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.34/1.52  
% 6.34/1.52  ------ Combination Options
% 6.34/1.52  
% 6.34/1.52  --comb_res_mult                         3
% 6.34/1.52  --comb_sup_mult                         2
% 6.34/1.52  --comb_inst_mult                        10
% 6.34/1.52  
% 6.34/1.52  ------ Debug Options
% 6.34/1.52  
% 6.34/1.52  --dbg_backtrace                         false
% 6.34/1.52  --dbg_dump_prop_clauses                 false
% 6.34/1.52  --dbg_dump_prop_clauses_file            -
% 6.34/1.52  --dbg_out_stat                          false
% 6.34/1.52  ------ Parsing...
% 6.34/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.34/1.52  
% 6.34/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.34/1.52  
% 6.34/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.34/1.52  
% 6.34/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.34/1.52  ------ Proving...
% 6.34/1.52  ------ Problem Properties 
% 6.34/1.52  
% 6.34/1.52  
% 6.34/1.52  clauses                                 15
% 6.34/1.52  conjectures                             2
% 6.34/1.52  EPR                                     3
% 6.34/1.52  Horn                                    15
% 6.34/1.52  unary                                   4
% 6.34/1.52  binary                                  6
% 6.34/1.52  lits                                    31
% 6.34/1.52  lits eq                                 3
% 6.34/1.52  fd_pure                                 0
% 6.34/1.52  fd_pseudo                               0
% 6.34/1.52  fd_cond                                 0
% 6.34/1.52  fd_pseudo_cond                          0
% 6.34/1.52  AC symbols                              0
% 6.34/1.52  
% 6.34/1.52  ------ Schedule dynamic 5 is on 
% 6.34/1.52  
% 6.34/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.34/1.52  
% 6.34/1.52  
% 6.34/1.52  ------ 
% 6.34/1.52  Current options:
% 6.34/1.52  ------ 
% 6.34/1.52  
% 6.34/1.52  ------ Input Options
% 6.34/1.52  
% 6.34/1.52  --out_options                           all
% 6.34/1.52  --tptp_safe_out                         true
% 6.34/1.52  --problem_path                          ""
% 6.34/1.52  --include_path                          ""
% 6.34/1.52  --clausifier                            res/vclausify_rel
% 6.34/1.52  --clausifier_options                    --mode clausify
% 6.34/1.52  --stdin                                 false
% 6.34/1.52  --stats_out                             all
% 6.34/1.52  
% 6.34/1.52  ------ General Options
% 6.34/1.52  
% 6.34/1.52  --fof                                   false
% 6.34/1.52  --time_out_real                         305.
% 6.34/1.52  --time_out_virtual                      -1.
% 6.34/1.52  --symbol_type_check                     false
% 6.34/1.52  --clausify_out                          false
% 6.34/1.52  --sig_cnt_out                           false
% 6.34/1.52  --trig_cnt_out                          false
% 6.34/1.52  --trig_cnt_out_tolerance                1.
% 6.34/1.52  --trig_cnt_out_sk_spl                   false
% 6.34/1.52  --abstr_cl_out                          false
% 6.34/1.52  
% 6.34/1.52  ------ Global Options
% 6.34/1.52  
% 6.34/1.52  --schedule                              default
% 6.34/1.52  --add_important_lit                     false
% 6.34/1.52  --prop_solver_per_cl                    1000
% 6.34/1.52  --min_unsat_core                        false
% 6.34/1.52  --soft_assumptions                      false
% 6.34/1.52  --soft_lemma_size                       3
% 6.34/1.52  --prop_impl_unit_size                   0
% 6.34/1.52  --prop_impl_unit                        []
% 6.34/1.52  --share_sel_clauses                     true
% 6.34/1.52  --reset_solvers                         false
% 6.34/1.52  --bc_imp_inh                            [conj_cone]
% 6.34/1.52  --conj_cone_tolerance                   3.
% 6.34/1.52  --extra_neg_conj                        none
% 6.34/1.52  --large_theory_mode                     true
% 6.34/1.52  --prolific_symb_bound                   200
% 6.34/1.52  --lt_threshold                          2000
% 6.34/1.52  --clause_weak_htbl                      true
% 6.34/1.52  --gc_record_bc_elim                     false
% 6.34/1.52  
% 6.34/1.52  ------ Preprocessing Options
% 6.34/1.52  
% 6.34/1.52  --preprocessing_flag                    true
% 6.34/1.52  --time_out_prep_mult                    0.1
% 6.34/1.52  --splitting_mode                        input
% 6.34/1.52  --splitting_grd                         true
% 6.34/1.52  --splitting_cvd                         false
% 6.34/1.52  --splitting_cvd_svl                     false
% 6.34/1.52  --splitting_nvd                         32
% 6.34/1.52  --sub_typing                            true
% 6.34/1.52  --prep_gs_sim                           true
% 6.34/1.52  --prep_unflatten                        true
% 6.34/1.52  --prep_res_sim                          true
% 6.34/1.52  --prep_upred                            true
% 6.34/1.52  --prep_sem_filter                       exhaustive
% 6.34/1.52  --prep_sem_filter_out                   false
% 6.34/1.52  --pred_elim                             true
% 6.34/1.52  --res_sim_input                         true
% 6.34/1.52  --eq_ax_congr_red                       true
% 6.34/1.52  --pure_diseq_elim                       true
% 6.34/1.52  --brand_transform                       false
% 6.34/1.52  --non_eq_to_eq                          false
% 6.34/1.52  --prep_def_merge                        true
% 6.34/1.52  --prep_def_merge_prop_impl              false
% 6.34/1.52  --prep_def_merge_mbd                    true
% 6.34/1.52  --prep_def_merge_tr_red                 false
% 6.34/1.52  --prep_def_merge_tr_cl                  false
% 6.34/1.52  --smt_preprocessing                     true
% 6.34/1.52  --smt_ac_axioms                         fast
% 6.34/1.52  --preprocessed_out                      false
% 6.34/1.52  --preprocessed_stats                    false
% 6.34/1.52  
% 6.34/1.52  ------ Abstraction refinement Options
% 6.34/1.52  
% 6.34/1.52  --abstr_ref                             []
% 6.34/1.52  --abstr_ref_prep                        false
% 6.34/1.52  --abstr_ref_until_sat                   false
% 6.34/1.52  --abstr_ref_sig_restrict                funpre
% 6.34/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 6.34/1.52  --abstr_ref_under                       []
% 6.34/1.52  
% 6.34/1.52  ------ SAT Options
% 6.34/1.52  
% 6.34/1.52  --sat_mode                              false
% 6.34/1.52  --sat_fm_restart_options                ""
% 6.34/1.52  --sat_gr_def                            false
% 6.34/1.52  --sat_epr_types                         true
% 6.34/1.52  --sat_non_cyclic_types                  false
% 6.34/1.52  --sat_finite_models                     false
% 6.34/1.52  --sat_fm_lemmas                         false
% 6.34/1.52  --sat_fm_prep                           false
% 6.34/1.52  --sat_fm_uc_incr                        true
% 6.34/1.52  --sat_out_model                         small
% 6.34/1.52  --sat_out_clauses                       false
% 6.34/1.52  
% 6.34/1.52  ------ QBF Options
% 6.34/1.52  
% 6.34/1.52  --qbf_mode                              false
% 6.34/1.52  --qbf_elim_univ                         false
% 6.34/1.52  --qbf_dom_inst                          none
% 6.34/1.52  --qbf_dom_pre_inst                      false
% 6.34/1.52  --qbf_sk_in                             false
% 6.34/1.52  --qbf_pred_elim                         true
% 6.34/1.52  --qbf_split                             512
% 6.34/1.52  
% 6.34/1.52  ------ BMC1 Options
% 6.34/1.52  
% 6.34/1.52  --bmc1_incremental                      false
% 6.34/1.52  --bmc1_axioms                           reachable_all
% 6.34/1.52  --bmc1_min_bound                        0
% 6.34/1.52  --bmc1_max_bound                        -1
% 6.34/1.52  --bmc1_max_bound_default                -1
% 6.34/1.52  --bmc1_symbol_reachability              true
% 6.34/1.52  --bmc1_property_lemmas                  false
% 6.34/1.52  --bmc1_k_induction                      false
% 6.34/1.52  --bmc1_non_equiv_states                 false
% 6.34/1.52  --bmc1_deadlock                         false
% 6.34/1.52  --bmc1_ucm                              false
% 6.34/1.52  --bmc1_add_unsat_core                   none
% 6.34/1.52  --bmc1_unsat_core_children              false
% 6.34/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 6.34/1.52  --bmc1_out_stat                         full
% 6.34/1.52  --bmc1_ground_init                      false
% 6.34/1.52  --bmc1_pre_inst_next_state              false
% 6.34/1.52  --bmc1_pre_inst_state                   false
% 6.34/1.52  --bmc1_pre_inst_reach_state             false
% 6.34/1.52  --bmc1_out_unsat_core                   false
% 6.34/1.52  --bmc1_aig_witness_out                  false
% 6.34/1.52  --bmc1_verbose                          false
% 6.34/1.52  --bmc1_dump_clauses_tptp                false
% 6.34/1.52  --bmc1_dump_unsat_core_tptp             false
% 6.34/1.52  --bmc1_dump_file                        -
% 6.34/1.52  --bmc1_ucm_expand_uc_limit              128
% 6.34/1.52  --bmc1_ucm_n_expand_iterations          6
% 6.34/1.52  --bmc1_ucm_extend_mode                  1
% 6.34/1.52  --bmc1_ucm_init_mode                    2
% 6.34/1.52  --bmc1_ucm_cone_mode                    none
% 6.34/1.52  --bmc1_ucm_reduced_relation_type        0
% 6.34/1.52  --bmc1_ucm_relax_model                  4
% 6.34/1.52  --bmc1_ucm_full_tr_after_sat            true
% 6.34/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 6.34/1.52  --bmc1_ucm_layered_model                none
% 6.34/1.52  --bmc1_ucm_max_lemma_size               10
% 6.34/1.52  
% 6.34/1.52  ------ AIG Options
% 6.34/1.52  
% 6.34/1.52  --aig_mode                              false
% 6.34/1.52  
% 6.34/1.52  ------ Instantiation Options
% 6.34/1.52  
% 6.34/1.52  --instantiation_flag                    true
% 6.34/1.52  --inst_sos_flag                         false
% 6.34/1.52  --inst_sos_phase                        true
% 6.34/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.34/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.34/1.52  --inst_lit_sel_side                     none
% 6.34/1.52  --inst_solver_per_active                1400
% 6.34/1.52  --inst_solver_calls_frac                1.
% 6.34/1.52  --inst_passive_queue_type               priority_queues
% 6.34/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.34/1.52  --inst_passive_queues_freq              [25;2]
% 6.34/1.52  --inst_dismatching                      true
% 6.34/1.52  --inst_eager_unprocessed_to_passive     true
% 6.34/1.52  --inst_prop_sim_given                   true
% 6.34/1.52  --inst_prop_sim_new                     false
% 6.34/1.52  --inst_subs_new                         false
% 6.34/1.52  --inst_eq_res_simp                      false
% 6.34/1.52  --inst_subs_given                       false
% 6.34/1.52  --inst_orphan_elimination               true
% 6.34/1.52  --inst_learning_loop_flag               true
% 6.34/1.52  --inst_learning_start                   3000
% 6.34/1.52  --inst_learning_factor                  2
% 6.34/1.52  --inst_start_prop_sim_after_learn       3
% 6.34/1.52  --inst_sel_renew                        solver
% 6.34/1.52  --inst_lit_activity_flag                true
% 6.34/1.52  --inst_restr_to_given                   false
% 6.34/1.52  --inst_activity_threshold               500
% 6.34/1.52  --inst_out_proof                        true
% 6.34/1.52  
% 6.34/1.52  ------ Resolution Options
% 6.34/1.52  
% 6.34/1.52  --resolution_flag                       false
% 6.34/1.52  --res_lit_sel                           adaptive
% 6.34/1.52  --res_lit_sel_side                      none
% 6.34/1.52  --res_ordering                          kbo
% 6.34/1.52  --res_to_prop_solver                    active
% 6.34/1.52  --res_prop_simpl_new                    false
% 6.34/1.52  --res_prop_simpl_given                  true
% 6.34/1.52  --res_passive_queue_type                priority_queues
% 6.34/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.34/1.52  --res_passive_queues_freq               [15;5]
% 6.34/1.52  --res_forward_subs                      full
% 6.34/1.52  --res_backward_subs                     full
% 6.34/1.52  --res_forward_subs_resolution           true
% 6.34/1.52  --res_backward_subs_resolution          true
% 6.34/1.52  --res_orphan_elimination                true
% 6.34/1.52  --res_time_limit                        2.
% 6.34/1.52  --res_out_proof                         true
% 6.34/1.52  
% 6.34/1.52  ------ Superposition Options
% 6.34/1.52  
% 6.34/1.52  --superposition_flag                    true
% 6.34/1.52  --sup_passive_queue_type                priority_queues
% 6.34/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.34/1.52  --sup_passive_queues_freq               [8;1;4]
% 6.34/1.52  --demod_completeness_check              fast
% 6.34/1.52  --demod_use_ground                      true
% 6.34/1.52  --sup_to_prop_solver                    passive
% 6.34/1.52  --sup_prop_simpl_new                    true
% 6.34/1.52  --sup_prop_simpl_given                  true
% 6.34/1.52  --sup_fun_splitting                     false
% 6.34/1.52  --sup_smt_interval                      50000
% 6.34/1.52  
% 6.34/1.52  ------ Superposition Simplification Setup
% 6.34/1.52  
% 6.34/1.52  --sup_indices_passive                   []
% 6.34/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.34/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 6.34/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.52  --sup_full_bw                           [BwDemod]
% 6.34/1.52  --sup_immed_triv                        [TrivRules]
% 6.34/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.34/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.52  --sup_immed_bw_main                     []
% 6.34/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.34/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 6.34/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.34/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.34/1.52  
% 6.34/1.52  ------ Combination Options
% 6.34/1.52  
% 6.34/1.52  --comb_res_mult                         3
% 6.34/1.52  --comb_sup_mult                         2
% 6.34/1.52  --comb_inst_mult                        10
% 6.34/1.52  
% 6.34/1.52  ------ Debug Options
% 6.34/1.52  
% 6.34/1.52  --dbg_backtrace                         false
% 6.34/1.52  --dbg_dump_prop_clauses                 false
% 6.34/1.52  --dbg_dump_prop_clauses_file            -
% 6.34/1.52  --dbg_out_stat                          false
% 6.34/1.52  
% 6.34/1.52  
% 6.34/1.52  
% 6.34/1.52  
% 6.34/1.52  ------ Proving...
% 6.34/1.52  
% 6.34/1.52  
% 6.34/1.52  % SZS status Theorem for theBenchmark.p
% 6.34/1.52  
% 6.34/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 6.34/1.52  
% 6.34/1.52  fof(f11,conjecture,(
% 6.34/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f12,negated_conjecture,(
% 6.34/1.52    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 6.34/1.52    inference(negated_conjecture,[],[f11])).
% 6.34/1.52  
% 6.34/1.52  fof(f24,plain,(
% 6.34/1.52    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.34/1.52    inference(ennf_transformation,[],[f12])).
% 6.34/1.52  
% 6.34/1.52  fof(f25,plain,(
% 6.34/1.52    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.34/1.52    inference(flattening,[],[f24])).
% 6.34/1.52  
% 6.34/1.52  fof(f28,plain,(
% 6.34/1.52    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 6.34/1.52    introduced(choice_axiom,[])).
% 6.34/1.52  
% 6.34/1.52  fof(f29,plain,(
% 6.34/1.52    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 6.34/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f28])).
% 6.34/1.52  
% 6.34/1.52  fof(f44,plain,(
% 6.34/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 6.34/1.52    inference(cnf_transformation,[],[f29])).
% 6.34/1.52  
% 6.34/1.52  fof(f3,axiom,(
% 6.34/1.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f26,plain,(
% 6.34/1.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.34/1.52    inference(nnf_transformation,[],[f3])).
% 6.34/1.52  
% 6.34/1.52  fof(f33,plain,(
% 6.34/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.34/1.52    inference(cnf_transformation,[],[f26])).
% 6.34/1.52  
% 6.34/1.52  fof(f8,axiom,(
% 6.34/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f19,plain,(
% 6.34/1.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.34/1.52    inference(ennf_transformation,[],[f8])).
% 6.34/1.52  
% 6.34/1.52  fof(f20,plain,(
% 6.34/1.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.34/1.52    inference(flattening,[],[f19])).
% 6.34/1.52  
% 6.34/1.52  fof(f40,plain,(
% 6.34/1.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.34/1.52    inference(cnf_transformation,[],[f20])).
% 6.34/1.52  
% 6.34/1.52  fof(f4,axiom,(
% 6.34/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f16,plain,(
% 6.34/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.34/1.52    inference(ennf_transformation,[],[f4])).
% 6.34/1.52  
% 6.34/1.52  fof(f35,plain,(
% 6.34/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.34/1.52    inference(cnf_transformation,[],[f16])).
% 6.34/1.52  
% 6.34/1.52  fof(f34,plain,(
% 6.34/1.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.34/1.52    inference(cnf_transformation,[],[f26])).
% 6.34/1.52  
% 6.34/1.52  fof(f7,axiom,(
% 6.34/1.52    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f38,plain,(
% 6.34/1.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 6.34/1.52    inference(cnf_transformation,[],[f7])).
% 6.34/1.52  
% 6.34/1.52  fof(f45,plain,(
% 6.34/1.52    r1_tarski(sK1,sK2)),
% 6.34/1.52    inference(cnf_transformation,[],[f29])).
% 6.34/1.52  
% 6.34/1.52  fof(f1,axiom,(
% 6.34/1.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f13,plain,(
% 6.34/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.34/1.52    inference(ennf_transformation,[],[f1])).
% 6.34/1.52  
% 6.34/1.52  fof(f14,plain,(
% 6.34/1.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 6.34/1.52    inference(flattening,[],[f13])).
% 6.34/1.52  
% 6.34/1.52  fof(f30,plain,(
% 6.34/1.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 6.34/1.52    inference(cnf_transformation,[],[f14])).
% 6.34/1.52  
% 6.34/1.52  fof(f5,axiom,(
% 6.34/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f36,plain,(
% 6.34/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.34/1.52    inference(cnf_transformation,[],[f5])).
% 6.34/1.52  
% 6.34/1.52  fof(f6,axiom,(
% 6.34/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f17,plain,(
% 6.34/1.52    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.34/1.52    inference(ennf_transformation,[],[f6])).
% 6.34/1.52  
% 6.34/1.52  fof(f18,plain,(
% 6.34/1.52    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 6.34/1.52    inference(flattening,[],[f17])).
% 6.34/1.52  
% 6.34/1.52  fof(f37,plain,(
% 6.34/1.52    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.34/1.52    inference(cnf_transformation,[],[f18])).
% 6.34/1.52  
% 6.34/1.52  fof(f9,axiom,(
% 6.34/1.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f21,plain,(
% 6.34/1.52    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.34/1.52    inference(ennf_transformation,[],[f9])).
% 6.34/1.52  
% 6.34/1.52  fof(f41,plain,(
% 6.34/1.52    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.34/1.52    inference(cnf_transformation,[],[f21])).
% 6.34/1.52  
% 6.34/1.52  fof(f10,axiom,(
% 6.34/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 6.34/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.34/1.52  
% 6.34/1.52  fof(f22,plain,(
% 6.34/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 6.34/1.52    inference(ennf_transformation,[],[f10])).
% 6.34/1.52  
% 6.34/1.52  fof(f23,plain,(
% 6.34/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.34/1.52    inference(flattening,[],[f22])).
% 6.34/1.52  
% 6.34/1.52  fof(f27,plain,(
% 6.34/1.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.34/1.52    inference(nnf_transformation,[],[f23])).
% 6.34/1.52  
% 6.34/1.52  fof(f43,plain,(
% 6.34/1.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.34/1.52    inference(cnf_transformation,[],[f27])).
% 6.34/1.52  
% 6.34/1.52  fof(f47,plain,(
% 6.34/1.52    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.34/1.52    inference(equality_resolution,[],[f43])).
% 6.34/1.52  
% 6.34/1.52  fof(f46,plain,(
% 6.34/1.52    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 6.34/1.52    inference(cnf_transformation,[],[f29])).
% 6.34/1.52  
% 6.34/1.52  cnf(c_16,negated_conjecture,
% 6.34/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 6.34/1.52      inference(cnf_transformation,[],[f44]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_898,plain,
% 6.34/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_4,plain,
% 6.34/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.34/1.52      inference(cnf_transformation,[],[f33]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_904,plain,
% 6.34/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.34/1.52      | r1_tarski(X0,X1) = iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_1207,plain,
% 6.34/1.52      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_898,c_904]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_9,plain,
% 6.34/1.52      ( ~ r1_tarski(X0,X1)
% 6.34/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 6.34/1.52      | ~ v1_relat_1(X0)
% 6.34/1.52      | ~ v1_relat_1(X1) ),
% 6.34/1.52      inference(cnf_transformation,[],[f40]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_5,plain,
% 6.34/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.34/1.52      | ~ v1_relat_1(X1)
% 6.34/1.52      | v1_relat_1(X0) ),
% 6.34/1.52      inference(cnf_transformation,[],[f35]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_3,plain,
% 6.34/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.34/1.52      inference(cnf_transformation,[],[f34]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_102,plain,
% 6.34/1.52      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 6.34/1.52      | ~ r1_tarski(X0,X1)
% 6.34/1.52      | ~ v1_relat_1(X1) ),
% 6.34/1.52      inference(global_propositional_subsumption,
% 6.34/1.52                [status(thm)],
% 6.34/1.52                [c_9,c_5,c_3]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_103,plain,
% 6.34/1.52      ( ~ r1_tarski(X0,X1)
% 6.34/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 6.34/1.52      | ~ v1_relat_1(X1) ),
% 6.34/1.52      inference(renaming,[status(thm)],[c_102]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_896,plain,
% 6.34/1.52      ( r1_tarski(X0,X1) != iProver_top
% 6.34/1.52      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 6.34/1.52      | v1_relat_1(X1) != iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_103]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_8,plain,
% 6.34/1.52      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
% 6.34/1.52      inference(cnf_transformation,[],[f38]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_901,plain,
% 6.34/1.52      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_15,negated_conjecture,
% 6.34/1.52      ( r1_tarski(sK1,sK2) ),
% 6.34/1.52      inference(cnf_transformation,[],[f45]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_899,plain,
% 6.34/1.52      ( r1_tarski(sK1,sK2) = iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_0,plain,
% 6.34/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 6.34/1.52      inference(cnf_transformation,[],[f30]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_908,plain,
% 6.34/1.52      ( r1_tarski(X0,X1) != iProver_top
% 6.34/1.52      | r1_tarski(X2,X0) != iProver_top
% 6.34/1.52      | r1_tarski(X2,X1) = iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_2436,plain,
% 6.34/1.52      ( r1_tarski(X0,sK2) = iProver_top
% 6.34/1.52      | r1_tarski(X0,sK1) != iProver_top ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_899,c_908]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_2587,plain,
% 6.34/1.52      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,sK1)),sK2) = iProver_top ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_901,c_2436]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_2593,plain,
% 6.34/1.52      ( r1_tarski(X0,k2_relat_1(k2_zfmisc_1(X1,sK1))) != iProver_top
% 6.34/1.52      | r1_tarski(X0,sK2) = iProver_top ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_2587,c_908]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_3159,plain,
% 6.34/1.52      ( r1_tarski(X0,k2_zfmisc_1(X1,sK1)) != iProver_top
% 6.34/1.52      | r1_tarski(k2_relat_1(X0),sK2) = iProver_top
% 6.34/1.52      | v1_relat_1(k2_zfmisc_1(X1,sK1)) != iProver_top ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_896,c_2593]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_6,plain,
% 6.34/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 6.34/1.52      inference(cnf_transformation,[],[f36]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_903,plain,
% 6.34/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_20970,plain,
% 6.34/1.52      ( r1_tarski(X0,k2_zfmisc_1(X1,sK1)) != iProver_top
% 6.34/1.52      | r1_tarski(k2_relat_1(X0),sK2) = iProver_top ),
% 6.34/1.52      inference(forward_subsumption_resolution,
% 6.34/1.52                [status(thm)],
% 6.34/1.52                [c_3159,c_903]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_20977,plain,
% 6.34/1.52      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_1207,c_20970]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_7,plain,
% 6.34/1.52      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 6.34/1.52      | ~ v1_relat_1(X0)
% 6.34/1.52      | k8_relat_1(X1,X0) = X0 ),
% 6.34/1.52      inference(cnf_transformation,[],[f37]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_902,plain,
% 6.34/1.52      ( k8_relat_1(X0,X1) = X1
% 6.34/1.52      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 6.34/1.52      | v1_relat_1(X1) != iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_21573,plain,
% 6.34/1.52      ( k8_relat_1(sK2,sK3) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_20977,c_902]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_140,plain,
% 6.34/1.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 6.34/1.52      inference(prop_impl,[status(thm)],[c_3]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_141,plain,
% 6.34/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 6.34/1.52      inference(renaming,[status(thm)],[c_140]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_171,plain,
% 6.34/1.52      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 6.34/1.52      inference(bin_hyper_res,[status(thm)],[c_5,c_141]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_895,plain,
% 6.34/1.52      ( r1_tarski(X0,X1) != iProver_top
% 6.34/1.52      | v1_relat_1(X1) != iProver_top
% 6.34/1.52      | v1_relat_1(X0) = iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_1479,plain,
% 6.34/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 6.34/1.52      | v1_relat_1(sK3) = iProver_top ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_1207,c_895]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_1867,plain,
% 6.34/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 6.34/1.52      inference(forward_subsumption_resolution,
% 6.34/1.52                [status(thm)],
% 6.34/1.52                [c_1479,c_903]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_7439,plain,
% 6.34/1.52      ( ~ r1_tarski(k2_relat_1(sK3),X0)
% 6.34/1.52      | ~ v1_relat_1(sK3)
% 6.34/1.52      | k8_relat_1(X0,sK3) = sK3 ),
% 6.34/1.52      inference(instantiation,[status(thm)],[c_7]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_16094,plain,
% 6.34/1.52      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 6.34/1.52      | ~ v1_relat_1(sK3)
% 6.34/1.52      | k8_relat_1(sK2,sK3) = sK3 ),
% 6.34/1.52      inference(instantiation,[status(thm)],[c_7439]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_16099,plain,
% 6.34/1.52      ( k8_relat_1(sK2,sK3) = sK3
% 6.34/1.52      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 6.34/1.52      | v1_relat_1(sK3) != iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_16094]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_22430,plain,
% 6.34/1.52      ( k8_relat_1(sK2,sK3) = sK3 ),
% 6.34/1.52      inference(global_propositional_subsumption,
% 6.34/1.52                [status(thm)],
% 6.34/1.52                [c_21573,c_1867,c_16099,c_20977]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_11,plain,
% 6.34/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.52      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 6.34/1.52      inference(cnf_transformation,[],[f41]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_900,plain,
% 6.34/1.52      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
% 6.34/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_1638,plain,
% 6.34/1.52      ( k6_relset_1(sK0,sK1,X0,sK3) = k8_relat_1(X0,sK3) ),
% 6.34/1.52      inference(superposition,[status(thm)],[c_898,c_900]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_12,plain,
% 6.34/1.52      ( r2_relset_1(X0,X1,X2,X2)
% 6.34/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 6.34/1.52      inference(cnf_transformation,[],[f47]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_14,negated_conjecture,
% 6.34/1.52      ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
% 6.34/1.52      inference(cnf_transformation,[],[f46]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_236,plain,
% 6.34/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.34/1.52      | k6_relset_1(sK0,sK1,sK2,sK3) != X0
% 6.34/1.52      | sK3 != X0
% 6.34/1.52      | sK1 != X2
% 6.34/1.52      | sK0 != X1 ),
% 6.34/1.52      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_237,plain,
% 6.34/1.52      ( ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 6.34/1.52      | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
% 6.34/1.52      inference(unflattening,[status(thm)],[c_236]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_894,plain,
% 6.34/1.52      ( sK3 != k6_relset_1(sK0,sK1,sK2,sK3)
% 6.34/1.52      | m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_1789,plain,
% 6.34/1.52      ( k8_relat_1(sK2,sK3) != sK3
% 6.34/1.52      | m1_subset_1(k8_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 6.34/1.52      inference(demodulation,[status(thm)],[c_1638,c_894]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_22433,plain,
% 6.34/1.52      ( sK3 != sK3
% 6.34/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 6.34/1.52      inference(demodulation,[status(thm)],[c_22430,c_1789]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_520,plain,( X0 = X0 ),theory(equality) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_1216,plain,
% 6.34/1.52      ( sK3 = sK3 ),
% 6.34/1.52      inference(instantiation,[status(thm)],[c_520]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(c_17,plain,
% 6.34/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 6.34/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.34/1.52  
% 6.34/1.52  cnf(contradiction,plain,
% 6.34/1.52      ( $false ),
% 6.34/1.52      inference(minisat,[status(thm)],[c_22433,c_1216,c_17]) ).
% 6.34/1.52  
% 6.34/1.52  
% 6.34/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 6.34/1.52  
% 6.34/1.52  ------                               Statistics
% 6.34/1.52  
% 6.34/1.52  ------ General
% 6.34/1.52  
% 6.34/1.52  abstr_ref_over_cycles:                  0
% 6.34/1.52  abstr_ref_under_cycles:                 0
% 6.34/1.52  gc_basic_clause_elim:                   0
% 6.34/1.52  forced_gc_time:                         0
% 6.34/1.52  parsing_time:                           0.024
% 6.34/1.52  unif_index_cands_time:                  0.
% 6.34/1.52  unif_index_add_time:                    0.
% 6.34/1.52  orderings_time:                         0.
% 6.34/1.52  out_proof_time:                         0.008
% 6.34/1.52  total_time:                             0.696
% 6.34/1.52  num_of_symbols:                         45
% 6.34/1.52  num_of_terms:                           31275
% 6.34/1.52  
% 6.34/1.52  ------ Preprocessing
% 6.34/1.52  
% 6.34/1.52  num_of_splits:                          0
% 6.34/1.52  num_of_split_atoms:                     0
% 6.34/1.52  num_of_reused_defs:                     0
% 6.34/1.52  num_eq_ax_congr_red:                    9
% 6.34/1.52  num_of_sem_filtered_clauses:            1
% 6.34/1.52  num_of_subtypes:                        0
% 6.34/1.52  monotx_restored_types:                  0
% 6.34/1.52  sat_num_of_epr_types:                   0
% 6.34/1.52  sat_num_of_non_cyclic_types:            0
% 6.34/1.52  sat_guarded_non_collapsed_types:        0
% 6.34/1.52  num_pure_diseq_elim:                    0
% 6.34/1.52  simp_replaced_by:                       0
% 6.34/1.52  res_preprocessed:                       81
% 6.34/1.52  prep_upred:                             0
% 6.34/1.52  prep_unflattend:                        15
% 6.34/1.52  smt_new_axioms:                         0
% 6.34/1.52  pred_elim_cands:                        3
% 6.34/1.52  pred_elim:                              1
% 6.34/1.52  pred_elim_cl:                           2
% 6.34/1.52  pred_elim_cycles:                       3
% 6.34/1.52  merged_defs:                            8
% 6.34/1.52  merged_defs_ncl:                        0
% 6.34/1.52  bin_hyper_res:                          9
% 6.34/1.52  prep_cycles:                            4
% 6.34/1.52  pred_elim_time:                         0.004
% 6.34/1.52  splitting_time:                         0.
% 6.34/1.52  sem_filter_time:                        0.
% 6.34/1.52  monotx_time:                            0.
% 6.34/1.52  subtype_inf_time:                       0.
% 6.34/1.52  
% 6.34/1.52  ------ Problem properties
% 6.34/1.52  
% 6.34/1.52  clauses:                                15
% 6.34/1.52  conjectures:                            2
% 6.34/1.52  epr:                                    3
% 6.34/1.52  horn:                                   15
% 6.34/1.52  ground:                                 3
% 6.34/1.52  unary:                                  4
% 6.34/1.52  binary:                                 6
% 6.34/1.52  lits:                                   31
% 6.34/1.52  lits_eq:                                3
% 6.34/1.52  fd_pure:                                0
% 6.34/1.52  fd_pseudo:                              0
% 6.34/1.52  fd_cond:                                0
% 6.34/1.52  fd_pseudo_cond:                         0
% 6.34/1.52  ac_symbols:                             0
% 6.34/1.52  
% 6.34/1.52  ------ Propositional Solver
% 6.34/1.52  
% 6.34/1.52  prop_solver_calls:                      30
% 6.34/1.52  prop_fast_solver_calls:                 764
% 6.34/1.52  smt_solver_calls:                       0
% 6.34/1.52  smt_fast_solver_calls:                  0
% 6.34/1.52  prop_num_of_clauses:                    9615
% 6.34/1.52  prop_preprocess_simplified:             21157
% 6.34/1.52  prop_fo_subsumed:                       8
% 6.34/1.52  prop_solver_time:                       0.
% 6.34/1.52  smt_solver_time:                        0.
% 6.34/1.52  smt_fast_solver_time:                   0.
% 6.34/1.52  prop_fast_solver_time:                  0.
% 6.34/1.52  prop_unsat_core_time:                   0.001
% 6.34/1.52  
% 6.34/1.52  ------ QBF
% 6.34/1.52  
% 6.34/1.52  qbf_q_res:                              0
% 6.34/1.52  qbf_num_tautologies:                    0
% 6.34/1.52  qbf_prep_cycles:                        0
% 6.34/1.52  
% 6.34/1.52  ------ BMC1
% 6.34/1.52  
% 6.34/1.52  bmc1_current_bound:                     -1
% 6.34/1.52  bmc1_last_solved_bound:                 -1
% 6.34/1.52  bmc1_unsat_core_size:                   -1
% 6.34/1.52  bmc1_unsat_core_parents_size:           -1
% 6.34/1.52  bmc1_merge_next_fun:                    0
% 6.34/1.52  bmc1_unsat_core_clauses_time:           0.
% 6.34/1.52  
% 6.34/1.52  ------ Instantiation
% 6.34/1.52  
% 6.34/1.52  inst_num_of_clauses:                    2603
% 6.34/1.52  inst_num_in_passive:                    1285
% 6.34/1.52  inst_num_in_active:                     659
% 6.34/1.52  inst_num_in_unprocessed:                659
% 6.34/1.52  inst_num_of_loops:                      750
% 6.34/1.52  inst_num_of_learning_restarts:          0
% 6.34/1.52  inst_num_moves_active_passive:          90
% 6.34/1.52  inst_lit_activity:                      0
% 6.34/1.52  inst_lit_activity_moves:                2
% 6.34/1.52  inst_num_tautologies:                   0
% 6.34/1.52  inst_num_prop_implied:                  0
% 6.34/1.52  inst_num_existing_simplified:           0
% 6.34/1.52  inst_num_eq_res_simplified:             0
% 6.34/1.52  inst_num_child_elim:                    0
% 6.34/1.52  inst_num_of_dismatching_blockings:      2301
% 6.34/1.52  inst_num_of_non_proper_insts:           1690
% 6.34/1.52  inst_num_of_duplicates:                 0
% 6.34/1.52  inst_inst_num_from_inst_to_res:         0
% 6.34/1.52  inst_dismatching_checking_time:         0.
% 6.34/1.52  
% 6.34/1.52  ------ Resolution
% 6.34/1.52  
% 6.34/1.52  res_num_of_clauses:                     0
% 6.34/1.52  res_num_in_passive:                     0
% 6.34/1.52  res_num_in_active:                      0
% 6.34/1.52  res_num_of_loops:                       85
% 6.34/1.52  res_forward_subset_subsumed:            52
% 6.34/1.52  res_backward_subset_subsumed:           0
% 6.34/1.52  res_forward_subsumed:                   0
% 6.34/1.52  res_backward_subsumed:                  0
% 6.34/1.52  res_forward_subsumption_resolution:     0
% 6.34/1.52  res_backward_subsumption_resolution:    0
% 6.34/1.52  res_clause_to_clause_subsumption:       2517
% 6.34/1.52  res_orphan_elimination:                 0
% 6.34/1.52  res_tautology_del:                      300
% 6.34/1.52  res_num_eq_res_simplified:              0
% 6.34/1.52  res_num_sel_changes:                    0
% 6.34/1.52  res_moves_from_active_to_pass:          0
% 6.34/1.52  
% 6.34/1.52  ------ Superposition
% 6.34/1.52  
% 6.34/1.52  sup_time_total:                         0.
% 6.34/1.52  sup_time_generating:                    0.
% 6.34/1.52  sup_time_sim_full:                      0.
% 6.34/1.52  sup_time_sim_immed:                     0.
% 6.34/1.52  
% 6.34/1.52  sup_num_of_clauses:                     503
% 6.34/1.52  sup_num_in_active:                      146
% 6.34/1.52  sup_num_in_passive:                     357
% 6.34/1.52  sup_num_of_loops:                       148
% 6.34/1.52  sup_fw_superposition:                   269
% 6.34/1.52  sup_bw_superposition:                   381
% 6.34/1.52  sup_immediate_simplified:               130
% 6.34/1.52  sup_given_eliminated:                   0
% 6.34/1.52  comparisons_done:                       0
% 6.34/1.52  comparisons_avoided:                    0
% 6.34/1.52  
% 6.34/1.52  ------ Simplifications
% 6.34/1.52  
% 6.34/1.52  
% 6.34/1.52  sim_fw_subset_subsumed:                 85
% 6.34/1.52  sim_bw_subset_subsumed:                 12
% 6.34/1.52  sim_fw_subsumed:                        31
% 6.34/1.52  sim_bw_subsumed:                        7
% 6.34/1.52  sim_fw_subsumption_res:                 18
% 6.34/1.52  sim_bw_subsumption_res:                 0
% 6.34/1.52  sim_tautology_del:                      1
% 6.34/1.52  sim_eq_tautology_del:                   0
% 6.34/1.52  sim_eq_res_simp:                        0
% 6.34/1.52  sim_fw_demodulated:                     0
% 6.34/1.52  sim_bw_demodulated:                     2
% 6.34/1.52  sim_light_normalised:                   0
% 6.34/1.52  sim_joinable_taut:                      0
% 6.34/1.52  sim_joinable_simp:                      0
% 6.34/1.52  sim_ac_normalised:                      0
% 6.34/1.52  sim_smt_subsumption:                    0
% 6.34/1.52  
%------------------------------------------------------------------------------
