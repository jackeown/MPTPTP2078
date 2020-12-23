%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:56 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 178 expanded)
%              Number of clauses        :   63 (  84 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  248 ( 475 expanded)
%              Number of equality atoms :   88 ( 104 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0_42,X0_43)
    | m1_subset_1(X1_42,X1_43)
    | X1_43 != X0_43
    | X1_42 != X0_42 ),
    theory(equality)).

cnf(c_564,plain,
    ( m1_subset_1(X0_42,X0_43)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0_43 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | X0_42 != sK3 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_595,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | X0_42 != sK3 ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_1127,plain,
    ( m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k6_relset_1(sK0,sK1,sK2,sK3) != sK3 ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_238,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_467,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_238])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_3,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_153,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_6,c_3])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)))
    | r1_tarski(k2_relat_1(X0_42),X0_45)
    | ~ v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_470,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top
    | r1_tarski(k2_relat_1(X0_42),X0_45) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_242,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_270,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_242])).

cnf(c_285,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top
    | r1_tarski(k2_relat_1(X0_42),X0_45) = iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_243,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42))
    | ~ v1_relat_1(X1_42)
    | v1_relat_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)))
    | v1_relat_1(X0_42)
    | ~ v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_538,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top
    | v1_relat_1(X0_42) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_868,plain,
    ( r1_tarski(k2_relat_1(X0_42),X0_45) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_270,c_285,c_538])).

cnf(c_869,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top
    | r1_tarski(k2_relat_1(X0_42),X0_45) = iProver_top ),
    inference(renaming,[status(thm)],[c_868])).

cnf(c_876,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_467,c_869])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_239,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_466,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0_45,X1_45)
    | ~ r1_tarski(X2_45,X0_45)
    | r1_tarski(X2_45,X1_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_461,plain,
    ( r1_tarski(X0_45,X1_45) != iProver_top
    | r1_tarski(X2_45,X0_45) != iProver_top
    | r1_tarski(X2_45,X1_45) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_244])).

cnf(c_680,plain,
    ( r1_tarski(X0_45,sK2) = iProver_top
    | r1_tarski(X0_45,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_466,c_461])).

cnf(c_882,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_876,c_680])).

cnf(c_5,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_241,plain,
    ( ~ r1_tarski(k2_relat_1(X0_42),X0_45)
    | ~ v1_relat_1(X0_42)
    | k8_relat_1(X0_45,X0_42) = X0_42 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_790,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | k8_relat_1(sK2,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_791,plain,
    ( k8_relat_1(sK2,sK3) = sK3
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_251,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_611,plain,
    ( X0_42 != X1_42
    | k6_relset_1(sK0,sK1,sK2,sK3) != X1_42
    | k6_relset_1(sK0,sK1,sK2,sK3) = X0_42 ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_663,plain,
    ( X0_42 != k8_relat_1(sK2,sK3)
    | k6_relset_1(sK0,sK1,sK2,sK3) = X0_42
    | k6_relset_1(sK0,sK1,sK2,sK3) != k8_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_664,plain,
    ( k6_relset_1(sK0,sK1,sK2,sK3) != k8_relat_1(sK2,sK3)
    | k6_relset_1(sK0,sK1,sK2,sK3) = sK3
    | sK3 != k8_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_652,plain,
    ( k8_relat_1(sK2,sK3) != X0_42
    | sK3 != X0_42
    | sK3 = k8_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_653,plain,
    ( k8_relat_1(sK2,sK3) != sK3
    | sK3 = k8_relat_1(sK2,sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_652])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)))
    | k6_relset_1(X0_44,X0_45,X1_45,X0_42) = k8_relat_1(X1_45,X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_607,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k6_relset_1(sK0,sK1,sK2,sK3) = k8_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_574,plain,
    ( k6_relset_1(sK0,sK1,sK2,sK3) != X0_42
    | sK3 != X0_42
    | sK3 = k6_relset_1(sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_606,plain,
    ( k6_relset_1(sK0,sK1,sK2,sK3) != k8_relat_1(sK2,sK3)
    | sK3 = k6_relset_1(sK0,sK1,sK2,sK3)
    | sK3 != k8_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_249,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_596,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_249])).

cnf(c_540,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(sK0,sK1,sK2,sK3) != X0
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_134])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_135])).

cnf(c_246,plain,
    ( ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sP0_iProver_split
    | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_237])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_237])).

cnf(c_283,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_312,plain,
    ( ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_11,c_283])).

cnf(c_272,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_248,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_265,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_12,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1127,c_882,c_791,c_664,c_653,c_607,c_606,c_596,c_540,c_312,c_272,c_265,c_12,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:18:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 0.83/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.83/1.05  
% 0.83/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.83/1.05  
% 0.83/1.05  ------  iProver source info
% 0.83/1.05  
% 0.83/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.83/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.83/1.05  git: non_committed_changes: false
% 0.83/1.05  git: last_make_outside_of_git: false
% 0.83/1.05  
% 0.83/1.05  ------ 
% 0.83/1.05  
% 0.83/1.05  ------ Input Options
% 0.83/1.05  
% 0.83/1.05  --out_options                           all
% 0.83/1.05  --tptp_safe_out                         true
% 0.83/1.05  --problem_path                          ""
% 0.83/1.05  --include_path                          ""
% 0.83/1.05  --clausifier                            res/vclausify_rel
% 0.83/1.05  --clausifier_options                    --mode clausify
% 0.83/1.05  --stdin                                 false
% 0.83/1.05  --stats_out                             all
% 0.83/1.05  
% 0.83/1.05  ------ General Options
% 0.83/1.05  
% 0.83/1.05  --fof                                   false
% 0.83/1.05  --time_out_real                         305.
% 0.83/1.05  --time_out_virtual                      -1.
% 0.83/1.05  --symbol_type_check                     false
% 0.83/1.05  --clausify_out                          false
% 0.83/1.05  --sig_cnt_out                           false
% 0.83/1.05  --trig_cnt_out                          false
% 0.83/1.05  --trig_cnt_out_tolerance                1.
% 0.83/1.05  --trig_cnt_out_sk_spl                   false
% 0.83/1.05  --abstr_cl_out                          false
% 0.83/1.05  
% 0.83/1.05  ------ Global Options
% 0.83/1.05  
% 0.83/1.05  --schedule                              default
% 0.83/1.05  --add_important_lit                     false
% 0.83/1.05  --prop_solver_per_cl                    1000
% 0.83/1.05  --min_unsat_core                        false
% 0.83/1.05  --soft_assumptions                      false
% 0.83/1.05  --soft_lemma_size                       3
% 0.83/1.05  --prop_impl_unit_size                   0
% 0.83/1.05  --prop_impl_unit                        []
% 0.83/1.05  --share_sel_clauses                     true
% 0.83/1.05  --reset_solvers                         false
% 0.83/1.05  --bc_imp_inh                            [conj_cone]
% 0.83/1.05  --conj_cone_tolerance                   3.
% 0.83/1.05  --extra_neg_conj                        none
% 0.83/1.05  --large_theory_mode                     true
% 0.83/1.05  --prolific_symb_bound                   200
% 0.83/1.05  --lt_threshold                          2000
% 0.83/1.05  --clause_weak_htbl                      true
% 0.83/1.05  --gc_record_bc_elim                     false
% 0.83/1.05  
% 0.83/1.05  ------ Preprocessing Options
% 0.83/1.05  
% 0.83/1.05  --preprocessing_flag                    true
% 0.83/1.05  --time_out_prep_mult                    0.1
% 0.83/1.05  --splitting_mode                        input
% 0.83/1.05  --splitting_grd                         true
% 0.83/1.05  --splitting_cvd                         false
% 0.83/1.05  --splitting_cvd_svl                     false
% 0.83/1.05  --splitting_nvd                         32
% 0.83/1.05  --sub_typing                            true
% 0.83/1.05  --prep_gs_sim                           true
% 0.83/1.05  --prep_unflatten                        true
% 0.83/1.05  --prep_res_sim                          true
% 0.83/1.05  --prep_upred                            true
% 0.83/1.05  --prep_sem_filter                       exhaustive
% 0.83/1.05  --prep_sem_filter_out                   false
% 0.83/1.05  --pred_elim                             true
% 0.83/1.05  --res_sim_input                         true
% 0.83/1.05  --eq_ax_congr_red                       true
% 0.83/1.05  --pure_diseq_elim                       true
% 0.83/1.05  --brand_transform                       false
% 0.83/1.05  --non_eq_to_eq                          false
% 0.83/1.05  --prep_def_merge                        true
% 0.83/1.05  --prep_def_merge_prop_impl              false
% 0.83/1.05  --prep_def_merge_mbd                    true
% 0.83/1.05  --prep_def_merge_tr_red                 false
% 0.83/1.05  --prep_def_merge_tr_cl                  false
% 0.83/1.05  --smt_preprocessing                     true
% 0.83/1.05  --smt_ac_axioms                         fast
% 0.83/1.05  --preprocessed_out                      false
% 0.83/1.05  --preprocessed_stats                    false
% 0.83/1.05  
% 0.83/1.05  ------ Abstraction refinement Options
% 0.83/1.05  
% 0.83/1.05  --abstr_ref                             []
% 0.83/1.05  --abstr_ref_prep                        false
% 0.83/1.05  --abstr_ref_until_sat                   false
% 0.83/1.05  --abstr_ref_sig_restrict                funpre
% 0.83/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/1.05  --abstr_ref_under                       []
% 0.83/1.05  
% 0.83/1.05  ------ SAT Options
% 0.83/1.05  
% 0.83/1.05  --sat_mode                              false
% 0.83/1.05  --sat_fm_restart_options                ""
% 0.83/1.05  --sat_gr_def                            false
% 0.83/1.05  --sat_epr_types                         true
% 0.83/1.05  --sat_non_cyclic_types                  false
% 0.83/1.05  --sat_finite_models                     false
% 0.83/1.05  --sat_fm_lemmas                         false
% 0.83/1.05  --sat_fm_prep                           false
% 0.83/1.05  --sat_fm_uc_incr                        true
% 0.83/1.05  --sat_out_model                         small
% 0.83/1.05  --sat_out_clauses                       false
% 0.83/1.05  
% 0.83/1.05  ------ QBF Options
% 0.83/1.05  
% 0.83/1.05  --qbf_mode                              false
% 0.83/1.05  --qbf_elim_univ                         false
% 0.83/1.05  --qbf_dom_inst                          none
% 0.83/1.05  --qbf_dom_pre_inst                      false
% 0.83/1.05  --qbf_sk_in                             false
% 0.83/1.05  --qbf_pred_elim                         true
% 0.83/1.05  --qbf_split                             512
% 0.83/1.05  
% 0.83/1.05  ------ BMC1 Options
% 0.83/1.05  
% 0.83/1.05  --bmc1_incremental                      false
% 0.83/1.05  --bmc1_axioms                           reachable_all
% 0.83/1.05  --bmc1_min_bound                        0
% 0.83/1.05  --bmc1_max_bound                        -1
% 0.83/1.05  --bmc1_max_bound_default                -1
% 0.83/1.05  --bmc1_symbol_reachability              true
% 0.83/1.05  --bmc1_property_lemmas                  false
% 0.83/1.05  --bmc1_k_induction                      false
% 0.83/1.05  --bmc1_non_equiv_states                 false
% 0.83/1.05  --bmc1_deadlock                         false
% 0.83/1.05  --bmc1_ucm                              false
% 0.83/1.05  --bmc1_add_unsat_core                   none
% 0.83/1.05  --bmc1_unsat_core_children              false
% 0.83/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/1.05  --bmc1_out_stat                         full
% 0.83/1.05  --bmc1_ground_init                      false
% 0.83/1.05  --bmc1_pre_inst_next_state              false
% 0.83/1.05  --bmc1_pre_inst_state                   false
% 0.83/1.05  --bmc1_pre_inst_reach_state             false
% 0.83/1.05  --bmc1_out_unsat_core                   false
% 0.83/1.05  --bmc1_aig_witness_out                  false
% 0.83/1.05  --bmc1_verbose                          false
% 0.83/1.05  --bmc1_dump_clauses_tptp                false
% 0.83/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.83/1.05  --bmc1_dump_file                        -
% 0.83/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.83/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.83/1.05  --bmc1_ucm_extend_mode                  1
% 0.83/1.05  --bmc1_ucm_init_mode                    2
% 0.83/1.05  --bmc1_ucm_cone_mode                    none
% 0.83/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.83/1.05  --bmc1_ucm_relax_model                  4
% 0.83/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.83/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/1.05  --bmc1_ucm_layered_model                none
% 0.83/1.05  --bmc1_ucm_max_lemma_size               10
% 0.83/1.05  
% 0.83/1.05  ------ AIG Options
% 0.83/1.05  
% 0.83/1.05  --aig_mode                              false
% 0.83/1.05  
% 0.83/1.05  ------ Instantiation Options
% 0.83/1.05  
% 0.83/1.05  --instantiation_flag                    true
% 0.83/1.05  --inst_sos_flag                         false
% 0.83/1.05  --inst_sos_phase                        true
% 0.83/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/1.05  --inst_lit_sel_side                     num_symb
% 0.83/1.05  --inst_solver_per_active                1400
% 0.83/1.05  --inst_solver_calls_frac                1.
% 0.83/1.05  --inst_passive_queue_type               priority_queues
% 0.83/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/1.05  --inst_passive_queues_freq              [25;2]
% 0.83/1.05  --inst_dismatching                      true
% 0.83/1.05  --inst_eager_unprocessed_to_passive     true
% 0.83/1.05  --inst_prop_sim_given                   true
% 0.83/1.05  --inst_prop_sim_new                     false
% 0.83/1.05  --inst_subs_new                         false
% 0.83/1.05  --inst_eq_res_simp                      false
% 0.83/1.05  --inst_subs_given                       false
% 0.83/1.05  --inst_orphan_elimination               true
% 0.83/1.05  --inst_learning_loop_flag               true
% 0.83/1.05  --inst_learning_start                   3000
% 0.83/1.05  --inst_learning_factor                  2
% 0.83/1.05  --inst_start_prop_sim_after_learn       3
% 0.83/1.05  --inst_sel_renew                        solver
% 0.83/1.05  --inst_lit_activity_flag                true
% 0.83/1.05  --inst_restr_to_given                   false
% 0.83/1.05  --inst_activity_threshold               500
% 0.83/1.05  --inst_out_proof                        true
% 0.83/1.05  
% 0.83/1.05  ------ Resolution Options
% 0.83/1.05  
% 0.83/1.05  --resolution_flag                       true
% 0.83/1.05  --res_lit_sel                           adaptive
% 0.83/1.05  --res_lit_sel_side                      none
% 0.83/1.05  --res_ordering                          kbo
% 0.83/1.05  --res_to_prop_solver                    active
% 0.83/1.05  --res_prop_simpl_new                    false
% 0.83/1.05  --res_prop_simpl_given                  true
% 0.83/1.05  --res_passive_queue_type                priority_queues
% 0.83/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/1.05  --res_passive_queues_freq               [15;5]
% 0.83/1.05  --res_forward_subs                      full
% 0.83/1.05  --res_backward_subs                     full
% 0.83/1.05  --res_forward_subs_resolution           true
% 0.83/1.05  --res_backward_subs_resolution          true
% 0.83/1.05  --res_orphan_elimination                true
% 0.83/1.05  --res_time_limit                        2.
% 0.83/1.05  --res_out_proof                         true
% 0.83/1.05  
% 0.83/1.05  ------ Superposition Options
% 0.83/1.05  
% 0.83/1.05  --superposition_flag                    true
% 0.83/1.05  --sup_passive_queue_type                priority_queues
% 0.83/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.83/1.05  --demod_completeness_check              fast
% 0.83/1.05  --demod_use_ground                      true
% 0.83/1.05  --sup_to_prop_solver                    passive
% 0.83/1.05  --sup_prop_simpl_new                    true
% 0.83/1.05  --sup_prop_simpl_given                  true
% 0.83/1.05  --sup_fun_splitting                     false
% 0.83/1.05  --sup_smt_interval                      50000
% 0.83/1.05  
% 0.83/1.05  ------ Superposition Simplification Setup
% 0.83/1.05  
% 0.83/1.05  --sup_indices_passive                   []
% 0.83/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.05  --sup_full_bw                           [BwDemod]
% 0.83/1.05  --sup_immed_triv                        [TrivRules]
% 0.83/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.05  --sup_immed_bw_main                     []
% 0.83/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.05  
% 0.83/1.05  ------ Combination Options
% 0.83/1.05  
% 0.83/1.05  --comb_res_mult                         3
% 0.83/1.05  --comb_sup_mult                         2
% 0.83/1.05  --comb_inst_mult                        10
% 0.83/1.05  
% 0.83/1.05  ------ Debug Options
% 0.83/1.05  
% 0.83/1.05  --dbg_backtrace                         false
% 0.83/1.05  --dbg_dump_prop_clauses                 false
% 0.83/1.05  --dbg_dump_prop_clauses_file            -
% 0.83/1.05  --dbg_out_stat                          false
% 0.83/1.05  ------ Parsing...
% 0.83/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.83/1.05  
% 0.83/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.83/1.05  
% 0.83/1.05  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.83/1.05  
% 0.83/1.05  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.83/1.05  ------ Proving...
% 0.83/1.05  ------ Problem Properties 
% 0.83/1.05  
% 0.83/1.05  
% 0.83/1.05  clauses                                 10
% 0.83/1.05  conjectures                             2
% 0.83/1.05  EPR                                     2
% 0.83/1.05  Horn                                    10
% 0.83/1.05  unary                                   3
% 0.83/1.05  binary                                  2
% 0.83/1.05  lits                                    22
% 0.83/1.05  lits eq                                 3
% 0.83/1.05  fd_pure                                 0
% 0.83/1.05  fd_pseudo                               0
% 0.83/1.05  fd_cond                                 0
% 0.83/1.05  fd_pseudo_cond                          0
% 0.83/1.05  AC symbols                              0
% 0.83/1.05  
% 0.83/1.05  ------ Schedule dynamic 5 is on 
% 0.83/1.05  
% 0.83/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.83/1.05  
% 0.83/1.05  
% 0.83/1.05  ------ 
% 0.83/1.05  Current options:
% 0.83/1.05  ------ 
% 0.83/1.05  
% 0.83/1.05  ------ Input Options
% 0.83/1.05  
% 0.83/1.05  --out_options                           all
% 0.83/1.05  --tptp_safe_out                         true
% 0.83/1.05  --problem_path                          ""
% 0.83/1.05  --include_path                          ""
% 0.83/1.05  --clausifier                            res/vclausify_rel
% 0.83/1.05  --clausifier_options                    --mode clausify
% 0.83/1.05  --stdin                                 false
% 0.83/1.05  --stats_out                             all
% 0.83/1.05  
% 0.83/1.05  ------ General Options
% 0.83/1.05  
% 0.83/1.05  --fof                                   false
% 0.83/1.05  --time_out_real                         305.
% 0.83/1.05  --time_out_virtual                      -1.
% 0.83/1.05  --symbol_type_check                     false
% 0.83/1.05  --clausify_out                          false
% 0.83/1.05  --sig_cnt_out                           false
% 0.83/1.05  --trig_cnt_out                          false
% 0.83/1.05  --trig_cnt_out_tolerance                1.
% 0.83/1.05  --trig_cnt_out_sk_spl                   false
% 0.83/1.05  --abstr_cl_out                          false
% 0.83/1.05  
% 0.83/1.05  ------ Global Options
% 0.83/1.05  
% 0.83/1.05  --schedule                              default
% 0.83/1.05  --add_important_lit                     false
% 0.83/1.05  --prop_solver_per_cl                    1000
% 0.83/1.05  --min_unsat_core                        false
% 0.83/1.05  --soft_assumptions                      false
% 0.83/1.05  --soft_lemma_size                       3
% 0.83/1.05  --prop_impl_unit_size                   0
% 0.83/1.05  --prop_impl_unit                        []
% 0.83/1.05  --share_sel_clauses                     true
% 0.83/1.05  --reset_solvers                         false
% 0.83/1.05  --bc_imp_inh                            [conj_cone]
% 0.83/1.05  --conj_cone_tolerance                   3.
% 0.83/1.05  --extra_neg_conj                        none
% 0.83/1.05  --large_theory_mode                     true
% 0.83/1.05  --prolific_symb_bound                   200
% 0.83/1.05  --lt_threshold                          2000
% 0.83/1.05  --clause_weak_htbl                      true
% 0.83/1.05  --gc_record_bc_elim                     false
% 0.83/1.05  
% 0.83/1.05  ------ Preprocessing Options
% 0.83/1.05  
% 0.83/1.05  --preprocessing_flag                    true
% 0.83/1.05  --time_out_prep_mult                    0.1
% 0.83/1.05  --splitting_mode                        input
% 0.83/1.05  --splitting_grd                         true
% 0.83/1.05  --splitting_cvd                         false
% 0.83/1.05  --splitting_cvd_svl                     false
% 0.83/1.05  --splitting_nvd                         32
% 0.83/1.05  --sub_typing                            true
% 0.83/1.05  --prep_gs_sim                           true
% 0.83/1.05  --prep_unflatten                        true
% 0.83/1.05  --prep_res_sim                          true
% 0.83/1.05  --prep_upred                            true
% 0.83/1.05  --prep_sem_filter                       exhaustive
% 0.83/1.05  --prep_sem_filter_out                   false
% 0.83/1.05  --pred_elim                             true
% 0.83/1.05  --res_sim_input                         true
% 0.83/1.05  --eq_ax_congr_red                       true
% 0.83/1.05  --pure_diseq_elim                       true
% 0.83/1.05  --brand_transform                       false
% 0.83/1.05  --non_eq_to_eq                          false
% 0.83/1.05  --prep_def_merge                        true
% 0.83/1.05  --prep_def_merge_prop_impl              false
% 0.83/1.05  --prep_def_merge_mbd                    true
% 0.83/1.05  --prep_def_merge_tr_red                 false
% 0.83/1.05  --prep_def_merge_tr_cl                  false
% 0.83/1.05  --smt_preprocessing                     true
% 0.83/1.05  --smt_ac_axioms                         fast
% 0.83/1.05  --preprocessed_out                      false
% 0.83/1.05  --preprocessed_stats                    false
% 0.83/1.05  
% 0.83/1.05  ------ Abstraction refinement Options
% 0.83/1.05  
% 0.83/1.05  --abstr_ref                             []
% 0.83/1.05  --abstr_ref_prep                        false
% 0.83/1.05  --abstr_ref_until_sat                   false
% 0.83/1.05  --abstr_ref_sig_restrict                funpre
% 0.83/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/1.05  --abstr_ref_under                       []
% 0.83/1.05  
% 0.83/1.05  ------ SAT Options
% 0.83/1.05  
% 0.83/1.05  --sat_mode                              false
% 0.83/1.05  --sat_fm_restart_options                ""
% 0.83/1.05  --sat_gr_def                            false
% 0.83/1.05  --sat_epr_types                         true
% 0.83/1.05  --sat_non_cyclic_types                  false
% 0.83/1.05  --sat_finite_models                     false
% 0.83/1.05  --sat_fm_lemmas                         false
% 0.83/1.05  --sat_fm_prep                           false
% 0.83/1.05  --sat_fm_uc_incr                        true
% 0.83/1.05  --sat_out_model                         small
% 0.83/1.05  --sat_out_clauses                       false
% 0.83/1.05  
% 0.83/1.05  ------ QBF Options
% 0.83/1.05  
% 0.83/1.05  --qbf_mode                              false
% 0.83/1.05  --qbf_elim_univ                         false
% 0.83/1.05  --qbf_dom_inst                          none
% 0.83/1.05  --qbf_dom_pre_inst                      false
% 0.83/1.05  --qbf_sk_in                             false
% 0.83/1.05  --qbf_pred_elim                         true
% 0.83/1.05  --qbf_split                             512
% 0.83/1.05  
% 0.83/1.05  ------ BMC1 Options
% 0.83/1.05  
% 0.83/1.05  --bmc1_incremental                      false
% 0.83/1.05  --bmc1_axioms                           reachable_all
% 0.83/1.05  --bmc1_min_bound                        0
% 0.83/1.05  --bmc1_max_bound                        -1
% 0.83/1.05  --bmc1_max_bound_default                -1
% 0.83/1.05  --bmc1_symbol_reachability              true
% 0.83/1.05  --bmc1_property_lemmas                  false
% 0.83/1.05  --bmc1_k_induction                      false
% 0.83/1.05  --bmc1_non_equiv_states                 false
% 0.83/1.05  --bmc1_deadlock                         false
% 0.83/1.05  --bmc1_ucm                              false
% 0.83/1.05  --bmc1_add_unsat_core                   none
% 0.83/1.05  --bmc1_unsat_core_children              false
% 0.83/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/1.05  --bmc1_out_stat                         full
% 0.83/1.05  --bmc1_ground_init                      false
% 0.83/1.05  --bmc1_pre_inst_next_state              false
% 0.83/1.05  --bmc1_pre_inst_state                   false
% 0.83/1.05  --bmc1_pre_inst_reach_state             false
% 0.83/1.05  --bmc1_out_unsat_core                   false
% 0.83/1.05  --bmc1_aig_witness_out                  false
% 0.83/1.05  --bmc1_verbose                          false
% 0.83/1.05  --bmc1_dump_clauses_tptp                false
% 0.83/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.83/1.05  --bmc1_dump_file                        -
% 0.83/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.83/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.83/1.05  --bmc1_ucm_extend_mode                  1
% 0.83/1.05  --bmc1_ucm_init_mode                    2
% 0.83/1.05  --bmc1_ucm_cone_mode                    none
% 0.83/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.83/1.05  --bmc1_ucm_relax_model                  4
% 0.83/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.83/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/1.05  --bmc1_ucm_layered_model                none
% 0.83/1.05  --bmc1_ucm_max_lemma_size               10
% 0.83/1.05  
% 0.83/1.05  ------ AIG Options
% 0.83/1.05  
% 0.83/1.05  --aig_mode                              false
% 0.83/1.05  
% 0.83/1.05  ------ Instantiation Options
% 0.83/1.05  
% 0.83/1.05  --instantiation_flag                    true
% 0.83/1.05  --inst_sos_flag                         false
% 0.83/1.05  --inst_sos_phase                        true
% 0.83/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/1.05  --inst_lit_sel_side                     none
% 0.83/1.05  --inst_solver_per_active                1400
% 0.83/1.05  --inst_solver_calls_frac                1.
% 0.83/1.05  --inst_passive_queue_type               priority_queues
% 0.83/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/1.05  --inst_passive_queues_freq              [25;2]
% 0.83/1.05  --inst_dismatching                      true
% 0.83/1.05  --inst_eager_unprocessed_to_passive     true
% 0.83/1.05  --inst_prop_sim_given                   true
% 0.83/1.05  --inst_prop_sim_new                     false
% 0.83/1.05  --inst_subs_new                         false
% 0.83/1.05  --inst_eq_res_simp                      false
% 0.83/1.05  --inst_subs_given                       false
% 0.83/1.05  --inst_orphan_elimination               true
% 0.83/1.05  --inst_learning_loop_flag               true
% 0.83/1.05  --inst_learning_start                   3000
% 0.83/1.05  --inst_learning_factor                  2
% 0.83/1.05  --inst_start_prop_sim_after_learn       3
% 0.83/1.05  --inst_sel_renew                        solver
% 0.83/1.05  --inst_lit_activity_flag                true
% 0.83/1.05  --inst_restr_to_given                   false
% 0.83/1.05  --inst_activity_threshold               500
% 0.83/1.05  --inst_out_proof                        true
% 0.83/1.05  
% 0.83/1.05  ------ Resolution Options
% 0.83/1.05  
% 0.83/1.05  --resolution_flag                       false
% 0.83/1.05  --res_lit_sel                           adaptive
% 0.83/1.05  --res_lit_sel_side                      none
% 0.83/1.05  --res_ordering                          kbo
% 0.83/1.05  --res_to_prop_solver                    active
% 0.83/1.05  --res_prop_simpl_new                    false
% 0.83/1.05  --res_prop_simpl_given                  true
% 0.83/1.05  --res_passive_queue_type                priority_queues
% 0.83/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/1.05  --res_passive_queues_freq               [15;5]
% 0.83/1.05  --res_forward_subs                      full
% 0.83/1.05  --res_backward_subs                     full
% 0.83/1.05  --res_forward_subs_resolution           true
% 0.83/1.05  --res_backward_subs_resolution          true
% 0.83/1.05  --res_orphan_elimination                true
% 0.83/1.05  --res_time_limit                        2.
% 0.83/1.05  --res_out_proof                         true
% 0.83/1.05  
% 0.83/1.05  ------ Superposition Options
% 0.83/1.05  
% 0.83/1.05  --superposition_flag                    true
% 0.83/1.05  --sup_passive_queue_type                priority_queues
% 0.83/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.83/1.05  --demod_completeness_check              fast
% 0.83/1.05  --demod_use_ground                      true
% 0.83/1.05  --sup_to_prop_solver                    passive
% 0.83/1.05  --sup_prop_simpl_new                    true
% 0.83/1.05  --sup_prop_simpl_given                  true
% 0.83/1.05  --sup_fun_splitting                     false
% 0.83/1.05  --sup_smt_interval                      50000
% 0.83/1.05  
% 0.83/1.05  ------ Superposition Simplification Setup
% 0.83/1.05  
% 0.83/1.05  --sup_indices_passive                   []
% 0.83/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.05  --sup_full_bw                           [BwDemod]
% 0.83/1.05  --sup_immed_triv                        [TrivRules]
% 0.83/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.05  --sup_immed_bw_main                     []
% 0.83/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.05  
% 0.83/1.05  ------ Combination Options
% 0.83/1.05  
% 0.83/1.05  --comb_res_mult                         3
% 0.83/1.05  --comb_sup_mult                         2
% 0.83/1.05  --comb_inst_mult                        10
% 0.83/1.05  
% 0.83/1.05  ------ Debug Options
% 0.83/1.05  
% 0.83/1.05  --dbg_backtrace                         false
% 0.83/1.05  --dbg_dump_prop_clauses                 false
% 0.83/1.05  --dbg_dump_prop_clauses_file            -
% 0.83/1.05  --dbg_out_stat                          false
% 0.83/1.05  
% 0.83/1.05  
% 0.83/1.05  
% 0.83/1.05  
% 0.83/1.05  ------ Proving...
% 0.83/1.05  
% 0.83/1.05  
% 0.83/1.05  % SZS status Theorem for theBenchmark.p
% 0.83/1.05  
% 0.83/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.83/1.05  
% 0.83/1.05  fof(f9,conjecture,(
% 0.83/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f10,negated_conjecture,(
% 0.83/1.05    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 0.83/1.05    inference(negated_conjecture,[],[f9])).
% 0.83/1.05  
% 0.83/1.05  fof(f22,plain,(
% 0.83/1.05    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.83/1.05    inference(ennf_transformation,[],[f10])).
% 0.83/1.05  
% 0.83/1.05  fof(f23,plain,(
% 0.83/1.05    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.83/1.05    inference(flattening,[],[f22])).
% 0.83/1.05  
% 0.83/1.05  fof(f25,plain,(
% 0.83/1.05    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.83/1.05    introduced(choice_axiom,[])).
% 0.83/1.05  
% 0.83/1.05  fof(f26,plain,(
% 0.83/1.05    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.83/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f25])).
% 0.83/1.05  
% 0.83/1.05  fof(f36,plain,(
% 0.83/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.83/1.05    inference(cnf_transformation,[],[f26])).
% 0.83/1.05  
% 0.83/1.05  fof(f6,axiom,(
% 0.83/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f11,plain,(
% 0.83/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.83/1.05    inference(pure_predicate_removal,[],[f6])).
% 0.83/1.05  
% 0.83/1.05  fof(f18,plain,(
% 0.83/1.05    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.83/1.05    inference(ennf_transformation,[],[f11])).
% 0.83/1.05  
% 0.83/1.05  fof(f33,plain,(
% 0.83/1.05    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.83/1.05    inference(cnf_transformation,[],[f18])).
% 0.83/1.05  
% 0.83/1.05  fof(f3,axiom,(
% 0.83/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f15,plain,(
% 0.83/1.05    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.83/1.05    inference(ennf_transformation,[],[f3])).
% 0.83/1.05  
% 0.83/1.05  fof(f24,plain,(
% 0.83/1.05    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.83/1.05    inference(nnf_transformation,[],[f15])).
% 0.83/1.05  
% 0.83/1.05  fof(f29,plain,(
% 0.83/1.05    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.83/1.05    inference(cnf_transformation,[],[f24])).
% 0.83/1.05  
% 0.83/1.05  fof(f4,axiom,(
% 0.83/1.05    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f31,plain,(
% 0.83/1.05    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.83/1.05    inference(cnf_transformation,[],[f4])).
% 0.83/1.05  
% 0.83/1.05  fof(f2,axiom,(
% 0.83/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f14,plain,(
% 0.83/1.05    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.83/1.05    inference(ennf_transformation,[],[f2])).
% 0.83/1.05  
% 0.83/1.05  fof(f28,plain,(
% 0.83/1.05    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.83/1.05    inference(cnf_transformation,[],[f14])).
% 0.83/1.05  
% 0.83/1.05  fof(f37,plain,(
% 0.83/1.05    r1_tarski(sK1,sK2)),
% 0.83/1.05    inference(cnf_transformation,[],[f26])).
% 0.83/1.05  
% 0.83/1.05  fof(f1,axiom,(
% 0.83/1.05    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f12,plain,(
% 0.83/1.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.83/1.05    inference(ennf_transformation,[],[f1])).
% 0.83/1.05  
% 0.83/1.05  fof(f13,plain,(
% 0.83/1.05    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.83/1.05    inference(flattening,[],[f12])).
% 0.83/1.05  
% 0.83/1.05  fof(f27,plain,(
% 0.83/1.05    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.83/1.05    inference(cnf_transformation,[],[f13])).
% 0.83/1.05  
% 0.83/1.05  fof(f5,axiom,(
% 0.83/1.05    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f16,plain,(
% 0.83/1.05    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.83/1.05    inference(ennf_transformation,[],[f5])).
% 0.83/1.05  
% 0.83/1.05  fof(f17,plain,(
% 0.83/1.05    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.83/1.05    inference(flattening,[],[f16])).
% 0.83/1.05  
% 0.83/1.05  fof(f32,plain,(
% 0.83/1.05    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.83/1.05    inference(cnf_transformation,[],[f17])).
% 0.83/1.05  
% 0.83/1.05  fof(f7,axiom,(
% 0.83/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f19,plain,(
% 0.83/1.05    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.83/1.05    inference(ennf_transformation,[],[f7])).
% 0.83/1.05  
% 0.83/1.05  fof(f34,plain,(
% 0.83/1.05    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.83/1.05    inference(cnf_transformation,[],[f19])).
% 0.83/1.05  
% 0.83/1.05  fof(f8,axiom,(
% 0.83/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.83/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.05  
% 0.83/1.05  fof(f20,plain,(
% 0.83/1.05    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.83/1.05    inference(ennf_transformation,[],[f8])).
% 0.83/1.05  
% 0.83/1.05  fof(f21,plain,(
% 0.83/1.05    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.83/1.05    inference(flattening,[],[f20])).
% 0.83/1.05  
% 0.83/1.05  fof(f35,plain,(
% 0.83/1.05    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.83/1.05    inference(cnf_transformation,[],[f21])).
% 0.83/1.05  
% 0.83/1.05  fof(f38,plain,(
% 0.83/1.05    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 0.83/1.05    inference(cnf_transformation,[],[f26])).
% 0.83/1.05  
% 0.83/1.05  cnf(c_255,plain,
% 0.83/1.05      ( ~ m1_subset_1(X0_42,X0_43)
% 0.83/1.05      | m1_subset_1(X1_42,X1_43)
% 0.83/1.05      | X1_43 != X0_43
% 0.83/1.05      | X1_42 != X0_42 ),
% 0.83/1.05      theory(equality) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_564,plain,
% 0.83/1.05      ( m1_subset_1(X0_42,X0_43)
% 0.83/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.05      | X0_43 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.83/1.05      | X0_42 != sK3 ),
% 0.83/1.05      inference(instantiation,[status(thm)],[c_255]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_595,plain,
% 0.83/1.05      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.83/1.05      | X0_42 != sK3 ),
% 0.83/1.05      inference(instantiation,[status(thm)],[c_564]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_1127,plain,
% 0.83/1.05      ( m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.83/1.05      | k6_relset_1(sK0,sK1,sK2,sK3) != sK3 ),
% 0.83/1.05      inference(instantiation,[status(thm)],[c_595]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_11,negated_conjecture,
% 0.83/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.83/1.05      inference(cnf_transformation,[],[f36]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_238,negated_conjecture,
% 0.83/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.83/1.05      inference(subtyping,[status(esa)],[c_11]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_467,plain,
% 0.83/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.83/1.05      inference(predicate_to_equality,[status(thm)],[c_238]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_6,plain,
% 0.83/1.05      ( v5_relat_1(X0,X1)
% 0.83/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 0.83/1.05      inference(cnf_transformation,[],[f33]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_3,plain,
% 0.83/1.05      ( ~ v5_relat_1(X0,X1)
% 0.83/1.05      | r1_tarski(k2_relat_1(X0),X1)
% 0.83/1.05      | ~ v1_relat_1(X0) ),
% 0.83/1.05      inference(cnf_transformation,[],[f29]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_153,plain,
% 0.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.83/1.05      | r1_tarski(k2_relat_1(X0),X2)
% 0.83/1.05      | ~ v1_relat_1(X0) ),
% 0.83/1.05      inference(resolution,[status(thm)],[c_6,c_3]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_236,plain,
% 0.83/1.05      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)))
% 0.83/1.05      | r1_tarski(k2_relat_1(X0_42),X0_45)
% 0.83/1.05      | ~ v1_relat_1(X0_42) ),
% 0.83/1.05      inference(subtyping,[status(esa)],[c_153]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_470,plain,
% 0.83/1.05      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top
% 0.83/1.05      | r1_tarski(k2_relat_1(X0_42),X0_45) = iProver_top
% 0.83/1.05      | v1_relat_1(X0_42) != iProver_top ),
% 0.83/1.05      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_4,plain,
% 0.83/1.05      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 0.83/1.05      inference(cnf_transformation,[],[f31]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_242,plain,
% 0.83/1.05      ( v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) ),
% 0.83/1.05      inference(subtyping,[status(esa)],[c_4]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_270,plain,
% 0.83/1.05      ( v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) = iProver_top ),
% 0.83/1.05      inference(predicate_to_equality,[status(thm)],[c_242]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_285,plain,
% 0.83/1.05      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top
% 0.83/1.05      | r1_tarski(k2_relat_1(X0_42),X0_45) = iProver_top
% 0.83/1.05      | v1_relat_1(X0_42) != iProver_top ),
% 0.83/1.05      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_1,plain,
% 0.83/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.83/1.05      | ~ v1_relat_1(X1)
% 0.83/1.05      | v1_relat_1(X0) ),
% 0.83/1.05      inference(cnf_transformation,[],[f28]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_243,plain,
% 0.83/1.05      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42))
% 0.83/1.05      | ~ v1_relat_1(X1_42)
% 0.83/1.05      | v1_relat_1(X0_42) ),
% 0.83/1.05      inference(subtyping,[status(esa)],[c_1]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_537,plain,
% 0.83/1.05      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)))
% 0.83/1.05      | v1_relat_1(X0_42)
% 0.83/1.05      | ~ v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) ),
% 0.83/1.05      inference(instantiation,[status(thm)],[c_243]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_538,plain,
% 0.83/1.05      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top
% 0.83/1.05      | v1_relat_1(X0_42) = iProver_top
% 0.83/1.05      | v1_relat_1(k2_zfmisc_1(X0_44,X0_45)) != iProver_top ),
% 0.83/1.05      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_868,plain,
% 0.83/1.05      ( r1_tarski(k2_relat_1(X0_42),X0_45) = iProver_top
% 0.83/1.05      | m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top ),
% 0.83/1.05      inference(global_propositional_subsumption,
% 0.83/1.05                [status(thm)],
% 0.83/1.05                [c_470,c_270,c_285,c_538]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_869,plain,
% 0.83/1.05      ( m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45))) != iProver_top
% 0.83/1.05      | r1_tarski(k2_relat_1(X0_42),X0_45) = iProver_top ),
% 0.83/1.05      inference(renaming,[status(thm)],[c_868]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_876,plain,
% 0.83/1.05      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 0.83/1.05      inference(superposition,[status(thm)],[c_467,c_869]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_10,negated_conjecture,
% 0.83/1.05      ( r1_tarski(sK1,sK2) ),
% 0.83/1.05      inference(cnf_transformation,[],[f37]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_239,negated_conjecture,
% 0.83/1.05      ( r1_tarski(sK1,sK2) ),
% 0.83/1.05      inference(subtyping,[status(esa)],[c_10]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_466,plain,
% 0.83/1.05      ( r1_tarski(sK1,sK2) = iProver_top ),
% 0.83/1.05      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_0,plain,
% 0.83/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 0.83/1.05      inference(cnf_transformation,[],[f27]) ).
% 0.83/1.05  
% 0.83/1.05  cnf(c_244,plain,
% 0.83/1.05      ( ~ r1_tarski(X0_45,X1_45)
% 0.83/1.06      | ~ r1_tarski(X2_45,X0_45)
% 0.83/1.06      | r1_tarski(X2_45,X1_45) ),
% 0.83/1.06      inference(subtyping,[status(esa)],[c_0]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_461,plain,
% 0.83/1.06      ( r1_tarski(X0_45,X1_45) != iProver_top
% 0.83/1.06      | r1_tarski(X2_45,X0_45) != iProver_top
% 0.83/1.06      | r1_tarski(X2_45,X1_45) = iProver_top ),
% 0.83/1.06      inference(predicate_to_equality,[status(thm)],[c_244]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_680,plain,
% 0.83/1.06      ( r1_tarski(X0_45,sK2) = iProver_top
% 0.83/1.06      | r1_tarski(X0_45,sK1) != iProver_top ),
% 0.83/1.06      inference(superposition,[status(thm)],[c_466,c_461]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_882,plain,
% 0.83/1.06      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 0.83/1.06      inference(superposition,[status(thm)],[c_876,c_680]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_5,plain,
% 0.83/1.06      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 0.83/1.06      | ~ v1_relat_1(X0)
% 0.83/1.06      | k8_relat_1(X1,X0) = X0 ),
% 0.83/1.06      inference(cnf_transformation,[],[f32]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_241,plain,
% 0.83/1.06      ( ~ r1_tarski(k2_relat_1(X0_42),X0_45)
% 0.83/1.06      | ~ v1_relat_1(X0_42)
% 0.83/1.06      | k8_relat_1(X0_45,X0_42) = X0_42 ),
% 0.83/1.06      inference(subtyping,[status(esa)],[c_5]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_790,plain,
% 0.83/1.06      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 0.83/1.06      | ~ v1_relat_1(sK3)
% 0.83/1.06      | k8_relat_1(sK2,sK3) = sK3 ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_241]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_791,plain,
% 0.83/1.06      ( k8_relat_1(sK2,sK3) = sK3
% 0.83/1.06      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 0.83/1.06      | v1_relat_1(sK3) != iProver_top ),
% 0.83/1.06      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_251,plain,
% 0.83/1.06      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 0.83/1.06      theory(equality) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_611,plain,
% 0.83/1.06      ( X0_42 != X1_42
% 0.83/1.06      | k6_relset_1(sK0,sK1,sK2,sK3) != X1_42
% 0.83/1.06      | k6_relset_1(sK0,sK1,sK2,sK3) = X0_42 ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_251]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_663,plain,
% 0.83/1.06      ( X0_42 != k8_relat_1(sK2,sK3)
% 0.83/1.06      | k6_relset_1(sK0,sK1,sK2,sK3) = X0_42
% 0.83/1.06      | k6_relset_1(sK0,sK1,sK2,sK3) != k8_relat_1(sK2,sK3) ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_611]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_664,plain,
% 0.83/1.06      ( k6_relset_1(sK0,sK1,sK2,sK3) != k8_relat_1(sK2,sK3)
% 0.83/1.06      | k6_relset_1(sK0,sK1,sK2,sK3) = sK3
% 0.83/1.06      | sK3 != k8_relat_1(sK2,sK3) ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_663]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_652,plain,
% 0.83/1.06      ( k8_relat_1(sK2,sK3) != X0_42
% 0.83/1.06      | sK3 != X0_42
% 0.83/1.06      | sK3 = k8_relat_1(sK2,sK3) ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_251]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_653,plain,
% 0.83/1.06      ( k8_relat_1(sK2,sK3) != sK3
% 0.83/1.06      | sK3 = k8_relat_1(sK2,sK3)
% 0.83/1.06      | sK3 != sK3 ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_652]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_7,plain,
% 0.83/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.83/1.06      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 0.83/1.06      inference(cnf_transformation,[],[f34]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_240,plain,
% 0.83/1.06      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)))
% 0.83/1.06      | k6_relset_1(X0_44,X0_45,X1_45,X0_42) = k8_relat_1(X1_45,X0_42) ),
% 0.83/1.06      inference(subtyping,[status(esa)],[c_7]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_607,plain,
% 0.83/1.06      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | k6_relset_1(sK0,sK1,sK2,sK3) = k8_relat_1(sK2,sK3) ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_240]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_574,plain,
% 0.83/1.06      ( k6_relset_1(sK0,sK1,sK2,sK3) != X0_42
% 0.83/1.06      | sK3 != X0_42
% 0.83/1.06      | sK3 = k6_relset_1(sK0,sK1,sK2,sK3) ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_251]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_606,plain,
% 0.83/1.06      ( k6_relset_1(sK0,sK1,sK2,sK3) != k8_relat_1(sK2,sK3)
% 0.83/1.06      | sK3 = k6_relset_1(sK0,sK1,sK2,sK3)
% 0.83/1.06      | sK3 != k8_relat_1(sK2,sK3) ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_574]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_249,plain,( X0_43 = X0_43 ),theory(equality) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_596,plain,
% 0.83/1.06      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_249]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_540,plain,
% 0.83/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 0.83/1.06      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 0.83/1.06      | v1_relat_1(sK3) = iProver_top ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_538]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_8,plain,
% 0.83/1.06      ( r2_relset_1(X0,X1,X2,X2)
% 0.83/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.83/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.83/1.06      inference(cnf_transformation,[],[f35]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_9,negated_conjecture,
% 0.83/1.06      ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
% 0.83/1.06      inference(cnf_transformation,[],[f38]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_134,plain,
% 0.83/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.83/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.83/1.06      | k6_relset_1(sK0,sK1,sK2,sK3) != X0
% 0.83/1.06      | sK3 != X0
% 0.83/1.06      | sK1 != X2
% 0.83/1.06      | sK0 != X1 ),
% 0.83/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_135,plain,
% 0.83/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
% 0.83/1.06      inference(unflattening,[status(thm)],[c_134]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_237,plain,
% 0.83/1.06      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
% 0.83/1.06      inference(subtyping,[status(esa)],[c_135]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_246,plain,
% 0.83/1.06      ( ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | sP0_iProver_split
% 0.83/1.06      | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
% 0.83/1.06      inference(splitting,
% 0.83/1.06                [splitting(split),new_symbols(definition,[])],
% 0.83/1.06                [c_237]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_245,plain,
% 0.83/1.06      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | ~ sP0_iProver_split ),
% 0.83/1.06      inference(splitting,
% 0.83/1.06                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.83/1.06                [c_237]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_283,plain,
% 0.83/1.06      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | ~ sP0_iProver_split ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_245]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_312,plain,
% 0.83/1.06      ( ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.83/1.06      | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
% 0.83/1.06      inference(global_propositional_subsumption,
% 0.83/1.06                [status(thm)],
% 0.83/1.06                [c_246,c_11,c_283]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_272,plain,
% 0.83/1.06      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_270]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_248,plain,( X0_42 = X0_42 ),theory(equality) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_265,plain,
% 0.83/1.06      ( sK3 = sK3 ),
% 0.83/1.06      inference(instantiation,[status(thm)],[c_248]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(c_12,plain,
% 0.83/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 0.83/1.06      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.83/1.06  
% 0.83/1.06  cnf(contradiction,plain,
% 0.83/1.06      ( $false ),
% 0.83/1.06      inference(minisat,
% 0.83/1.06                [status(thm)],
% 0.83/1.06                [c_1127,c_882,c_791,c_664,c_653,c_607,c_606,c_596,c_540,
% 0.83/1.06                 c_312,c_272,c_265,c_12,c_11]) ).
% 0.83/1.06  
% 0.83/1.06  
% 0.83/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 0.83/1.06  
% 0.83/1.06  ------                               Statistics
% 0.83/1.06  
% 0.83/1.06  ------ General
% 0.83/1.06  
% 0.83/1.06  abstr_ref_over_cycles:                  0
% 0.83/1.06  abstr_ref_under_cycles:                 0
% 0.83/1.06  gc_basic_clause_elim:                   0
% 0.83/1.06  forced_gc_time:                         0
% 0.83/1.06  parsing_time:                           0.007
% 0.83/1.06  unif_index_cands_time:                  0.
% 0.83/1.06  unif_index_add_time:                    0.
% 0.83/1.06  orderings_time:                         0.
% 0.83/1.06  out_proof_time:                         0.013
% 0.83/1.06  total_time:                             0.092
% 0.83/1.06  num_of_symbols:                         47
% 0.83/1.06  num_of_terms:                           1185
% 0.83/1.06  
% 0.83/1.06  ------ Preprocessing
% 0.83/1.06  
% 0.83/1.06  num_of_splits:                          1
% 0.83/1.06  num_of_split_atoms:                     1
% 0.83/1.06  num_of_reused_defs:                     0
% 0.83/1.06  num_eq_ax_congr_red:                    13
% 0.83/1.06  num_of_sem_filtered_clauses:            2
% 0.83/1.06  num_of_subtypes:                        4
% 0.83/1.06  monotx_restored_types:                  1
% 0.83/1.06  sat_num_of_epr_types:                   0
% 0.83/1.06  sat_num_of_non_cyclic_types:            0
% 0.83/1.06  sat_guarded_non_collapsed_types:        0
% 0.83/1.06  num_pure_diseq_elim:                    0
% 0.83/1.06  simp_replaced_by:                       0
% 0.83/1.06  res_preprocessed:                       61
% 0.83/1.06  prep_upred:                             0
% 0.83/1.06  prep_unflattend:                        3
% 0.83/1.06  smt_new_axioms:                         0
% 0.83/1.06  pred_elim_cands:                        3
% 0.83/1.06  pred_elim:                              2
% 0.83/1.06  pred_elim_cl:                           3
% 0.83/1.06  pred_elim_cycles:                       4
% 0.83/1.06  merged_defs:                            0
% 0.83/1.06  merged_defs_ncl:                        0
% 0.83/1.06  bin_hyper_res:                          0
% 0.83/1.06  prep_cycles:                            4
% 0.83/1.06  pred_elim_time:                         0.001
% 0.83/1.06  splitting_time:                         0.
% 0.83/1.06  sem_filter_time:                        0.
% 0.83/1.06  monotx_time:                            0.
% 0.83/1.06  subtype_inf_time:                       0.001
% 0.83/1.06  
% 0.83/1.06  ------ Problem properties
% 0.83/1.06  
% 0.83/1.06  clauses:                                10
% 0.83/1.06  conjectures:                            2
% 0.83/1.06  epr:                                    2
% 0.83/1.06  horn:                                   10
% 0.83/1.06  ground:                                 3
% 0.83/1.06  unary:                                  3
% 0.83/1.06  binary:                                 2
% 0.83/1.06  lits:                                   22
% 0.83/1.06  lits_eq:                                3
% 0.83/1.06  fd_pure:                                0
% 0.83/1.06  fd_pseudo:                              0
% 0.83/1.06  fd_cond:                                0
% 0.83/1.06  fd_pseudo_cond:                         0
% 0.83/1.06  ac_symbols:                             0
% 0.83/1.06  
% 0.83/1.06  ------ Propositional Solver
% 0.83/1.06  
% 0.83/1.06  prop_solver_calls:                      27
% 0.83/1.06  prop_fast_solver_calls:                 323
% 0.83/1.06  smt_solver_calls:                       0
% 0.83/1.06  smt_fast_solver_calls:                  0
% 0.83/1.06  prop_num_of_clauses:                    367
% 0.83/1.06  prop_preprocess_simplified:             2038
% 0.83/1.06  prop_fo_subsumed:                       7
% 0.83/1.06  prop_solver_time:                       0.
% 0.83/1.06  smt_solver_time:                        0.
% 0.83/1.06  smt_fast_solver_time:                   0.
% 0.83/1.06  prop_fast_solver_time:                  0.
% 0.83/1.06  prop_unsat_core_time:                   0.
% 0.83/1.06  
% 0.83/1.06  ------ QBF
% 0.83/1.06  
% 0.83/1.06  qbf_q_res:                              0
% 0.83/1.06  qbf_num_tautologies:                    0
% 0.83/1.06  qbf_prep_cycles:                        0
% 0.83/1.06  
% 0.83/1.06  ------ BMC1
% 0.83/1.06  
% 0.83/1.06  bmc1_current_bound:                     -1
% 0.83/1.06  bmc1_last_solved_bound:                 -1
% 0.83/1.06  bmc1_unsat_core_size:                   -1
% 0.83/1.06  bmc1_unsat_core_parents_size:           -1
% 0.83/1.06  bmc1_merge_next_fun:                    0
% 0.83/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.83/1.06  
% 0.83/1.06  ------ Instantiation
% 0.83/1.06  
% 0.83/1.06  inst_num_of_clauses:                    142
% 0.83/1.06  inst_num_in_passive:                    55
% 0.83/1.06  inst_num_in_active:                     86
% 0.83/1.06  inst_num_in_unprocessed:                0
% 0.83/1.06  inst_num_of_loops:                      100
% 0.83/1.06  inst_num_of_learning_restarts:          0
% 0.83/1.06  inst_num_moves_active_passive:          10
% 0.83/1.06  inst_lit_activity:                      0
% 0.83/1.06  inst_lit_activity_moves:                0
% 0.83/1.06  inst_num_tautologies:                   0
% 0.83/1.06  inst_num_prop_implied:                  0
% 0.83/1.06  inst_num_existing_simplified:           0
% 0.83/1.06  inst_num_eq_res_simplified:             0
% 0.83/1.06  inst_num_child_elim:                    0
% 0.83/1.06  inst_num_of_dismatching_blockings:      33
% 0.83/1.06  inst_num_of_non_proper_insts:           103
% 0.83/1.06  inst_num_of_duplicates:                 0
% 0.83/1.06  inst_inst_num_from_inst_to_res:         0
% 0.83/1.06  inst_dismatching_checking_time:         0.
% 0.83/1.06  
% 0.83/1.06  ------ Resolution
% 0.83/1.06  
% 0.83/1.06  res_num_of_clauses:                     0
% 0.83/1.06  res_num_in_passive:                     0
% 0.83/1.06  res_num_in_active:                      0
% 0.83/1.06  res_num_of_loops:                       65
% 0.83/1.06  res_forward_subset_subsumed:            15
% 0.83/1.06  res_backward_subset_subsumed:           0
% 0.83/1.06  res_forward_subsumed:                   0
% 0.83/1.06  res_backward_subsumed:                  0
% 0.83/1.06  res_forward_subsumption_resolution:     0
% 0.83/1.06  res_backward_subsumption_resolution:    0
% 0.83/1.06  res_clause_to_clause_subsumption:       20
% 0.83/1.06  res_orphan_elimination:                 0
% 0.83/1.06  res_tautology_del:                      17
% 0.83/1.06  res_num_eq_res_simplified:              0
% 0.83/1.06  res_num_sel_changes:                    0
% 0.83/1.06  res_moves_from_active_to_pass:          0
% 0.83/1.06  
% 0.83/1.06  ------ Superposition
% 0.83/1.06  
% 0.83/1.06  sup_time_total:                         0.
% 0.83/1.06  sup_time_generating:                    0.
% 0.83/1.06  sup_time_sim_full:                      0.
% 0.83/1.06  sup_time_sim_immed:                     0.
% 0.83/1.06  
% 0.83/1.06  sup_num_of_clauses:                     19
% 0.83/1.06  sup_num_in_active:                      17
% 0.83/1.06  sup_num_in_passive:                     2
% 0.83/1.06  sup_num_of_loops:                       18
% 0.83/1.06  sup_fw_superposition:                   4
% 0.83/1.06  sup_bw_superposition:                   5
% 0.83/1.06  sup_immediate_simplified:               0
% 0.83/1.06  sup_given_eliminated:                   0
% 0.83/1.06  comparisons_done:                       0
% 0.83/1.06  comparisons_avoided:                    0
% 0.83/1.06  
% 0.83/1.06  ------ Simplifications
% 0.83/1.06  
% 0.83/1.06  
% 0.83/1.06  sim_fw_subset_subsumed:                 0
% 0.83/1.06  sim_bw_subset_subsumed:                 0
% 0.83/1.06  sim_fw_subsumed:                        0
% 0.83/1.06  sim_bw_subsumed:                        0
% 0.83/1.06  sim_fw_subsumption_res:                 1
% 0.83/1.06  sim_bw_subsumption_res:                 0
% 0.83/1.06  sim_tautology_del:                      0
% 0.83/1.06  sim_eq_tautology_del:                   0
% 0.83/1.06  sim_eq_res_simp:                        0
% 0.83/1.06  sim_fw_demodulated:                     0
% 0.83/1.06  sim_bw_demodulated:                     1
% 0.83/1.06  sim_light_normalised:                   0
% 0.83/1.06  sim_joinable_taut:                      0
% 0.83/1.06  sim_joinable_simp:                      0
% 0.83/1.06  sim_ac_normalised:                      0
% 0.83/1.06  sim_smt_subsumption:                    0
% 0.83/1.06  
%------------------------------------------------------------------------------
