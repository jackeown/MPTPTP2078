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
% DateTime   : Thu Dec  3 11:55:55 EST 2020

% Result     : Theorem 1.11s
% Output     : CNFRefutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 265 expanded)
%              Number of clauses        :   65 ( 125 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  252 ( 696 expanded)
%              Number of equality atoms :  105 ( 173 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f40,plain,(
    ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_164,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_165,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_164])).

cnf(c_440,plain,
    ( ~ v1_relat_1(X0_42)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_165])).

cnf(c_592,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_42)
    | v1_relat_1(X0_42) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_455,plain,
    ( X0_44 != X1_44
    | k2_zfmisc_1(X0_43,X0_44) = k2_zfmisc_1(X0_43,X1_44) ),
    theory(equality)).

cnf(c_462,plain,
    ( sK1 != sK1
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_447,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_467,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_447])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_444,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_469,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_471,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_642,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_43,X0_44))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_643,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44))
    | v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_645,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_452,plain,
    ( k1_zfmisc_1(X0_42) = k1_zfmisc_1(X1_42)
    | X0_42 != X1_42 ),
    theory(equality)).

cnf(c_647,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(X0_43,X0_44) != k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_648,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_692,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_462,c_467,c_471,c_645,c_648])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_441,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_591,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_442,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ v1_relat_1(X0_42)
    | k8_relat_1(X1_44,k8_relat_1(X0_44,X0_42)) = k8_relat_1(X0_44,X0_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_590,plain,
    ( k8_relat_1(X0_44,k8_relat_1(X1_44,X0_42)) = k8_relat_1(X1_44,X0_42)
    | r1_tarski(X1_44,X0_44) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_827,plain,
    ( k8_relat_1(sK2,k8_relat_1(sK1,X0_42)) = k8_relat_1(sK1,X0_42)
    | v1_relat_1(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_590])).

cnf(c_944,plain,
    ( k8_relat_1(sK2,k8_relat_1(sK1,sK3)) = k8_relat_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_692,c_827])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_179,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_180,plain,
    ( v5_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(c_219,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_180])).

cnf(c_220,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_438,plain,
    ( r1_tarski(k2_relat_1(sK3),X0_44)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_220])).

cnf(c_593,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK3),X0_44) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_481,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK3),X0_44) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_733,plain,
    ( r1_tarski(k2_relat_1(sK3),X0_44) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_593,c_462,c_467,c_471,c_481,c_645,c_648])).

cnf(c_734,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_relat_1(sK3),X0_44) = iProver_top ),
    inference(renaming,[status(thm)],[c_733])).

cnf(c_741,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_734])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_443,plain,
    ( ~ r1_tarski(k2_relat_1(X0_42),X0_44)
    | ~ v1_relat_1(X0_42)
    | k8_relat_1(X0_44,X0_42) = X0_42 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_589,plain,
    ( k8_relat_1(X0_44,X0_42) = X0_42
    | r1_tarski(k2_relat_1(X0_42),X0_44) != iProver_top
    | v1_relat_1(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_800,plain,
    ( k8_relat_1(sK1,sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_589])).

cnf(c_470,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_473,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | k8_relat_1(sK1,sK3) = sK3 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_482,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_644,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_844,plain,
    ( k8_relat_1(sK1,sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_800,c_462,c_467,c_470,c_473,c_482,c_644,c_648])).

cnf(c_949,plain,
    ( k8_relat_1(sK2,sK3) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_944,c_844])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_191,plain,
    ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_192,plain,
    ( k6_relset_1(X0,X1,X2,sK3) = k8_relat_1(X2,sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_439,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k6_relset_1(X0_43,X0_44,X1_44,sK3) = k8_relat_1(X1_44,sK3) ),
    inference(subtyping,[status(esa)],[c_192])).

cnf(c_663,plain,
    ( k6_relset_1(sK0,sK1,X0_44,sK3) = k8_relat_1(X0_44,sK3) ),
    inference(equality_resolution,[status(thm)],[c_439])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_151,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(sK0,sK1,sK2,sK3) != X0
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_152,plain,
    ( ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_200,plain,
    ( k6_relset_1(sK0,sK1,sK2,sK3) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_152])).

cnf(c_325,plain,
    ( k6_relset_1(sK0,sK1,sK2,sK3) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_200])).

cnf(c_437,plain,
    ( k6_relset_1(sK0,sK1,sK2,sK3) != sK3 ),
    inference(subtyping,[status(esa)],[c_325])).

cnf(c_681,plain,
    ( k8_relat_1(sK2,sK3) != sK3 ),
    inference(demodulation,[status(thm)],[c_663,c_437])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_949,c_681])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:57:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 1.11/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.11/1.04  
% 1.11/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.11/1.04  
% 1.11/1.04  ------  iProver source info
% 1.11/1.04  
% 1.11/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.11/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.11/1.04  git: non_committed_changes: false
% 1.11/1.04  git: last_make_outside_of_git: false
% 1.11/1.04  
% 1.11/1.04  ------ 
% 1.11/1.04  
% 1.11/1.04  ------ Input Options
% 1.11/1.04  
% 1.11/1.04  --out_options                           all
% 1.11/1.04  --tptp_safe_out                         true
% 1.11/1.04  --problem_path                          ""
% 1.11/1.04  --include_path                          ""
% 1.11/1.04  --clausifier                            res/vclausify_rel
% 1.11/1.04  --clausifier_options                    --mode clausify
% 1.11/1.04  --stdin                                 false
% 1.11/1.04  --stats_out                             all
% 1.11/1.04  
% 1.11/1.04  ------ General Options
% 1.11/1.04  
% 1.11/1.04  --fof                                   false
% 1.11/1.04  --time_out_real                         305.
% 1.11/1.04  --time_out_virtual                      -1.
% 1.11/1.04  --symbol_type_check                     false
% 1.11/1.04  --clausify_out                          false
% 1.11/1.04  --sig_cnt_out                           false
% 1.11/1.04  --trig_cnt_out                          false
% 1.11/1.04  --trig_cnt_out_tolerance                1.
% 1.11/1.04  --trig_cnt_out_sk_spl                   false
% 1.11/1.04  --abstr_cl_out                          false
% 1.11/1.04  
% 1.11/1.04  ------ Global Options
% 1.11/1.04  
% 1.11/1.04  --schedule                              default
% 1.11/1.04  --add_important_lit                     false
% 1.11/1.04  --prop_solver_per_cl                    1000
% 1.11/1.04  --min_unsat_core                        false
% 1.11/1.04  --soft_assumptions                      false
% 1.11/1.04  --soft_lemma_size                       3
% 1.11/1.04  --prop_impl_unit_size                   0
% 1.11/1.04  --prop_impl_unit                        []
% 1.11/1.04  --share_sel_clauses                     true
% 1.11/1.04  --reset_solvers                         false
% 1.11/1.04  --bc_imp_inh                            [conj_cone]
% 1.11/1.04  --conj_cone_tolerance                   3.
% 1.11/1.04  --extra_neg_conj                        none
% 1.11/1.04  --large_theory_mode                     true
% 1.11/1.04  --prolific_symb_bound                   200
% 1.11/1.04  --lt_threshold                          2000
% 1.11/1.04  --clause_weak_htbl                      true
% 1.11/1.04  --gc_record_bc_elim                     false
% 1.11/1.04  
% 1.11/1.04  ------ Preprocessing Options
% 1.11/1.04  
% 1.11/1.04  --preprocessing_flag                    true
% 1.11/1.04  --time_out_prep_mult                    0.1
% 1.11/1.04  --splitting_mode                        input
% 1.11/1.04  --splitting_grd                         true
% 1.11/1.04  --splitting_cvd                         false
% 1.11/1.04  --splitting_cvd_svl                     false
% 1.11/1.04  --splitting_nvd                         32
% 1.11/1.04  --sub_typing                            true
% 1.11/1.04  --prep_gs_sim                           true
% 1.11/1.04  --prep_unflatten                        true
% 1.11/1.04  --prep_res_sim                          true
% 1.11/1.04  --prep_upred                            true
% 1.11/1.04  --prep_sem_filter                       exhaustive
% 1.11/1.04  --prep_sem_filter_out                   false
% 1.11/1.04  --pred_elim                             true
% 1.11/1.04  --res_sim_input                         true
% 1.11/1.04  --eq_ax_congr_red                       true
% 1.11/1.04  --pure_diseq_elim                       true
% 1.11/1.04  --brand_transform                       false
% 1.11/1.04  --non_eq_to_eq                          false
% 1.11/1.04  --prep_def_merge                        true
% 1.11/1.04  --prep_def_merge_prop_impl              false
% 1.11/1.04  --prep_def_merge_mbd                    true
% 1.11/1.04  --prep_def_merge_tr_red                 false
% 1.11/1.04  --prep_def_merge_tr_cl                  false
% 1.11/1.04  --smt_preprocessing                     true
% 1.11/1.04  --smt_ac_axioms                         fast
% 1.11/1.04  --preprocessed_out                      false
% 1.11/1.04  --preprocessed_stats                    false
% 1.11/1.04  
% 1.11/1.04  ------ Abstraction refinement Options
% 1.11/1.04  
% 1.11/1.04  --abstr_ref                             []
% 1.11/1.04  --abstr_ref_prep                        false
% 1.11/1.04  --abstr_ref_until_sat                   false
% 1.11/1.04  --abstr_ref_sig_restrict                funpre
% 1.11/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.11/1.04  --abstr_ref_under                       []
% 1.11/1.04  
% 1.11/1.04  ------ SAT Options
% 1.11/1.04  
% 1.11/1.04  --sat_mode                              false
% 1.11/1.04  --sat_fm_restart_options                ""
% 1.11/1.04  --sat_gr_def                            false
% 1.11/1.04  --sat_epr_types                         true
% 1.11/1.04  --sat_non_cyclic_types                  false
% 1.11/1.04  --sat_finite_models                     false
% 1.11/1.04  --sat_fm_lemmas                         false
% 1.11/1.04  --sat_fm_prep                           false
% 1.11/1.04  --sat_fm_uc_incr                        true
% 1.11/1.04  --sat_out_model                         small
% 1.11/1.04  --sat_out_clauses                       false
% 1.11/1.04  
% 1.11/1.04  ------ QBF Options
% 1.11/1.04  
% 1.11/1.04  --qbf_mode                              false
% 1.11/1.04  --qbf_elim_univ                         false
% 1.11/1.04  --qbf_dom_inst                          none
% 1.11/1.04  --qbf_dom_pre_inst                      false
% 1.11/1.04  --qbf_sk_in                             false
% 1.11/1.04  --qbf_pred_elim                         true
% 1.11/1.04  --qbf_split                             512
% 1.11/1.04  
% 1.11/1.04  ------ BMC1 Options
% 1.11/1.04  
% 1.11/1.04  --bmc1_incremental                      false
% 1.11/1.04  --bmc1_axioms                           reachable_all
% 1.11/1.04  --bmc1_min_bound                        0
% 1.11/1.04  --bmc1_max_bound                        -1
% 1.11/1.04  --bmc1_max_bound_default                -1
% 1.11/1.04  --bmc1_symbol_reachability              true
% 1.11/1.04  --bmc1_property_lemmas                  false
% 1.11/1.04  --bmc1_k_induction                      false
% 1.11/1.04  --bmc1_non_equiv_states                 false
% 1.11/1.04  --bmc1_deadlock                         false
% 1.11/1.04  --bmc1_ucm                              false
% 1.11/1.04  --bmc1_add_unsat_core                   none
% 1.11/1.04  --bmc1_unsat_core_children              false
% 1.11/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.11/1.04  --bmc1_out_stat                         full
% 1.11/1.04  --bmc1_ground_init                      false
% 1.11/1.04  --bmc1_pre_inst_next_state              false
% 1.11/1.04  --bmc1_pre_inst_state                   false
% 1.11/1.04  --bmc1_pre_inst_reach_state             false
% 1.11/1.04  --bmc1_out_unsat_core                   false
% 1.11/1.04  --bmc1_aig_witness_out                  false
% 1.11/1.04  --bmc1_verbose                          false
% 1.11/1.04  --bmc1_dump_clauses_tptp                false
% 1.11/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.11/1.04  --bmc1_dump_file                        -
% 1.11/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.11/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.11/1.04  --bmc1_ucm_extend_mode                  1
% 1.11/1.04  --bmc1_ucm_init_mode                    2
% 1.11/1.04  --bmc1_ucm_cone_mode                    none
% 1.11/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.11/1.04  --bmc1_ucm_relax_model                  4
% 1.11/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.11/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.11/1.04  --bmc1_ucm_layered_model                none
% 1.11/1.04  --bmc1_ucm_max_lemma_size               10
% 1.11/1.04  
% 1.11/1.04  ------ AIG Options
% 1.11/1.04  
% 1.11/1.04  --aig_mode                              false
% 1.11/1.04  
% 1.11/1.04  ------ Instantiation Options
% 1.11/1.04  
% 1.11/1.04  --instantiation_flag                    true
% 1.11/1.04  --inst_sos_flag                         false
% 1.11/1.04  --inst_sos_phase                        true
% 1.11/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.11/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.11/1.04  --inst_lit_sel_side                     num_symb
% 1.11/1.04  --inst_solver_per_active                1400
% 1.11/1.04  --inst_solver_calls_frac                1.
% 1.11/1.04  --inst_passive_queue_type               priority_queues
% 1.11/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.11/1.04  --inst_passive_queues_freq              [25;2]
% 1.11/1.04  --inst_dismatching                      true
% 1.11/1.04  --inst_eager_unprocessed_to_passive     true
% 1.11/1.04  --inst_prop_sim_given                   true
% 1.11/1.04  --inst_prop_sim_new                     false
% 1.11/1.04  --inst_subs_new                         false
% 1.11/1.04  --inst_eq_res_simp                      false
% 1.11/1.04  --inst_subs_given                       false
% 1.11/1.04  --inst_orphan_elimination               true
% 1.11/1.04  --inst_learning_loop_flag               true
% 1.11/1.04  --inst_learning_start                   3000
% 1.11/1.04  --inst_learning_factor                  2
% 1.11/1.04  --inst_start_prop_sim_after_learn       3
% 1.11/1.04  --inst_sel_renew                        solver
% 1.11/1.04  --inst_lit_activity_flag                true
% 1.11/1.04  --inst_restr_to_given                   false
% 1.11/1.04  --inst_activity_threshold               500
% 1.11/1.04  --inst_out_proof                        true
% 1.11/1.04  
% 1.11/1.04  ------ Resolution Options
% 1.11/1.04  
% 1.11/1.04  --resolution_flag                       true
% 1.11/1.04  --res_lit_sel                           adaptive
% 1.11/1.04  --res_lit_sel_side                      none
% 1.11/1.04  --res_ordering                          kbo
% 1.11/1.04  --res_to_prop_solver                    active
% 1.11/1.04  --res_prop_simpl_new                    false
% 1.11/1.04  --res_prop_simpl_given                  true
% 1.11/1.04  --res_passive_queue_type                priority_queues
% 1.11/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.11/1.04  --res_passive_queues_freq               [15;5]
% 1.11/1.04  --res_forward_subs                      full
% 1.11/1.04  --res_backward_subs                     full
% 1.11/1.04  --res_forward_subs_resolution           true
% 1.11/1.04  --res_backward_subs_resolution          true
% 1.11/1.04  --res_orphan_elimination                true
% 1.11/1.04  --res_time_limit                        2.
% 1.11/1.04  --res_out_proof                         true
% 1.11/1.04  
% 1.11/1.04  ------ Superposition Options
% 1.11/1.04  
% 1.11/1.04  --superposition_flag                    true
% 1.11/1.04  --sup_passive_queue_type                priority_queues
% 1.11/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.11/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.11/1.04  --demod_completeness_check              fast
% 1.11/1.04  --demod_use_ground                      true
% 1.11/1.04  --sup_to_prop_solver                    passive
% 1.11/1.04  --sup_prop_simpl_new                    true
% 1.11/1.04  --sup_prop_simpl_given                  true
% 1.11/1.04  --sup_fun_splitting                     false
% 1.11/1.04  --sup_smt_interval                      50000
% 1.11/1.05  
% 1.11/1.05  ------ Superposition Simplification Setup
% 1.11/1.05  
% 1.11/1.05  --sup_indices_passive                   []
% 1.11/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.11/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.05  --sup_full_bw                           [BwDemod]
% 1.11/1.05  --sup_immed_triv                        [TrivRules]
% 1.11/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.11/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.05  --sup_immed_bw_main                     []
% 1.11/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.11/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/1.05  
% 1.11/1.05  ------ Combination Options
% 1.11/1.05  
% 1.11/1.05  --comb_res_mult                         3
% 1.11/1.05  --comb_sup_mult                         2
% 1.11/1.05  --comb_inst_mult                        10
% 1.11/1.05  
% 1.11/1.05  ------ Debug Options
% 1.11/1.05  
% 1.11/1.05  --dbg_backtrace                         false
% 1.11/1.05  --dbg_dump_prop_clauses                 false
% 1.11/1.05  --dbg_dump_prop_clauses_file            -
% 1.11/1.05  --dbg_out_stat                          false
% 1.11/1.05  ------ Parsing...
% 1.11/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.11/1.05  
% 1.11/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.11/1.05  
% 1.11/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.11/1.05  
% 1.11/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.11/1.05  ------ Proving...
% 1.11/1.05  ------ Problem Properties 
% 1.11/1.05  
% 1.11/1.05  
% 1.11/1.05  clauses                                 8
% 1.11/1.05  conjectures                             1
% 1.11/1.05  EPR                                     1
% 1.11/1.05  Horn                                    8
% 1.11/1.05  unary                                   3
% 1.11/1.05  binary                                  1
% 1.11/1.05  lits                                    17
% 1.11/1.05  lits eq                                 7
% 1.11/1.05  fd_pure                                 0
% 1.11/1.05  fd_pseudo                               0
% 1.11/1.05  fd_cond                                 0
% 1.11/1.05  fd_pseudo_cond                          0
% 1.11/1.05  AC symbols                              0
% 1.11/1.05  
% 1.11/1.05  ------ Schedule dynamic 5 is on 
% 1.11/1.05  
% 1.11/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.11/1.05  
% 1.11/1.05  
% 1.11/1.05  ------ 
% 1.11/1.05  Current options:
% 1.11/1.05  ------ 
% 1.11/1.05  
% 1.11/1.05  ------ Input Options
% 1.11/1.05  
% 1.11/1.05  --out_options                           all
% 1.11/1.05  --tptp_safe_out                         true
% 1.11/1.05  --problem_path                          ""
% 1.11/1.05  --include_path                          ""
% 1.11/1.05  --clausifier                            res/vclausify_rel
% 1.11/1.05  --clausifier_options                    --mode clausify
% 1.11/1.05  --stdin                                 false
% 1.11/1.05  --stats_out                             all
% 1.11/1.05  
% 1.11/1.05  ------ General Options
% 1.11/1.05  
% 1.11/1.05  --fof                                   false
% 1.11/1.05  --time_out_real                         305.
% 1.11/1.05  --time_out_virtual                      -1.
% 1.11/1.05  --symbol_type_check                     false
% 1.11/1.05  --clausify_out                          false
% 1.11/1.05  --sig_cnt_out                           false
% 1.11/1.05  --trig_cnt_out                          false
% 1.11/1.05  --trig_cnt_out_tolerance                1.
% 1.11/1.05  --trig_cnt_out_sk_spl                   false
% 1.11/1.05  --abstr_cl_out                          false
% 1.11/1.05  
% 1.11/1.05  ------ Global Options
% 1.11/1.05  
% 1.11/1.05  --schedule                              default
% 1.11/1.05  --add_important_lit                     false
% 1.11/1.05  --prop_solver_per_cl                    1000
% 1.11/1.05  --min_unsat_core                        false
% 1.11/1.05  --soft_assumptions                      false
% 1.11/1.05  --soft_lemma_size                       3
% 1.11/1.05  --prop_impl_unit_size                   0
% 1.11/1.05  --prop_impl_unit                        []
% 1.11/1.05  --share_sel_clauses                     true
% 1.11/1.05  --reset_solvers                         false
% 1.11/1.05  --bc_imp_inh                            [conj_cone]
% 1.11/1.05  --conj_cone_tolerance                   3.
% 1.11/1.05  --extra_neg_conj                        none
% 1.11/1.05  --large_theory_mode                     true
% 1.11/1.05  --prolific_symb_bound                   200
% 1.11/1.05  --lt_threshold                          2000
% 1.11/1.05  --clause_weak_htbl                      true
% 1.11/1.05  --gc_record_bc_elim                     false
% 1.11/1.05  
% 1.11/1.05  ------ Preprocessing Options
% 1.11/1.05  
% 1.11/1.05  --preprocessing_flag                    true
% 1.11/1.05  --time_out_prep_mult                    0.1
% 1.11/1.05  --splitting_mode                        input
% 1.11/1.05  --splitting_grd                         true
% 1.11/1.05  --splitting_cvd                         false
% 1.11/1.05  --splitting_cvd_svl                     false
% 1.11/1.05  --splitting_nvd                         32
% 1.11/1.05  --sub_typing                            true
% 1.11/1.05  --prep_gs_sim                           true
% 1.11/1.05  --prep_unflatten                        true
% 1.11/1.05  --prep_res_sim                          true
% 1.11/1.05  --prep_upred                            true
% 1.11/1.05  --prep_sem_filter                       exhaustive
% 1.11/1.05  --prep_sem_filter_out                   false
% 1.11/1.05  --pred_elim                             true
% 1.11/1.05  --res_sim_input                         true
% 1.11/1.05  --eq_ax_congr_red                       true
% 1.11/1.05  --pure_diseq_elim                       true
% 1.11/1.05  --brand_transform                       false
% 1.11/1.05  --non_eq_to_eq                          false
% 1.11/1.05  --prep_def_merge                        true
% 1.11/1.05  --prep_def_merge_prop_impl              false
% 1.11/1.05  --prep_def_merge_mbd                    true
% 1.11/1.05  --prep_def_merge_tr_red                 false
% 1.11/1.05  --prep_def_merge_tr_cl                  false
% 1.11/1.05  --smt_preprocessing                     true
% 1.11/1.05  --smt_ac_axioms                         fast
% 1.11/1.05  --preprocessed_out                      false
% 1.11/1.05  --preprocessed_stats                    false
% 1.11/1.05  
% 1.11/1.05  ------ Abstraction refinement Options
% 1.11/1.05  
% 1.11/1.05  --abstr_ref                             []
% 1.11/1.05  --abstr_ref_prep                        false
% 1.11/1.05  --abstr_ref_until_sat                   false
% 1.11/1.05  --abstr_ref_sig_restrict                funpre
% 1.11/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.11/1.05  --abstr_ref_under                       []
% 1.11/1.05  
% 1.11/1.05  ------ SAT Options
% 1.11/1.05  
% 1.11/1.05  --sat_mode                              false
% 1.11/1.05  --sat_fm_restart_options                ""
% 1.11/1.05  --sat_gr_def                            false
% 1.11/1.05  --sat_epr_types                         true
% 1.11/1.05  --sat_non_cyclic_types                  false
% 1.11/1.05  --sat_finite_models                     false
% 1.11/1.05  --sat_fm_lemmas                         false
% 1.11/1.05  --sat_fm_prep                           false
% 1.11/1.05  --sat_fm_uc_incr                        true
% 1.11/1.05  --sat_out_model                         small
% 1.11/1.05  --sat_out_clauses                       false
% 1.11/1.05  
% 1.11/1.05  ------ QBF Options
% 1.11/1.05  
% 1.11/1.05  --qbf_mode                              false
% 1.11/1.05  --qbf_elim_univ                         false
% 1.11/1.05  --qbf_dom_inst                          none
% 1.11/1.05  --qbf_dom_pre_inst                      false
% 1.11/1.05  --qbf_sk_in                             false
% 1.11/1.05  --qbf_pred_elim                         true
% 1.11/1.05  --qbf_split                             512
% 1.11/1.05  
% 1.11/1.05  ------ BMC1 Options
% 1.11/1.05  
% 1.11/1.05  --bmc1_incremental                      false
% 1.11/1.05  --bmc1_axioms                           reachable_all
% 1.11/1.05  --bmc1_min_bound                        0
% 1.11/1.05  --bmc1_max_bound                        -1
% 1.11/1.05  --bmc1_max_bound_default                -1
% 1.11/1.05  --bmc1_symbol_reachability              true
% 1.11/1.05  --bmc1_property_lemmas                  false
% 1.11/1.05  --bmc1_k_induction                      false
% 1.11/1.05  --bmc1_non_equiv_states                 false
% 1.11/1.05  --bmc1_deadlock                         false
% 1.11/1.05  --bmc1_ucm                              false
% 1.11/1.05  --bmc1_add_unsat_core                   none
% 1.11/1.05  --bmc1_unsat_core_children              false
% 1.11/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.11/1.05  --bmc1_out_stat                         full
% 1.11/1.05  --bmc1_ground_init                      false
% 1.11/1.05  --bmc1_pre_inst_next_state              false
% 1.11/1.05  --bmc1_pre_inst_state                   false
% 1.11/1.05  --bmc1_pre_inst_reach_state             false
% 1.11/1.05  --bmc1_out_unsat_core                   false
% 1.11/1.05  --bmc1_aig_witness_out                  false
% 1.11/1.05  --bmc1_verbose                          false
% 1.11/1.05  --bmc1_dump_clauses_tptp                false
% 1.11/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.11/1.05  --bmc1_dump_file                        -
% 1.11/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.11/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.11/1.05  --bmc1_ucm_extend_mode                  1
% 1.11/1.05  --bmc1_ucm_init_mode                    2
% 1.11/1.05  --bmc1_ucm_cone_mode                    none
% 1.11/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.11/1.05  --bmc1_ucm_relax_model                  4
% 1.11/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.11/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.11/1.05  --bmc1_ucm_layered_model                none
% 1.11/1.05  --bmc1_ucm_max_lemma_size               10
% 1.11/1.05  
% 1.11/1.05  ------ AIG Options
% 1.11/1.05  
% 1.11/1.05  --aig_mode                              false
% 1.11/1.05  
% 1.11/1.05  ------ Instantiation Options
% 1.11/1.05  
% 1.11/1.05  --instantiation_flag                    true
% 1.11/1.05  --inst_sos_flag                         false
% 1.11/1.05  --inst_sos_phase                        true
% 1.11/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.11/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.11/1.05  --inst_lit_sel_side                     none
% 1.11/1.05  --inst_solver_per_active                1400
% 1.11/1.05  --inst_solver_calls_frac                1.
% 1.11/1.05  --inst_passive_queue_type               priority_queues
% 1.11/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.11/1.05  --inst_passive_queues_freq              [25;2]
% 1.11/1.05  --inst_dismatching                      true
% 1.11/1.05  --inst_eager_unprocessed_to_passive     true
% 1.11/1.05  --inst_prop_sim_given                   true
% 1.11/1.05  --inst_prop_sim_new                     false
% 1.11/1.05  --inst_subs_new                         false
% 1.11/1.05  --inst_eq_res_simp                      false
% 1.11/1.05  --inst_subs_given                       false
% 1.11/1.05  --inst_orphan_elimination               true
% 1.11/1.05  --inst_learning_loop_flag               true
% 1.11/1.05  --inst_learning_start                   3000
% 1.11/1.05  --inst_learning_factor                  2
% 1.11/1.05  --inst_start_prop_sim_after_learn       3
% 1.11/1.05  --inst_sel_renew                        solver
% 1.11/1.05  --inst_lit_activity_flag                true
% 1.11/1.05  --inst_restr_to_given                   false
% 1.11/1.05  --inst_activity_threshold               500
% 1.11/1.05  --inst_out_proof                        true
% 1.11/1.05  
% 1.11/1.05  ------ Resolution Options
% 1.11/1.05  
% 1.11/1.05  --resolution_flag                       false
% 1.11/1.05  --res_lit_sel                           adaptive
% 1.11/1.05  --res_lit_sel_side                      none
% 1.11/1.05  --res_ordering                          kbo
% 1.11/1.05  --res_to_prop_solver                    active
% 1.11/1.05  --res_prop_simpl_new                    false
% 1.11/1.05  --res_prop_simpl_given                  true
% 1.11/1.05  --res_passive_queue_type                priority_queues
% 1.11/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.11/1.05  --res_passive_queues_freq               [15;5]
% 1.11/1.05  --res_forward_subs                      full
% 1.11/1.05  --res_backward_subs                     full
% 1.11/1.05  --res_forward_subs_resolution           true
% 1.11/1.05  --res_backward_subs_resolution          true
% 1.11/1.05  --res_orphan_elimination                true
% 1.11/1.05  --res_time_limit                        2.
% 1.11/1.05  --res_out_proof                         true
% 1.11/1.05  
% 1.11/1.05  ------ Superposition Options
% 1.11/1.05  
% 1.11/1.05  --superposition_flag                    true
% 1.11/1.05  --sup_passive_queue_type                priority_queues
% 1.11/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.11/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.11/1.05  --demod_completeness_check              fast
% 1.11/1.05  --demod_use_ground                      true
% 1.11/1.05  --sup_to_prop_solver                    passive
% 1.11/1.05  --sup_prop_simpl_new                    true
% 1.11/1.05  --sup_prop_simpl_given                  true
% 1.11/1.05  --sup_fun_splitting                     false
% 1.11/1.05  --sup_smt_interval                      50000
% 1.11/1.05  
% 1.11/1.05  ------ Superposition Simplification Setup
% 1.11/1.05  
% 1.11/1.05  --sup_indices_passive                   []
% 1.11/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.11/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.11/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.05  --sup_full_bw                           [BwDemod]
% 1.11/1.05  --sup_immed_triv                        [TrivRules]
% 1.11/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.11/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.05  --sup_immed_bw_main                     []
% 1.11/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.11/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.11/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.11/1.05  
% 1.11/1.05  ------ Combination Options
% 1.11/1.05  
% 1.11/1.05  --comb_res_mult                         3
% 1.11/1.05  --comb_sup_mult                         2
% 1.11/1.05  --comb_inst_mult                        10
% 1.11/1.05  
% 1.11/1.05  ------ Debug Options
% 1.11/1.05  
% 1.11/1.05  --dbg_backtrace                         false
% 1.11/1.05  --dbg_dump_prop_clauses                 false
% 1.11/1.05  --dbg_dump_prop_clauses_file            -
% 1.11/1.05  --dbg_out_stat                          false
% 1.11/1.05  
% 1.11/1.05  
% 1.11/1.05  
% 1.11/1.05  
% 1.11/1.05  ------ Proving...
% 1.11/1.05  
% 1.11/1.05  
% 1.11/1.05  % SZS status Theorem for theBenchmark.p
% 1.11/1.05  
% 1.11/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.11/1.05  
% 1.11/1.05  fof(f1,axiom,(
% 1.11/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f12,plain,(
% 1.11/1.05    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.11/1.05    inference(ennf_transformation,[],[f1])).
% 1.11/1.05  
% 1.11/1.05  fof(f28,plain,(
% 1.11/1.05    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.11/1.05    inference(cnf_transformation,[],[f12])).
% 1.11/1.05  
% 1.11/1.05  fof(f9,conjecture,(
% 1.11/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f10,negated_conjecture,(
% 1.11/1.05    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 1.11/1.05    inference(negated_conjecture,[],[f9])).
% 1.11/1.05  
% 1.11/1.05  fof(f22,plain,(
% 1.11/1.05    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.11/1.05    inference(ennf_transformation,[],[f10])).
% 1.11/1.05  
% 1.11/1.05  fof(f23,plain,(
% 1.11/1.05    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.11/1.05    inference(flattening,[],[f22])).
% 1.11/1.05  
% 1.11/1.05  fof(f26,plain,(
% 1.11/1.05    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.11/1.05    introduced(choice_axiom,[])).
% 1.11/1.05  
% 1.11/1.05  fof(f27,plain,(
% 1.11/1.05    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.11/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26])).
% 1.11/1.05  
% 1.11/1.05  fof(f38,plain,(
% 1.11/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.11/1.05    inference(cnf_transformation,[],[f27])).
% 1.11/1.05  
% 1.11/1.05  fof(f3,axiom,(
% 1.11/1.05    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f31,plain,(
% 1.11/1.05    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.11/1.05    inference(cnf_transformation,[],[f3])).
% 1.11/1.05  
% 1.11/1.05  fof(f39,plain,(
% 1.11/1.05    r1_tarski(sK1,sK2)),
% 1.11/1.05    inference(cnf_transformation,[],[f27])).
% 1.11/1.05  
% 1.11/1.05  fof(f5,axiom,(
% 1.11/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f16,plain,(
% 1.11/1.05    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 1.11/1.05    inference(ennf_transformation,[],[f5])).
% 1.11/1.05  
% 1.11/1.05  fof(f17,plain,(
% 1.11/1.05    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 1.11/1.05    inference(flattening,[],[f16])).
% 1.11/1.05  
% 1.11/1.05  fof(f33,plain,(
% 1.11/1.05    ( ! [X2,X0,X1] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 1.11/1.05    inference(cnf_transformation,[],[f17])).
% 1.11/1.05  
% 1.11/1.05  fof(f2,axiom,(
% 1.11/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f13,plain,(
% 1.11/1.05    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.11/1.05    inference(ennf_transformation,[],[f2])).
% 1.11/1.05  
% 1.11/1.05  fof(f24,plain,(
% 1.11/1.05    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.11/1.05    inference(nnf_transformation,[],[f13])).
% 1.11/1.05  
% 1.11/1.05  fof(f29,plain,(
% 1.11/1.05    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.11/1.05    inference(cnf_transformation,[],[f24])).
% 1.11/1.05  
% 1.11/1.05  fof(f6,axiom,(
% 1.11/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f11,plain,(
% 1.11/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.11/1.05    inference(pure_predicate_removal,[],[f6])).
% 1.11/1.05  
% 1.11/1.05  fof(f18,plain,(
% 1.11/1.05    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.11/1.05    inference(ennf_transformation,[],[f11])).
% 1.11/1.05  
% 1.11/1.05  fof(f34,plain,(
% 1.11/1.05    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.11/1.05    inference(cnf_transformation,[],[f18])).
% 1.11/1.05  
% 1.11/1.05  fof(f4,axiom,(
% 1.11/1.05    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f14,plain,(
% 1.11/1.05    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.11/1.05    inference(ennf_transformation,[],[f4])).
% 1.11/1.05  
% 1.11/1.05  fof(f15,plain,(
% 1.11/1.05    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.11/1.05    inference(flattening,[],[f14])).
% 1.11/1.05  
% 1.11/1.05  fof(f32,plain,(
% 1.11/1.05    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.11/1.05    inference(cnf_transformation,[],[f15])).
% 1.11/1.05  
% 1.11/1.05  fof(f7,axiom,(
% 1.11/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f19,plain,(
% 1.11/1.05    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.11/1.05    inference(ennf_transformation,[],[f7])).
% 1.11/1.05  
% 1.11/1.05  fof(f35,plain,(
% 1.11/1.05    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.11/1.05    inference(cnf_transformation,[],[f19])).
% 1.11/1.05  
% 1.11/1.05  fof(f8,axiom,(
% 1.11/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.11/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.11/1.05  
% 1.11/1.05  fof(f20,plain,(
% 1.11/1.05    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.11/1.05    inference(ennf_transformation,[],[f8])).
% 1.11/1.05  
% 1.11/1.05  fof(f21,plain,(
% 1.11/1.05    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.11/1.05    inference(flattening,[],[f20])).
% 1.11/1.05  
% 1.11/1.05  fof(f25,plain,(
% 1.11/1.05    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.11/1.05    inference(nnf_transformation,[],[f21])).
% 1.11/1.05  
% 1.11/1.05  fof(f37,plain,(
% 1.11/1.05    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.11/1.05    inference(cnf_transformation,[],[f25])).
% 1.11/1.05  
% 1.11/1.05  fof(f41,plain,(
% 1.11/1.05    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.11/1.05    inference(equality_resolution,[],[f37])).
% 1.11/1.05  
% 1.11/1.05  fof(f40,plain,(
% 1.11/1.05    ~r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3)),
% 1.11/1.05    inference(cnf_transformation,[],[f27])).
% 1.11/1.05  
% 1.11/1.05  cnf(c_0,plain,
% 1.11/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.11/1.05      | ~ v1_relat_1(X1)
% 1.11/1.05      | v1_relat_1(X0) ),
% 1.11/1.05      inference(cnf_transformation,[],[f28]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_12,negated_conjecture,
% 1.11/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.11/1.05      inference(cnf_transformation,[],[f38]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_164,plain,
% 1.11/1.05      ( ~ v1_relat_1(X0)
% 1.11/1.05      | v1_relat_1(X1)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0)
% 1.11/1.05      | sK3 != X1 ),
% 1.11/1.05      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_165,plain,
% 1.11/1.05      ( ~ v1_relat_1(X0)
% 1.11/1.05      | v1_relat_1(sK3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0) ),
% 1.11/1.05      inference(unflattening,[status(thm)],[c_164]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_440,plain,
% 1.11/1.05      ( ~ v1_relat_1(X0_42)
% 1.11/1.05      | v1_relat_1(sK3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_42) ),
% 1.11/1.05      inference(subtyping,[status(esa)],[c_165]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_592,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(X0_42)
% 1.11/1.05      | v1_relat_1(X0_42) != iProver_top
% 1.11/1.05      | v1_relat_1(sK3) = iProver_top ),
% 1.11/1.05      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_455,plain,
% 1.11/1.05      ( X0_44 != X1_44
% 1.11/1.05      | k2_zfmisc_1(X0_43,X0_44) = k2_zfmisc_1(X0_43,X1_44) ),
% 1.11/1.05      theory(equality) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_462,plain,
% 1.11/1.05      ( sK1 != sK1 | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK1) ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_455]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_447,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_467,plain,
% 1.11/1.05      ( sK1 = sK1 ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_447]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_3,plain,
% 1.11/1.05      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.11/1.05      inference(cnf_transformation,[],[f31]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_444,plain,
% 1.11/1.05      ( v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) ),
% 1.11/1.05      inference(subtyping,[status(esa)],[c_3]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_469,plain,
% 1.11/1.05      ( v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) = iProver_top ),
% 1.11/1.05      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_471,plain,
% 1.11/1.05      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_469]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_642,plain,
% 1.11/1.05      ( ~ v1_relat_1(k2_zfmisc_1(X0_43,X0_44))
% 1.11/1.05      | v1_relat_1(sK3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_440]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_643,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44))
% 1.11/1.05      | v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) != iProver_top
% 1.11/1.05      | v1_relat_1(sK3) = iProver_top ),
% 1.11/1.05      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_645,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 1.11/1.05      | v1_relat_1(sK3) = iProver_top ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_643]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_452,plain,
% 1.11/1.05      ( k1_zfmisc_1(X0_42) = k1_zfmisc_1(X1_42) | X0_42 != X1_42 ),
% 1.11/1.05      theory(equality) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_647,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | k2_zfmisc_1(X0_43,X0_44) != k2_zfmisc_1(sK0,sK1) ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_452]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_648,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1) ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_647]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_692,plain,
% 1.11/1.05      ( v1_relat_1(sK3) = iProver_top ),
% 1.11/1.05      inference(global_propositional_subsumption,
% 1.11/1.05                [status(thm)],
% 1.11/1.05                [c_592,c_462,c_467,c_471,c_645,c_648]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_11,negated_conjecture,
% 1.11/1.05      ( r1_tarski(sK1,sK2) ),
% 1.11/1.05      inference(cnf_transformation,[],[f39]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_441,negated_conjecture,
% 1.11/1.05      ( r1_tarski(sK1,sK2) ),
% 1.11/1.05      inference(subtyping,[status(esa)],[c_11]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_591,plain,
% 1.11/1.05      ( r1_tarski(sK1,sK2) = iProver_top ),
% 1.11/1.05      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_5,plain,
% 1.11/1.05      ( ~ r1_tarski(X0,X1)
% 1.11/1.05      | ~ v1_relat_1(X2)
% 1.11/1.05      | k8_relat_1(X1,k8_relat_1(X0,X2)) = k8_relat_1(X0,X2) ),
% 1.11/1.05      inference(cnf_transformation,[],[f33]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_442,plain,
% 1.11/1.05      ( ~ r1_tarski(X0_44,X1_44)
% 1.11/1.05      | ~ v1_relat_1(X0_42)
% 1.11/1.05      | k8_relat_1(X1_44,k8_relat_1(X0_44,X0_42)) = k8_relat_1(X0_44,X0_42) ),
% 1.11/1.05      inference(subtyping,[status(esa)],[c_5]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_590,plain,
% 1.11/1.05      ( k8_relat_1(X0_44,k8_relat_1(X1_44,X0_42)) = k8_relat_1(X1_44,X0_42)
% 1.11/1.05      | r1_tarski(X1_44,X0_44) != iProver_top
% 1.11/1.05      | v1_relat_1(X0_42) != iProver_top ),
% 1.11/1.05      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_827,plain,
% 1.11/1.05      ( k8_relat_1(sK2,k8_relat_1(sK1,X0_42)) = k8_relat_1(sK1,X0_42)
% 1.11/1.05      | v1_relat_1(X0_42) != iProver_top ),
% 1.11/1.05      inference(superposition,[status(thm)],[c_591,c_590]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_944,plain,
% 1.11/1.05      ( k8_relat_1(sK2,k8_relat_1(sK1,sK3)) = k8_relat_1(sK1,sK3) ),
% 1.11/1.05      inference(superposition,[status(thm)],[c_692,c_827]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_2,plain,
% 1.11/1.05      ( r1_tarski(k2_relat_1(X0),X1)
% 1.11/1.05      | ~ v5_relat_1(X0,X1)
% 1.11/1.05      | ~ v1_relat_1(X0) ),
% 1.11/1.05      inference(cnf_transformation,[],[f29]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_6,plain,
% 1.11/1.05      ( v5_relat_1(X0,X1)
% 1.11/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.11/1.05      inference(cnf_transformation,[],[f34]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_179,plain,
% 1.11/1.05      ( v5_relat_1(X0,X1)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | sK3 != X0 ),
% 1.11/1.05      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_180,plain,
% 1.11/1.05      ( v5_relat_1(sK3,X0)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(unflattening,[status(thm)],[c_179]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_219,plain,
% 1.11/1.05      ( r1_tarski(k2_relat_1(X0),X1)
% 1.11/1.05      | ~ v1_relat_1(X0)
% 1.11/1.05      | X2 != X1
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(X3,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | sK3 != X0 ),
% 1.11/1.05      inference(resolution_lifted,[status(thm)],[c_2,c_180]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_220,plain,
% 1.11/1.05      ( r1_tarski(k2_relat_1(sK3),X0)
% 1.11/1.05      | ~ v1_relat_1(sK3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(unflattening,[status(thm)],[c_219]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_438,plain,
% 1.11/1.05      ( r1_tarski(k2_relat_1(sK3),X0_44)
% 1.11/1.05      | ~ v1_relat_1(sK3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(subtyping,[status(esa)],[c_220]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_593,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | r1_tarski(k2_relat_1(sK3),X0_44) = iProver_top
% 1.11/1.05      | v1_relat_1(sK3) != iProver_top ),
% 1.11/1.05      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_481,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | r1_tarski(k2_relat_1(sK3),X0_44) = iProver_top
% 1.11/1.05      | v1_relat_1(sK3) != iProver_top ),
% 1.11/1.05      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_733,plain,
% 1.11/1.05      ( r1_tarski(k2_relat_1(sK3),X0_44) = iProver_top
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(global_propositional_subsumption,
% 1.11/1.05                [status(thm)],
% 1.11/1.05                [c_593,c_462,c_467,c_471,c_481,c_645,c_648]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_734,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | r1_tarski(k2_relat_1(sK3),X0_44) = iProver_top ),
% 1.11/1.05      inference(renaming,[status(thm)],[c_733]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_741,plain,
% 1.11/1.05      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 1.11/1.05      inference(equality_resolution,[status(thm)],[c_734]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_4,plain,
% 1.11/1.05      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.11/1.05      | ~ v1_relat_1(X0)
% 1.11/1.05      | k8_relat_1(X1,X0) = X0 ),
% 1.11/1.05      inference(cnf_transformation,[],[f32]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_443,plain,
% 1.11/1.05      ( ~ r1_tarski(k2_relat_1(X0_42),X0_44)
% 1.11/1.05      | ~ v1_relat_1(X0_42)
% 1.11/1.05      | k8_relat_1(X0_44,X0_42) = X0_42 ),
% 1.11/1.05      inference(subtyping,[status(esa)],[c_4]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_589,plain,
% 1.11/1.05      ( k8_relat_1(X0_44,X0_42) = X0_42
% 1.11/1.05      | r1_tarski(k2_relat_1(X0_42),X0_44) != iProver_top
% 1.11/1.05      | v1_relat_1(X0_42) != iProver_top ),
% 1.11/1.05      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_800,plain,
% 1.11/1.05      ( k8_relat_1(sK1,sK3) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 1.11/1.05      inference(superposition,[status(thm)],[c_741,c_589]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_470,plain,
% 1.11/1.05      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_444]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_473,plain,
% 1.11/1.05      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 1.11/1.05      | ~ v1_relat_1(sK3)
% 1.11/1.05      | k8_relat_1(sK1,sK3) = sK3 ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_443]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_482,plain,
% 1.11/1.05      ( r1_tarski(k2_relat_1(sK3),sK1)
% 1.11/1.05      | ~ v1_relat_1(sK3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_438]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_644,plain,
% 1.11/1.05      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | v1_relat_1(sK3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(instantiation,[status(thm)],[c_642]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_844,plain,
% 1.11/1.05      ( k8_relat_1(sK1,sK3) = sK3 ),
% 1.11/1.05      inference(global_propositional_subsumption,
% 1.11/1.05                [status(thm)],
% 1.11/1.05                [c_800,c_462,c_467,c_470,c_473,c_482,c_644,c_648]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_949,plain,
% 1.11/1.05      ( k8_relat_1(sK2,sK3) = sK3 ),
% 1.11/1.05      inference(light_normalisation,[status(thm)],[c_944,c_844]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_7,plain,
% 1.11/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.05      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 1.11/1.05      inference(cnf_transformation,[],[f35]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_191,plain,
% 1.11/1.05      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | sK3 != X3 ),
% 1.11/1.05      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_192,plain,
% 1.11/1.05      ( k6_relset_1(X0,X1,X2,sK3) = k8_relat_1(X2,sK3)
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(unflattening,[status(thm)],[c_191]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_439,plain,
% 1.11/1.05      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 1.11/1.05      | k6_relset_1(X0_43,X0_44,X1_44,sK3) = k8_relat_1(X1_44,sK3) ),
% 1.11/1.05      inference(subtyping,[status(esa)],[c_192]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_663,plain,
% 1.11/1.05      ( k6_relset_1(sK0,sK1,X0_44,sK3) = k8_relat_1(X0_44,sK3) ),
% 1.11/1.05      inference(equality_resolution,[status(thm)],[c_439]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_8,plain,
% 1.11/1.05      ( r2_relset_1(X0,X1,X2,X2)
% 1.11/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.11/1.05      inference(cnf_transformation,[],[f41]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_10,negated_conjecture,
% 1.11/1.05      ( ~ r2_relset_1(sK0,sK1,k6_relset_1(sK0,sK1,sK2,sK3),sK3) ),
% 1.11/1.05      inference(cnf_transformation,[],[f40]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_151,plain,
% 1.11/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.11/1.05      | k6_relset_1(sK0,sK1,sK2,sK3) != X0
% 1.11/1.05      | sK3 != X0
% 1.11/1.05      | sK1 != X2
% 1.11/1.05      | sK0 != X1 ),
% 1.11/1.05      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_152,plain,
% 1.11/1.05      ( ~ m1_subset_1(k6_relset_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.11/1.05      | sK3 != k6_relset_1(sK0,sK1,sK2,sK3) ),
% 1.11/1.05      inference(unflattening,[status(thm)],[c_151]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_200,plain,
% 1.11/1.05      ( k6_relset_1(sK0,sK1,sK2,sK3) != sK3
% 1.11/1.05      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 1.11/1.05      inference(resolution_lifted,[status(thm)],[c_12,c_152]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_325,plain,
% 1.11/1.05      ( k6_relset_1(sK0,sK1,sK2,sK3) != sK3 ),
% 1.11/1.05      inference(equality_resolution_simp,[status(thm)],[c_200]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_437,plain,
% 1.11/1.05      ( k6_relset_1(sK0,sK1,sK2,sK3) != sK3 ),
% 1.11/1.05      inference(subtyping,[status(esa)],[c_325]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(c_681,plain,
% 1.11/1.05      ( k8_relat_1(sK2,sK3) != sK3 ),
% 1.11/1.05      inference(demodulation,[status(thm)],[c_663,c_437]) ).
% 1.11/1.05  
% 1.11/1.05  cnf(contradiction,plain,
% 1.11/1.05      ( $false ),
% 1.11/1.05      inference(minisat,[status(thm)],[c_949,c_681]) ).
% 1.11/1.05  
% 1.11/1.05  
% 1.11/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.11/1.05  
% 1.11/1.05  ------                               Statistics
% 1.11/1.05  
% 1.11/1.05  ------ General
% 1.11/1.05  
% 1.11/1.05  abstr_ref_over_cycles:                  0
% 1.11/1.05  abstr_ref_under_cycles:                 0
% 1.11/1.05  gc_basic_clause_elim:                   0
% 1.11/1.05  forced_gc_time:                         0
% 1.11/1.05  parsing_time:                           0.01
% 1.11/1.05  unif_index_cands_time:                  0.
% 1.11/1.05  unif_index_add_time:                    0.
% 1.11/1.05  orderings_time:                         0.
% 1.11/1.05  out_proof_time:                         0.014
% 1.11/1.05  total_time:                             0.093
% 1.11/1.05  num_of_symbols:                         46
% 1.11/1.05  num_of_terms:                           1171
% 1.11/1.05  
% 1.11/1.05  ------ Preprocessing
% 1.11/1.05  
% 1.11/1.05  num_of_splits:                          0
% 1.11/1.05  num_of_split_atoms:                     0
% 1.11/1.05  num_of_reused_defs:                     0
% 1.11/1.05  num_eq_ax_congr_red:                    8
% 1.11/1.05  num_of_sem_filtered_clauses:            1
% 1.11/1.05  num_of_subtypes:                        4
% 1.11/1.05  monotx_restored_types:                  0
% 1.11/1.05  sat_num_of_epr_types:                   0
% 1.11/1.05  sat_num_of_non_cyclic_types:            0
% 1.11/1.05  sat_guarded_non_collapsed_types:        1
% 1.11/1.05  num_pure_diseq_elim:                    0
% 1.11/1.05  simp_replaced_by:                       0
% 1.11/1.05  res_preprocessed:                       62
% 1.11/1.05  prep_upred:                             0
% 1.11/1.05  prep_unflattend:                        24
% 1.11/1.05  smt_new_axioms:                         0
% 1.11/1.05  pred_elim_cands:                        2
% 1.11/1.05  pred_elim:                              3
% 1.11/1.05  pred_elim_cl:                           5
% 1.11/1.05  pred_elim_cycles:                       5
% 1.11/1.05  merged_defs:                            0
% 1.11/1.05  merged_defs_ncl:                        0
% 1.11/1.05  bin_hyper_res:                          0
% 1.11/1.05  prep_cycles:                            4
% 1.11/1.05  pred_elim_time:                         0.006
% 1.11/1.05  splitting_time:                         0.
% 1.11/1.05  sem_filter_time:                        0.
% 1.11/1.05  monotx_time:                            0.
% 1.11/1.05  subtype_inf_time:                       0.
% 1.11/1.05  
% 1.11/1.05  ------ Problem properties
% 1.11/1.05  
% 1.11/1.05  clauses:                                8
% 1.11/1.05  conjectures:                            1
% 1.11/1.05  epr:                                    1
% 1.11/1.05  horn:                                   8
% 1.11/1.05  ground:                                 2
% 1.11/1.05  unary:                                  3
% 1.11/1.05  binary:                                 1
% 1.11/1.05  lits:                                   17
% 1.11/1.05  lits_eq:                                7
% 1.11/1.05  fd_pure:                                0
% 1.11/1.05  fd_pseudo:                              0
% 1.11/1.05  fd_cond:                                0
% 1.11/1.05  fd_pseudo_cond:                         0
% 1.11/1.05  ac_symbols:                             0
% 1.11/1.05  
% 1.11/1.05  ------ Propositional Solver
% 1.11/1.05  
% 1.11/1.05  prop_solver_calls:                      26
% 1.11/1.05  prop_fast_solver_calls:                 344
% 1.11/1.05  smt_solver_calls:                       0
% 1.11/1.05  smt_fast_solver_calls:                  0
% 1.11/1.05  prop_num_of_clauses:                    283
% 1.11/1.05  prop_preprocess_simplified:             1752
% 1.11/1.05  prop_fo_subsumed:                       4
% 1.11/1.05  prop_solver_time:                       0.
% 1.11/1.05  smt_solver_time:                        0.
% 1.11/1.05  smt_fast_solver_time:                   0.
% 1.11/1.05  prop_fast_solver_time:                  0.
% 1.11/1.05  prop_unsat_core_time:                   0.
% 1.11/1.05  
% 1.11/1.05  ------ QBF
% 1.11/1.05  
% 1.11/1.05  qbf_q_res:                              0
% 1.11/1.05  qbf_num_tautologies:                    0
% 1.11/1.05  qbf_prep_cycles:                        0
% 1.11/1.05  
% 1.11/1.05  ------ BMC1
% 1.11/1.05  
% 1.11/1.05  bmc1_current_bound:                     -1
% 1.11/1.05  bmc1_last_solved_bound:                 -1
% 1.11/1.05  bmc1_unsat_core_size:                   -1
% 1.11/1.05  bmc1_unsat_core_parents_size:           -1
% 1.11/1.05  bmc1_merge_next_fun:                    0
% 1.11/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.11/1.05  
% 1.11/1.05  ------ Instantiation
% 1.11/1.05  
% 1.11/1.05  inst_num_of_clauses:                    92
% 1.11/1.05  inst_num_in_passive:                    27
% 1.11/1.05  inst_num_in_active:                     62
% 1.11/1.05  inst_num_in_unprocessed:                3
% 1.11/1.05  inst_num_of_loops:                      70
% 1.11/1.05  inst_num_of_learning_restarts:          0
% 1.11/1.05  inst_num_moves_active_passive:          6
% 1.11/1.05  inst_lit_activity:                      0
% 1.11/1.05  inst_lit_activity_moves:                0
% 1.11/1.05  inst_num_tautologies:                   0
% 1.11/1.05  inst_num_prop_implied:                  0
% 1.11/1.05  inst_num_existing_simplified:           0
% 1.11/1.05  inst_num_eq_res_simplified:             0
% 1.11/1.05  inst_num_child_elim:                    0
% 1.11/1.05  inst_num_of_dismatching_blockings:      9
% 1.11/1.05  inst_num_of_non_proper_insts:           48
% 1.11/1.05  inst_num_of_duplicates:                 0
% 1.11/1.05  inst_inst_num_from_inst_to_res:         0
% 1.11/1.05  inst_dismatching_checking_time:         0.
% 1.11/1.05  
% 1.11/1.05  ------ Resolution
% 1.11/1.05  
% 1.11/1.05  res_num_of_clauses:                     0
% 1.11/1.05  res_num_in_passive:                     0
% 1.11/1.05  res_num_in_active:                      0
% 1.11/1.05  res_num_of_loops:                       66
% 1.11/1.05  res_forward_subset_subsumed:            6
% 1.11/1.05  res_backward_subset_subsumed:           0
% 1.11/1.05  res_forward_subsumed:                   0
% 1.11/1.05  res_backward_subsumed:                  0
% 1.11/1.05  res_forward_subsumption_resolution:     0
% 1.11/1.05  res_backward_subsumption_resolution:    0
% 1.11/1.05  res_clause_to_clause_subsumption:       17
% 1.11/1.05  res_orphan_elimination:                 0
% 1.11/1.05  res_tautology_del:                      8
% 1.11/1.05  res_num_eq_res_simplified:              1
% 1.11/1.05  res_num_sel_changes:                    0
% 1.11/1.05  res_moves_from_active_to_pass:          0
% 1.11/1.05  
% 1.11/1.05  ------ Superposition
% 1.11/1.05  
% 1.11/1.05  sup_time_total:                         0.
% 1.11/1.05  sup_time_generating:                    0.
% 1.11/1.05  sup_time_sim_full:                      0.
% 1.11/1.05  sup_time_sim_immed:                     0.
% 1.11/1.05  
% 1.11/1.05  sup_num_of_clauses:                     15
% 1.11/1.05  sup_num_in_active:                      12
% 1.11/1.05  sup_num_in_passive:                     3
% 1.11/1.05  sup_num_of_loops:                       12
% 1.11/1.05  sup_fw_superposition:                   5
% 1.11/1.05  sup_bw_superposition:                   0
% 1.11/1.05  sup_immediate_simplified:               1
% 1.11/1.05  sup_given_eliminated:                   0
% 1.11/1.05  comparisons_done:                       0
% 1.11/1.05  comparisons_avoided:                    0
% 1.11/1.05  
% 1.11/1.05  ------ Simplifications
% 1.11/1.05  
% 1.11/1.05  
% 1.11/1.05  sim_fw_subset_subsumed:                 0
% 1.11/1.05  sim_bw_subset_subsumed:                 0
% 1.11/1.05  sim_fw_subsumed:                        0
% 1.11/1.05  sim_bw_subsumed:                        0
% 1.11/1.05  sim_fw_subsumption_res:                 0
% 1.11/1.05  sim_bw_subsumption_res:                 0
% 1.11/1.05  sim_tautology_del:                      0
% 1.11/1.05  sim_eq_tautology_del:                   0
% 1.11/1.05  sim_eq_res_simp:                        0
% 1.11/1.05  sim_fw_demodulated:                     0
% 1.11/1.05  sim_bw_demodulated:                     1
% 1.11/1.05  sim_light_normalised:                   1
% 1.11/1.05  sim_joinable_taut:                      0
% 1.11/1.05  sim_joinable_simp:                      0
% 1.11/1.05  sim_ac_normalised:                      0
% 1.11/1.05  sim_smt_subsumption:                    0
% 1.11/1.05  
%------------------------------------------------------------------------------
