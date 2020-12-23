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
% DateTime   : Thu Dec  3 11:55:41 EST 2020

% Result     : Theorem 0.94s
% Output     : CNFRefutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 186 expanded)
%              Number of clauses        :   57 (  87 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  237 ( 487 expanded)
%              Number of equality atoms :   89 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
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
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_185,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_186,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_216,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_186])).

cnf(c_217,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_283,plain,
    ( r1_tarski(k1_relat_1(sK3),X0_43)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(subtyping,[status(esa)],[c_217])).

cnf(c_436,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_300,plain,
    ( X0_43 != X1_43
    | k2_zfmisc_1(X0_43,X0_44) = k2_zfmisc_1(X1_43,X0_44) ),
    theory(equality)).

cnf(c_307,plain,
    ( sK1 != sK1
    | k2_zfmisc_1(sK1,sK0) = k2_zfmisc_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_300])).

cnf(c_292,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_312,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_288,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_315,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_317,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_324,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_161,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_162,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_161])).

cnf(c_285,plain,
    ( ~ v1_relat_1(X0_42)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0_42) ),
    inference(subtyping,[status(esa)],[c_162])).

cnf(c_485,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0_43,X0_44))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_486,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44))
    | v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_488,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_298,plain,
    ( k1_zfmisc_1(X0_42) = k1_zfmisc_1(X1_42)
    | X0_42 != X1_42 ),
    theory(equality)).

cnf(c_490,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k2_zfmisc_1(X0_43,X0_44) != k2_zfmisc_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_491,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k2_zfmisc_1(sK1,sK0) != k2_zfmisc_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_490])).

cnf(c_579,plain,
    ( r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_307,c_312,c_317,c_324,c_488,c_491])).

cnf(c_580,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_579])).

cnf(c_587,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_580])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_286,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_434,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_289,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X0_43)
    | r1_tarski(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_431,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X2_43,X0_43) != iProver_top
    | r1_tarski(X2_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_640,plain,
    ( r1_tarski(X0_43,sK2) = iProver_top
    | r1_tarski(X0_43,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_434,c_431])).

cnf(c_796,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_640])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_287,plain,
    ( ~ r1_tarski(k1_relat_1(X0_42),X0_43)
    | ~ v1_relat_1(X0_42)
    | k7_relat_1(X0_42,X0_43) = X0_42 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_673,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_674,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_176,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_177,plain,
    ( k5_relset_1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_284,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k5_relset_1(X0_43,X0_44,sK3,X1_43) = k7_relat_1(sK3,X1_43) ),
    inference(subtyping,[status(esa)],[c_177])).

cnf(c_504,plain,
    ( k5_relset_1(sK1,sK0,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
    inference(equality_resolution,[status(thm)],[c_284])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(sK1,sK0,sK3,sK2) != X0
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_149,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_148])).

cnf(c_197,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_12,c_149])).

cnf(c_242,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_197])).

cnf(c_282,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_242])).

cnf(c_522,plain,
    ( k7_relat_1(sK3,sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_504,c_282])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_796,c_674,c_522,c_491,c_488,c_317,c_312,c_307])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.94/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.94/0.99  
% 0.94/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.94/0.99  
% 0.94/0.99  ------  iProver source info
% 0.94/0.99  
% 0.94/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.94/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.94/0.99  git: non_committed_changes: false
% 0.94/0.99  git: last_make_outside_of_git: false
% 0.94/0.99  
% 0.94/0.99  ------ 
% 0.94/0.99  
% 0.94/0.99  ------ Input Options
% 0.94/0.99  
% 0.94/0.99  --out_options                           all
% 0.94/0.99  --tptp_safe_out                         true
% 0.94/0.99  --problem_path                          ""
% 0.94/0.99  --include_path                          ""
% 0.94/0.99  --clausifier                            res/vclausify_rel
% 0.94/0.99  --clausifier_options                    --mode clausify
% 0.94/0.99  --stdin                                 false
% 0.94/0.99  --stats_out                             all
% 0.94/0.99  
% 0.94/0.99  ------ General Options
% 0.94/0.99  
% 0.94/0.99  --fof                                   false
% 0.94/0.99  --time_out_real                         305.
% 0.94/0.99  --time_out_virtual                      -1.
% 0.94/0.99  --symbol_type_check                     false
% 0.94/0.99  --clausify_out                          false
% 0.94/0.99  --sig_cnt_out                           false
% 0.94/0.99  --trig_cnt_out                          false
% 0.94/0.99  --trig_cnt_out_tolerance                1.
% 0.94/0.99  --trig_cnt_out_sk_spl                   false
% 0.94/0.99  --abstr_cl_out                          false
% 0.94/0.99  
% 0.94/0.99  ------ Global Options
% 0.94/0.99  
% 0.94/0.99  --schedule                              default
% 0.94/0.99  --add_important_lit                     false
% 0.94/0.99  --prop_solver_per_cl                    1000
% 0.94/0.99  --min_unsat_core                        false
% 0.94/0.99  --soft_assumptions                      false
% 0.94/0.99  --soft_lemma_size                       3
% 0.94/0.99  --prop_impl_unit_size                   0
% 0.94/0.99  --prop_impl_unit                        []
% 0.94/0.99  --share_sel_clauses                     true
% 0.94/0.99  --reset_solvers                         false
% 0.94/0.99  --bc_imp_inh                            [conj_cone]
% 0.94/0.99  --conj_cone_tolerance                   3.
% 0.94/0.99  --extra_neg_conj                        none
% 0.94/0.99  --large_theory_mode                     true
% 0.94/0.99  --prolific_symb_bound                   200
% 0.94/0.99  --lt_threshold                          2000
% 0.94/0.99  --clause_weak_htbl                      true
% 0.94/0.99  --gc_record_bc_elim                     false
% 0.94/0.99  
% 0.94/0.99  ------ Preprocessing Options
% 0.94/0.99  
% 0.94/0.99  --preprocessing_flag                    true
% 0.94/0.99  --time_out_prep_mult                    0.1
% 0.94/0.99  --splitting_mode                        input
% 0.94/0.99  --splitting_grd                         true
% 0.94/0.99  --splitting_cvd                         false
% 0.94/0.99  --splitting_cvd_svl                     false
% 0.94/0.99  --splitting_nvd                         32
% 0.94/0.99  --sub_typing                            true
% 0.94/0.99  --prep_gs_sim                           true
% 0.94/0.99  --prep_unflatten                        true
% 0.94/0.99  --prep_res_sim                          true
% 0.94/0.99  --prep_upred                            true
% 0.94/0.99  --prep_sem_filter                       exhaustive
% 0.94/0.99  --prep_sem_filter_out                   false
% 0.94/0.99  --pred_elim                             true
% 0.94/0.99  --res_sim_input                         true
% 0.94/0.99  --eq_ax_congr_red                       true
% 0.94/0.99  --pure_diseq_elim                       true
% 0.94/0.99  --brand_transform                       false
% 0.94/0.99  --non_eq_to_eq                          false
% 0.94/0.99  --prep_def_merge                        true
% 0.94/0.99  --prep_def_merge_prop_impl              false
% 0.94/0.99  --prep_def_merge_mbd                    true
% 0.94/0.99  --prep_def_merge_tr_red                 false
% 0.94/0.99  --prep_def_merge_tr_cl                  false
% 0.94/0.99  --smt_preprocessing                     true
% 0.94/0.99  --smt_ac_axioms                         fast
% 0.94/0.99  --preprocessed_out                      false
% 0.94/0.99  --preprocessed_stats                    false
% 0.94/0.99  
% 0.94/0.99  ------ Abstraction refinement Options
% 0.94/0.99  
% 0.94/0.99  --abstr_ref                             []
% 0.94/0.99  --abstr_ref_prep                        false
% 0.94/0.99  --abstr_ref_until_sat                   false
% 0.94/0.99  --abstr_ref_sig_restrict                funpre
% 0.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.94/0.99  --abstr_ref_under                       []
% 0.94/0.99  
% 0.94/0.99  ------ SAT Options
% 0.94/0.99  
% 0.94/0.99  --sat_mode                              false
% 0.94/0.99  --sat_fm_restart_options                ""
% 0.94/0.99  --sat_gr_def                            false
% 0.94/0.99  --sat_epr_types                         true
% 0.94/0.99  --sat_non_cyclic_types                  false
% 0.94/0.99  --sat_finite_models                     false
% 0.94/0.99  --sat_fm_lemmas                         false
% 0.94/0.99  --sat_fm_prep                           false
% 0.94/0.99  --sat_fm_uc_incr                        true
% 0.94/0.99  --sat_out_model                         small
% 0.94/0.99  --sat_out_clauses                       false
% 0.94/0.99  
% 0.94/0.99  ------ QBF Options
% 0.94/0.99  
% 0.94/0.99  --qbf_mode                              false
% 0.94/0.99  --qbf_elim_univ                         false
% 0.94/0.99  --qbf_dom_inst                          none
% 0.94/0.99  --qbf_dom_pre_inst                      false
% 0.94/0.99  --qbf_sk_in                             false
% 0.94/0.99  --qbf_pred_elim                         true
% 0.94/0.99  --qbf_split                             512
% 0.94/0.99  
% 0.94/0.99  ------ BMC1 Options
% 0.94/0.99  
% 0.94/0.99  --bmc1_incremental                      false
% 0.94/0.99  --bmc1_axioms                           reachable_all
% 0.94/0.99  --bmc1_min_bound                        0
% 0.94/0.99  --bmc1_max_bound                        -1
% 0.94/0.99  --bmc1_max_bound_default                -1
% 0.94/0.99  --bmc1_symbol_reachability              true
% 0.94/0.99  --bmc1_property_lemmas                  false
% 0.94/0.99  --bmc1_k_induction                      false
% 0.94/0.99  --bmc1_non_equiv_states                 false
% 0.94/0.99  --bmc1_deadlock                         false
% 0.94/0.99  --bmc1_ucm                              false
% 0.94/0.99  --bmc1_add_unsat_core                   none
% 0.94/0.99  --bmc1_unsat_core_children              false
% 0.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.94/0.99  --bmc1_out_stat                         full
% 0.94/0.99  --bmc1_ground_init                      false
% 0.94/0.99  --bmc1_pre_inst_next_state              false
% 0.94/0.99  --bmc1_pre_inst_state                   false
% 0.94/0.99  --bmc1_pre_inst_reach_state             false
% 0.94/0.99  --bmc1_out_unsat_core                   false
% 0.94/0.99  --bmc1_aig_witness_out                  false
% 0.94/0.99  --bmc1_verbose                          false
% 0.94/0.99  --bmc1_dump_clauses_tptp                false
% 0.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.94/0.99  --bmc1_dump_file                        -
% 0.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.94/0.99  --bmc1_ucm_extend_mode                  1
% 0.94/0.99  --bmc1_ucm_init_mode                    2
% 0.94/0.99  --bmc1_ucm_cone_mode                    none
% 0.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.94/0.99  --bmc1_ucm_relax_model                  4
% 0.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.94/0.99  --bmc1_ucm_layered_model                none
% 0.94/0.99  --bmc1_ucm_max_lemma_size               10
% 0.94/0.99  
% 0.94/0.99  ------ AIG Options
% 0.94/0.99  
% 0.94/0.99  --aig_mode                              false
% 0.94/0.99  
% 0.94/0.99  ------ Instantiation Options
% 0.94/0.99  
% 0.94/0.99  --instantiation_flag                    true
% 0.94/0.99  --inst_sos_flag                         false
% 0.94/0.99  --inst_sos_phase                        true
% 0.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.94/0.99  --inst_lit_sel_side                     num_symb
% 0.94/0.99  --inst_solver_per_active                1400
% 0.94/0.99  --inst_solver_calls_frac                1.
% 0.94/0.99  --inst_passive_queue_type               priority_queues
% 0.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.94/0.99  --inst_passive_queues_freq              [25;2]
% 0.94/0.99  --inst_dismatching                      true
% 0.94/0.99  --inst_eager_unprocessed_to_passive     true
% 0.94/0.99  --inst_prop_sim_given                   true
% 0.94/0.99  --inst_prop_sim_new                     false
% 0.94/0.99  --inst_subs_new                         false
% 0.94/0.99  --inst_eq_res_simp                      false
% 0.94/0.99  --inst_subs_given                       false
% 0.94/0.99  --inst_orphan_elimination               true
% 0.94/0.99  --inst_learning_loop_flag               true
% 0.94/0.99  --inst_learning_start                   3000
% 0.94/0.99  --inst_learning_factor                  2
% 0.94/0.99  --inst_start_prop_sim_after_learn       3
% 0.94/0.99  --inst_sel_renew                        solver
% 0.94/0.99  --inst_lit_activity_flag                true
% 0.94/0.99  --inst_restr_to_given                   false
% 0.94/0.99  --inst_activity_threshold               500
% 0.94/0.99  --inst_out_proof                        true
% 0.94/0.99  
% 0.94/0.99  ------ Resolution Options
% 0.94/0.99  
% 0.94/0.99  --resolution_flag                       true
% 0.94/0.99  --res_lit_sel                           adaptive
% 0.94/0.99  --res_lit_sel_side                      none
% 0.94/0.99  --res_ordering                          kbo
% 0.94/0.99  --res_to_prop_solver                    active
% 0.94/0.99  --res_prop_simpl_new                    false
% 0.94/0.99  --res_prop_simpl_given                  true
% 0.94/0.99  --res_passive_queue_type                priority_queues
% 0.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.94/0.99  --res_passive_queues_freq               [15;5]
% 0.94/0.99  --res_forward_subs                      full
% 0.94/0.99  --res_backward_subs                     full
% 0.94/0.99  --res_forward_subs_resolution           true
% 0.94/0.99  --res_backward_subs_resolution          true
% 0.94/0.99  --res_orphan_elimination                true
% 0.94/0.99  --res_time_limit                        2.
% 0.94/0.99  --res_out_proof                         true
% 0.94/0.99  
% 0.94/0.99  ------ Superposition Options
% 0.94/0.99  
% 0.94/0.99  --superposition_flag                    true
% 0.94/0.99  --sup_passive_queue_type                priority_queues
% 0.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.94/0.99  --demod_completeness_check              fast
% 0.94/0.99  --demod_use_ground                      true
% 0.94/0.99  --sup_to_prop_solver                    passive
% 0.94/0.99  --sup_prop_simpl_new                    true
% 0.94/0.99  --sup_prop_simpl_given                  true
% 0.94/0.99  --sup_fun_splitting                     false
% 0.94/0.99  --sup_smt_interval                      50000
% 0.94/0.99  
% 0.94/0.99  ------ Superposition Simplification Setup
% 0.94/0.99  
% 0.94/0.99  --sup_indices_passive                   []
% 0.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/0.99  --sup_full_bw                           [BwDemod]
% 0.94/0.99  --sup_immed_triv                        [TrivRules]
% 0.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/0.99  --sup_immed_bw_main                     []
% 0.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/0.99  
% 0.94/0.99  ------ Combination Options
% 0.94/0.99  
% 0.94/0.99  --comb_res_mult                         3
% 0.94/0.99  --comb_sup_mult                         2
% 0.94/0.99  --comb_inst_mult                        10
% 0.94/0.99  
% 0.94/0.99  ------ Debug Options
% 0.94/0.99  
% 0.94/0.99  --dbg_backtrace                         false
% 0.94/0.99  --dbg_dump_prop_clauses                 false
% 0.94/0.99  --dbg_dump_prop_clauses_file            -
% 0.94/0.99  --dbg_out_stat                          false
% 0.94/0.99  ------ Parsing...
% 0.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.94/0.99  
% 0.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.94/0.99  
% 0.94/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.94/0.99  
% 0.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.94/0.99  ------ Proving...
% 0.94/0.99  ------ Problem Properties 
% 0.94/0.99  
% 0.94/0.99  
% 0.94/0.99  clauses                                 8
% 0.94/0.99  conjectures                             1
% 0.94/0.99  EPR                                     2
% 0.94/0.99  Horn                                    8
% 0.94/0.99  unary                                   3
% 0.94/0.99  binary                                  1
% 0.94/0.99  lits                                    17
% 0.94/0.99  lits eq                                 6
% 0.94/0.99  fd_pure                                 0
% 0.94/0.99  fd_pseudo                               0
% 0.94/0.99  fd_cond                                 0
% 0.94/0.99  fd_pseudo_cond                          0
% 0.94/0.99  AC symbols                              0
% 0.94/0.99  
% 0.94/0.99  ------ Schedule dynamic 5 is on 
% 0.94/0.99  
% 0.94/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.94/0.99  
% 0.94/0.99  
% 0.94/0.99  ------ 
% 0.94/0.99  Current options:
% 0.94/0.99  ------ 
% 0.94/0.99  
% 0.94/0.99  ------ Input Options
% 0.94/0.99  
% 0.94/0.99  --out_options                           all
% 0.94/0.99  --tptp_safe_out                         true
% 0.94/0.99  --problem_path                          ""
% 0.94/0.99  --include_path                          ""
% 0.94/0.99  --clausifier                            res/vclausify_rel
% 0.94/0.99  --clausifier_options                    --mode clausify
% 0.94/0.99  --stdin                                 false
% 0.94/0.99  --stats_out                             all
% 0.94/0.99  
% 0.94/0.99  ------ General Options
% 0.94/0.99  
% 0.94/0.99  --fof                                   false
% 0.94/0.99  --time_out_real                         305.
% 0.94/0.99  --time_out_virtual                      -1.
% 0.94/0.99  --symbol_type_check                     false
% 0.94/0.99  --clausify_out                          false
% 0.94/0.99  --sig_cnt_out                           false
% 0.94/0.99  --trig_cnt_out                          false
% 0.94/0.99  --trig_cnt_out_tolerance                1.
% 0.94/0.99  --trig_cnt_out_sk_spl                   false
% 0.94/0.99  --abstr_cl_out                          false
% 0.94/0.99  
% 0.94/0.99  ------ Global Options
% 0.94/0.99  
% 0.94/0.99  --schedule                              default
% 0.94/0.99  --add_important_lit                     false
% 0.94/0.99  --prop_solver_per_cl                    1000
% 0.94/0.99  --min_unsat_core                        false
% 0.94/0.99  --soft_assumptions                      false
% 0.94/0.99  --soft_lemma_size                       3
% 0.94/0.99  --prop_impl_unit_size                   0
% 0.94/0.99  --prop_impl_unit                        []
% 0.94/0.99  --share_sel_clauses                     true
% 0.94/0.99  --reset_solvers                         false
% 0.94/0.99  --bc_imp_inh                            [conj_cone]
% 0.94/0.99  --conj_cone_tolerance                   3.
% 0.94/0.99  --extra_neg_conj                        none
% 0.94/0.99  --large_theory_mode                     true
% 0.94/0.99  --prolific_symb_bound                   200
% 0.94/0.99  --lt_threshold                          2000
% 0.94/0.99  --clause_weak_htbl                      true
% 0.94/0.99  --gc_record_bc_elim                     false
% 0.94/0.99  
% 0.94/0.99  ------ Preprocessing Options
% 0.94/0.99  
% 0.94/0.99  --preprocessing_flag                    true
% 0.94/0.99  --time_out_prep_mult                    0.1
% 0.94/0.99  --splitting_mode                        input
% 0.94/0.99  --splitting_grd                         true
% 0.94/0.99  --splitting_cvd                         false
% 0.94/0.99  --splitting_cvd_svl                     false
% 0.94/0.99  --splitting_nvd                         32
% 0.94/0.99  --sub_typing                            true
% 0.94/0.99  --prep_gs_sim                           true
% 0.94/0.99  --prep_unflatten                        true
% 0.94/0.99  --prep_res_sim                          true
% 0.94/0.99  --prep_upred                            true
% 0.94/0.99  --prep_sem_filter                       exhaustive
% 0.94/0.99  --prep_sem_filter_out                   false
% 0.94/0.99  --pred_elim                             true
% 0.94/0.99  --res_sim_input                         true
% 0.94/0.99  --eq_ax_congr_red                       true
% 0.94/0.99  --pure_diseq_elim                       true
% 0.94/0.99  --brand_transform                       false
% 0.94/0.99  --non_eq_to_eq                          false
% 0.94/0.99  --prep_def_merge                        true
% 0.94/0.99  --prep_def_merge_prop_impl              false
% 0.94/0.99  --prep_def_merge_mbd                    true
% 0.94/0.99  --prep_def_merge_tr_red                 false
% 0.94/0.99  --prep_def_merge_tr_cl                  false
% 0.94/0.99  --smt_preprocessing                     true
% 0.94/0.99  --smt_ac_axioms                         fast
% 0.94/0.99  --preprocessed_out                      false
% 0.94/0.99  --preprocessed_stats                    false
% 0.94/0.99  
% 0.94/0.99  ------ Abstraction refinement Options
% 0.94/0.99  
% 0.94/0.99  --abstr_ref                             []
% 0.94/0.99  --abstr_ref_prep                        false
% 0.94/0.99  --abstr_ref_until_sat                   false
% 0.94/0.99  --abstr_ref_sig_restrict                funpre
% 0.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.94/0.99  --abstr_ref_under                       []
% 0.94/0.99  
% 0.94/0.99  ------ SAT Options
% 0.94/0.99  
% 0.94/0.99  --sat_mode                              false
% 0.94/0.99  --sat_fm_restart_options                ""
% 0.94/0.99  --sat_gr_def                            false
% 0.94/0.99  --sat_epr_types                         true
% 0.94/0.99  --sat_non_cyclic_types                  false
% 0.94/0.99  --sat_finite_models                     false
% 0.94/0.99  --sat_fm_lemmas                         false
% 0.94/0.99  --sat_fm_prep                           false
% 0.94/0.99  --sat_fm_uc_incr                        true
% 0.94/0.99  --sat_out_model                         small
% 0.94/0.99  --sat_out_clauses                       false
% 0.94/0.99  
% 0.94/0.99  ------ QBF Options
% 0.94/0.99  
% 0.94/0.99  --qbf_mode                              false
% 0.94/0.99  --qbf_elim_univ                         false
% 0.94/0.99  --qbf_dom_inst                          none
% 0.94/0.99  --qbf_dom_pre_inst                      false
% 0.94/0.99  --qbf_sk_in                             false
% 0.94/0.99  --qbf_pred_elim                         true
% 0.94/0.99  --qbf_split                             512
% 0.94/0.99  
% 0.94/0.99  ------ BMC1 Options
% 0.94/0.99  
% 0.94/0.99  --bmc1_incremental                      false
% 0.94/0.99  --bmc1_axioms                           reachable_all
% 0.94/0.99  --bmc1_min_bound                        0
% 0.94/0.99  --bmc1_max_bound                        -1
% 0.94/0.99  --bmc1_max_bound_default                -1
% 0.94/0.99  --bmc1_symbol_reachability              true
% 0.94/0.99  --bmc1_property_lemmas                  false
% 0.94/0.99  --bmc1_k_induction                      false
% 0.94/0.99  --bmc1_non_equiv_states                 false
% 0.94/0.99  --bmc1_deadlock                         false
% 0.94/0.99  --bmc1_ucm                              false
% 0.94/0.99  --bmc1_add_unsat_core                   none
% 0.94/0.99  --bmc1_unsat_core_children              false
% 0.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.94/0.99  --bmc1_out_stat                         full
% 0.94/0.99  --bmc1_ground_init                      false
% 0.94/0.99  --bmc1_pre_inst_next_state              false
% 0.94/0.99  --bmc1_pre_inst_state                   false
% 0.94/0.99  --bmc1_pre_inst_reach_state             false
% 0.94/0.99  --bmc1_out_unsat_core                   false
% 0.94/0.99  --bmc1_aig_witness_out                  false
% 0.94/0.99  --bmc1_verbose                          false
% 0.94/0.99  --bmc1_dump_clauses_tptp                false
% 0.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.94/0.99  --bmc1_dump_file                        -
% 0.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.94/0.99  --bmc1_ucm_extend_mode                  1
% 0.94/0.99  --bmc1_ucm_init_mode                    2
% 0.94/0.99  --bmc1_ucm_cone_mode                    none
% 0.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.94/0.99  --bmc1_ucm_relax_model                  4
% 0.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.94/0.99  --bmc1_ucm_layered_model                none
% 0.94/0.99  --bmc1_ucm_max_lemma_size               10
% 0.94/0.99  
% 0.94/0.99  ------ AIG Options
% 0.94/0.99  
% 0.94/0.99  --aig_mode                              false
% 0.94/0.99  
% 0.94/0.99  ------ Instantiation Options
% 0.94/0.99  
% 0.94/0.99  --instantiation_flag                    true
% 0.94/0.99  --inst_sos_flag                         false
% 0.94/0.99  --inst_sos_phase                        true
% 0.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.94/0.99  --inst_lit_sel_side                     none
% 0.94/0.99  --inst_solver_per_active                1400
% 0.94/0.99  --inst_solver_calls_frac                1.
% 0.94/0.99  --inst_passive_queue_type               priority_queues
% 0.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.94/0.99  --inst_passive_queues_freq              [25;2]
% 0.94/0.99  --inst_dismatching                      true
% 0.94/0.99  --inst_eager_unprocessed_to_passive     true
% 0.94/0.99  --inst_prop_sim_given                   true
% 0.94/0.99  --inst_prop_sim_new                     false
% 0.94/0.99  --inst_subs_new                         false
% 0.94/0.99  --inst_eq_res_simp                      false
% 0.94/0.99  --inst_subs_given                       false
% 0.94/0.99  --inst_orphan_elimination               true
% 0.94/0.99  --inst_learning_loop_flag               true
% 0.94/0.99  --inst_learning_start                   3000
% 0.94/0.99  --inst_learning_factor                  2
% 0.94/0.99  --inst_start_prop_sim_after_learn       3
% 0.94/0.99  --inst_sel_renew                        solver
% 0.94/0.99  --inst_lit_activity_flag                true
% 0.94/0.99  --inst_restr_to_given                   false
% 0.94/0.99  --inst_activity_threshold               500
% 0.94/0.99  --inst_out_proof                        true
% 0.94/0.99  
% 0.94/0.99  ------ Resolution Options
% 0.94/0.99  
% 0.94/0.99  --resolution_flag                       false
% 0.94/0.99  --res_lit_sel                           adaptive
% 0.94/0.99  --res_lit_sel_side                      none
% 0.94/0.99  --res_ordering                          kbo
% 0.94/0.99  --res_to_prop_solver                    active
% 0.94/0.99  --res_prop_simpl_new                    false
% 0.94/0.99  --res_prop_simpl_given                  true
% 0.94/0.99  --res_passive_queue_type                priority_queues
% 0.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.94/0.99  --res_passive_queues_freq               [15;5]
% 0.94/0.99  --res_forward_subs                      full
% 0.94/0.99  --res_backward_subs                     full
% 0.94/0.99  --res_forward_subs_resolution           true
% 0.94/0.99  --res_backward_subs_resolution          true
% 0.94/0.99  --res_orphan_elimination                true
% 0.94/0.99  --res_time_limit                        2.
% 0.94/0.99  --res_out_proof                         true
% 0.94/0.99  
% 0.94/0.99  ------ Superposition Options
% 0.94/0.99  
% 0.94/0.99  --superposition_flag                    true
% 0.94/0.99  --sup_passive_queue_type                priority_queues
% 0.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.94/0.99  --demod_completeness_check              fast
% 0.94/0.99  --demod_use_ground                      true
% 0.94/0.99  --sup_to_prop_solver                    passive
% 0.94/0.99  --sup_prop_simpl_new                    true
% 0.94/0.99  --sup_prop_simpl_given                  true
% 0.94/0.99  --sup_fun_splitting                     false
% 0.94/0.99  --sup_smt_interval                      50000
% 0.94/0.99  
% 0.94/0.99  ------ Superposition Simplification Setup
% 0.94/0.99  
% 0.94/0.99  --sup_indices_passive                   []
% 0.94/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/0.99  --sup_full_bw                           [BwDemod]
% 0.94/0.99  --sup_immed_triv                        [TrivRules]
% 0.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/0.99  --sup_immed_bw_main                     []
% 0.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.94/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.94/0.99  
% 0.94/0.99  ------ Combination Options
% 0.94/0.99  
% 0.94/0.99  --comb_res_mult                         3
% 0.94/0.99  --comb_sup_mult                         2
% 0.94/0.99  --comb_inst_mult                        10
% 0.94/0.99  
% 0.94/0.99  ------ Debug Options
% 0.94/0.99  
% 0.94/0.99  --dbg_backtrace                         false
% 0.94/0.99  --dbg_dump_prop_clauses                 false
% 0.94/0.99  --dbg_dump_prop_clauses_file            -
% 0.94/0.99  --dbg_out_stat                          false
% 0.94/0.99  
% 0.94/0.99  
% 0.94/0.99  
% 0.94/0.99  
% 0.94/0.99  ------ Proving...
% 0.94/0.99  
% 0.94/0.99  
% 0.94/0.99  % SZS status Theorem for theBenchmark.p
% 0.94/0.99  
% 0.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.94/0.99  
% 0.94/0.99  fof(f3,axiom,(
% 0.94/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f15,plain,(
% 0.94/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.94/0.99    inference(ennf_transformation,[],[f3])).
% 0.94/0.99  
% 0.94/0.99  fof(f24,plain,(
% 0.94/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.94/0.99    inference(nnf_transformation,[],[f15])).
% 0.94/0.99  
% 0.94/0.99  fof(f30,plain,(
% 0.94/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.94/0.99    inference(cnf_transformation,[],[f24])).
% 0.94/0.99  
% 0.94/0.99  fof(f6,axiom,(
% 0.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f11,plain,(
% 0.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.94/0.99    inference(pure_predicate_removal,[],[f6])).
% 0.94/0.99  
% 0.94/0.99  fof(f18,plain,(
% 0.94/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.94/0.99    inference(ennf_transformation,[],[f11])).
% 0.94/0.99  
% 0.94/0.99  fof(f34,plain,(
% 0.94/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.94/0.99    inference(cnf_transformation,[],[f18])).
% 0.94/0.99  
% 0.94/0.99  fof(f9,conjecture,(
% 0.94/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f10,negated_conjecture,(
% 0.94/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.94/0.99    inference(negated_conjecture,[],[f9])).
% 0.94/0.99  
% 0.94/0.99  fof(f22,plain,(
% 0.94/0.99    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.94/0.99    inference(ennf_transformation,[],[f10])).
% 0.94/0.99  
% 0.94/0.99  fof(f23,plain,(
% 0.94/0.99    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.94/0.99    inference(flattening,[],[f22])).
% 0.94/0.99  
% 0.94/0.99  fof(f26,plain,(
% 0.94/0.99    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.94/0.99    introduced(choice_axiom,[])).
% 0.94/0.99  
% 0.94/0.99  fof(f27,plain,(
% 0.94/0.99    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f26])).
% 0.94/0.99  
% 0.94/0.99  fof(f38,plain,(
% 0.94/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.94/0.99    inference(cnf_transformation,[],[f27])).
% 0.94/0.99  
% 0.94/0.99  fof(f4,axiom,(
% 0.94/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f32,plain,(
% 0.94/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.94/0.99    inference(cnf_transformation,[],[f4])).
% 0.94/0.99  
% 0.94/0.99  fof(f2,axiom,(
% 0.94/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f14,plain,(
% 0.94/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.94/0.99    inference(ennf_transformation,[],[f2])).
% 0.94/0.99  
% 0.94/0.99  fof(f29,plain,(
% 0.94/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.94/0.99    inference(cnf_transformation,[],[f14])).
% 0.94/0.99  
% 0.94/0.99  fof(f39,plain,(
% 0.94/0.99    r1_tarski(sK1,sK2)),
% 0.94/0.99    inference(cnf_transformation,[],[f27])).
% 0.94/0.99  
% 0.94/0.99  fof(f1,axiom,(
% 0.94/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f12,plain,(
% 0.94/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.94/0.99    inference(ennf_transformation,[],[f1])).
% 0.94/0.99  
% 0.94/0.99  fof(f13,plain,(
% 0.94/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.94/0.99    inference(flattening,[],[f12])).
% 0.94/0.99  
% 0.94/0.99  fof(f28,plain,(
% 0.94/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.94/0.99    inference(cnf_transformation,[],[f13])).
% 0.94/0.99  
% 0.94/0.99  fof(f5,axiom,(
% 0.94/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f16,plain,(
% 0.94/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.94/0.99    inference(ennf_transformation,[],[f5])).
% 0.94/0.99  
% 0.94/0.99  fof(f17,plain,(
% 0.94/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.94/0.99    inference(flattening,[],[f16])).
% 0.94/0.99  
% 0.94/0.99  fof(f33,plain,(
% 0.94/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.94/0.99    inference(cnf_transformation,[],[f17])).
% 0.94/0.99  
% 0.94/0.99  fof(f7,axiom,(
% 0.94/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f19,plain,(
% 0.94/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.94/0.99    inference(ennf_transformation,[],[f7])).
% 0.94/0.99  
% 0.94/0.99  fof(f35,plain,(
% 0.94/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.94/0.99    inference(cnf_transformation,[],[f19])).
% 0.94/0.99  
% 0.94/0.99  fof(f8,axiom,(
% 0.94/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.94/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.94/0.99  
% 0.94/0.99  fof(f20,plain,(
% 0.94/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.94/0.99    inference(ennf_transformation,[],[f8])).
% 0.94/0.99  
% 0.94/0.99  fof(f21,plain,(
% 0.94/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.94/0.99    inference(flattening,[],[f20])).
% 0.94/0.99  
% 0.94/0.99  fof(f25,plain,(
% 0.94/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.94/0.99    inference(nnf_transformation,[],[f21])).
% 0.94/0.99  
% 0.94/0.99  fof(f37,plain,(
% 0.94/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.94/0.99    inference(cnf_transformation,[],[f25])).
% 0.94/0.99  
% 0.94/0.99  fof(f41,plain,(
% 0.94/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.94/0.99    inference(equality_resolution,[],[f37])).
% 0.94/0.99  
% 0.94/0.99  fof(f40,plain,(
% 0.94/0.99    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.94/0.99    inference(cnf_transformation,[],[f27])).
% 0.94/0.99  
% 0.94/0.99  cnf(c_3,plain,
% 0.94/0.99      ( ~ v4_relat_1(X0,X1)
% 0.94/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 0.94/0.99      | ~ v1_relat_1(X0) ),
% 0.94/0.99      inference(cnf_transformation,[],[f30]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_6,plain,
% 0.94/0.99      ( v4_relat_1(X0,X1)
% 0.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.94/0.99      inference(cnf_transformation,[],[f34]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_12,negated_conjecture,
% 0.94/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 0.94/0.99      inference(cnf_transformation,[],[f38]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_185,plain,
% 0.94/0.99      ( v4_relat_1(X0,X1)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | sK3 != X0 ),
% 0.94/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_186,plain,
% 0.94/0.99      ( v4_relat_1(sK3,X0)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.94/0.99      inference(unflattening,[status(thm)],[c_185]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_216,plain,
% 0.94/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 0.94/0.99      | ~ v1_relat_1(X0)
% 0.94/0.99      | X2 != X1
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | sK3 != X0 ),
% 0.94/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_186]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_217,plain,
% 0.94/0.99      ( r1_tarski(k1_relat_1(sK3),X0)
% 0.94/0.99      | ~ v1_relat_1(sK3)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.94/0.99      inference(unflattening,[status(thm)],[c_216]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_283,plain,
% 0.94/0.99      ( r1_tarski(k1_relat_1(sK3),X0_43)
% 0.94/0.99      | ~ v1_relat_1(sK3)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.94/0.99      inference(subtyping,[status(esa)],[c_217]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_436,plain,
% 0.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
% 0.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 0.94/0.99      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_300,plain,
% 0.94/0.99      ( X0_43 != X1_43
% 0.94/0.99      | k2_zfmisc_1(X0_43,X0_44) = k2_zfmisc_1(X1_43,X0_44) ),
% 0.94/0.99      theory(equality) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_307,plain,
% 0.94/0.99      ( sK1 != sK1 | k2_zfmisc_1(sK1,sK0) = k2_zfmisc_1(sK1,sK0) ),
% 0.94/0.99      inference(instantiation,[status(thm)],[c_300]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_292,plain,( X0_43 = X0_43 ),theory(equality) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_312,plain,
% 0.94/0.99      ( sK1 = sK1 ),
% 0.94/0.99      inference(instantiation,[status(thm)],[c_292]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_4,plain,
% 0.94/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 0.94/0.99      inference(cnf_transformation,[],[f32]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_288,plain,
% 0.94/0.99      ( v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) ),
% 0.94/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_315,plain,
% 0.94/0.99      ( v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) = iProver_top ),
% 0.94/0.99      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_317,plain,
% 0.94/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 0.94/0.99      inference(instantiation,[status(thm)],[c_315]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_324,plain,
% 0.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
% 0.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 0.94/0.99      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_1,plain,
% 0.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.94/0.99      | ~ v1_relat_1(X1)
% 0.94/0.99      | v1_relat_1(X0) ),
% 0.94/0.99      inference(cnf_transformation,[],[f29]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_161,plain,
% 0.94/0.99      ( ~ v1_relat_1(X0)
% 0.94/0.99      | v1_relat_1(X1)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0)
% 0.94/0.99      | sK3 != X1 ),
% 0.94/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_12]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_162,plain,
% 0.94/0.99      ( ~ v1_relat_1(X0)
% 0.94/0.99      | v1_relat_1(sK3)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0) ),
% 0.94/0.99      inference(unflattening,[status(thm)],[c_161]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_285,plain,
% 0.94/0.99      ( ~ v1_relat_1(X0_42)
% 0.94/0.99      | v1_relat_1(sK3)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(X0_42) ),
% 0.94/0.99      inference(subtyping,[status(esa)],[c_162]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_485,plain,
% 0.94/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0_43,X0_44))
% 0.94/0.99      | v1_relat_1(sK3)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) ),
% 0.94/0.99      inference(instantiation,[status(thm)],[c_285]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_486,plain,
% 0.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44))
% 0.94/0.99      | v1_relat_1(k2_zfmisc_1(X0_43,X0_44)) != iProver_top
% 0.94/0.99      | v1_relat_1(sK3) = iProver_top ),
% 0.94/0.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_488,plain,
% 0.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 0.94/0.99      | v1_relat_1(sK3) = iProver_top ),
% 0.94/0.99      inference(instantiation,[status(thm)],[c_486]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_298,plain,
% 0.94/0.99      ( k1_zfmisc_1(X0_42) = k1_zfmisc_1(X1_42) | X0_42 != X1_42 ),
% 0.94/0.99      theory(equality) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_490,plain,
% 0.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | k2_zfmisc_1(X0_43,X0_44) != k2_zfmisc_1(sK1,sK0) ),
% 0.94/0.99      inference(instantiation,[status(thm)],[c_298]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_491,plain,
% 0.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | k2_zfmisc_1(sK1,sK0) != k2_zfmisc_1(sK1,sK0) ),
% 0.94/0.99      inference(instantiation,[status(thm)],[c_490]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_579,plain,
% 0.94/0.99      ( r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.94/0.99      inference(global_propositional_subsumption,
% 0.94/0.99                [status(thm)],
% 0.94/0.99                [c_436,c_307,c_312,c_317,c_324,c_488,c_491]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_580,plain,
% 0.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top ),
% 0.94/0.99      inference(renaming,[status(thm)],[c_579]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_587,plain,
% 0.94/0.99      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 0.94/0.99      inference(equality_resolution,[status(thm)],[c_580]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_11,negated_conjecture,
% 0.94/0.99      ( r1_tarski(sK1,sK2) ),
% 0.94/0.99      inference(cnf_transformation,[],[f39]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_286,negated_conjecture,
% 0.94/0.99      ( r1_tarski(sK1,sK2) ),
% 0.94/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_434,plain,
% 0.94/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 0.94/0.99      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_0,plain,
% 0.94/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 0.94/0.99      inference(cnf_transformation,[],[f28]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_289,plain,
% 0.94/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 0.94/0.99      | ~ r1_tarski(X2_43,X0_43)
% 0.94/0.99      | r1_tarski(X2_43,X1_43) ),
% 0.94/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_431,plain,
% 0.94/0.99      ( r1_tarski(X0_43,X1_43) != iProver_top
% 0.94/0.99      | r1_tarski(X2_43,X0_43) != iProver_top
% 0.94/0.99      | r1_tarski(X2_43,X1_43) = iProver_top ),
% 0.94/0.99      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_640,plain,
% 0.94/0.99      ( r1_tarski(X0_43,sK2) = iProver_top
% 0.94/0.99      | r1_tarski(X0_43,sK1) != iProver_top ),
% 0.94/0.99      inference(superposition,[status(thm)],[c_434,c_431]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_796,plain,
% 0.94/0.99      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 0.94/0.99      inference(superposition,[status(thm)],[c_587,c_640]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_5,plain,
% 0.94/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 0.94/0.99      | ~ v1_relat_1(X0)
% 0.94/0.99      | k7_relat_1(X0,X1) = X0 ),
% 0.94/0.99      inference(cnf_transformation,[],[f33]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_287,plain,
% 0.94/0.99      ( ~ r1_tarski(k1_relat_1(X0_42),X0_43)
% 0.94/0.99      | ~ v1_relat_1(X0_42)
% 0.94/0.99      | k7_relat_1(X0_42,X0_43) = X0_42 ),
% 0.94/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_673,plain,
% 0.94/0.99      ( ~ r1_tarski(k1_relat_1(sK3),sK2)
% 0.94/0.99      | ~ v1_relat_1(sK3)
% 0.94/0.99      | k7_relat_1(sK3,sK2) = sK3 ),
% 0.94/0.99      inference(instantiation,[status(thm)],[c_287]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_674,plain,
% 0.94/0.99      ( k7_relat_1(sK3,sK2) = sK3
% 0.94/0.99      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 0.94/0.99      | v1_relat_1(sK3) != iProver_top ),
% 0.94/0.99      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_7,plain,
% 0.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.94/0.99      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 0.94/0.99      inference(cnf_transformation,[],[f35]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_176,plain,
% 0.94/0.99      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | sK3 != X2 ),
% 0.94/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_177,plain,
% 0.94/0.99      ( k5_relset_1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.94/0.99      inference(unflattening,[status(thm)],[c_176]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_284,plain,
% 0.94/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.94/0.99      | k5_relset_1(X0_43,X0_44,sK3,X1_43) = k7_relat_1(sK3,X1_43) ),
% 0.94/0.99      inference(subtyping,[status(esa)],[c_177]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_504,plain,
% 0.94/0.99      ( k5_relset_1(sK1,sK0,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
% 0.94/0.99      inference(equality_resolution,[status(thm)],[c_284]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_8,plain,
% 0.94/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 0.94/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.94/0.99      inference(cnf_transformation,[],[f41]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_10,negated_conjecture,
% 0.94/0.99      ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
% 0.94/0.99      inference(cnf_transformation,[],[f40]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_148,plain,
% 0.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.94/0.99      | k5_relset_1(sK1,sK0,sK3,sK2) != X0
% 0.94/0.99      | sK3 != X0
% 0.94/0.99      | sK0 != X2
% 0.94/0.99      | sK1 != X1 ),
% 0.94/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_10]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_149,plain,
% 0.94/0.99      ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.94/0.99      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 0.94/0.99      inference(unflattening,[status(thm)],[c_148]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_197,plain,
% 0.94/0.99      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3
% 0.94/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.94/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_149]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_242,plain,
% 0.94/0.99      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
% 0.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_197]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_282,plain,
% 0.94/0.99      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
% 0.94/0.99      inference(subtyping,[status(esa)],[c_242]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(c_522,plain,
% 0.94/0.99      ( k7_relat_1(sK3,sK2) != sK3 ),
% 0.94/0.99      inference(demodulation,[status(thm)],[c_504,c_282]) ).
% 0.94/0.99  
% 0.94/0.99  cnf(contradiction,plain,
% 0.94/0.99      ( $false ),
% 0.94/0.99      inference(minisat,
% 0.94/0.99                [status(thm)],
% 0.94/0.99                [c_796,c_674,c_522,c_491,c_488,c_317,c_312,c_307]) ).
% 0.94/0.99  
% 0.94/0.99  
% 0.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.94/0.99  
% 0.94/0.99  ------                               Statistics
% 0.94/0.99  
% 0.94/0.99  ------ General
% 0.94/0.99  
% 0.94/0.99  abstr_ref_over_cycles:                  0
% 0.94/0.99  abstr_ref_under_cycles:                 0
% 0.94/0.99  gc_basic_clause_elim:                   0
% 0.94/0.99  forced_gc_time:                         0
% 0.94/0.99  parsing_time:                           0.009
% 0.94/0.99  unif_index_cands_time:                  0.
% 0.94/0.99  unif_index_add_time:                    0.
% 0.94/0.99  orderings_time:                         0.
% 0.94/0.99  out_proof_time:                         0.01
% 0.94/0.99  total_time:                             0.062
% 0.94/0.99  num_of_symbols:                         46
% 0.94/0.99  num_of_terms:                           987
% 0.94/0.99  
% 0.94/0.99  ------ Preprocessing
% 0.94/0.99  
% 0.94/0.99  num_of_splits:                          0
% 0.94/0.99  num_of_split_atoms:                     0
% 0.94/0.99  num_of_reused_defs:                     0
% 0.94/0.99  num_eq_ax_congr_red:                    9
% 0.94/0.99  num_of_sem_filtered_clauses:            1
% 0.94/0.99  num_of_subtypes:                        4
% 0.94/0.99  monotx_restored_types:                  0
% 0.94/0.99  sat_num_of_epr_types:                   0
% 0.94/0.99  sat_num_of_non_cyclic_types:            0
% 0.94/0.99  sat_guarded_non_collapsed_types:        1
% 0.94/0.99  num_pure_diseq_elim:                    0
% 0.94/0.99  simp_replaced_by:                       0
% 0.94/0.99  res_preprocessed:                       62
% 0.94/0.99  prep_upred:                             0
% 0.94/0.99  prep_unflattend:                        12
% 0.94/0.99  smt_new_axioms:                         0
% 0.94/0.99  pred_elim_cands:                        2
% 0.94/0.99  pred_elim:                              3
% 0.94/0.99  pred_elim_cl:                           5
% 0.94/0.99  pred_elim_cycles:                       5
% 0.94/0.99  merged_defs:                            0
% 0.94/0.99  merged_defs_ncl:                        0
% 0.94/0.99  bin_hyper_res:                          0
% 0.94/0.99  prep_cycles:                            4
% 0.94/0.99  pred_elim_time:                         0.002
% 0.94/0.99  splitting_time:                         0.
% 0.94/0.99  sem_filter_time:                        0.
% 0.94/0.99  monotx_time:                            0.
% 0.94/0.99  subtype_inf_time:                       0.
% 0.94/0.99  
% 0.94/0.99  ------ Problem properties
% 0.94/0.99  
% 0.94/0.99  clauses:                                8
% 0.94/0.99  conjectures:                            1
% 0.94/0.99  epr:                                    2
% 0.94/0.99  horn:                                   8
% 0.94/0.99  ground:                                 2
% 0.94/0.99  unary:                                  3
% 0.94/0.99  binary:                                 1
% 0.94/0.99  lits:                                   17
% 0.94/0.99  lits_eq:                                6
% 0.94/0.99  fd_pure:                                0
% 0.94/0.99  fd_pseudo:                              0
% 0.94/0.99  fd_cond:                                0
% 0.94/0.99  fd_pseudo_cond:                         0
% 0.94/0.99  ac_symbols:                             0
% 0.94/0.99  
% 0.94/0.99  ------ Propositional Solver
% 0.94/0.99  
% 0.94/0.99  prop_solver_calls:                      26
% 0.94/0.99  prop_fast_solver_calls:                 316
% 0.94/0.99  smt_solver_calls:                       0
% 0.94/0.99  smt_fast_solver_calls:                  0
% 0.94/0.99  prop_num_of_clauses:                    255
% 0.94/0.99  prop_preprocess_simplified:             1714
% 0.94/0.99  prop_fo_subsumed:                       4
% 0.94/0.99  prop_solver_time:                       0.
% 0.94/0.99  smt_solver_time:                        0.
% 0.94/0.99  smt_fast_solver_time:                   0.
% 0.94/0.99  prop_fast_solver_time:                  0.
% 0.94/0.99  prop_unsat_core_time:                   0.
% 0.94/0.99  
% 0.94/0.99  ------ QBF
% 0.94/0.99  
% 0.94/0.99  qbf_q_res:                              0
% 0.94/0.99  qbf_num_tautologies:                    0
% 0.94/0.99  qbf_prep_cycles:                        0
% 0.94/0.99  
% 0.94/0.99  ------ BMC1
% 0.94/0.99  
% 0.94/0.99  bmc1_current_bound:                     -1
% 0.94/0.99  bmc1_last_solved_bound:                 -1
% 0.94/0.99  bmc1_unsat_core_size:                   -1
% 0.94/0.99  bmc1_unsat_core_parents_size:           -1
% 0.94/0.99  bmc1_merge_next_fun:                    0
% 0.94/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.94/0.99  
% 0.94/0.99  ------ Instantiation
% 0.94/0.99  
% 0.94/0.99  inst_num_of_clauses:                    92
% 0.94/0.99  inst_num_in_passive:                    25
% 0.94/0.99  inst_num_in_active:                     63
% 0.94/0.99  inst_num_in_unprocessed:                4
% 0.94/0.99  inst_num_of_loops:                      70
% 0.94/0.99  inst_num_of_learning_restarts:          0
% 0.94/0.99  inst_num_moves_active_passive:          5
% 0.94/0.99  inst_lit_activity:                      0
% 0.94/0.99  inst_lit_activity_moves:                0
% 0.94/0.99  inst_num_tautologies:                   0
% 0.94/0.99  inst_num_prop_implied:                  0
% 0.94/0.99  inst_num_existing_simplified:           0
% 0.94/0.99  inst_num_eq_res_simplified:             0
% 0.94/0.99  inst_num_child_elim:                    0
% 0.94/0.99  inst_num_of_dismatching_blockings:      11
% 0.94/0.99  inst_num_of_non_proper_insts:           52
% 0.94/0.99  inst_num_of_duplicates:                 0
% 0.94/0.99  inst_inst_num_from_inst_to_res:         0
% 0.94/0.99  inst_dismatching_checking_time:         0.
% 0.94/0.99  
% 0.94/0.99  ------ Resolution
% 0.94/0.99  
% 0.94/0.99  res_num_of_clauses:                     0
% 0.94/0.99  res_num_in_passive:                     0
% 0.94/0.99  res_num_in_active:                      0
% 0.94/0.99  res_num_of_loops:                       66
% 0.94/0.99  res_forward_subset_subsumed:            6
% 0.94/0.99  res_backward_subset_subsumed:           0
% 0.94/0.99  res_forward_subsumed:                   0
% 0.94/0.99  res_backward_subsumed:                  0
% 0.94/0.99  res_forward_subsumption_resolution:     0
% 0.94/0.99  res_backward_subsumption_resolution:    0
% 0.94/0.99  res_clause_to_clause_subsumption:       12
% 0.94/0.99  res_orphan_elimination:                 0
% 0.94/0.99  res_tautology_del:                      10
% 0.94/0.99  res_num_eq_res_simplified:              1
% 0.94/0.99  res_num_sel_changes:                    0
% 0.94/0.99  res_moves_from_active_to_pass:          0
% 0.94/0.99  
% 0.94/0.99  ------ Superposition
% 0.94/0.99  
% 0.94/0.99  sup_time_total:                         0.
% 0.94/0.99  sup_time_generating:                    0.
% 0.94/0.99  sup_time_sim_full:                      0.
% 0.94/0.99  sup_time_sim_immed:                     0.
% 0.94/0.99  
% 0.94/0.99  sup_num_of_clauses:                     14
% 0.94/0.99  sup_num_in_active:                      12
% 0.94/0.99  sup_num_in_passive:                     2
% 0.94/0.99  sup_num_of_loops:                       12
% 0.94/0.99  sup_fw_superposition:                   4
% 0.94/0.99  sup_bw_superposition:                   0
% 0.94/0.99  sup_immediate_simplified:               0
% 0.94/0.99  sup_given_eliminated:                   0
% 0.94/0.99  comparisons_done:                       0
% 0.94/0.99  comparisons_avoided:                    0
% 0.94/0.99  
% 0.94/0.99  ------ Simplifications
% 0.94/0.99  
% 0.94/0.99  
% 0.94/0.99  sim_fw_subset_subsumed:                 0
% 0.94/0.99  sim_bw_subset_subsumed:                 0
% 0.94/0.99  sim_fw_subsumed:                        0
% 0.94/0.99  sim_bw_subsumed:                        0
% 0.94/0.99  sim_fw_subsumption_res:                 0
% 0.94/0.99  sim_bw_subsumption_res:                 0
% 0.94/0.99  sim_tautology_del:                      0
% 0.94/0.99  sim_eq_tautology_del:                   0
% 0.94/0.99  sim_eq_res_simp:                        0
% 0.94/0.99  sim_fw_demodulated:                     0
% 0.94/0.99  sim_bw_demodulated:                     1
% 0.94/0.99  sim_light_normalised:                   0
% 0.94/0.99  sim_joinable_taut:                      0
% 0.94/0.99  sim_joinable_simp:                      0
% 0.94/0.99  sim_ac_normalised:                      0
% 0.94/0.99  sim_smt_subsumption:                    0
% 0.94/0.99  
%------------------------------------------------------------------------------
