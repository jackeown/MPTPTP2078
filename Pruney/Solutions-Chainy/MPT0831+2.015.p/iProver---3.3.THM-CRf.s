%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:38 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 285 expanded)
%              Number of clauses        :   64 ( 123 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   19
%              Number of atoms          :  242 ( 724 expanded)
%              Number of equality atoms :   97 ( 177 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f24])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f40,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_221,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_11])).

cnf(c_222,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_249,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_222])).

cnf(c_250,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_318,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0_43)
    | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k7_relat_1(sK3,X0_43) = sK3 ),
    inference(subtyping,[status(esa)],[c_250])).

cnf(c_324,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0_43)
    | k7_relat_1(sK3,X0_43) = sK3
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_318])).

cnf(c_680,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ sP1_iProver_split
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_262,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_222])).

cnf(c_263,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_317,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43)
    | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(subtyping,[status(esa)],[c_263])).

cnf(c_326,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_317])).

cnf(c_488,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_338,plain,
    ( k2_zfmisc_1(X0_43,X0_44) = k2_zfmisc_1(X1_43,X0_44)
    | X0_43 != X1_43 ),
    theory(equality)).

cnf(c_344,plain,
    ( k2_zfmisc_1(sK1,sK0) = k2_zfmisc_1(sK1,sK0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_338])).

cnf(c_330,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_349,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_323,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_318])).

cnf(c_360,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_362,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_327,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_317])).

cnf(c_363,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_364,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_339,plain,
    ( X0_46 != X1_46
    | k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) ),
    theory(equality)).

cnf(c_545,plain,
    ( k2_zfmisc_1(X0_43,X0_44) != k2_zfmisc_1(sK1,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_546,plain,
    ( k2_zfmisc_1(sK1,sK0) != k2_zfmisc_1(sK1,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_609,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_488,c_344,c_349,c_362,c_363,c_364,c_546])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_321,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_483,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_321])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_322,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X0_43)
    | r1_tarski(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_482,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X2_43,X0_43) != iProver_top
    | r1_tarski(X2_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_658,plain,
    ( r1_tarski(X0_43,sK2) = iProver_top
    | r1_tarski(X0_43,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_482])).

cnf(c_675,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_658])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_139,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_5,c_1])).

cnf(c_143,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_139,c_5,c_4,c_1])).

cnf(c_203,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_143,c_11])).

cnf(c_204,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_203])).

cnf(c_320,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k7_relat_1(sK3,X0_43) = sK3 ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_551,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_320])).

cnf(c_676,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_675,c_551])).

cnf(c_677,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_676])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_212,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_213,plain,
    ( k5_relset_1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_319,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k5_relset_1(X0_43,X0_44,sK3,X1_43) = k7_relat_1(sK3,X1_43) ),
    inference(subtyping,[status(esa)],[c_213])).

cnf(c_569,plain,
    ( k5_relset_1(sK1,sK0,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
    inference(equality_resolution,[status(thm)],[c_319])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(sK1,sK0,sK3,sK2) != X0
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_191,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_233,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_191])).

cnf(c_287,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_233])).

cnf(c_316,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_287])).

cnf(c_585,plain,
    ( k7_relat_1(sK3,sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_569,c_316])).

cnf(c_361,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_323])).

cnf(c_325,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_318])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_680,c_677,c_585,c_546,c_361,c_325,c_349,c_344])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.93/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.93/1.00  
% 0.93/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.93/1.00  
% 0.93/1.00  ------  iProver source info
% 0.93/1.00  
% 0.93/1.00  git: date: 2020-06-30 10:37:57 +0100
% 0.93/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.93/1.00  git: non_committed_changes: false
% 0.93/1.00  git: last_make_outside_of_git: false
% 0.93/1.00  
% 0.93/1.00  ------ 
% 0.93/1.00  
% 0.93/1.00  ------ Input Options
% 0.93/1.00  
% 0.93/1.00  --out_options                           all
% 0.93/1.00  --tptp_safe_out                         true
% 0.93/1.00  --problem_path                          ""
% 0.93/1.00  --include_path                          ""
% 0.93/1.00  --clausifier                            res/vclausify_rel
% 0.93/1.00  --clausifier_options                    --mode clausify
% 0.93/1.00  --stdin                                 false
% 0.93/1.00  --stats_out                             all
% 0.93/1.00  
% 0.93/1.00  ------ General Options
% 0.93/1.00  
% 0.93/1.00  --fof                                   false
% 0.93/1.00  --time_out_real                         305.
% 0.93/1.00  --time_out_virtual                      -1.
% 0.93/1.00  --symbol_type_check                     false
% 0.93/1.00  --clausify_out                          false
% 0.93/1.00  --sig_cnt_out                           false
% 0.93/1.00  --trig_cnt_out                          false
% 0.93/1.00  --trig_cnt_out_tolerance                1.
% 0.93/1.00  --trig_cnt_out_sk_spl                   false
% 0.93/1.00  --abstr_cl_out                          false
% 0.93/1.00  
% 0.93/1.00  ------ Global Options
% 0.93/1.00  
% 0.93/1.00  --schedule                              default
% 0.93/1.00  --add_important_lit                     false
% 0.93/1.00  --prop_solver_per_cl                    1000
% 0.93/1.00  --min_unsat_core                        false
% 0.93/1.00  --soft_assumptions                      false
% 0.93/1.00  --soft_lemma_size                       3
% 0.93/1.00  --prop_impl_unit_size                   0
% 0.93/1.00  --prop_impl_unit                        []
% 0.93/1.00  --share_sel_clauses                     true
% 0.93/1.00  --reset_solvers                         false
% 0.93/1.00  --bc_imp_inh                            [conj_cone]
% 0.93/1.00  --conj_cone_tolerance                   3.
% 0.93/1.00  --extra_neg_conj                        none
% 0.93/1.00  --large_theory_mode                     true
% 0.93/1.00  --prolific_symb_bound                   200
% 0.93/1.00  --lt_threshold                          2000
% 0.93/1.00  --clause_weak_htbl                      true
% 0.93/1.00  --gc_record_bc_elim                     false
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing Options
% 0.93/1.00  
% 0.93/1.00  --preprocessing_flag                    true
% 0.93/1.00  --time_out_prep_mult                    0.1
% 0.93/1.00  --splitting_mode                        input
% 0.93/1.00  --splitting_grd                         true
% 0.93/1.00  --splitting_cvd                         false
% 0.93/1.00  --splitting_cvd_svl                     false
% 0.93/1.00  --splitting_nvd                         32
% 0.93/1.00  --sub_typing                            true
% 0.93/1.00  --prep_gs_sim                           true
% 0.93/1.00  --prep_unflatten                        true
% 0.93/1.00  --prep_res_sim                          true
% 0.93/1.00  --prep_upred                            true
% 0.93/1.00  --prep_sem_filter                       exhaustive
% 0.93/1.00  --prep_sem_filter_out                   false
% 0.93/1.00  --pred_elim                             true
% 0.93/1.00  --res_sim_input                         true
% 0.93/1.00  --eq_ax_congr_red                       true
% 0.93/1.00  --pure_diseq_elim                       true
% 0.93/1.00  --brand_transform                       false
% 0.93/1.00  --non_eq_to_eq                          false
% 0.93/1.00  --prep_def_merge                        true
% 0.93/1.00  --prep_def_merge_prop_impl              false
% 0.93/1.00  --prep_def_merge_mbd                    true
% 0.93/1.00  --prep_def_merge_tr_red                 false
% 0.93/1.00  --prep_def_merge_tr_cl                  false
% 0.93/1.00  --smt_preprocessing                     true
% 0.93/1.00  --smt_ac_axioms                         fast
% 0.93/1.00  --preprocessed_out                      false
% 0.93/1.00  --preprocessed_stats                    false
% 0.93/1.00  
% 0.93/1.00  ------ Abstraction refinement Options
% 0.93/1.00  
% 0.93/1.00  --abstr_ref                             []
% 0.93/1.00  --abstr_ref_prep                        false
% 0.93/1.00  --abstr_ref_until_sat                   false
% 0.93/1.00  --abstr_ref_sig_restrict                funpre
% 0.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/1.00  --abstr_ref_under                       []
% 0.93/1.00  
% 0.93/1.00  ------ SAT Options
% 0.93/1.00  
% 0.93/1.00  --sat_mode                              false
% 0.93/1.00  --sat_fm_restart_options                ""
% 0.93/1.00  --sat_gr_def                            false
% 0.93/1.00  --sat_epr_types                         true
% 0.93/1.00  --sat_non_cyclic_types                  false
% 0.93/1.00  --sat_finite_models                     false
% 0.93/1.00  --sat_fm_lemmas                         false
% 0.93/1.00  --sat_fm_prep                           false
% 0.93/1.00  --sat_fm_uc_incr                        true
% 0.93/1.00  --sat_out_model                         small
% 0.93/1.00  --sat_out_clauses                       false
% 0.93/1.00  
% 0.93/1.00  ------ QBF Options
% 0.93/1.00  
% 0.93/1.00  --qbf_mode                              false
% 0.93/1.00  --qbf_elim_univ                         false
% 0.93/1.00  --qbf_dom_inst                          none
% 0.93/1.00  --qbf_dom_pre_inst                      false
% 0.93/1.00  --qbf_sk_in                             false
% 0.93/1.00  --qbf_pred_elim                         true
% 0.93/1.00  --qbf_split                             512
% 0.93/1.00  
% 0.93/1.00  ------ BMC1 Options
% 0.93/1.00  
% 0.93/1.00  --bmc1_incremental                      false
% 0.93/1.00  --bmc1_axioms                           reachable_all
% 0.93/1.00  --bmc1_min_bound                        0
% 0.93/1.00  --bmc1_max_bound                        -1
% 0.93/1.00  --bmc1_max_bound_default                -1
% 0.93/1.00  --bmc1_symbol_reachability              true
% 0.93/1.00  --bmc1_property_lemmas                  false
% 0.93/1.00  --bmc1_k_induction                      false
% 0.93/1.00  --bmc1_non_equiv_states                 false
% 0.93/1.00  --bmc1_deadlock                         false
% 0.93/1.00  --bmc1_ucm                              false
% 0.93/1.00  --bmc1_add_unsat_core                   none
% 0.93/1.00  --bmc1_unsat_core_children              false
% 0.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/1.00  --bmc1_out_stat                         full
% 0.93/1.00  --bmc1_ground_init                      false
% 0.93/1.00  --bmc1_pre_inst_next_state              false
% 0.93/1.00  --bmc1_pre_inst_state                   false
% 0.93/1.00  --bmc1_pre_inst_reach_state             false
% 0.93/1.00  --bmc1_out_unsat_core                   false
% 0.93/1.00  --bmc1_aig_witness_out                  false
% 0.93/1.00  --bmc1_verbose                          false
% 0.93/1.00  --bmc1_dump_clauses_tptp                false
% 0.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.93/1.00  --bmc1_dump_file                        -
% 0.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.93/1.00  --bmc1_ucm_extend_mode                  1
% 0.93/1.00  --bmc1_ucm_init_mode                    2
% 0.93/1.00  --bmc1_ucm_cone_mode                    none
% 0.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.93/1.00  --bmc1_ucm_relax_model                  4
% 0.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/1.00  --bmc1_ucm_layered_model                none
% 0.93/1.00  --bmc1_ucm_max_lemma_size               10
% 0.93/1.00  
% 0.93/1.00  ------ AIG Options
% 0.93/1.00  
% 0.93/1.00  --aig_mode                              false
% 0.93/1.00  
% 0.93/1.00  ------ Instantiation Options
% 0.93/1.00  
% 0.93/1.00  --instantiation_flag                    true
% 0.93/1.00  --inst_sos_flag                         false
% 0.93/1.00  --inst_sos_phase                        true
% 0.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/1.00  --inst_lit_sel_side                     num_symb
% 0.93/1.00  --inst_solver_per_active                1400
% 0.93/1.00  --inst_solver_calls_frac                1.
% 0.93/1.00  --inst_passive_queue_type               priority_queues
% 0.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/1.00  --inst_passive_queues_freq              [25;2]
% 0.93/1.00  --inst_dismatching                      true
% 0.93/1.00  --inst_eager_unprocessed_to_passive     true
% 0.93/1.00  --inst_prop_sim_given                   true
% 0.93/1.00  --inst_prop_sim_new                     false
% 0.93/1.00  --inst_subs_new                         false
% 0.93/1.00  --inst_eq_res_simp                      false
% 0.93/1.00  --inst_subs_given                       false
% 0.93/1.00  --inst_orphan_elimination               true
% 0.93/1.00  --inst_learning_loop_flag               true
% 0.93/1.00  --inst_learning_start                   3000
% 0.93/1.00  --inst_learning_factor                  2
% 0.93/1.00  --inst_start_prop_sim_after_learn       3
% 0.93/1.00  --inst_sel_renew                        solver
% 0.93/1.00  --inst_lit_activity_flag                true
% 0.93/1.00  --inst_restr_to_given                   false
% 0.93/1.00  --inst_activity_threshold               500
% 0.93/1.00  --inst_out_proof                        true
% 0.93/1.00  
% 0.93/1.00  ------ Resolution Options
% 0.93/1.00  
% 0.93/1.00  --resolution_flag                       true
% 0.93/1.00  --res_lit_sel                           adaptive
% 0.93/1.00  --res_lit_sel_side                      none
% 0.93/1.00  --res_ordering                          kbo
% 0.93/1.00  --res_to_prop_solver                    active
% 0.93/1.00  --res_prop_simpl_new                    false
% 0.93/1.00  --res_prop_simpl_given                  true
% 0.93/1.00  --res_passive_queue_type                priority_queues
% 0.93/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/1.00  --res_passive_queues_freq               [15;5]
% 0.93/1.00  --res_forward_subs                      full
% 0.93/1.00  --res_backward_subs                     full
% 0.93/1.00  --res_forward_subs_resolution           true
% 0.93/1.00  --res_backward_subs_resolution          true
% 0.93/1.00  --res_orphan_elimination                true
% 0.93/1.00  --res_time_limit                        2.
% 0.93/1.00  --res_out_proof                         true
% 0.93/1.00  
% 0.93/1.00  ------ Superposition Options
% 0.93/1.00  
% 0.93/1.00  --superposition_flag                    true
% 0.93/1.00  --sup_passive_queue_type                priority_queues
% 0.93/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.93/1.00  --demod_completeness_check              fast
% 0.93/1.00  --demod_use_ground                      true
% 0.93/1.00  --sup_to_prop_solver                    passive
% 0.93/1.00  --sup_prop_simpl_new                    true
% 0.93/1.00  --sup_prop_simpl_given                  true
% 0.93/1.00  --sup_fun_splitting                     false
% 0.93/1.00  --sup_smt_interval                      50000
% 0.93/1.00  
% 0.93/1.00  ------ Superposition Simplification Setup
% 0.93/1.00  
% 0.93/1.00  --sup_indices_passive                   []
% 0.93/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_full_bw                           [BwDemod]
% 0.93/1.00  --sup_immed_triv                        [TrivRules]
% 0.93/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_immed_bw_main                     []
% 0.93/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.00  
% 0.93/1.00  ------ Combination Options
% 0.93/1.00  
% 0.93/1.00  --comb_res_mult                         3
% 0.93/1.00  --comb_sup_mult                         2
% 0.93/1.00  --comb_inst_mult                        10
% 0.93/1.00  
% 0.93/1.00  ------ Debug Options
% 0.93/1.00  
% 0.93/1.00  --dbg_backtrace                         false
% 0.93/1.00  --dbg_dump_prop_clauses                 false
% 0.93/1.00  --dbg_dump_prop_clauses_file            -
% 0.93/1.00  --dbg_out_stat                          false
% 0.93/1.00  ------ Parsing...
% 0.93/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.93/1.00  ------ Proving...
% 0.93/1.00  ------ Problem Properties 
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  clauses                                 11
% 0.93/1.00  conjectures                             1
% 0.93/1.00  EPR                                     4
% 0.93/1.00  Horn                                    9
% 0.93/1.00  unary                                   2
% 0.93/1.00  binary                                  7
% 0.93/1.00  lits                                    22
% 0.93/1.00  lits eq                                 8
% 0.93/1.00  fd_pure                                 0
% 0.93/1.00  fd_pseudo                               0
% 0.93/1.00  fd_cond                                 0
% 0.93/1.00  fd_pseudo_cond                          0
% 0.93/1.00  AC symbols                              0
% 0.93/1.00  
% 0.93/1.00  ------ Schedule dynamic 5 is on 
% 0.93/1.00  
% 0.93/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.93/1.00  
% 0.93/1.00  
% 0.93/1.00  ------ 
% 0.93/1.00  Current options:
% 0.93/1.00  ------ 
% 0.93/1.00  
% 0.93/1.00  ------ Input Options
% 0.93/1.00  
% 0.93/1.00  --out_options                           all
% 0.93/1.00  --tptp_safe_out                         true
% 0.93/1.00  --problem_path                          ""
% 0.93/1.00  --include_path                          ""
% 0.93/1.00  --clausifier                            res/vclausify_rel
% 0.93/1.00  --clausifier_options                    --mode clausify
% 0.93/1.00  --stdin                                 false
% 0.93/1.00  --stats_out                             all
% 0.93/1.00  
% 0.93/1.00  ------ General Options
% 0.93/1.00  
% 0.93/1.00  --fof                                   false
% 0.93/1.00  --time_out_real                         305.
% 0.93/1.00  --time_out_virtual                      -1.
% 0.93/1.00  --symbol_type_check                     false
% 0.93/1.00  --clausify_out                          false
% 0.93/1.00  --sig_cnt_out                           false
% 0.93/1.00  --trig_cnt_out                          false
% 0.93/1.00  --trig_cnt_out_tolerance                1.
% 0.93/1.00  --trig_cnt_out_sk_spl                   false
% 0.93/1.00  --abstr_cl_out                          false
% 0.93/1.00  
% 0.93/1.00  ------ Global Options
% 0.93/1.00  
% 0.93/1.00  --schedule                              default
% 0.93/1.00  --add_important_lit                     false
% 0.93/1.00  --prop_solver_per_cl                    1000
% 0.93/1.00  --min_unsat_core                        false
% 0.93/1.00  --soft_assumptions                      false
% 0.93/1.00  --soft_lemma_size                       3
% 0.93/1.00  --prop_impl_unit_size                   0
% 0.93/1.00  --prop_impl_unit                        []
% 0.93/1.00  --share_sel_clauses                     true
% 0.93/1.00  --reset_solvers                         false
% 0.93/1.00  --bc_imp_inh                            [conj_cone]
% 0.93/1.00  --conj_cone_tolerance                   3.
% 0.93/1.00  --extra_neg_conj                        none
% 0.93/1.00  --large_theory_mode                     true
% 0.93/1.00  --prolific_symb_bound                   200
% 0.93/1.00  --lt_threshold                          2000
% 0.93/1.00  --clause_weak_htbl                      true
% 0.93/1.00  --gc_record_bc_elim                     false
% 0.93/1.00  
% 0.93/1.00  ------ Preprocessing Options
% 0.93/1.00  
% 0.93/1.00  --preprocessing_flag                    true
% 0.93/1.00  --time_out_prep_mult                    0.1
% 0.93/1.00  --splitting_mode                        input
% 0.93/1.00  --splitting_grd                         true
% 0.93/1.00  --splitting_cvd                         false
% 0.93/1.00  --splitting_cvd_svl                     false
% 0.93/1.00  --splitting_nvd                         32
% 0.93/1.00  --sub_typing                            true
% 0.93/1.00  --prep_gs_sim                           true
% 0.93/1.00  --prep_unflatten                        true
% 0.93/1.00  --prep_res_sim                          true
% 0.93/1.00  --prep_upred                            true
% 0.93/1.00  --prep_sem_filter                       exhaustive
% 0.93/1.00  --prep_sem_filter_out                   false
% 0.93/1.00  --pred_elim                             true
% 0.93/1.00  --res_sim_input                         true
% 0.93/1.00  --eq_ax_congr_red                       true
% 0.93/1.00  --pure_diseq_elim                       true
% 0.93/1.00  --brand_transform                       false
% 0.93/1.00  --non_eq_to_eq                          false
% 0.93/1.00  --prep_def_merge                        true
% 0.93/1.00  --prep_def_merge_prop_impl              false
% 0.93/1.00  --prep_def_merge_mbd                    true
% 0.93/1.00  --prep_def_merge_tr_red                 false
% 0.93/1.00  --prep_def_merge_tr_cl                  false
% 0.93/1.00  --smt_preprocessing                     true
% 0.93/1.00  --smt_ac_axioms                         fast
% 0.93/1.00  --preprocessed_out                      false
% 0.93/1.00  --preprocessed_stats                    false
% 0.93/1.00  
% 0.93/1.00  ------ Abstraction refinement Options
% 0.93/1.00  
% 0.93/1.00  --abstr_ref                             []
% 0.93/1.00  --abstr_ref_prep                        false
% 0.93/1.00  --abstr_ref_until_sat                   false
% 0.93/1.00  --abstr_ref_sig_restrict                funpre
% 0.93/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/1.00  --abstr_ref_under                       []
% 0.93/1.00  
% 0.93/1.00  ------ SAT Options
% 0.93/1.00  
% 0.93/1.00  --sat_mode                              false
% 0.93/1.00  --sat_fm_restart_options                ""
% 0.93/1.00  --sat_gr_def                            false
% 0.93/1.00  --sat_epr_types                         true
% 0.93/1.00  --sat_non_cyclic_types                  false
% 0.93/1.00  --sat_finite_models                     false
% 0.93/1.00  --sat_fm_lemmas                         false
% 0.93/1.00  --sat_fm_prep                           false
% 0.93/1.00  --sat_fm_uc_incr                        true
% 0.93/1.00  --sat_out_model                         small
% 0.93/1.00  --sat_out_clauses                       false
% 0.93/1.00  
% 0.93/1.00  ------ QBF Options
% 0.93/1.00  
% 0.93/1.00  --qbf_mode                              false
% 0.93/1.00  --qbf_elim_univ                         false
% 0.93/1.00  --qbf_dom_inst                          none
% 0.93/1.00  --qbf_dom_pre_inst                      false
% 0.93/1.00  --qbf_sk_in                             false
% 0.93/1.00  --qbf_pred_elim                         true
% 0.93/1.00  --qbf_split                             512
% 0.93/1.00  
% 0.93/1.00  ------ BMC1 Options
% 0.93/1.00  
% 0.93/1.00  --bmc1_incremental                      false
% 0.93/1.00  --bmc1_axioms                           reachable_all
% 0.93/1.00  --bmc1_min_bound                        0
% 0.93/1.00  --bmc1_max_bound                        -1
% 0.93/1.00  --bmc1_max_bound_default                -1
% 0.93/1.00  --bmc1_symbol_reachability              true
% 0.93/1.00  --bmc1_property_lemmas                  false
% 0.93/1.00  --bmc1_k_induction                      false
% 0.93/1.00  --bmc1_non_equiv_states                 false
% 0.93/1.00  --bmc1_deadlock                         false
% 0.93/1.00  --bmc1_ucm                              false
% 0.93/1.00  --bmc1_add_unsat_core                   none
% 0.93/1.00  --bmc1_unsat_core_children              false
% 0.93/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/1.00  --bmc1_out_stat                         full
% 0.93/1.00  --bmc1_ground_init                      false
% 0.93/1.00  --bmc1_pre_inst_next_state              false
% 0.93/1.00  --bmc1_pre_inst_state                   false
% 0.93/1.00  --bmc1_pre_inst_reach_state             false
% 0.93/1.00  --bmc1_out_unsat_core                   false
% 0.93/1.00  --bmc1_aig_witness_out                  false
% 0.93/1.00  --bmc1_verbose                          false
% 0.93/1.00  --bmc1_dump_clauses_tptp                false
% 0.93/1.00  --bmc1_dump_unsat_core_tptp             false
% 0.93/1.00  --bmc1_dump_file                        -
% 0.93/1.00  --bmc1_ucm_expand_uc_limit              128
% 0.93/1.00  --bmc1_ucm_n_expand_iterations          6
% 0.93/1.00  --bmc1_ucm_extend_mode                  1
% 0.93/1.00  --bmc1_ucm_init_mode                    2
% 0.93/1.00  --bmc1_ucm_cone_mode                    none
% 0.93/1.00  --bmc1_ucm_reduced_relation_type        0
% 0.93/1.00  --bmc1_ucm_relax_model                  4
% 0.93/1.00  --bmc1_ucm_full_tr_after_sat            true
% 0.93/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/1.00  --bmc1_ucm_layered_model                none
% 0.93/1.00  --bmc1_ucm_max_lemma_size               10
% 0.93/1.00  
% 0.93/1.00  ------ AIG Options
% 0.93/1.00  
% 0.93/1.00  --aig_mode                              false
% 0.93/1.00  
% 0.93/1.00  ------ Instantiation Options
% 0.93/1.00  
% 0.93/1.00  --instantiation_flag                    true
% 0.93/1.00  --inst_sos_flag                         false
% 0.93/1.00  --inst_sos_phase                        true
% 0.93/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/1.00  --inst_lit_sel_side                     none
% 0.93/1.00  --inst_solver_per_active                1400
% 0.93/1.00  --inst_solver_calls_frac                1.
% 0.93/1.00  --inst_passive_queue_type               priority_queues
% 0.93/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/1.01  --inst_passive_queues_freq              [25;2]
% 0.93/1.01  --inst_dismatching                      true
% 0.93/1.01  --inst_eager_unprocessed_to_passive     true
% 0.93/1.01  --inst_prop_sim_given                   true
% 0.93/1.01  --inst_prop_sim_new                     false
% 0.93/1.01  --inst_subs_new                         false
% 0.93/1.01  --inst_eq_res_simp                      false
% 0.93/1.01  --inst_subs_given                       false
% 0.93/1.01  --inst_orphan_elimination               true
% 0.93/1.01  --inst_learning_loop_flag               true
% 0.93/1.01  --inst_learning_start                   3000
% 0.93/1.01  --inst_learning_factor                  2
% 0.93/1.01  --inst_start_prop_sim_after_learn       3
% 0.93/1.01  --inst_sel_renew                        solver
% 0.93/1.01  --inst_lit_activity_flag                true
% 0.93/1.01  --inst_restr_to_given                   false
% 0.93/1.01  --inst_activity_threshold               500
% 0.93/1.01  --inst_out_proof                        true
% 0.93/1.01  
% 0.93/1.01  ------ Resolution Options
% 0.93/1.01  
% 0.93/1.01  --resolution_flag                       false
% 0.93/1.01  --res_lit_sel                           adaptive
% 0.93/1.01  --res_lit_sel_side                      none
% 0.93/1.01  --res_ordering                          kbo
% 0.93/1.01  --res_to_prop_solver                    active
% 0.93/1.01  --res_prop_simpl_new                    false
% 0.93/1.01  --res_prop_simpl_given                  true
% 0.93/1.01  --res_passive_queue_type                priority_queues
% 0.93/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/1.01  --res_passive_queues_freq               [15;5]
% 0.93/1.01  --res_forward_subs                      full
% 0.93/1.01  --res_backward_subs                     full
% 0.93/1.01  --res_forward_subs_resolution           true
% 0.93/1.01  --res_backward_subs_resolution          true
% 0.93/1.01  --res_orphan_elimination                true
% 0.93/1.01  --res_time_limit                        2.
% 0.93/1.01  --res_out_proof                         true
% 0.93/1.01  
% 0.93/1.01  ------ Superposition Options
% 0.93/1.01  
% 0.93/1.01  --superposition_flag                    true
% 0.93/1.01  --sup_passive_queue_type                priority_queues
% 0.93/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.93/1.01  --demod_completeness_check              fast
% 0.93/1.01  --demod_use_ground                      true
% 0.93/1.01  --sup_to_prop_solver                    passive
% 0.93/1.01  --sup_prop_simpl_new                    true
% 0.93/1.01  --sup_prop_simpl_given                  true
% 0.93/1.01  --sup_fun_splitting                     false
% 0.93/1.01  --sup_smt_interval                      50000
% 0.93/1.01  
% 0.93/1.01  ------ Superposition Simplification Setup
% 0.93/1.01  
% 0.93/1.01  --sup_indices_passive                   []
% 0.93/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.01  --sup_full_bw                           [BwDemod]
% 0.93/1.01  --sup_immed_triv                        [TrivRules]
% 0.93/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.01  --sup_immed_bw_main                     []
% 0.93/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/1.01  
% 0.93/1.01  ------ Combination Options
% 0.93/1.01  
% 0.93/1.01  --comb_res_mult                         3
% 0.93/1.01  --comb_sup_mult                         2
% 0.93/1.01  --comb_inst_mult                        10
% 0.93/1.01  
% 0.93/1.01  ------ Debug Options
% 0.93/1.01  
% 0.93/1.01  --dbg_backtrace                         false
% 0.93/1.01  --dbg_dump_prop_clauses                 false
% 0.93/1.01  --dbg_dump_prop_clauses_file            -
% 0.93/1.01  --dbg_out_stat                          false
% 0.93/1.01  
% 0.93/1.01  
% 0.93/1.01  
% 0.93/1.01  
% 0.93/1.01  ------ Proving...
% 0.93/1.01  
% 0.93/1.01  
% 0.93/1.01  % SZS status Theorem for theBenchmark.p
% 0.93/1.01  
% 0.93/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.93/1.01  
% 0.93/1.01  fof(f4,axiom,(
% 0.93/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f17,plain,(
% 0.93/1.01    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.93/1.01    inference(ennf_transformation,[],[f4])).
% 0.93/1.01  
% 0.93/1.01  fof(f18,plain,(
% 0.93/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.93/1.01    inference(flattening,[],[f17])).
% 0.93/1.01  
% 0.93/1.01  fof(f32,plain,(
% 0.93/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.93/1.01    inference(cnf_transformation,[],[f18])).
% 0.93/1.01  
% 0.93/1.01  fof(f5,axiom,(
% 0.93/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f19,plain,(
% 0.93/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.01    inference(ennf_transformation,[],[f5])).
% 0.93/1.01  
% 0.93/1.01  fof(f33,plain,(
% 0.93/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.01    inference(cnf_transformation,[],[f19])).
% 0.93/1.01  
% 0.93/1.01  fof(f9,conjecture,(
% 0.93/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f10,negated_conjecture,(
% 0.93/1.01    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.93/1.01    inference(negated_conjecture,[],[f9])).
% 0.93/1.01  
% 0.93/1.01  fof(f24,plain,(
% 0.93/1.01    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.93/1.01    inference(ennf_transformation,[],[f10])).
% 0.93/1.01  
% 0.93/1.01  fof(f25,plain,(
% 0.93/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.93/1.01    inference(flattening,[],[f24])).
% 0.93/1.01  
% 0.93/1.01  fof(f27,plain,(
% 0.93/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.93/1.01    introduced(choice_axiom,[])).
% 0.93/1.01  
% 0.93/1.01  fof(f28,plain,(
% 0.93/1.01    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.93/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f27])).
% 0.93/1.01  
% 0.93/1.01  fof(f38,plain,(
% 0.93/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.93/1.01    inference(cnf_transformation,[],[f28])).
% 0.93/1.01  
% 0.93/1.01  fof(f3,axiom,(
% 0.93/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f16,plain,(
% 0.93/1.01    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.93/1.01    inference(ennf_transformation,[],[f3])).
% 0.93/1.01  
% 0.93/1.01  fof(f31,plain,(
% 0.93/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.93/1.01    inference(cnf_transformation,[],[f16])).
% 0.93/1.01  
% 0.93/1.01  fof(f39,plain,(
% 0.93/1.01    r1_tarski(sK1,sK2)),
% 0.93/1.01    inference(cnf_transformation,[],[f28])).
% 0.93/1.01  
% 0.93/1.01  fof(f1,axiom,(
% 0.93/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f12,plain,(
% 0.93/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.93/1.01    inference(ennf_transformation,[],[f1])).
% 0.93/1.01  
% 0.93/1.01  fof(f13,plain,(
% 0.93/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.93/1.01    inference(flattening,[],[f12])).
% 0.93/1.01  
% 0.93/1.01  fof(f29,plain,(
% 0.93/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.93/1.01    inference(cnf_transformation,[],[f13])).
% 0.93/1.01  
% 0.93/1.01  fof(f6,axiom,(
% 0.93/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f11,plain,(
% 0.93/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.93/1.01    inference(pure_predicate_removal,[],[f6])).
% 0.93/1.01  
% 0.93/1.01  fof(f20,plain,(
% 0.93/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.01    inference(ennf_transformation,[],[f11])).
% 0.93/1.01  
% 0.93/1.01  fof(f34,plain,(
% 0.93/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.01    inference(cnf_transformation,[],[f20])).
% 0.93/1.01  
% 0.93/1.01  fof(f2,axiom,(
% 0.93/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f14,plain,(
% 0.93/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.93/1.01    inference(ennf_transformation,[],[f2])).
% 0.93/1.01  
% 0.93/1.01  fof(f15,plain,(
% 0.93/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.93/1.01    inference(flattening,[],[f14])).
% 0.93/1.01  
% 0.93/1.01  fof(f30,plain,(
% 0.93/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.93/1.01    inference(cnf_transformation,[],[f15])).
% 0.93/1.01  
% 0.93/1.01  fof(f7,axiom,(
% 0.93/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f21,plain,(
% 0.93/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.01    inference(ennf_transformation,[],[f7])).
% 0.93/1.01  
% 0.93/1.01  fof(f35,plain,(
% 0.93/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.01    inference(cnf_transformation,[],[f21])).
% 0.93/1.01  
% 0.93/1.01  fof(f8,axiom,(
% 0.93/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.93/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.93/1.01  
% 0.93/1.01  fof(f22,plain,(
% 0.93/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.93/1.01    inference(ennf_transformation,[],[f8])).
% 0.93/1.01  
% 0.93/1.01  fof(f23,plain,(
% 0.93/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.01    inference(flattening,[],[f22])).
% 0.93/1.01  
% 0.93/1.01  fof(f26,plain,(
% 0.93/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.93/1.01    inference(nnf_transformation,[],[f23])).
% 0.93/1.01  
% 0.93/1.01  fof(f37,plain,(
% 0.93/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.01    inference(cnf_transformation,[],[f26])).
% 0.93/1.01  
% 0.93/1.01  fof(f41,plain,(
% 0.93/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.93/1.01    inference(equality_resolution,[],[f37])).
% 0.93/1.01  
% 0.93/1.01  fof(f40,plain,(
% 0.93/1.01    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.93/1.01    inference(cnf_transformation,[],[f28])).
% 0.93/1.01  
% 0.93/1.01  cnf(c_3,plain,
% 0.93/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 0.93/1.01      | ~ v1_relat_1(X0)
% 0.93/1.01      | k7_relat_1(X0,X1) = X0 ),
% 0.93/1.01      inference(cnf_transformation,[],[f32]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_4,plain,
% 0.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.01      | v1_relat_1(X0) ),
% 0.93/1.01      inference(cnf_transformation,[],[f33]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_11,negated_conjecture,
% 0.93/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 0.93/1.01      inference(cnf_transformation,[],[f38]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_221,plain,
% 0.93/1.01      ( v1_relat_1(X0)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | sK3 != X0 ),
% 0.93/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_11]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_222,plain,
% 0.93/1.01      ( v1_relat_1(sK3)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(unflattening,[status(thm)],[c_221]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_249,plain,
% 0.93/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 0.93/1.01      | k7_relat_1(X0,X1) = X0
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | sK3 != X0 ),
% 0.93/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_222]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_250,plain,
% 0.93/1.01      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 0.93/1.01      | k7_relat_1(sK3,X0) = sK3
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(unflattening,[status(thm)],[c_249]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_318,plain,
% 0.93/1.01      ( ~ r1_tarski(k1_relat_1(sK3),X0_43)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | k7_relat_1(sK3,X0_43) = sK3 ),
% 0.93/1.01      inference(subtyping,[status(esa)],[c_250]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_324,plain,
% 0.93/1.01      ( ~ r1_tarski(k1_relat_1(sK3),X0_43)
% 0.93/1.01      | k7_relat_1(sK3,X0_43) = sK3
% 0.93/1.01      | ~ sP1_iProver_split ),
% 0.93/1.01      inference(splitting,
% 0.93/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 0.93/1.01                [c_318]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_680,plain,
% 0.93/1.01      ( ~ r1_tarski(k1_relat_1(sK3),sK2)
% 0.93/1.01      | ~ sP1_iProver_split
% 0.93/1.01      | k7_relat_1(sK3,sK2) = sK3 ),
% 0.93/1.01      inference(instantiation,[status(thm)],[c_324]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_2,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 0.93/1.01      inference(cnf_transformation,[],[f31]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_262,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | sK3 != X0 ),
% 0.93/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_222]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_263,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(unflattening,[status(thm)],[c_262]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_317,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(subtyping,[status(esa)],[c_263]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_326,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43)
% 0.93/1.01      | ~ sP2_iProver_split ),
% 0.93/1.01      inference(splitting,
% 0.93/1.01                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 0.93/1.01                [c_317]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_488,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43) = iProver_top
% 0.93/1.01      | sP2_iProver_split != iProver_top ),
% 0.93/1.01      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_338,plain,
% 0.93/1.01      ( k2_zfmisc_1(X0_43,X0_44) = k2_zfmisc_1(X1_43,X0_44)
% 0.93/1.01      | X0_43 != X1_43 ),
% 0.93/1.01      theory(equality) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_344,plain,
% 0.93/1.01      ( k2_zfmisc_1(sK1,sK0) = k2_zfmisc_1(sK1,sK0) | sK1 != sK1 ),
% 0.93/1.01      inference(instantiation,[status(thm)],[c_338]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_330,plain,( X0_43 = X0_43 ),theory(equality) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_349,plain,
% 0.93/1.01      ( sK1 = sK1 ),
% 0.93/1.01      inference(instantiation,[status(thm)],[c_330]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_323,plain,
% 0.93/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | ~ sP0_iProver_split ),
% 0.93/1.01      inference(splitting,
% 0.93/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.93/1.01                [c_318]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_360,plain,
% 0.93/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | sP0_iProver_split != iProver_top ),
% 0.93/1.01      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_362,plain,
% 0.93/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | sP0_iProver_split != iProver_top ),
% 0.93/1.01      inference(instantiation,[status(thm)],[c_360]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_327,plain,
% 0.93/1.01      ( sP2_iProver_split | sP0_iProver_split ),
% 0.93/1.01      inference(splitting,
% 0.93/1.01                [splitting(split),new_symbols(definition,[])],
% 0.93/1.01                [c_317]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_363,plain,
% 0.93/1.01      ( sP2_iProver_split = iProver_top
% 0.93/1.01      | sP0_iProver_split = iProver_top ),
% 0.93/1.01      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_364,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43) = iProver_top
% 0.93/1.01      | sP2_iProver_split != iProver_top ),
% 0.93/1.01      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_339,plain,
% 0.93/1.01      ( X0_46 != X1_46 | k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) ),
% 0.93/1.01      theory(equality) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_545,plain,
% 0.93/1.01      ( k2_zfmisc_1(X0_43,X0_44) != k2_zfmisc_1(sK1,sK0)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(instantiation,[status(thm)],[c_339]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_546,plain,
% 0.93/1.01      ( k2_zfmisc_1(sK1,sK0) != k2_zfmisc_1(sK1,sK0)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(instantiation,[status(thm)],[c_545]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_609,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0_43)),X0_43) = iProver_top ),
% 0.93/1.01      inference(global_propositional_subsumption,
% 0.93/1.01                [status(thm)],
% 0.93/1.01                [c_488,c_344,c_349,c_362,c_363,c_364,c_546]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_10,negated_conjecture,
% 0.93/1.01      ( r1_tarski(sK1,sK2) ),
% 0.93/1.01      inference(cnf_transformation,[],[f39]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_321,negated_conjecture,
% 0.93/1.01      ( r1_tarski(sK1,sK2) ),
% 0.93/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_483,plain,
% 0.93/1.01      ( r1_tarski(sK1,sK2) = iProver_top ),
% 0.93/1.01      inference(predicate_to_equality,[status(thm)],[c_321]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_0,plain,
% 0.93/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 0.93/1.01      inference(cnf_transformation,[],[f29]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_322,plain,
% 0.93/1.01      ( ~ r1_tarski(X0_43,X1_43)
% 0.93/1.01      | ~ r1_tarski(X2_43,X0_43)
% 0.93/1.01      | r1_tarski(X2_43,X1_43) ),
% 0.93/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_482,plain,
% 0.93/1.01      ( r1_tarski(X0_43,X1_43) != iProver_top
% 0.93/1.01      | r1_tarski(X2_43,X0_43) != iProver_top
% 0.93/1.01      | r1_tarski(X2_43,X1_43) = iProver_top ),
% 0.93/1.01      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_658,plain,
% 0.93/1.01      ( r1_tarski(X0_43,sK2) = iProver_top
% 0.93/1.01      | r1_tarski(X0_43,sK1) != iProver_top ),
% 0.93/1.01      inference(superposition,[status(thm)],[c_483,c_482]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_675,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK2) = iProver_top ),
% 0.93/1.01      inference(superposition,[status(thm)],[c_609,c_658]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_5,plain,
% 0.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.01      | v4_relat_1(X0,X1) ),
% 0.93/1.01      inference(cnf_transformation,[],[f34]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_1,plain,
% 0.93/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.93/1.01      inference(cnf_transformation,[],[f30]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_139,plain,
% 0.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.01      | ~ v1_relat_1(X0)
% 0.93/1.01      | k7_relat_1(X0,X1) = X0 ),
% 0.93/1.01      inference(resolution,[status(thm)],[c_5,c_1]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_143,plain,
% 0.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.01      | k7_relat_1(X0,X1) = X0 ),
% 0.93/1.01      inference(global_propositional_subsumption,
% 0.93/1.01                [status(thm)],
% 0.93/1.01                [c_139,c_5,c_4,c_1]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_203,plain,
% 0.93/1.01      ( k7_relat_1(X0,X1) = X0
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | sK3 != X0 ),
% 0.93/1.01      inference(resolution_lifted,[status(thm)],[c_143,c_11]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_204,plain,
% 0.93/1.01      ( k7_relat_1(sK3,X0) = sK3
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(unflattening,[status(thm)],[c_203]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_320,plain,
% 0.93/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | k7_relat_1(sK3,X0_43) = sK3 ),
% 0.93/1.01      inference(subtyping,[status(esa)],[c_204]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_551,plain,
% 0.93/1.01      ( k7_relat_1(sK3,sK1) = sK3 ),
% 0.93/1.01      inference(equality_resolution,[status(thm)],[c_320]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_676,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 0.93/1.01      inference(light_normalisation,[status(thm)],[c_675,c_551]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_677,plain,
% 0.93/1.01      ( r1_tarski(k1_relat_1(sK3),sK2) ),
% 0.93/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_676]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_6,plain,
% 0.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.01      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 0.93/1.01      inference(cnf_transformation,[],[f35]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_212,plain,
% 0.93/1.01      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | sK3 != X2 ),
% 0.93/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_213,plain,
% 0.93/1.01      ( k5_relset_1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(unflattening,[status(thm)],[c_212]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_319,plain,
% 0.93/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.93/1.01      | k5_relset_1(X0_43,X0_44,sK3,X1_43) = k7_relat_1(sK3,X1_43) ),
% 0.93/1.01      inference(subtyping,[status(esa)],[c_213]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_569,plain,
% 0.93/1.01      ( k5_relset_1(sK1,sK0,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
% 0.93/1.01      inference(equality_resolution,[status(thm)],[c_319]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_7,plain,
% 0.93/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 0.93/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.93/1.01      inference(cnf_transformation,[],[f41]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_9,negated_conjecture,
% 0.93/1.01      ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
% 0.93/1.01      inference(cnf_transformation,[],[f40]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_190,plain,
% 0.93/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.93/1.01      | k5_relset_1(sK1,sK0,sK3,sK2) != X0
% 0.93/1.01      | sK3 != X0
% 0.93/1.01      | sK0 != X2
% 0.93/1.01      | sK1 != X1 ),
% 0.93/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_191,plain,
% 0.93/1.01      ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.93/1.01      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 0.93/1.01      inference(unflattening,[status(thm)],[c_190]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_233,plain,
% 0.93/1.01      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_191]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_287,plain,
% 0.93/1.01      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
% 0.93/1.01      inference(equality_resolution_simp,[status(thm)],[c_233]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_316,plain,
% 0.93/1.01      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
% 0.93/1.01      inference(subtyping,[status(esa)],[c_287]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_585,plain,
% 0.93/1.01      ( k7_relat_1(sK3,sK2) != sK3 ),
% 0.93/1.01      inference(demodulation,[status(thm)],[c_569,c_316]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_361,plain,
% 0.93/1.01      ( ~ sP0_iProver_split
% 0.93/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.93/1.01      inference(instantiation,[status(thm)],[c_323]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(c_325,plain,
% 0.93/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 0.93/1.01      inference(splitting,
% 0.93/1.01                [splitting(split),new_symbols(definition,[])],
% 0.93/1.01                [c_318]) ).
% 0.93/1.01  
% 0.93/1.01  cnf(contradiction,plain,
% 0.93/1.01      ( $false ),
% 0.93/1.01      inference(minisat,
% 0.93/1.01                [status(thm)],
% 0.93/1.01                [c_680,c_677,c_585,c_546,c_361,c_325,c_349,c_344]) ).
% 0.93/1.01  
% 0.93/1.01  
% 0.93/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.93/1.01  
% 0.93/1.01  ------                               Statistics
% 0.93/1.01  
% 0.93/1.01  ------ General
% 0.93/1.01  
% 0.93/1.01  abstr_ref_over_cycles:                  0
% 0.93/1.01  abstr_ref_under_cycles:                 0
% 0.93/1.01  gc_basic_clause_elim:                   0
% 0.93/1.01  forced_gc_time:                         0
% 0.93/1.01  parsing_time:                           0.009
% 0.93/1.01  unif_index_cands_time:                  0.
% 0.93/1.01  unif_index_add_time:                    0.
% 0.93/1.01  orderings_time:                         0.
% 0.93/1.01  out_proof_time:                         0.011
% 0.93/1.01  total_time:                             0.059
% 0.93/1.01  num_of_symbols:                         50
% 0.93/1.01  num_of_terms:                           805
% 0.93/1.01  
% 0.93/1.01  ------ Preprocessing
% 0.93/1.01  
% 0.93/1.01  num_of_splits:                          4
% 0.93/1.01  num_of_split_atoms:                     3
% 0.93/1.01  num_of_reused_defs:                     1
% 0.93/1.01  num_eq_ax_congr_red:                    9
% 0.93/1.01  num_of_sem_filtered_clauses:            1
% 0.93/1.01  num_of_subtypes:                        5
% 0.93/1.01  monotx_restored_types:                  0
% 0.93/1.01  sat_num_of_epr_types:                   0
% 0.93/1.01  sat_num_of_non_cyclic_types:            0
% 0.93/1.01  sat_guarded_non_collapsed_types:        0
% 0.93/1.01  num_pure_diseq_elim:                    0
% 0.93/1.01  simp_replaced_by:                       0
% 0.93/1.01  res_preprocessed:                       64
% 0.93/1.01  prep_upred:                             0
% 0.93/1.01  prep_unflattend:                        12
% 0.93/1.01  smt_new_axioms:                         0
% 0.93/1.01  pred_elim_cands:                        1
% 0.93/1.01  pred_elim:                              4
% 0.93/1.01  pred_elim_cl:                           5
% 0.93/1.01  pred_elim_cycles:                       7
% 0.93/1.01  merged_defs:                            0
% 0.93/1.01  merged_defs_ncl:                        0
% 0.93/1.01  bin_hyper_res:                          0
% 0.93/1.01  prep_cycles:                            4
% 0.93/1.01  pred_elim_time:                         0.002
% 0.93/1.01  splitting_time:                         0.
% 0.93/1.01  sem_filter_time:                        0.
% 0.93/1.01  monotx_time:                            0.
% 0.93/1.01  subtype_inf_time:                       0.
% 0.93/1.01  
% 0.93/1.01  ------ Problem properties
% 0.93/1.01  
% 0.93/1.01  clauses:                                11
% 0.93/1.01  conjectures:                            1
% 0.93/1.01  epr:                                    4
% 0.93/1.01  horn:                                   9
% 0.93/1.01  ground:                                 4
% 0.93/1.01  unary:                                  2
% 0.93/1.01  binary:                                 7
% 0.93/1.01  lits:                                   22
% 0.93/1.01  lits_eq:                                8
% 0.93/1.01  fd_pure:                                0
% 0.93/1.01  fd_pseudo:                              0
% 0.93/1.01  fd_cond:                                0
% 0.93/1.01  fd_pseudo_cond:                         0
% 0.93/1.01  ac_symbols:                             0
% 0.93/1.01  
% 0.93/1.01  ------ Propositional Solver
% 0.93/1.01  
% 0.93/1.01  prop_solver_calls:                      25
% 0.93/1.01  prop_fast_solver_calls:                 310
% 0.93/1.01  smt_solver_calls:                       0
% 0.93/1.01  smt_fast_solver_calls:                  0
% 0.93/1.01  prop_num_of_clauses:                    196
% 0.93/1.01  prop_preprocess_simplified:             1486
% 0.93/1.01  prop_fo_subsumed:                       2
% 0.93/1.01  prop_solver_time:                       0.
% 0.93/1.01  smt_solver_time:                        0.
% 0.93/1.01  smt_fast_solver_time:                   0.
% 0.93/1.01  prop_fast_solver_time:                  0.
% 0.93/1.01  prop_unsat_core_time:                   0.
% 0.93/1.01  
% 0.93/1.01  ------ QBF
% 0.93/1.01  
% 0.93/1.01  qbf_q_res:                              0
% 0.93/1.01  qbf_num_tautologies:                    0
% 0.93/1.01  qbf_prep_cycles:                        0
% 0.93/1.01  
% 0.93/1.01  ------ BMC1
% 0.93/1.01  
% 0.93/1.01  bmc1_current_bound:                     -1
% 0.93/1.01  bmc1_last_solved_bound:                 -1
% 0.93/1.01  bmc1_unsat_core_size:                   -1
% 0.93/1.01  bmc1_unsat_core_parents_size:           -1
% 0.93/1.01  bmc1_merge_next_fun:                    0
% 0.93/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.93/1.01  
% 0.93/1.01  ------ Instantiation
% 0.93/1.01  
% 0.93/1.01  inst_num_of_clauses:                    55
% 0.93/1.01  inst_num_in_passive:                    3
% 0.93/1.01  inst_num_in_active:                     42
% 0.93/1.01  inst_num_in_unprocessed:                9
% 0.93/1.01  inst_num_of_loops:                      52
% 0.93/1.01  inst_num_of_learning_restarts:          0
% 0.93/1.01  inst_num_moves_active_passive:          7
% 0.93/1.01  inst_lit_activity:                      0
% 0.93/1.01  inst_lit_activity_moves:                0
% 0.93/1.01  inst_num_tautologies:                   0
% 0.93/1.01  inst_num_prop_implied:                  0
% 0.93/1.01  inst_num_existing_simplified:           0
% 0.93/1.01  inst_num_eq_res_simplified:             0
% 0.93/1.01  inst_num_child_elim:                    0
% 0.93/1.01  inst_num_of_dismatching_blockings:      1
% 0.93/1.01  inst_num_of_non_proper_insts:           17
% 0.93/1.01  inst_num_of_duplicates:                 0
% 0.93/1.01  inst_inst_num_from_inst_to_res:         0
% 0.93/1.01  inst_dismatching_checking_time:         0.
% 0.93/1.01  
% 0.93/1.01  ------ Resolution
% 0.93/1.01  
% 0.93/1.01  res_num_of_clauses:                     0
% 0.93/1.01  res_num_in_passive:                     0
% 0.93/1.01  res_num_in_active:                      0
% 0.93/1.01  res_num_of_loops:                       68
% 0.93/1.01  res_forward_subset_subsumed:            0
% 0.93/1.01  res_backward_subset_subsumed:           0
% 0.93/1.01  res_forward_subsumed:                   0
% 0.93/1.01  res_backward_subsumed:                  0
% 0.93/1.01  res_forward_subsumption_resolution:     0
% 0.93/1.01  res_backward_subsumption_resolution:    0
% 0.93/1.01  res_clause_to_clause_subsumption:       18
% 0.93/1.01  res_orphan_elimination:                 0
% 0.93/1.01  res_tautology_del:                      1
% 0.93/1.01  res_num_eq_res_simplified:              1
% 0.93/1.01  res_num_sel_changes:                    0
% 0.93/1.01  res_moves_from_active_to_pass:          0
% 0.93/1.01  
% 0.93/1.01  ------ Superposition
% 0.93/1.01  
% 0.93/1.01  sup_time_total:                         0.
% 0.93/1.01  sup_time_generating:                    0.
% 0.93/1.01  sup_time_sim_full:                      0.
% 0.93/1.01  sup_time_sim_immed:                     0.
% 0.93/1.01  
% 0.93/1.01  sup_num_of_clauses:                     16
% 0.93/1.01  sup_num_in_active:                      9
% 0.93/1.01  sup_num_in_passive:                     7
% 0.93/1.01  sup_num_of_loops:                       10
% 0.93/1.01  sup_fw_superposition:                   4
% 0.93/1.01  sup_bw_superposition:                   0
% 0.93/1.01  sup_immediate_simplified:               1
% 0.93/1.01  sup_given_eliminated:                   0
% 0.93/1.01  comparisons_done:                       0
% 0.93/1.01  comparisons_avoided:                    0
% 0.93/1.01  
% 0.93/1.01  ------ Simplifications
% 0.93/1.01  
% 0.93/1.01  
% 0.93/1.01  sim_fw_subset_subsumed:                 0
% 0.93/1.01  sim_bw_subset_subsumed:                 0
% 0.93/1.01  sim_fw_subsumed:                        0
% 0.93/1.01  sim_bw_subsumed:                        0
% 0.93/1.01  sim_fw_subsumption_res:                 0
% 0.93/1.01  sim_bw_subsumption_res:                 0
% 0.93/1.01  sim_tautology_del:                      0
% 0.93/1.01  sim_eq_tautology_del:                   0
% 0.93/1.01  sim_eq_res_simp:                        0
% 0.93/1.01  sim_fw_demodulated:                     0
% 0.93/1.01  sim_bw_demodulated:                     1
% 0.93/1.01  sim_light_normalised:                   1
% 0.93/1.01  sim_joinable_taut:                      0
% 0.93/1.01  sim_joinable_simp:                      0
% 0.93/1.01  sim_ac_normalised:                      0
% 0.93/1.01  sim_smt_subsumption:                    0
% 0.93/1.01  
%------------------------------------------------------------------------------
