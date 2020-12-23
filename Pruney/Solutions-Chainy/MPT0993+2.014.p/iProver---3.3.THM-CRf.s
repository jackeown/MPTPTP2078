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
% DateTime   : Thu Dec  3 12:04:04 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 345 expanded)
%              Number of clauses        :   74 ( 144 expanded)
%              Number of leaves         :   12 (  58 expanded)
%              Depth                    :   19
%              Number of atoms          :  301 (1091 expanded)
%              Number of equality atoms :  112 ( 201 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f27,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
      & r1_tarski(sK0,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    & r1_tarski(sK0,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f41,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

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

cnf(c_2,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_188,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_11])).

cnf(c_189,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_244,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_189])).

cnf(c_245,plain,
    ( ~ v4_relat_1(sK3,X0)
    | r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_438,plain,
    ( ~ v4_relat_1(sK3,X0_44)
    | r1_tarski(k1_relat_1(sK3),X0_44)
    | k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_245])).

cnf(c_446,plain,
    ( ~ v4_relat_1(sK3,X0_44)
    | r1_tarski(k1_relat_1(sK3),X0_44)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_438])).

cnf(c_676,plain,
    ( v4_relat_1(sK3,X0_44) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_44) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_461,plain,
    ( k2_zfmisc_1(X0_44,X0_45) = k2_zfmisc_1(X1_44,X0_45)
    | X0_44 != X1_44 ),
    theory(equality)).

cnf(c_468,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_452,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_473,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_229,plain,
    ( ~ v4_relat_1(X0,X1)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_189])).

cnf(c_230,plain,
    ( ~ v4_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_439,plain,
    ( ~ v4_relat_1(sK3,X0_44)
    | k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k7_relat_1(sK3,X0_44) = sK3 ),
    inference(subtyping,[status(esa)],[c_230])).

cnf(c_443,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_439])).

cnf(c_485,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_487,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_447,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_438])).

cnf(c_488,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_489,plain,
    ( v4_relat_1(sK3,X0_44) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_44) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_462,plain,
    ( X0_47 != X1_47
    | k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47) ),
    theory(equality)).

cnf(c_758,plain,
    ( k2_zfmisc_1(X0_44,X0_45) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_462])).

cnf(c_759,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1045,plain,
    ( r1_tarski(k1_relat_1(sK3),X0_44) = iProver_top
    | v4_relat_1(sK3,X0_44) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_468,c_473,c_487,c_488,c_489,c_759])).

cnf(c_1046,plain,
    ( v4_relat_1(sK3,X0_44) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_44) = iProver_top ),
    inference(renaming,[status(thm)],[c_1045])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_441,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_670,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_442,plain,
    ( ~ r1_tarski(X0_44,X1_44)
    | ~ r1_tarski(X2_44,X0_44)
    | r1_tarski(X2_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_669,plain,
    ( r1_tarski(X0_44,X1_44) != iProver_top
    | r1_tarski(X2_44,X0_44) != iProver_top
    | r1_tarski(X2_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_442])).

cnf(c_843,plain,
    ( r1_tarski(X0_44,sK2) = iProver_top
    | r1_tarski(X0_44,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_670,c_669])).

cnf(c_1054,plain,
    ( v4_relat_1(sK3,sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_843])).

cnf(c_1,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_259,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_189])).

cnf(c_260,plain,
    ( v4_relat_1(sK3,X0)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_259])).

cnf(c_437,plain,
    ( v4_relat_1(sK3,X0_44)
    | ~ r1_tarski(k1_relat_1(sK3),X0_44)
    | k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_260])).

cnf(c_448,plain,
    ( v4_relat_1(sK3,X0_44)
    | ~ r1_tarski(k1_relat_1(sK3),X0_44)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_437])).

cnf(c_1015,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ sP3_iProver_split ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_1021,plain,
    ( v4_relat_1(sK3,sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_444,plain,
    ( ~ v4_relat_1(sK3,X0_44)
    | k7_relat_1(sK3,X0_44) = sK3
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_439])).

cnf(c_934,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ sP1_iProver_split
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_935,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | v4_relat_1(sK3,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_934])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_146,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_147,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_146])).

cnf(c_200,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_147])).

cnf(c_347,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_200])).

cnf(c_435,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k2_partfun1(X0_44,X0_45,sK3,X1_44) = k7_relat_1(sK3,X1_44) ),
    inference(subtyping,[status(esa)],[c_347])).

cnf(c_783,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0_44) = k7_relat_1(sK3,X0_44) ),
    inference(equality_resolution,[status(thm)],[c_435])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_163,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_164,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_211,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_164])).

cnf(c_346,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_211])).

cnf(c_436,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_800,plain,
    ( k7_relat_1(sK3,sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_783,c_436])).

cnf(c_449,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_437])).

cnf(c_493,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_445,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_439])).

cnf(c_481,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_176,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_177,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_440,plain,
    ( v4_relat_1(sK3,X0_44)
    | k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(subtyping,[status(esa)],[c_177])).

cnf(c_478,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v4_relat_1(sK3,X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_480,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v4_relat_1(sK3,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1054,c_1021,c_935,c_800,c_759,c_493,c_487,c_481,c_480,c_473,c_468])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.96/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.96/1.01  
% 0.96/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.96/1.01  
% 0.96/1.01  ------  iProver source info
% 0.96/1.01  
% 0.96/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.96/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.96/1.01  git: non_committed_changes: false
% 0.96/1.01  git: last_make_outside_of_git: false
% 0.96/1.01  
% 0.96/1.01  ------ 
% 0.96/1.01  
% 0.96/1.01  ------ Input Options
% 0.96/1.01  
% 0.96/1.01  --out_options                           all
% 0.96/1.01  --tptp_safe_out                         true
% 0.96/1.01  --problem_path                          ""
% 0.96/1.01  --include_path                          ""
% 0.96/1.01  --clausifier                            res/vclausify_rel
% 0.96/1.01  --clausifier_options                    --mode clausify
% 0.96/1.01  --stdin                                 false
% 0.96/1.01  --stats_out                             all
% 0.96/1.01  
% 0.96/1.01  ------ General Options
% 0.96/1.01  
% 0.96/1.01  --fof                                   false
% 0.96/1.01  --time_out_real                         305.
% 0.96/1.01  --time_out_virtual                      -1.
% 0.96/1.01  --symbol_type_check                     false
% 0.96/1.01  --clausify_out                          false
% 0.96/1.01  --sig_cnt_out                           false
% 0.96/1.01  --trig_cnt_out                          false
% 0.96/1.01  --trig_cnt_out_tolerance                1.
% 0.96/1.01  --trig_cnt_out_sk_spl                   false
% 0.96/1.01  --abstr_cl_out                          false
% 0.96/1.01  
% 0.96/1.01  ------ Global Options
% 0.96/1.01  
% 0.96/1.01  --schedule                              default
% 0.96/1.01  --add_important_lit                     false
% 0.96/1.01  --prop_solver_per_cl                    1000
% 0.96/1.01  --min_unsat_core                        false
% 0.96/1.01  --soft_assumptions                      false
% 0.96/1.01  --soft_lemma_size                       3
% 0.96/1.01  --prop_impl_unit_size                   0
% 0.96/1.01  --prop_impl_unit                        []
% 0.96/1.01  --share_sel_clauses                     true
% 0.96/1.01  --reset_solvers                         false
% 0.96/1.01  --bc_imp_inh                            [conj_cone]
% 0.96/1.01  --conj_cone_tolerance                   3.
% 0.96/1.01  --extra_neg_conj                        none
% 0.96/1.01  --large_theory_mode                     true
% 0.96/1.01  --prolific_symb_bound                   200
% 0.96/1.01  --lt_threshold                          2000
% 0.96/1.01  --clause_weak_htbl                      true
% 0.96/1.01  --gc_record_bc_elim                     false
% 0.96/1.01  
% 0.96/1.01  ------ Preprocessing Options
% 0.96/1.01  
% 0.96/1.01  --preprocessing_flag                    true
% 0.96/1.01  --time_out_prep_mult                    0.1
% 0.96/1.01  --splitting_mode                        input
% 0.96/1.01  --splitting_grd                         true
% 0.96/1.01  --splitting_cvd                         false
% 0.96/1.01  --splitting_cvd_svl                     false
% 0.96/1.01  --splitting_nvd                         32
% 0.96/1.01  --sub_typing                            true
% 0.96/1.01  --prep_gs_sim                           true
% 0.96/1.01  --prep_unflatten                        true
% 0.96/1.01  --prep_res_sim                          true
% 0.96/1.01  --prep_upred                            true
% 0.96/1.01  --prep_sem_filter                       exhaustive
% 0.96/1.01  --prep_sem_filter_out                   false
% 0.96/1.01  --pred_elim                             true
% 0.96/1.01  --res_sim_input                         true
% 0.96/1.01  --eq_ax_congr_red                       true
% 0.96/1.01  --pure_diseq_elim                       true
% 0.96/1.01  --brand_transform                       false
% 0.96/1.01  --non_eq_to_eq                          false
% 0.96/1.01  --prep_def_merge                        true
% 0.96/1.01  --prep_def_merge_prop_impl              false
% 0.96/1.01  --prep_def_merge_mbd                    true
% 0.96/1.01  --prep_def_merge_tr_red                 false
% 0.96/1.01  --prep_def_merge_tr_cl                  false
% 0.96/1.01  --smt_preprocessing                     true
% 0.96/1.01  --smt_ac_axioms                         fast
% 0.96/1.01  --preprocessed_out                      false
% 0.96/1.01  --preprocessed_stats                    false
% 0.96/1.01  
% 0.96/1.01  ------ Abstraction refinement Options
% 0.96/1.01  
% 0.96/1.01  --abstr_ref                             []
% 0.96/1.01  --abstr_ref_prep                        false
% 0.96/1.01  --abstr_ref_until_sat                   false
% 0.96/1.01  --abstr_ref_sig_restrict                funpre
% 0.96/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/1.01  --abstr_ref_under                       []
% 0.96/1.01  
% 0.96/1.01  ------ SAT Options
% 0.96/1.01  
% 0.96/1.01  --sat_mode                              false
% 0.96/1.01  --sat_fm_restart_options                ""
% 0.96/1.01  --sat_gr_def                            false
% 0.96/1.01  --sat_epr_types                         true
% 0.96/1.01  --sat_non_cyclic_types                  false
% 0.96/1.01  --sat_finite_models                     false
% 0.96/1.01  --sat_fm_lemmas                         false
% 0.96/1.01  --sat_fm_prep                           false
% 0.96/1.01  --sat_fm_uc_incr                        true
% 0.96/1.01  --sat_out_model                         small
% 0.96/1.01  --sat_out_clauses                       false
% 0.96/1.01  
% 0.96/1.01  ------ QBF Options
% 0.96/1.01  
% 0.96/1.01  --qbf_mode                              false
% 0.96/1.01  --qbf_elim_univ                         false
% 0.96/1.01  --qbf_dom_inst                          none
% 0.96/1.01  --qbf_dom_pre_inst                      false
% 0.96/1.01  --qbf_sk_in                             false
% 0.96/1.01  --qbf_pred_elim                         true
% 0.96/1.01  --qbf_split                             512
% 0.96/1.01  
% 0.96/1.01  ------ BMC1 Options
% 0.96/1.01  
% 0.96/1.01  --bmc1_incremental                      false
% 0.96/1.01  --bmc1_axioms                           reachable_all
% 0.96/1.01  --bmc1_min_bound                        0
% 0.96/1.01  --bmc1_max_bound                        -1
% 0.96/1.01  --bmc1_max_bound_default                -1
% 0.96/1.01  --bmc1_symbol_reachability              true
% 0.96/1.01  --bmc1_property_lemmas                  false
% 0.96/1.01  --bmc1_k_induction                      false
% 0.96/1.01  --bmc1_non_equiv_states                 false
% 0.96/1.01  --bmc1_deadlock                         false
% 0.96/1.01  --bmc1_ucm                              false
% 0.96/1.01  --bmc1_add_unsat_core                   none
% 0.96/1.01  --bmc1_unsat_core_children              false
% 0.96/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/1.01  --bmc1_out_stat                         full
% 0.96/1.01  --bmc1_ground_init                      false
% 0.96/1.01  --bmc1_pre_inst_next_state              false
% 0.96/1.01  --bmc1_pre_inst_state                   false
% 0.96/1.01  --bmc1_pre_inst_reach_state             false
% 0.96/1.01  --bmc1_out_unsat_core                   false
% 0.96/1.01  --bmc1_aig_witness_out                  false
% 0.96/1.01  --bmc1_verbose                          false
% 0.96/1.01  --bmc1_dump_clauses_tptp                false
% 0.96/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.96/1.01  --bmc1_dump_file                        -
% 0.96/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.96/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.96/1.01  --bmc1_ucm_extend_mode                  1
% 0.96/1.01  --bmc1_ucm_init_mode                    2
% 0.96/1.01  --bmc1_ucm_cone_mode                    none
% 0.96/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.96/1.01  --bmc1_ucm_relax_model                  4
% 0.96/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.96/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/1.01  --bmc1_ucm_layered_model                none
% 0.96/1.01  --bmc1_ucm_max_lemma_size               10
% 0.96/1.01  
% 0.96/1.01  ------ AIG Options
% 0.96/1.01  
% 0.96/1.01  --aig_mode                              false
% 0.96/1.01  
% 0.96/1.01  ------ Instantiation Options
% 0.96/1.01  
% 0.96/1.01  --instantiation_flag                    true
% 0.96/1.01  --inst_sos_flag                         false
% 0.96/1.01  --inst_sos_phase                        true
% 0.96/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/1.01  --inst_lit_sel_side                     num_symb
% 0.96/1.01  --inst_solver_per_active                1400
% 0.96/1.01  --inst_solver_calls_frac                1.
% 0.96/1.01  --inst_passive_queue_type               priority_queues
% 0.96/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/1.01  --inst_passive_queues_freq              [25;2]
% 0.96/1.01  --inst_dismatching                      true
% 0.96/1.01  --inst_eager_unprocessed_to_passive     true
% 0.96/1.01  --inst_prop_sim_given                   true
% 0.96/1.01  --inst_prop_sim_new                     false
% 0.96/1.01  --inst_subs_new                         false
% 0.96/1.01  --inst_eq_res_simp                      false
% 0.96/1.01  --inst_subs_given                       false
% 0.96/1.01  --inst_orphan_elimination               true
% 0.96/1.01  --inst_learning_loop_flag               true
% 0.96/1.01  --inst_learning_start                   3000
% 0.96/1.01  --inst_learning_factor                  2
% 0.96/1.01  --inst_start_prop_sim_after_learn       3
% 0.96/1.01  --inst_sel_renew                        solver
% 0.96/1.01  --inst_lit_activity_flag                true
% 0.96/1.01  --inst_restr_to_given                   false
% 0.96/1.01  --inst_activity_threshold               500
% 0.96/1.01  --inst_out_proof                        true
% 0.96/1.01  
% 0.96/1.01  ------ Resolution Options
% 0.96/1.01  
% 0.96/1.01  --resolution_flag                       true
% 0.96/1.01  --res_lit_sel                           adaptive
% 0.96/1.01  --res_lit_sel_side                      none
% 0.96/1.01  --res_ordering                          kbo
% 0.96/1.01  --res_to_prop_solver                    active
% 0.96/1.01  --res_prop_simpl_new                    false
% 0.96/1.01  --res_prop_simpl_given                  true
% 0.96/1.01  --res_passive_queue_type                priority_queues
% 0.96/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/1.01  --res_passive_queues_freq               [15;5]
% 0.96/1.01  --res_forward_subs                      full
% 0.96/1.01  --res_backward_subs                     full
% 0.96/1.01  --res_forward_subs_resolution           true
% 0.96/1.01  --res_backward_subs_resolution          true
% 0.96/1.01  --res_orphan_elimination                true
% 0.96/1.01  --res_time_limit                        2.
% 0.96/1.01  --res_out_proof                         true
% 0.96/1.01  
% 0.96/1.01  ------ Superposition Options
% 0.96/1.01  
% 0.96/1.01  --superposition_flag                    true
% 0.96/1.01  --sup_passive_queue_type                priority_queues
% 0.96/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.96/1.01  --demod_completeness_check              fast
% 0.96/1.01  --demod_use_ground                      true
% 0.96/1.01  --sup_to_prop_solver                    passive
% 0.96/1.01  --sup_prop_simpl_new                    true
% 0.96/1.01  --sup_prop_simpl_given                  true
% 0.96/1.01  --sup_fun_splitting                     false
% 0.96/1.01  --sup_smt_interval                      50000
% 0.96/1.01  
% 0.96/1.01  ------ Superposition Simplification Setup
% 0.96/1.01  
% 0.96/1.01  --sup_indices_passive                   []
% 0.96/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.01  --sup_full_bw                           [BwDemod]
% 0.96/1.01  --sup_immed_triv                        [TrivRules]
% 0.96/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.01  --sup_immed_bw_main                     []
% 0.96/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/1.01  
% 0.96/1.01  ------ Combination Options
% 0.96/1.01  
% 0.96/1.01  --comb_res_mult                         3
% 0.96/1.01  --comb_sup_mult                         2
% 0.96/1.01  --comb_inst_mult                        10
% 0.96/1.01  
% 0.96/1.01  ------ Debug Options
% 0.96/1.01  
% 0.96/1.01  --dbg_backtrace                         false
% 0.96/1.01  --dbg_dump_prop_clauses                 false
% 0.96/1.01  --dbg_dump_prop_clauses_file            -
% 0.96/1.01  --dbg_out_stat                          false
% 0.96/1.01  ------ Parsing...
% 0.96/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.96/1.01  
% 0.96/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.96/1.01  
% 0.96/1.01  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.96/1.01  
% 0.96/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.96/1.01  ------ Proving...
% 0.96/1.01  ------ Problem Properties 
% 0.96/1.01  
% 0.96/1.01  
% 0.96/1.01  clauses                                 14
% 0.96/1.01  conjectures                             1
% 0.96/1.01  EPR                                     5
% 0.96/1.01  Horn                                    11
% 0.96/1.01  unary                                   2
% 0.96/1.01  binary                                  8
% 0.96/1.01  lits                                    30
% 0.96/1.01  lits eq                                 8
% 0.96/1.01  fd_pure                                 0
% 0.96/1.01  fd_pseudo                               0
% 0.96/1.01  fd_cond                                 0
% 0.96/1.01  fd_pseudo_cond                          0
% 0.96/1.01  AC symbols                              0
% 0.96/1.01  
% 0.96/1.01  ------ Schedule dynamic 5 is on 
% 0.96/1.01  
% 0.96/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.96/1.01  
% 0.96/1.01  
% 0.96/1.01  ------ 
% 0.96/1.01  Current options:
% 0.96/1.01  ------ 
% 0.96/1.01  
% 0.96/1.01  ------ Input Options
% 0.96/1.01  
% 0.96/1.01  --out_options                           all
% 0.96/1.01  --tptp_safe_out                         true
% 0.96/1.01  --problem_path                          ""
% 0.96/1.01  --include_path                          ""
% 0.96/1.01  --clausifier                            res/vclausify_rel
% 0.96/1.01  --clausifier_options                    --mode clausify
% 0.96/1.01  --stdin                                 false
% 0.96/1.01  --stats_out                             all
% 0.96/1.01  
% 0.96/1.01  ------ General Options
% 0.96/1.01  
% 0.96/1.01  --fof                                   false
% 0.96/1.01  --time_out_real                         305.
% 0.96/1.01  --time_out_virtual                      -1.
% 0.96/1.01  --symbol_type_check                     false
% 0.96/1.01  --clausify_out                          false
% 0.96/1.01  --sig_cnt_out                           false
% 0.96/1.01  --trig_cnt_out                          false
% 0.96/1.01  --trig_cnt_out_tolerance                1.
% 0.96/1.01  --trig_cnt_out_sk_spl                   false
% 0.96/1.01  --abstr_cl_out                          false
% 0.96/1.01  
% 0.96/1.01  ------ Global Options
% 0.96/1.01  
% 0.96/1.01  --schedule                              default
% 0.96/1.01  --add_important_lit                     false
% 0.96/1.01  --prop_solver_per_cl                    1000
% 0.96/1.01  --min_unsat_core                        false
% 0.96/1.01  --soft_assumptions                      false
% 0.96/1.01  --soft_lemma_size                       3
% 0.96/1.01  --prop_impl_unit_size                   0
% 0.96/1.01  --prop_impl_unit                        []
% 0.96/1.01  --share_sel_clauses                     true
% 0.96/1.01  --reset_solvers                         false
% 0.96/1.01  --bc_imp_inh                            [conj_cone]
% 0.96/1.01  --conj_cone_tolerance                   3.
% 0.96/1.01  --extra_neg_conj                        none
% 0.96/1.01  --large_theory_mode                     true
% 0.96/1.01  --prolific_symb_bound                   200
% 0.96/1.01  --lt_threshold                          2000
% 0.96/1.01  --clause_weak_htbl                      true
% 0.96/1.01  --gc_record_bc_elim                     false
% 0.96/1.01  
% 0.96/1.01  ------ Preprocessing Options
% 0.96/1.01  
% 0.96/1.01  --preprocessing_flag                    true
% 0.96/1.01  --time_out_prep_mult                    0.1
% 0.96/1.01  --splitting_mode                        input
% 0.96/1.01  --splitting_grd                         true
% 0.96/1.01  --splitting_cvd                         false
% 0.96/1.01  --splitting_cvd_svl                     false
% 0.96/1.01  --splitting_nvd                         32
% 0.96/1.01  --sub_typing                            true
% 0.96/1.01  --prep_gs_sim                           true
% 0.96/1.01  --prep_unflatten                        true
% 0.96/1.01  --prep_res_sim                          true
% 0.96/1.01  --prep_upred                            true
% 0.96/1.01  --prep_sem_filter                       exhaustive
% 0.96/1.01  --prep_sem_filter_out                   false
% 0.96/1.01  --pred_elim                             true
% 0.96/1.01  --res_sim_input                         true
% 0.96/1.01  --eq_ax_congr_red                       true
% 0.96/1.01  --pure_diseq_elim                       true
% 0.96/1.01  --brand_transform                       false
% 0.96/1.01  --non_eq_to_eq                          false
% 0.96/1.01  --prep_def_merge                        true
% 0.96/1.01  --prep_def_merge_prop_impl              false
% 0.96/1.01  --prep_def_merge_mbd                    true
% 0.96/1.01  --prep_def_merge_tr_red                 false
% 0.96/1.01  --prep_def_merge_tr_cl                  false
% 0.96/1.01  --smt_preprocessing                     true
% 0.96/1.01  --smt_ac_axioms                         fast
% 0.96/1.01  --preprocessed_out                      false
% 0.96/1.01  --preprocessed_stats                    false
% 0.96/1.01  
% 0.96/1.01  ------ Abstraction refinement Options
% 0.96/1.01  
% 0.96/1.01  --abstr_ref                             []
% 0.96/1.01  --abstr_ref_prep                        false
% 0.96/1.01  --abstr_ref_until_sat                   false
% 0.96/1.01  --abstr_ref_sig_restrict                funpre
% 0.96/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/1.01  --abstr_ref_under                       []
% 0.96/1.01  
% 0.96/1.01  ------ SAT Options
% 0.96/1.01  
% 0.96/1.01  --sat_mode                              false
% 0.96/1.01  --sat_fm_restart_options                ""
% 0.96/1.01  --sat_gr_def                            false
% 0.96/1.01  --sat_epr_types                         true
% 0.96/1.01  --sat_non_cyclic_types                  false
% 0.96/1.01  --sat_finite_models                     false
% 0.96/1.01  --sat_fm_lemmas                         false
% 0.96/1.01  --sat_fm_prep                           false
% 0.96/1.01  --sat_fm_uc_incr                        true
% 0.96/1.01  --sat_out_model                         small
% 0.96/1.01  --sat_out_clauses                       false
% 0.96/1.01  
% 0.96/1.01  ------ QBF Options
% 0.96/1.01  
% 0.96/1.01  --qbf_mode                              false
% 0.96/1.01  --qbf_elim_univ                         false
% 0.96/1.01  --qbf_dom_inst                          none
% 0.96/1.01  --qbf_dom_pre_inst                      false
% 0.96/1.01  --qbf_sk_in                             false
% 0.96/1.01  --qbf_pred_elim                         true
% 0.96/1.01  --qbf_split                             512
% 0.96/1.01  
% 0.96/1.01  ------ BMC1 Options
% 0.96/1.01  
% 0.96/1.01  --bmc1_incremental                      false
% 0.96/1.01  --bmc1_axioms                           reachable_all
% 0.96/1.01  --bmc1_min_bound                        0
% 0.96/1.01  --bmc1_max_bound                        -1
% 0.96/1.01  --bmc1_max_bound_default                -1
% 0.96/1.01  --bmc1_symbol_reachability              true
% 0.96/1.01  --bmc1_property_lemmas                  false
% 0.96/1.01  --bmc1_k_induction                      false
% 0.96/1.01  --bmc1_non_equiv_states                 false
% 0.96/1.01  --bmc1_deadlock                         false
% 0.96/1.01  --bmc1_ucm                              false
% 0.96/1.01  --bmc1_add_unsat_core                   none
% 0.96/1.01  --bmc1_unsat_core_children              false
% 0.96/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/1.01  --bmc1_out_stat                         full
% 0.96/1.01  --bmc1_ground_init                      false
% 0.96/1.01  --bmc1_pre_inst_next_state              false
% 0.96/1.01  --bmc1_pre_inst_state                   false
% 0.96/1.01  --bmc1_pre_inst_reach_state             false
% 0.96/1.01  --bmc1_out_unsat_core                   false
% 0.96/1.01  --bmc1_aig_witness_out                  false
% 0.96/1.01  --bmc1_verbose                          false
% 0.96/1.01  --bmc1_dump_clauses_tptp                false
% 0.96/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.96/1.01  --bmc1_dump_file                        -
% 0.96/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.96/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.96/1.01  --bmc1_ucm_extend_mode                  1
% 0.96/1.01  --bmc1_ucm_init_mode                    2
% 0.96/1.01  --bmc1_ucm_cone_mode                    none
% 0.96/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.96/1.01  --bmc1_ucm_relax_model                  4
% 0.96/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.96/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/1.01  --bmc1_ucm_layered_model                none
% 0.96/1.01  --bmc1_ucm_max_lemma_size               10
% 0.96/1.01  
% 0.96/1.01  ------ AIG Options
% 0.96/1.01  
% 0.96/1.01  --aig_mode                              false
% 0.96/1.01  
% 0.96/1.01  ------ Instantiation Options
% 0.96/1.01  
% 0.96/1.01  --instantiation_flag                    true
% 0.96/1.01  --inst_sos_flag                         false
% 0.96/1.01  --inst_sos_phase                        true
% 0.96/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/1.01  --inst_lit_sel_side                     none
% 0.96/1.01  --inst_solver_per_active                1400
% 0.96/1.01  --inst_solver_calls_frac                1.
% 0.96/1.01  --inst_passive_queue_type               priority_queues
% 0.96/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/1.01  --inst_passive_queues_freq              [25;2]
% 0.96/1.01  --inst_dismatching                      true
% 0.96/1.01  --inst_eager_unprocessed_to_passive     true
% 0.96/1.01  --inst_prop_sim_given                   true
% 0.96/1.01  --inst_prop_sim_new                     false
% 0.96/1.01  --inst_subs_new                         false
% 0.96/1.01  --inst_eq_res_simp                      false
% 0.96/1.01  --inst_subs_given                       false
% 0.96/1.01  --inst_orphan_elimination               true
% 0.96/1.01  --inst_learning_loop_flag               true
% 0.96/1.01  --inst_learning_start                   3000
% 0.96/1.01  --inst_learning_factor                  2
% 0.96/1.01  --inst_start_prop_sim_after_learn       3
% 0.96/1.01  --inst_sel_renew                        solver
% 0.96/1.01  --inst_lit_activity_flag                true
% 0.96/1.01  --inst_restr_to_given                   false
% 0.96/1.01  --inst_activity_threshold               500
% 0.96/1.01  --inst_out_proof                        true
% 0.96/1.01  
% 0.96/1.01  ------ Resolution Options
% 0.96/1.01  
% 0.96/1.01  --resolution_flag                       false
% 0.96/1.01  --res_lit_sel                           adaptive
% 0.96/1.01  --res_lit_sel_side                      none
% 0.96/1.01  --res_ordering                          kbo
% 0.96/1.01  --res_to_prop_solver                    active
% 0.96/1.01  --res_prop_simpl_new                    false
% 0.96/1.01  --res_prop_simpl_given                  true
% 0.96/1.01  --res_passive_queue_type                priority_queues
% 0.96/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/1.01  --res_passive_queues_freq               [15;5]
% 0.96/1.01  --res_forward_subs                      full
% 0.96/1.01  --res_backward_subs                     full
% 0.96/1.01  --res_forward_subs_resolution           true
% 0.96/1.01  --res_backward_subs_resolution          true
% 0.96/1.01  --res_orphan_elimination                true
% 0.96/1.01  --res_time_limit                        2.
% 0.96/1.01  --res_out_proof                         true
% 0.96/1.01  
% 0.96/1.01  ------ Superposition Options
% 0.96/1.01  
% 0.96/1.01  --superposition_flag                    true
% 0.96/1.01  --sup_passive_queue_type                priority_queues
% 0.96/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.96/1.01  --demod_completeness_check              fast
% 0.96/1.01  --demod_use_ground                      true
% 0.96/1.01  --sup_to_prop_solver                    passive
% 0.96/1.01  --sup_prop_simpl_new                    true
% 0.96/1.01  --sup_prop_simpl_given                  true
% 0.96/1.01  --sup_fun_splitting                     false
% 0.96/1.01  --sup_smt_interval                      50000
% 0.96/1.01  
% 0.96/1.01  ------ Superposition Simplification Setup
% 0.96/1.01  
% 0.96/1.01  --sup_indices_passive                   []
% 0.96/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.01  --sup_full_bw                           [BwDemod]
% 0.96/1.01  --sup_immed_triv                        [TrivRules]
% 0.96/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.01  --sup_immed_bw_main                     []
% 0.96/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/1.01  
% 0.96/1.01  ------ Combination Options
% 0.96/1.01  
% 0.96/1.01  --comb_res_mult                         3
% 0.96/1.01  --comb_sup_mult                         2
% 0.96/1.01  --comb_inst_mult                        10
% 0.96/1.01  
% 0.96/1.01  ------ Debug Options
% 0.96/1.01  
% 0.96/1.01  --dbg_backtrace                         false
% 0.96/1.01  --dbg_dump_prop_clauses                 false
% 0.96/1.01  --dbg_dump_prop_clauses_file            -
% 0.96/1.01  --dbg_out_stat                          false
% 0.96/1.01  
% 0.96/1.01  
% 0.96/1.01  
% 0.96/1.01  
% 0.96/1.01  ------ Proving...
% 0.96/1.01  
% 0.96/1.01  
% 0.96/1.01  % SZS status Theorem for theBenchmark.p
% 0.96/1.01  
% 0.96/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.96/1.01  
% 0.96/1.01  fof(f2,axiom,(
% 0.96/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.01  
% 0.96/1.01  fof(f14,plain,(
% 0.96/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.96/1.01    inference(ennf_transformation,[],[f2])).
% 0.96/1.01  
% 0.96/1.01  fof(f25,plain,(
% 0.96/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.96/1.01    inference(nnf_transformation,[],[f14])).
% 0.96/1.01  
% 0.96/1.01  fof(f30,plain,(
% 0.96/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.96/1.01    inference(cnf_transformation,[],[f25])).
% 0.96/1.01  
% 0.96/1.01  fof(f4,axiom,(
% 0.96/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.01  
% 0.96/1.01  fof(f17,plain,(
% 0.96/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.96/1.01    inference(ennf_transformation,[],[f4])).
% 0.96/1.01  
% 0.96/1.01  fof(f33,plain,(
% 0.96/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.96/1.01    inference(cnf_transformation,[],[f17])).
% 0.96/1.01  
% 0.96/1.01  fof(f8,conjecture,(
% 0.96/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.01  
% 0.96/1.01  fof(f9,negated_conjecture,(
% 0.96/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.96/1.01    inference(negated_conjecture,[],[f8])).
% 0.96/1.01  
% 0.96/1.01  fof(f10,plain,(
% 0.96/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.96/1.01    inference(pure_predicate_removal,[],[f9])).
% 0.96/1.01  
% 0.96/1.01  fof(f23,plain,(
% 0.96/1.01    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.96/1.01    inference(ennf_transformation,[],[f10])).
% 0.96/1.01  
% 0.96/1.01  fof(f24,plain,(
% 0.96/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.96/1.01    inference(flattening,[],[f23])).
% 0.96/1.01  
% 0.96/1.01  fof(f27,plain,(
% 0.96/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.96/1.01    introduced(choice_axiom,[])).
% 0.96/1.01  
% 0.96/1.01  fof(f28,plain,(
% 0.96/1.01    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.96/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f27])).
% 0.96/1.01  
% 0.96/1.01  fof(f39,plain,(
% 0.96/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.96/1.01    inference(cnf_transformation,[],[f28])).
% 0.96/1.01  
% 0.96/1.01  fof(f3,axiom,(
% 0.96/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.01  
% 0.96/1.01  fof(f15,plain,(
% 0.96/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.96/1.01    inference(ennf_transformation,[],[f3])).
% 0.96/1.01  
% 0.96/1.01  fof(f16,plain,(
% 0.96/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.96/1.01    inference(flattening,[],[f15])).
% 0.96/1.01  
% 0.96/1.01  fof(f32,plain,(
% 0.96/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.96/1.01    inference(cnf_transformation,[],[f16])).
% 0.96/1.01  
% 0.96/1.01  fof(f40,plain,(
% 0.96/1.01    r1_tarski(sK0,sK2)),
% 0.96/1.01    inference(cnf_transformation,[],[f28])).
% 0.96/1.01  
% 0.96/1.01  fof(f1,axiom,(
% 0.96/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.01  
% 0.96/1.01  fof(f12,plain,(
% 0.96/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.96/1.01    inference(ennf_transformation,[],[f1])).
% 0.96/1.01  
% 0.96/1.01  fof(f13,plain,(
% 0.96/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.96/1.01    inference(flattening,[],[f12])).
% 0.96/1.01  
% 0.96/1.01  fof(f29,plain,(
% 0.96/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.96/1.01    inference(cnf_transformation,[],[f13])).
% 0.96/1.01  
% 0.96/1.01  fof(f31,plain,(
% 0.96/1.01    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.96/1.01    inference(cnf_transformation,[],[f25])).
% 0.96/1.01  
% 0.96/1.01  fof(f7,axiom,(
% 0.96/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 0.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.01  
% 0.96/1.01  fof(f21,plain,(
% 0.96/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.96/1.01    inference(ennf_transformation,[],[f7])).
% 0.96/1.01  
% 0.96/1.01  fof(f22,plain,(
% 0.96/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.96/1.01    inference(flattening,[],[f21])).
% 0.96/1.01  
% 0.96/1.01  fof(f37,plain,(
% 0.96/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.96/1.01    inference(cnf_transformation,[],[f22])).
% 0.96/1.01  
% 0.96/1.01  fof(f38,plain,(
% 0.96/1.01    v1_funct_1(sK3)),
% 0.96/1.01    inference(cnf_transformation,[],[f28])).
% 0.96/1.01  
% 0.96/1.01  fof(f6,axiom,(
% 0.96/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.01  
% 0.96/1.01  fof(f19,plain,(
% 0.96/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.96/1.01    inference(ennf_transformation,[],[f6])).
% 0.96/1.01  
% 0.96/1.01  fof(f20,plain,(
% 0.96/1.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.96/1.01    inference(flattening,[],[f19])).
% 0.96/1.01  
% 0.96/1.01  fof(f26,plain,(
% 0.96/1.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.96/1.01    inference(nnf_transformation,[],[f20])).
% 0.96/1.01  
% 0.96/1.01  fof(f36,plain,(
% 0.96/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.96/1.01    inference(cnf_transformation,[],[f26])).
% 0.96/1.01  
% 0.96/1.01  fof(f42,plain,(
% 0.96/1.01    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.96/1.01    inference(equality_resolution,[],[f36])).
% 0.96/1.01  
% 0.96/1.01  fof(f41,plain,(
% 0.96/1.01    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.96/1.01    inference(cnf_transformation,[],[f28])).
% 0.96/1.01  
% 0.96/1.01  fof(f5,axiom,(
% 0.96/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.96/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.96/1.01  
% 0.96/1.01  fof(f11,plain,(
% 0.96/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.96/1.01    inference(pure_predicate_removal,[],[f5])).
% 0.96/1.01  
% 0.96/1.01  fof(f18,plain,(
% 0.96/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.96/1.01    inference(ennf_transformation,[],[f11])).
% 0.96/1.01  
% 0.96/1.01  fof(f34,plain,(
% 0.96/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.96/1.01    inference(cnf_transformation,[],[f18])).
% 0.96/1.01  
% 0.96/1.01  cnf(c_2,plain,
% 0.96/1.01      ( ~ v4_relat_1(X0,X1)
% 0.96/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 0.96/1.01      | ~ v1_relat_1(X0) ),
% 0.96/1.01      inference(cnf_transformation,[],[f30]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_4,plain,
% 0.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.96/1.01      | v1_relat_1(X0) ),
% 0.96/1.01      inference(cnf_transformation,[],[f33]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_11,negated_conjecture,
% 0.96/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.96/1.01      inference(cnf_transformation,[],[f39]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_188,plain,
% 0.96/1.01      ( v1_relat_1(X0)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | sK3 != X0 ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_11]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_189,plain,
% 0.96/1.01      ( v1_relat_1(sK3)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(unflattening,[status(thm)],[c_188]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_244,plain,
% 0.96/1.01      ( ~ v4_relat_1(X0,X1)
% 0.96/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | sK3 != X0 ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_189]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_245,plain,
% 0.96/1.01      ( ~ v4_relat_1(sK3,X0)
% 0.96/1.01      | r1_tarski(k1_relat_1(sK3),X0)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(unflattening,[status(thm)],[c_244]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_438,plain,
% 0.96/1.01      ( ~ v4_relat_1(sK3,X0_44)
% 0.96/1.01      | r1_tarski(k1_relat_1(sK3),X0_44)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(subtyping,[status(esa)],[c_245]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_446,plain,
% 0.96/1.01      ( ~ v4_relat_1(sK3,X0_44)
% 0.96/1.01      | r1_tarski(k1_relat_1(sK3),X0_44)
% 0.96/1.01      | ~ sP2_iProver_split ),
% 0.96/1.01      inference(splitting,
% 0.96/1.01                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 0.96/1.01                [c_438]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_676,plain,
% 0.96/1.01      ( v4_relat_1(sK3,X0_44) != iProver_top
% 0.96/1.01      | r1_tarski(k1_relat_1(sK3),X0_44) = iProver_top
% 0.96/1.01      | sP2_iProver_split != iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_461,plain,
% 0.96/1.01      ( k2_zfmisc_1(X0_44,X0_45) = k2_zfmisc_1(X1_44,X0_45)
% 0.96/1.01      | X0_44 != X1_44 ),
% 0.96/1.01      theory(equality) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_468,plain,
% 0.96/1.01      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK1) | sK0 != sK0 ),
% 0.96/1.01      inference(instantiation,[status(thm)],[c_461]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_452,plain,( X0_44 = X0_44 ),theory(equality) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_473,plain,
% 0.96/1.01      ( sK0 = sK0 ),
% 0.96/1.01      inference(instantiation,[status(thm)],[c_452]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_3,plain,
% 0.96/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.96/1.01      inference(cnf_transformation,[],[f32]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_229,plain,
% 0.96/1.01      ( ~ v4_relat_1(X0,X1)
% 0.96/1.01      | k7_relat_1(X0,X1) = X0
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | sK3 != X0 ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_189]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_230,plain,
% 0.96/1.01      ( ~ v4_relat_1(sK3,X0)
% 0.96/1.01      | k7_relat_1(sK3,X0) = sK3
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(unflattening,[status(thm)],[c_229]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_439,plain,
% 0.96/1.01      ( ~ v4_relat_1(sK3,X0_44)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | k7_relat_1(sK3,X0_44) = sK3 ),
% 0.96/1.01      inference(subtyping,[status(esa)],[c_230]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_443,plain,
% 0.96/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | ~ sP0_iProver_split ),
% 0.96/1.01      inference(splitting,
% 0.96/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.96/1.01                [c_439]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_485,plain,
% 0.96/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | sP0_iProver_split != iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_487,plain,
% 0.96/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | sP0_iProver_split != iProver_top ),
% 0.96/1.01      inference(instantiation,[status(thm)],[c_485]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_447,plain,
% 0.96/1.01      ( sP2_iProver_split | sP0_iProver_split ),
% 0.96/1.01      inference(splitting,
% 0.96/1.01                [splitting(split),new_symbols(definition,[])],
% 0.96/1.01                [c_438]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_488,plain,
% 0.96/1.01      ( sP2_iProver_split = iProver_top
% 0.96/1.01      | sP0_iProver_split = iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_489,plain,
% 0.96/1.01      ( v4_relat_1(sK3,X0_44) != iProver_top
% 0.96/1.01      | r1_tarski(k1_relat_1(sK3),X0_44) = iProver_top
% 0.96/1.01      | sP2_iProver_split != iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_462,plain,
% 0.96/1.01      ( X0_47 != X1_47 | k1_zfmisc_1(X0_47) = k1_zfmisc_1(X1_47) ),
% 0.96/1.01      theory(equality) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_758,plain,
% 0.96/1.01      ( k2_zfmisc_1(X0_44,X0_45) != k2_zfmisc_1(sK0,sK1)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(instantiation,[status(thm)],[c_462]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_759,plain,
% 0.96/1.01      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(instantiation,[status(thm)],[c_758]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_1045,plain,
% 0.96/1.01      ( r1_tarski(k1_relat_1(sK3),X0_44) = iProver_top
% 0.96/1.01      | v4_relat_1(sK3,X0_44) != iProver_top ),
% 0.96/1.01      inference(global_propositional_subsumption,
% 0.96/1.01                [status(thm)],
% 0.96/1.01                [c_676,c_468,c_473,c_487,c_488,c_489,c_759]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_1046,plain,
% 0.96/1.01      ( v4_relat_1(sK3,X0_44) != iProver_top
% 0.96/1.01      | r1_tarski(k1_relat_1(sK3),X0_44) = iProver_top ),
% 0.96/1.01      inference(renaming,[status(thm)],[c_1045]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_10,negated_conjecture,
% 0.96/1.01      ( r1_tarski(sK0,sK2) ),
% 0.96/1.01      inference(cnf_transformation,[],[f40]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_441,negated_conjecture,
% 0.96/1.01      ( r1_tarski(sK0,sK2) ),
% 0.96/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_670,plain,
% 0.96/1.01      ( r1_tarski(sK0,sK2) = iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_0,plain,
% 0.96/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 0.96/1.01      inference(cnf_transformation,[],[f29]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_442,plain,
% 0.96/1.01      ( ~ r1_tarski(X0_44,X1_44)
% 0.96/1.01      | ~ r1_tarski(X2_44,X0_44)
% 0.96/1.01      | r1_tarski(X2_44,X1_44) ),
% 0.96/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_669,plain,
% 0.96/1.01      ( r1_tarski(X0_44,X1_44) != iProver_top
% 0.96/1.01      | r1_tarski(X2_44,X0_44) != iProver_top
% 0.96/1.01      | r1_tarski(X2_44,X1_44) = iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_442]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_843,plain,
% 0.96/1.01      ( r1_tarski(X0_44,sK2) = iProver_top
% 0.96/1.01      | r1_tarski(X0_44,sK0) != iProver_top ),
% 0.96/1.01      inference(superposition,[status(thm)],[c_670,c_669]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_1054,plain,
% 0.96/1.01      ( v4_relat_1(sK3,sK0) != iProver_top
% 0.96/1.01      | r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 0.96/1.01      inference(superposition,[status(thm)],[c_1046,c_843]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_1,plain,
% 0.96/1.01      ( v4_relat_1(X0,X1)
% 0.96/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 0.96/1.01      | ~ v1_relat_1(X0) ),
% 0.96/1.01      inference(cnf_transformation,[],[f31]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_259,plain,
% 0.96/1.01      ( v4_relat_1(X0,X1)
% 0.96/1.01      | ~ r1_tarski(k1_relat_1(X0),X1)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | sK3 != X0 ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_189]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_260,plain,
% 0.96/1.01      ( v4_relat_1(sK3,X0)
% 0.96/1.01      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(unflattening,[status(thm)],[c_259]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_437,plain,
% 0.96/1.01      ( v4_relat_1(sK3,X0_44)
% 0.96/1.01      | ~ r1_tarski(k1_relat_1(sK3),X0_44)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(subtyping,[status(esa)],[c_260]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_448,plain,
% 0.96/1.01      ( v4_relat_1(sK3,X0_44)
% 0.96/1.01      | ~ r1_tarski(k1_relat_1(sK3),X0_44)
% 0.96/1.01      | ~ sP3_iProver_split ),
% 0.96/1.01      inference(splitting,
% 0.96/1.01                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 0.96/1.01                [c_437]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_1015,plain,
% 0.96/1.01      ( v4_relat_1(sK3,sK2)
% 0.96/1.01      | ~ r1_tarski(k1_relat_1(sK3),sK2)
% 0.96/1.01      | ~ sP3_iProver_split ),
% 0.96/1.01      inference(instantiation,[status(thm)],[c_448]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_1021,plain,
% 0.96/1.01      ( v4_relat_1(sK3,sK2) = iProver_top
% 0.96/1.01      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 0.96/1.01      | sP3_iProver_split != iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_1015]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_444,plain,
% 0.96/1.01      ( ~ v4_relat_1(sK3,X0_44)
% 0.96/1.01      | k7_relat_1(sK3,X0_44) = sK3
% 0.96/1.01      | ~ sP1_iProver_split ),
% 0.96/1.01      inference(splitting,
% 0.96/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 0.96/1.01                [c_439]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_934,plain,
% 0.96/1.01      ( ~ v4_relat_1(sK3,sK2)
% 0.96/1.01      | ~ sP1_iProver_split
% 0.96/1.01      | k7_relat_1(sK3,sK2) = sK3 ),
% 0.96/1.01      inference(instantiation,[status(thm)],[c_444]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_935,plain,
% 0.96/1.01      ( k7_relat_1(sK3,sK2) = sK3
% 0.96/1.01      | v4_relat_1(sK3,sK2) != iProver_top
% 0.96/1.01      | sP1_iProver_split != iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_934]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_8,plain,
% 0.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.96/1.01      | ~ v1_funct_1(X0)
% 0.96/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 0.96/1.01      inference(cnf_transformation,[],[f37]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_12,negated_conjecture,
% 0.96/1.01      ( v1_funct_1(sK3) ),
% 0.96/1.01      inference(cnf_transformation,[],[f38]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_146,plain,
% 0.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.96/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 0.96/1.01      | sK3 != X0 ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_147,plain,
% 0.96/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.96/1.01      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 0.96/1.01      inference(unflattening,[status(thm)],[c_146]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_200,plain,
% 0.96/1.01      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | sK3 != sK3 ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_147]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_347,plain,
% 0.96/1.01      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(equality_resolution_simp,[status(thm)],[c_200]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_435,plain,
% 0.96/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | k2_partfun1(X0_44,X0_45,sK3,X1_44) = k7_relat_1(sK3,X1_44) ),
% 0.96/1.01      inference(subtyping,[status(esa)],[c_347]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_783,plain,
% 0.96/1.01      ( k2_partfun1(sK0,sK1,sK3,X0_44) = k7_relat_1(sK3,X0_44) ),
% 0.96/1.01      inference(equality_resolution,[status(thm)],[c_435]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_6,plain,
% 0.96/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 0.96/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.96/1.01      inference(cnf_transformation,[],[f42]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_9,negated_conjecture,
% 0.96/1.01      ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
% 0.96/1.01      inference(cnf_transformation,[],[f41]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_163,plain,
% 0.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.96/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 0.96/1.01      | sK3 != X0
% 0.96/1.01      | sK1 != X2
% 0.96/1.01      | sK0 != X1 ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_164,plain,
% 0.96/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.96/1.01      | sK3 != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 0.96/1.01      inference(unflattening,[status(thm)],[c_163]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_211,plain,
% 0.96/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_164]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_346,plain,
% 0.96/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
% 0.96/1.01      inference(equality_resolution_simp,[status(thm)],[c_211]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_436,plain,
% 0.96/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
% 0.96/1.01      inference(subtyping,[status(esa)],[c_346]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_800,plain,
% 0.96/1.01      ( k7_relat_1(sK3,sK2) != sK3 ),
% 0.96/1.01      inference(demodulation,[status(thm)],[c_783,c_436]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_449,plain,
% 0.96/1.01      ( sP3_iProver_split | sP0_iProver_split ),
% 0.96/1.01      inference(splitting,
% 0.96/1.01                [splitting(split),new_symbols(definition,[])],
% 0.96/1.01                [c_437]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_493,plain,
% 0.96/1.01      ( sP3_iProver_split = iProver_top
% 0.96/1.01      | sP0_iProver_split = iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_445,plain,
% 0.96/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 0.96/1.01      inference(splitting,
% 0.96/1.01                [splitting(split),new_symbols(definition,[])],
% 0.96/1.01                [c_439]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_481,plain,
% 0.96/1.01      ( sP1_iProver_split = iProver_top
% 0.96/1.01      | sP0_iProver_split = iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_5,plain,
% 0.96/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.96/1.01      | v4_relat_1(X0,X1) ),
% 0.96/1.01      inference(cnf_transformation,[],[f34]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_176,plain,
% 0.96/1.01      ( v4_relat_1(X0,X1)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | sK3 != X0 ),
% 0.96/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_177,plain,
% 0.96/1.01      ( v4_relat_1(sK3,X0)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(unflattening,[status(thm)],[c_176]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_440,plain,
% 0.96/1.01      ( v4_relat_1(sK3,X0_44)
% 0.96/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.96/1.01      inference(subtyping,[status(esa)],[c_177]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_478,plain,
% 0.96/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0_44,X0_45)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | v4_relat_1(sK3,X0_44) = iProver_top ),
% 0.96/1.01      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(c_480,plain,
% 0.96/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.96/1.01      | v4_relat_1(sK3,sK0) = iProver_top ),
% 0.96/1.01      inference(instantiation,[status(thm)],[c_478]) ).
% 0.96/1.01  
% 0.96/1.01  cnf(contradiction,plain,
% 0.96/1.01      ( $false ),
% 0.96/1.01      inference(minisat,
% 0.96/1.01                [status(thm)],
% 0.96/1.01                [c_1054,c_1021,c_935,c_800,c_759,c_493,c_487,c_481,c_480,
% 0.96/1.01                 c_473,c_468]) ).
% 0.96/1.01  
% 0.96/1.01  
% 0.96/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.96/1.01  
% 0.96/1.01  ------                               Statistics
% 0.96/1.01  
% 0.96/1.01  ------ General
% 0.96/1.01  
% 0.96/1.01  abstr_ref_over_cycles:                  0
% 0.96/1.01  abstr_ref_under_cycles:                 0
% 0.96/1.01  gc_basic_clause_elim:                   0
% 0.96/1.01  forced_gc_time:                         0
% 0.96/1.01  parsing_time:                           0.017
% 0.96/1.01  unif_index_cands_time:                  0.
% 0.96/1.01  unif_index_add_time:                    0.
% 0.96/1.01  orderings_time:                         0.
% 0.96/1.01  out_proof_time:                         0.007
% 0.96/1.01  total_time:                             0.064
% 0.96/1.01  num_of_symbols:                         52
% 0.96/1.01  num_of_terms:                           981
% 0.96/1.01  
% 0.96/1.01  ------ Preprocessing
% 0.96/1.01  
% 0.96/1.01  num_of_splits:                          6
% 0.96/1.01  num_of_split_atoms:                     4
% 0.96/1.01  num_of_reused_defs:                     2
% 0.96/1.01  num_eq_ax_congr_red:                    12
% 0.96/1.01  num_of_sem_filtered_clauses:            1
% 0.96/1.01  num_of_subtypes:                        5
% 0.96/1.01  monotx_restored_types:                  0
% 0.96/1.01  sat_num_of_epr_types:                   0
% 0.96/1.01  sat_num_of_non_cyclic_types:            0
% 0.96/1.01  sat_guarded_non_collapsed_types:        0
% 0.96/1.01  num_pure_diseq_elim:                    0
% 0.96/1.01  simp_replaced_by:                       0
% 0.96/1.01  res_preprocessed:                       72
% 0.96/1.01  prep_upred:                             0
% 0.96/1.01  prep_unflattend:                        13
% 0.96/1.01  smt_new_axioms:                         0
% 0.96/1.01  pred_elim_cands:                        2
% 0.96/1.01  pred_elim:                              4
% 0.96/1.01  pred_elim_cl:                           5
% 0.96/1.01  pred_elim_cycles:                       6
% 0.96/1.01  merged_defs:                            0
% 0.96/1.01  merged_defs_ncl:                        0
% 0.96/1.01  bin_hyper_res:                          0
% 0.96/1.01  prep_cycles:                            4
% 0.96/1.01  pred_elim_time:                         0.003
% 0.96/1.01  splitting_time:                         0.
% 0.96/1.01  sem_filter_time:                        0.
% 0.96/1.01  monotx_time:                            0.
% 0.96/1.01  subtype_inf_time:                       0.
% 0.96/1.01  
% 0.96/1.01  ------ Problem properties
% 0.96/1.01  
% 0.96/1.01  clauses:                                14
% 0.96/1.01  conjectures:                            1
% 0.96/1.01  epr:                                    5
% 0.96/1.01  horn:                                   11
% 0.96/1.01  ground:                                 5
% 0.96/1.01  unary:                                  2
% 0.96/1.01  binary:                                 8
% 0.96/1.01  lits:                                   30
% 0.96/1.01  lits_eq:                                8
% 0.96/1.01  fd_pure:                                0
% 0.96/1.01  fd_pseudo:                              0
% 0.96/1.01  fd_cond:                                0
% 0.96/1.01  fd_pseudo_cond:                         0
% 0.96/1.01  ac_symbols:                             0
% 0.96/1.01  
% 0.96/1.01  ------ Propositional Solver
% 0.96/1.01  
% 0.96/1.01  prop_solver_calls:                      26
% 0.96/1.01  prop_fast_solver_calls:                 404
% 0.96/1.01  smt_solver_calls:                       0
% 0.96/1.01  smt_fast_solver_calls:                  0
% 0.96/1.01  prop_num_of_clauses:                    293
% 0.96/1.01  prop_preprocess_simplified:             1951
% 0.96/1.01  prop_fo_subsumed:                       8
% 0.96/1.01  prop_solver_time:                       0.
% 0.96/1.01  smt_solver_time:                        0.
% 0.96/1.01  smt_fast_solver_time:                   0.
% 0.96/1.01  prop_fast_solver_time:                  0.
% 0.96/1.01  prop_unsat_core_time:                   0.
% 0.96/1.01  
% 0.96/1.01  ------ QBF
% 0.96/1.01  
% 0.96/1.01  qbf_q_res:                              0
% 0.96/1.01  qbf_num_tautologies:                    0
% 0.96/1.01  qbf_prep_cycles:                        0
% 0.96/1.01  
% 0.96/1.01  ------ BMC1
% 0.96/1.01  
% 0.96/1.01  bmc1_current_bound:                     -1
% 0.96/1.01  bmc1_last_solved_bound:                 -1
% 0.96/1.01  bmc1_unsat_core_size:                   -1
% 0.96/1.01  bmc1_unsat_core_parents_size:           -1
% 0.96/1.01  bmc1_merge_next_fun:                    0
% 0.96/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.96/1.01  
% 0.96/1.01  ------ Instantiation
% 0.96/1.01  
% 0.96/1.01  inst_num_of_clauses:                    100
% 0.96/1.01  inst_num_in_passive:                    25
% 0.96/1.01  inst_num_in_active:                     66
% 0.96/1.01  inst_num_in_unprocessed:                9
% 0.96/1.01  inst_num_of_loops:                      80
% 0.96/1.01  inst_num_of_learning_restarts:          0
% 0.96/1.01  inst_num_moves_active_passive:          10
% 0.96/1.01  inst_lit_activity:                      0
% 0.96/1.01  inst_lit_activity_moves:                0
% 0.96/1.01  inst_num_tautologies:                   0
% 0.96/1.01  inst_num_prop_implied:                  0
% 0.96/1.01  inst_num_existing_simplified:           0
% 0.96/1.01  inst_num_eq_res_simplified:             0
% 0.96/1.01  inst_num_child_elim:                    0
% 0.96/1.01  inst_num_of_dismatching_blockings:      6
% 0.96/1.01  inst_num_of_non_proper_insts:           48
% 0.96/1.01  inst_num_of_duplicates:                 0
% 0.96/1.01  inst_inst_num_from_inst_to_res:         0
% 0.96/1.01  inst_dismatching_checking_time:         0.
% 0.96/1.01  
% 0.96/1.01  ------ Resolution
% 0.96/1.01  
% 0.96/1.01  res_num_of_clauses:                     0
% 0.96/1.01  res_num_in_passive:                     0
% 0.96/1.01  res_num_in_active:                      0
% 0.96/1.01  res_num_of_loops:                       76
% 0.96/1.01  res_forward_subset_subsumed:            6
% 0.96/1.01  res_backward_subset_subsumed:           0
% 0.96/1.01  res_forward_subsumed:                   0
% 0.96/1.01  res_backward_subsumed:                  0
% 0.96/1.01  res_forward_subsumption_resolution:     0
% 0.96/1.01  res_backward_subsumption_resolution:    0
% 0.96/1.01  res_clause_to_clause_subsumption:       22
% 0.96/1.01  res_orphan_elimination:                 0
% 0.96/1.01  res_tautology_del:                      12
% 0.96/1.01  res_num_eq_res_simplified:              2
% 0.96/1.01  res_num_sel_changes:                    0
% 0.96/1.01  res_moves_from_active_to_pass:          0
% 0.96/1.01  
% 0.96/1.01  ------ Superposition
% 0.96/1.01  
% 0.96/1.01  sup_time_total:                         0.
% 0.96/1.01  sup_time_generating:                    0.
% 0.96/1.01  sup_time_sim_full:                      0.
% 0.96/1.01  sup_time_sim_immed:                     0.
% 0.96/1.01  
% 0.96/1.01  sup_num_of_clauses:                     18
% 0.96/1.01  sup_num_in_active:                      14
% 0.96/1.01  sup_num_in_passive:                     4
% 0.96/1.01  sup_num_of_loops:                       14
% 0.96/1.01  sup_fw_superposition:                   2
% 0.96/1.01  sup_bw_superposition:                   2
% 0.96/1.01  sup_immediate_simplified:               0
% 0.96/1.01  sup_given_eliminated:                   0
% 0.96/1.01  comparisons_done:                       0
% 0.96/1.01  comparisons_avoided:                    0
% 0.96/1.01  
% 0.96/1.01  ------ Simplifications
% 0.96/1.01  
% 0.96/1.01  
% 0.96/1.01  sim_fw_subset_subsumed:                 0
% 0.96/1.01  sim_bw_subset_subsumed:                 0
% 0.96/1.01  sim_fw_subsumed:                        0
% 0.96/1.01  sim_bw_subsumed:                        0
% 0.96/1.01  sim_fw_subsumption_res:                 0
% 0.96/1.01  sim_bw_subsumption_res:                 0
% 0.96/1.01  sim_tautology_del:                      0
% 0.96/1.01  sim_eq_tautology_del:                   0
% 0.96/1.01  sim_eq_res_simp:                        0
% 0.96/1.01  sim_fw_demodulated:                     0
% 0.96/1.01  sim_bw_demodulated:                     1
% 0.96/1.01  sim_light_normalised:                   0
% 0.96/1.01  sim_joinable_taut:                      0
% 0.96/1.01  sim_joinable_simp:                      0
% 0.96/1.01  sim_ac_normalised:                      0
% 0.96/1.01  sim_smt_subsumption:                    0
% 0.96/1.01  
%------------------------------------------------------------------------------
