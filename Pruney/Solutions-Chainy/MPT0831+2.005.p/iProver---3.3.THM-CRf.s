%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:36 EST 2020

% Result     : Theorem 0.90s
% Output     : CNFRefutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 319 expanded)
%              Number of clauses        :   71 ( 141 expanded)
%              Number of leaves         :   12 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  274 ( 861 expanded)
%              Number of equality atoms :  108 ( 197 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f21])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f25])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

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

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f35])).

fof(f38,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_173,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_11])).

cnf(c_174,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_173])).

cnf(c_217,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_174])).

cnf(c_218,plain,
    ( ~ v4_relat_1(sK3,X0)
    | r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_408,plain,
    ( ~ v4_relat_1(sK3,X0_43)
    | r1_tarski(k1_relat_1(sK3),X0_43)
    | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(subtyping,[status(esa)],[c_218])).

cnf(c_417,plain,
    ( ~ v4_relat_1(sK3,X0_43)
    | r1_tarski(k1_relat_1(sK3),X0_43)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_408])).

cnf(c_647,plain,
    ( v4_relat_1(sK3,X0_43) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_432,plain,
    ( k2_zfmisc_1(X0_43,X0_44) = k2_zfmisc_1(X1_43,X0_44)
    | X0_43 != X1_43 ),
    theory(equality)).

cnf(c_439,plain,
    ( k2_zfmisc_1(sK1,sK0) = k2_zfmisc_1(sK1,sK0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_423,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_444,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_423])).

cnf(c_3,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_202,plain,
    ( ~ v4_relat_1(X0,X1)
    | k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_174])).

cnf(c_203,plain,
    ( ~ v4_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_409,plain,
    ( ~ v4_relat_1(sK3,X0_43)
    | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k7_relat_1(sK3,X0_43) = sK3 ),
    inference(subtyping,[status(esa)],[c_203])).

cnf(c_414,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_409])).

cnf(c_457,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_459,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sP0_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_418,plain,
    ( sP2_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_408])).

cnf(c_460,plain,
    ( sP2_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_461,plain,
    ( v4_relat_1(sK3,X0_43) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_433,plain,
    ( X0_46 != X1_46
    | k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) ),
    theory(equality)).

cnf(c_732,plain,
    ( k2_zfmisc_1(X0_43,X0_44) != k2_zfmisc_1(sK1,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_733,plain,
    ( k2_zfmisc_1(sK1,sK0) != k2_zfmisc_1(sK1,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_1015,plain,
    ( r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
    | v4_relat_1(sK3,X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_647,c_439,c_444,c_459,c_460,c_461,c_733])).

cnf(c_1016,plain,
    ( v4_relat_1(sK3,X0_43) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_1015])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_412,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_641,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_413,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X0_43)
    | r1_tarski(X2_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_640,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X2_43,X0_43) != iProver_top
    | r1_tarski(X2_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_814,plain,
    ( r1_tarski(X0_43,sK2) = iProver_top
    | r1_tarski(X0_43,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_640])).

cnf(c_1024,plain,
    ( v4_relat_1(sK3,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_814])).

cnf(c_1,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_232,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_174])).

cnf(c_233,plain,
    ( v4_relat_1(sK3,X0)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_407,plain,
    ( v4_relat_1(sK3,X0_43)
    | ~ r1_tarski(k1_relat_1(sK3),X0_43)
    | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(subtyping,[status(esa)],[c_233])).

cnf(c_419,plain,
    ( v4_relat_1(sK3,X0_43)
    | ~ r1_tarski(k1_relat_1(sK3),X0_43)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_407])).

cnf(c_896,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ sP3_iProver_split ),
    inference(instantiation,[status(thm)],[c_419])).

cnf(c_902,plain,
    ( v4_relat_1(sK3,sK2) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_415,plain,
    ( ~ v4_relat_1(sK3,X0_43)
    | k7_relat_1(sK3,X0_43) = sK3
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_409])).

cnf(c_839,plain,
    ( ~ v4_relat_1(sK3,sK2)
    | ~ sP1_iProver_split
    | k7_relat_1(sK3,sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_840,plain,
    ( k7_relat_1(sK3,sK2) = sK3
    | v4_relat_1(sK3,sK2) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_152,plain,
    ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_153,plain,
    ( k5_relset_1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_152])).

cnf(c_411,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k5_relset_1(X0_43,X0_44,sK3,X1_43) = k7_relat_1(sK3,X1_43) ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_730,plain,
    ( k5_relset_1(sK1,sK0,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
    inference(equality_resolution,[status(thm)],[c_411])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_139,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(sK1,sK0,sK3,sK2) != X0
    | sK3 != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_140,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_139])).

cnf(c_185,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_140])).

cnf(c_319,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_185])).

cnf(c_406,plain,
    ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_319])).

cnf(c_752,plain,
    ( k7_relat_1(sK3,sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_730,c_406])).

cnf(c_420,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_407])).

cnf(c_465,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_416,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_409])).

cnf(c_453,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_161,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_162,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_161])).

cnf(c_410,plain,
    ( v4_relat_1(sK3,X0_43)
    | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(subtyping,[status(esa)],[c_162])).

cnf(c_450,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v4_relat_1(sK3,X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_452,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | v4_relat_1(sK3,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_450])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1024,c_902,c_840,c_752,c_733,c_465,c_459,c_453,c_452,c_444,c_439])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n013.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 09:45:09 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.33  % Running in FOF mode
% 0.90/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.90/0.97  
% 0.90/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.90/0.97  
% 0.90/0.97  ------  iProver source info
% 0.90/0.97  
% 0.90/0.97  git: date: 2020-06-30 10:37:57 +0100
% 0.90/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.90/0.97  git: non_committed_changes: false
% 0.90/0.97  git: last_make_outside_of_git: false
% 0.90/0.97  
% 0.90/0.97  ------ 
% 0.90/0.97  
% 0.90/0.97  ------ Input Options
% 0.90/0.97  
% 0.90/0.97  --out_options                           all
% 0.90/0.97  --tptp_safe_out                         true
% 0.90/0.97  --problem_path                          ""
% 0.90/0.97  --include_path                          ""
% 0.90/0.97  --clausifier                            res/vclausify_rel
% 0.90/0.97  --clausifier_options                    --mode clausify
% 0.90/0.97  --stdin                                 false
% 0.90/0.97  --stats_out                             all
% 0.90/0.97  
% 0.90/0.97  ------ General Options
% 0.90/0.97  
% 0.90/0.97  --fof                                   false
% 0.90/0.97  --time_out_real                         305.
% 0.90/0.97  --time_out_virtual                      -1.
% 0.90/0.97  --symbol_type_check                     false
% 0.90/0.97  --clausify_out                          false
% 0.90/0.97  --sig_cnt_out                           false
% 0.90/0.97  --trig_cnt_out                          false
% 0.90/0.97  --trig_cnt_out_tolerance                1.
% 0.90/0.97  --trig_cnt_out_sk_spl                   false
% 0.90/0.97  --abstr_cl_out                          false
% 0.90/0.97  
% 0.90/0.97  ------ Global Options
% 0.90/0.97  
% 0.90/0.97  --schedule                              default
% 0.90/0.97  --add_important_lit                     false
% 0.90/0.97  --prop_solver_per_cl                    1000
% 0.90/0.97  --min_unsat_core                        false
% 0.90/0.97  --soft_assumptions                      false
% 0.90/0.97  --soft_lemma_size                       3
% 0.90/0.97  --prop_impl_unit_size                   0
% 0.90/0.97  --prop_impl_unit                        []
% 0.90/0.97  --share_sel_clauses                     true
% 0.90/0.97  --reset_solvers                         false
% 0.90/0.97  --bc_imp_inh                            [conj_cone]
% 0.90/0.97  --conj_cone_tolerance                   3.
% 0.90/0.97  --extra_neg_conj                        none
% 0.90/0.97  --large_theory_mode                     true
% 0.90/0.97  --prolific_symb_bound                   200
% 0.90/0.97  --lt_threshold                          2000
% 0.90/0.97  --clause_weak_htbl                      true
% 0.90/0.97  --gc_record_bc_elim                     false
% 0.90/0.97  
% 0.90/0.97  ------ Preprocessing Options
% 0.90/0.97  
% 0.90/0.97  --preprocessing_flag                    true
% 0.90/0.97  --time_out_prep_mult                    0.1
% 0.90/0.97  --splitting_mode                        input
% 0.90/0.97  --splitting_grd                         true
% 0.90/0.97  --splitting_cvd                         false
% 0.90/0.97  --splitting_cvd_svl                     false
% 0.90/0.97  --splitting_nvd                         32
% 0.90/0.97  --sub_typing                            true
% 0.90/0.97  --prep_gs_sim                           true
% 0.90/0.97  --prep_unflatten                        true
% 0.90/0.97  --prep_res_sim                          true
% 0.90/0.97  --prep_upred                            true
% 0.90/0.97  --prep_sem_filter                       exhaustive
% 0.90/0.97  --prep_sem_filter_out                   false
% 0.90/0.97  --pred_elim                             true
% 0.90/0.97  --res_sim_input                         true
% 0.90/0.97  --eq_ax_congr_red                       true
% 0.90/0.97  --pure_diseq_elim                       true
% 0.90/0.97  --brand_transform                       false
% 0.90/0.97  --non_eq_to_eq                          false
% 0.90/0.97  --prep_def_merge                        true
% 0.90/0.97  --prep_def_merge_prop_impl              false
% 0.90/0.97  --prep_def_merge_mbd                    true
% 0.90/0.97  --prep_def_merge_tr_red                 false
% 0.90/0.97  --prep_def_merge_tr_cl                  false
% 0.90/0.97  --smt_preprocessing                     true
% 0.90/0.97  --smt_ac_axioms                         fast
% 0.90/0.97  --preprocessed_out                      false
% 0.90/0.97  --preprocessed_stats                    false
% 0.90/0.97  
% 0.90/0.97  ------ Abstraction refinement Options
% 0.90/0.97  
% 0.90/0.97  --abstr_ref                             []
% 0.90/0.97  --abstr_ref_prep                        false
% 0.90/0.97  --abstr_ref_until_sat                   false
% 0.90/0.97  --abstr_ref_sig_restrict                funpre
% 0.90/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.90/0.97  --abstr_ref_under                       []
% 0.90/0.97  
% 0.90/0.97  ------ SAT Options
% 0.90/0.97  
% 0.90/0.97  --sat_mode                              false
% 0.90/0.97  --sat_fm_restart_options                ""
% 0.90/0.97  --sat_gr_def                            false
% 0.90/0.97  --sat_epr_types                         true
% 0.90/0.97  --sat_non_cyclic_types                  false
% 0.90/0.97  --sat_finite_models                     false
% 0.90/0.97  --sat_fm_lemmas                         false
% 0.90/0.97  --sat_fm_prep                           false
% 0.90/0.97  --sat_fm_uc_incr                        true
% 0.90/0.97  --sat_out_model                         small
% 0.90/0.97  --sat_out_clauses                       false
% 0.90/0.97  
% 0.90/0.97  ------ QBF Options
% 0.90/0.97  
% 0.90/0.97  --qbf_mode                              false
% 0.90/0.97  --qbf_elim_univ                         false
% 0.90/0.97  --qbf_dom_inst                          none
% 0.90/0.97  --qbf_dom_pre_inst                      false
% 0.90/0.97  --qbf_sk_in                             false
% 0.90/0.97  --qbf_pred_elim                         true
% 0.90/0.97  --qbf_split                             512
% 0.90/0.97  
% 0.90/0.97  ------ BMC1 Options
% 0.90/0.97  
% 0.90/0.97  --bmc1_incremental                      false
% 0.90/0.97  --bmc1_axioms                           reachable_all
% 0.90/0.97  --bmc1_min_bound                        0
% 0.90/0.97  --bmc1_max_bound                        -1
% 0.90/0.97  --bmc1_max_bound_default                -1
% 0.90/0.97  --bmc1_symbol_reachability              true
% 0.90/0.97  --bmc1_property_lemmas                  false
% 0.90/0.97  --bmc1_k_induction                      false
% 0.90/0.97  --bmc1_non_equiv_states                 false
% 0.90/0.97  --bmc1_deadlock                         false
% 0.90/0.97  --bmc1_ucm                              false
% 0.90/0.97  --bmc1_add_unsat_core                   none
% 0.90/0.97  --bmc1_unsat_core_children              false
% 0.90/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.90/0.97  --bmc1_out_stat                         full
% 0.90/0.97  --bmc1_ground_init                      false
% 0.90/0.97  --bmc1_pre_inst_next_state              false
% 0.90/0.97  --bmc1_pre_inst_state                   false
% 0.90/0.97  --bmc1_pre_inst_reach_state             false
% 0.90/0.97  --bmc1_out_unsat_core                   false
% 0.90/0.97  --bmc1_aig_witness_out                  false
% 0.90/0.97  --bmc1_verbose                          false
% 0.90/0.97  --bmc1_dump_clauses_tptp                false
% 0.90/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.90/0.97  --bmc1_dump_file                        -
% 0.90/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.90/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.90/0.97  --bmc1_ucm_extend_mode                  1
% 0.90/0.97  --bmc1_ucm_init_mode                    2
% 0.90/0.97  --bmc1_ucm_cone_mode                    none
% 0.90/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.90/0.97  --bmc1_ucm_relax_model                  4
% 0.90/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.90/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.90/0.97  --bmc1_ucm_layered_model                none
% 0.90/0.97  --bmc1_ucm_max_lemma_size               10
% 0.90/0.97  
% 0.90/0.97  ------ AIG Options
% 0.90/0.97  
% 0.90/0.97  --aig_mode                              false
% 0.90/0.97  
% 0.90/0.97  ------ Instantiation Options
% 0.90/0.97  
% 0.90/0.97  --instantiation_flag                    true
% 0.90/0.97  --inst_sos_flag                         false
% 0.90/0.97  --inst_sos_phase                        true
% 0.90/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.90/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.90/0.97  --inst_lit_sel_side                     num_symb
% 0.90/0.97  --inst_solver_per_active                1400
% 0.90/0.97  --inst_solver_calls_frac                1.
% 0.90/0.97  --inst_passive_queue_type               priority_queues
% 0.90/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.90/0.97  --inst_passive_queues_freq              [25;2]
% 0.90/0.97  --inst_dismatching                      true
% 0.90/0.97  --inst_eager_unprocessed_to_passive     true
% 0.90/0.97  --inst_prop_sim_given                   true
% 0.90/0.97  --inst_prop_sim_new                     false
% 0.90/0.97  --inst_subs_new                         false
% 0.90/0.97  --inst_eq_res_simp                      false
% 0.90/0.97  --inst_subs_given                       false
% 0.90/0.97  --inst_orphan_elimination               true
% 0.90/0.97  --inst_learning_loop_flag               true
% 0.90/0.97  --inst_learning_start                   3000
% 0.90/0.97  --inst_learning_factor                  2
% 0.90/0.97  --inst_start_prop_sim_after_learn       3
% 0.90/0.97  --inst_sel_renew                        solver
% 0.90/0.97  --inst_lit_activity_flag                true
% 0.90/0.97  --inst_restr_to_given                   false
% 0.90/0.97  --inst_activity_threshold               500
% 0.90/0.97  --inst_out_proof                        true
% 0.90/0.97  
% 0.90/0.97  ------ Resolution Options
% 0.90/0.97  
% 0.90/0.97  --resolution_flag                       true
% 0.90/0.97  --res_lit_sel                           adaptive
% 0.90/0.97  --res_lit_sel_side                      none
% 0.90/0.97  --res_ordering                          kbo
% 0.90/0.97  --res_to_prop_solver                    active
% 0.90/0.97  --res_prop_simpl_new                    false
% 0.90/0.97  --res_prop_simpl_given                  true
% 0.90/0.97  --res_passive_queue_type                priority_queues
% 0.90/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.90/0.97  --res_passive_queues_freq               [15;5]
% 0.90/0.97  --res_forward_subs                      full
% 0.90/0.97  --res_backward_subs                     full
% 0.90/0.97  --res_forward_subs_resolution           true
% 0.90/0.97  --res_backward_subs_resolution          true
% 0.90/0.97  --res_orphan_elimination                true
% 0.90/0.97  --res_time_limit                        2.
% 0.90/0.97  --res_out_proof                         true
% 0.90/0.97  
% 0.90/0.97  ------ Superposition Options
% 0.90/0.97  
% 0.90/0.97  --superposition_flag                    true
% 0.90/0.97  --sup_passive_queue_type                priority_queues
% 0.90/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.90/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.90/0.97  --demod_completeness_check              fast
% 0.90/0.97  --demod_use_ground                      true
% 0.90/0.97  --sup_to_prop_solver                    passive
% 0.90/0.97  --sup_prop_simpl_new                    true
% 0.90/0.97  --sup_prop_simpl_given                  true
% 0.90/0.97  --sup_fun_splitting                     false
% 0.90/0.97  --sup_smt_interval                      50000
% 0.90/0.97  
% 0.90/0.97  ------ Superposition Simplification Setup
% 0.90/0.97  
% 0.90/0.97  --sup_indices_passive                   []
% 0.90/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.90/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.97  --sup_full_bw                           [BwDemod]
% 0.90/0.97  --sup_immed_triv                        [TrivRules]
% 0.90/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.90/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.97  --sup_immed_bw_main                     []
% 0.90/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.90/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/0.97  
% 0.90/0.97  ------ Combination Options
% 0.90/0.97  
% 0.90/0.97  --comb_res_mult                         3
% 0.90/0.97  --comb_sup_mult                         2
% 0.90/0.97  --comb_inst_mult                        10
% 0.90/0.97  
% 0.90/0.97  ------ Debug Options
% 0.90/0.97  
% 0.90/0.97  --dbg_backtrace                         false
% 0.90/0.97  --dbg_dump_prop_clauses                 false
% 0.90/0.97  --dbg_dump_prop_clauses_file            -
% 0.90/0.97  --dbg_out_stat                          false
% 0.90/0.97  ------ Parsing...
% 0.90/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.90/0.97  
% 0.90/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.90/0.97  
% 0.90/0.97  ------ Preprocessing... gs_s  sp: 6 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.90/0.97  
% 0.90/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.90/0.97  ------ Proving...
% 0.90/0.97  ------ Problem Properties 
% 0.90/0.97  
% 0.90/0.97  
% 0.90/0.97  clauses                                 14
% 0.90/0.97  conjectures                             1
% 0.90/0.97  EPR                                     5
% 0.90/0.97  Horn                                    11
% 0.90/0.97  unary                                   2
% 0.90/0.97  binary                                  8
% 0.90/0.97  lits                                    30
% 0.90/0.97  lits eq                                 8
% 0.90/0.97  fd_pure                                 0
% 0.90/0.97  fd_pseudo                               0
% 0.90/0.97  fd_cond                                 0
% 0.90/0.97  fd_pseudo_cond                          0
% 0.90/0.97  AC symbols                              0
% 0.90/0.97  
% 0.90/0.97  ------ Schedule dynamic 5 is on 
% 0.90/0.97  
% 0.90/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.90/0.97  
% 0.90/0.97  
% 0.90/0.97  ------ 
% 0.90/0.97  Current options:
% 0.90/0.97  ------ 
% 0.90/0.97  
% 0.90/0.97  ------ Input Options
% 0.90/0.97  
% 0.90/0.97  --out_options                           all
% 0.90/0.97  --tptp_safe_out                         true
% 0.90/0.97  --problem_path                          ""
% 0.90/0.97  --include_path                          ""
% 0.90/0.97  --clausifier                            res/vclausify_rel
% 0.90/0.97  --clausifier_options                    --mode clausify
% 0.90/0.97  --stdin                                 false
% 0.90/0.97  --stats_out                             all
% 0.90/0.97  
% 0.90/0.97  ------ General Options
% 0.90/0.97  
% 0.90/0.97  --fof                                   false
% 0.90/0.97  --time_out_real                         305.
% 0.90/0.97  --time_out_virtual                      -1.
% 0.90/0.97  --symbol_type_check                     false
% 0.90/0.97  --clausify_out                          false
% 0.90/0.97  --sig_cnt_out                           false
% 0.90/0.97  --trig_cnt_out                          false
% 0.90/0.97  --trig_cnt_out_tolerance                1.
% 0.90/0.97  --trig_cnt_out_sk_spl                   false
% 0.90/0.97  --abstr_cl_out                          false
% 0.90/0.97  
% 0.90/0.97  ------ Global Options
% 0.90/0.97  
% 0.90/0.97  --schedule                              default
% 0.90/0.97  --add_important_lit                     false
% 0.90/0.97  --prop_solver_per_cl                    1000
% 0.90/0.97  --min_unsat_core                        false
% 0.90/0.97  --soft_assumptions                      false
% 0.90/0.97  --soft_lemma_size                       3
% 0.90/0.97  --prop_impl_unit_size                   0
% 0.90/0.97  --prop_impl_unit                        []
% 0.90/0.97  --share_sel_clauses                     true
% 0.90/0.97  --reset_solvers                         false
% 0.90/0.97  --bc_imp_inh                            [conj_cone]
% 0.90/0.97  --conj_cone_tolerance                   3.
% 0.90/0.97  --extra_neg_conj                        none
% 0.90/0.97  --large_theory_mode                     true
% 0.90/0.97  --prolific_symb_bound                   200
% 0.90/0.97  --lt_threshold                          2000
% 0.90/0.97  --clause_weak_htbl                      true
% 0.90/0.97  --gc_record_bc_elim                     false
% 0.90/0.97  
% 0.90/0.97  ------ Preprocessing Options
% 0.90/0.97  
% 0.90/0.97  --preprocessing_flag                    true
% 0.90/0.97  --time_out_prep_mult                    0.1
% 0.90/0.97  --splitting_mode                        input
% 0.90/0.97  --splitting_grd                         true
% 0.90/0.97  --splitting_cvd                         false
% 0.90/0.97  --splitting_cvd_svl                     false
% 0.90/0.97  --splitting_nvd                         32
% 0.90/0.97  --sub_typing                            true
% 0.90/0.97  --prep_gs_sim                           true
% 0.90/0.97  --prep_unflatten                        true
% 0.90/0.97  --prep_res_sim                          true
% 0.90/0.97  --prep_upred                            true
% 0.90/0.97  --prep_sem_filter                       exhaustive
% 0.90/0.97  --prep_sem_filter_out                   false
% 0.90/0.97  --pred_elim                             true
% 0.90/0.97  --res_sim_input                         true
% 0.90/0.97  --eq_ax_congr_red                       true
% 0.90/0.97  --pure_diseq_elim                       true
% 0.90/0.97  --brand_transform                       false
% 0.90/0.97  --non_eq_to_eq                          false
% 0.90/0.97  --prep_def_merge                        true
% 0.90/0.97  --prep_def_merge_prop_impl              false
% 0.90/0.97  --prep_def_merge_mbd                    true
% 0.90/0.97  --prep_def_merge_tr_red                 false
% 0.90/0.97  --prep_def_merge_tr_cl                  false
% 0.90/0.97  --smt_preprocessing                     true
% 0.90/0.97  --smt_ac_axioms                         fast
% 0.90/0.97  --preprocessed_out                      false
% 0.90/0.97  --preprocessed_stats                    false
% 0.90/0.97  
% 0.90/0.97  ------ Abstraction refinement Options
% 0.90/0.97  
% 0.90/0.97  --abstr_ref                             []
% 0.90/0.97  --abstr_ref_prep                        false
% 0.90/0.97  --abstr_ref_until_sat                   false
% 0.90/0.97  --abstr_ref_sig_restrict                funpre
% 0.90/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.90/0.97  --abstr_ref_under                       []
% 0.90/0.97  
% 0.90/0.97  ------ SAT Options
% 0.90/0.97  
% 0.90/0.97  --sat_mode                              false
% 0.90/0.97  --sat_fm_restart_options                ""
% 0.90/0.97  --sat_gr_def                            false
% 0.90/0.97  --sat_epr_types                         true
% 0.90/0.97  --sat_non_cyclic_types                  false
% 0.90/0.97  --sat_finite_models                     false
% 0.90/0.97  --sat_fm_lemmas                         false
% 0.90/0.97  --sat_fm_prep                           false
% 0.90/0.97  --sat_fm_uc_incr                        true
% 0.90/0.97  --sat_out_model                         small
% 0.90/0.97  --sat_out_clauses                       false
% 0.90/0.97  
% 0.90/0.97  ------ QBF Options
% 0.90/0.97  
% 0.90/0.97  --qbf_mode                              false
% 0.90/0.97  --qbf_elim_univ                         false
% 0.90/0.97  --qbf_dom_inst                          none
% 0.90/0.97  --qbf_dom_pre_inst                      false
% 0.90/0.97  --qbf_sk_in                             false
% 0.90/0.97  --qbf_pred_elim                         true
% 0.90/0.97  --qbf_split                             512
% 0.90/0.97  
% 0.90/0.97  ------ BMC1 Options
% 0.90/0.97  
% 0.90/0.97  --bmc1_incremental                      false
% 0.90/0.97  --bmc1_axioms                           reachable_all
% 0.90/0.97  --bmc1_min_bound                        0
% 0.90/0.97  --bmc1_max_bound                        -1
% 0.90/0.97  --bmc1_max_bound_default                -1
% 0.90/0.97  --bmc1_symbol_reachability              true
% 0.90/0.97  --bmc1_property_lemmas                  false
% 0.90/0.97  --bmc1_k_induction                      false
% 0.90/0.97  --bmc1_non_equiv_states                 false
% 0.90/0.97  --bmc1_deadlock                         false
% 0.90/0.97  --bmc1_ucm                              false
% 0.90/0.97  --bmc1_add_unsat_core                   none
% 0.90/0.97  --bmc1_unsat_core_children              false
% 0.90/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.90/0.97  --bmc1_out_stat                         full
% 0.90/0.97  --bmc1_ground_init                      false
% 0.90/0.97  --bmc1_pre_inst_next_state              false
% 0.90/0.97  --bmc1_pre_inst_state                   false
% 0.90/0.97  --bmc1_pre_inst_reach_state             false
% 0.90/0.97  --bmc1_out_unsat_core                   false
% 0.90/0.97  --bmc1_aig_witness_out                  false
% 0.90/0.97  --bmc1_verbose                          false
% 0.90/0.97  --bmc1_dump_clauses_tptp                false
% 0.90/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.90/0.97  --bmc1_dump_file                        -
% 0.90/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.90/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.90/0.97  --bmc1_ucm_extend_mode                  1
% 0.90/0.97  --bmc1_ucm_init_mode                    2
% 0.90/0.97  --bmc1_ucm_cone_mode                    none
% 0.90/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.90/0.97  --bmc1_ucm_relax_model                  4
% 0.90/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.90/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.90/0.97  --bmc1_ucm_layered_model                none
% 0.90/0.97  --bmc1_ucm_max_lemma_size               10
% 0.90/0.97  
% 0.90/0.97  ------ AIG Options
% 0.90/0.97  
% 0.90/0.97  --aig_mode                              false
% 0.90/0.97  
% 0.90/0.97  ------ Instantiation Options
% 0.90/0.97  
% 0.90/0.97  --instantiation_flag                    true
% 0.90/0.97  --inst_sos_flag                         false
% 0.90/0.97  --inst_sos_phase                        true
% 0.90/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.90/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.90/0.97  --inst_lit_sel_side                     none
% 0.90/0.97  --inst_solver_per_active                1400
% 0.90/0.97  --inst_solver_calls_frac                1.
% 0.90/0.97  --inst_passive_queue_type               priority_queues
% 0.90/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.90/0.97  --inst_passive_queues_freq              [25;2]
% 0.90/0.97  --inst_dismatching                      true
% 0.90/0.97  --inst_eager_unprocessed_to_passive     true
% 0.90/0.97  --inst_prop_sim_given                   true
% 0.90/0.97  --inst_prop_sim_new                     false
% 0.90/0.97  --inst_subs_new                         false
% 0.90/0.97  --inst_eq_res_simp                      false
% 0.90/0.97  --inst_subs_given                       false
% 0.90/0.97  --inst_orphan_elimination               true
% 0.90/0.97  --inst_learning_loop_flag               true
% 0.90/0.97  --inst_learning_start                   3000
% 0.90/0.97  --inst_learning_factor                  2
% 0.90/0.97  --inst_start_prop_sim_after_learn       3
% 0.90/0.97  --inst_sel_renew                        solver
% 0.90/0.97  --inst_lit_activity_flag                true
% 0.90/0.97  --inst_restr_to_given                   false
% 0.90/0.97  --inst_activity_threshold               500
% 0.90/0.97  --inst_out_proof                        true
% 0.90/0.97  
% 0.90/0.97  ------ Resolution Options
% 0.90/0.97  
% 0.90/0.97  --resolution_flag                       false
% 0.90/0.97  --res_lit_sel                           adaptive
% 0.90/0.97  --res_lit_sel_side                      none
% 0.90/0.97  --res_ordering                          kbo
% 0.90/0.97  --res_to_prop_solver                    active
% 0.90/0.97  --res_prop_simpl_new                    false
% 0.90/0.97  --res_prop_simpl_given                  true
% 0.90/0.97  --res_passive_queue_type                priority_queues
% 0.90/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.90/0.97  --res_passive_queues_freq               [15;5]
% 0.90/0.97  --res_forward_subs                      full
% 0.90/0.97  --res_backward_subs                     full
% 0.90/0.97  --res_forward_subs_resolution           true
% 0.90/0.97  --res_backward_subs_resolution          true
% 0.90/0.97  --res_orphan_elimination                true
% 0.90/0.97  --res_time_limit                        2.
% 0.90/0.97  --res_out_proof                         true
% 0.90/0.97  
% 0.90/0.97  ------ Superposition Options
% 0.90/0.97  
% 0.90/0.97  --superposition_flag                    true
% 0.90/0.97  --sup_passive_queue_type                priority_queues
% 0.90/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.90/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.90/0.97  --demod_completeness_check              fast
% 0.90/0.97  --demod_use_ground                      true
% 0.90/0.97  --sup_to_prop_solver                    passive
% 0.90/0.97  --sup_prop_simpl_new                    true
% 0.90/0.97  --sup_prop_simpl_given                  true
% 0.90/0.97  --sup_fun_splitting                     false
% 0.90/0.97  --sup_smt_interval                      50000
% 0.90/0.97  
% 0.90/0.97  ------ Superposition Simplification Setup
% 0.90/0.97  
% 0.90/0.97  --sup_indices_passive                   []
% 0.90/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.90/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.90/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.97  --sup_full_bw                           [BwDemod]
% 0.90/0.97  --sup_immed_triv                        [TrivRules]
% 0.90/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.90/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.97  --sup_immed_bw_main                     []
% 0.90/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.90/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.90/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.90/0.97  
% 0.90/0.97  ------ Combination Options
% 0.90/0.97  
% 0.90/0.97  --comb_res_mult                         3
% 0.90/0.97  --comb_sup_mult                         2
% 0.90/0.97  --comb_inst_mult                        10
% 0.90/0.97  
% 0.90/0.97  ------ Debug Options
% 0.90/0.97  
% 0.90/0.97  --dbg_backtrace                         false
% 0.90/0.97  --dbg_dump_prop_clauses                 false
% 0.90/0.97  --dbg_dump_prop_clauses_file            -
% 0.90/0.97  --dbg_out_stat                          false
% 0.90/0.97  
% 0.90/0.97  
% 0.90/0.97  
% 0.90/0.97  
% 0.90/0.97  ------ Proving...
% 0.90/0.97  
% 0.90/0.97  
% 0.90/0.97  % SZS status Theorem for theBenchmark.p
% 0.90/0.97  
% 0.90/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 0.90/0.97  
% 0.90/0.97  fof(f2,axiom,(
% 0.90/0.97    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.97  
% 0.90/0.97  fof(f13,plain,(
% 0.90/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.90/0.97    inference(ennf_transformation,[],[f2])).
% 0.90/0.97  
% 0.90/0.97  fof(f23,plain,(
% 0.90/0.97    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.90/0.97    inference(nnf_transformation,[],[f13])).
% 0.90/0.97  
% 0.90/0.97  fof(f28,plain,(
% 0.90/0.97    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.90/0.97    inference(cnf_transformation,[],[f23])).
% 0.90/0.97  
% 0.90/0.97  fof(f4,axiom,(
% 0.90/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.97  
% 0.90/0.97  fof(f16,plain,(
% 0.90/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.90/0.97    inference(ennf_transformation,[],[f4])).
% 0.90/0.97  
% 0.90/0.97  fof(f31,plain,(
% 0.90/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.90/0.97    inference(cnf_transformation,[],[f16])).
% 0.90/0.97  
% 0.90/0.97  fof(f8,conjecture,(
% 0.90/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.97  
% 0.90/0.97  fof(f9,negated_conjecture,(
% 0.90/0.97    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.90/0.97    inference(negated_conjecture,[],[f8])).
% 0.90/0.97  
% 0.90/0.97  fof(f21,plain,(
% 0.90/0.97    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.90/0.97    inference(ennf_transformation,[],[f9])).
% 0.90/0.97  
% 0.90/0.97  fof(f22,plain,(
% 0.90/0.97    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.90/0.97    inference(flattening,[],[f21])).
% 0.90/0.97  
% 0.90/0.97  fof(f25,plain,(
% 0.90/0.97    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.90/0.97    introduced(choice_axiom,[])).
% 0.90/0.97  
% 0.90/0.97  fof(f26,plain,(
% 0.90/0.97    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.90/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f25])).
% 0.90/0.97  
% 0.90/0.97  fof(f36,plain,(
% 0.90/0.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.90/0.97    inference(cnf_transformation,[],[f26])).
% 0.90/0.97  
% 0.90/0.97  fof(f3,axiom,(
% 0.90/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.97  
% 0.90/0.97  fof(f14,plain,(
% 0.90/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.90/0.97    inference(ennf_transformation,[],[f3])).
% 0.90/0.97  
% 0.90/0.97  fof(f15,plain,(
% 0.90/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.90/0.97    inference(flattening,[],[f14])).
% 0.90/0.97  
% 0.90/0.97  fof(f30,plain,(
% 0.90/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.90/0.97    inference(cnf_transformation,[],[f15])).
% 0.90/0.97  
% 0.90/0.97  fof(f37,plain,(
% 0.90/0.97    r1_tarski(sK1,sK2)),
% 0.90/0.97    inference(cnf_transformation,[],[f26])).
% 0.90/0.97  
% 0.90/0.97  fof(f1,axiom,(
% 0.90/0.97    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.97  
% 0.90/0.97  fof(f11,plain,(
% 0.90/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.90/0.97    inference(ennf_transformation,[],[f1])).
% 0.90/0.97  
% 0.90/0.97  fof(f12,plain,(
% 0.90/0.97    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.90/0.97    inference(flattening,[],[f11])).
% 0.90/0.97  
% 0.90/0.97  fof(f27,plain,(
% 0.90/0.97    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.90/0.97    inference(cnf_transformation,[],[f12])).
% 0.90/0.97  
% 0.90/0.97  fof(f29,plain,(
% 0.90/0.97    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.90/0.97    inference(cnf_transformation,[],[f23])).
% 0.90/0.97  
% 0.90/0.97  fof(f6,axiom,(
% 0.90/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 0.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.97  
% 0.90/0.97  fof(f18,plain,(
% 0.90/0.97    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.90/0.97    inference(ennf_transformation,[],[f6])).
% 0.90/0.97  
% 0.90/0.97  fof(f33,plain,(
% 0.90/0.97    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.90/0.97    inference(cnf_transformation,[],[f18])).
% 0.90/0.97  
% 0.90/0.97  fof(f7,axiom,(
% 0.90/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.97  
% 0.90/0.97  fof(f19,plain,(
% 0.90/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.90/0.97    inference(ennf_transformation,[],[f7])).
% 0.90/0.97  
% 0.90/0.97  fof(f20,plain,(
% 0.90/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.90/0.97    inference(flattening,[],[f19])).
% 0.90/0.97  
% 0.90/0.97  fof(f24,plain,(
% 0.90/0.97    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.90/0.97    inference(nnf_transformation,[],[f20])).
% 0.90/0.97  
% 0.90/0.97  fof(f35,plain,(
% 0.90/0.97    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.90/0.97    inference(cnf_transformation,[],[f24])).
% 0.90/0.97  
% 0.90/0.97  fof(f39,plain,(
% 0.90/0.97    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.90/0.97    inference(equality_resolution,[],[f35])).
% 0.90/0.97  
% 0.90/0.97  fof(f38,plain,(
% 0.90/0.97    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.90/0.97    inference(cnf_transformation,[],[f26])).
% 0.90/0.97  
% 0.90/0.97  fof(f5,axiom,(
% 0.90/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.90/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.90/0.97  
% 0.90/0.97  fof(f10,plain,(
% 0.90/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.90/0.97    inference(pure_predicate_removal,[],[f5])).
% 0.90/0.97  
% 0.90/0.97  fof(f17,plain,(
% 0.90/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.90/0.97    inference(ennf_transformation,[],[f10])).
% 0.90/0.97  
% 0.90/0.97  fof(f32,plain,(
% 0.90/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.90/0.97    inference(cnf_transformation,[],[f17])).
% 0.90/0.97  
% 0.90/0.97  cnf(c_2,plain,
% 0.90/0.97      ( ~ v4_relat_1(X0,X1)
% 0.90/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 0.90/0.97      | ~ v1_relat_1(X0) ),
% 0.90/0.97      inference(cnf_transformation,[],[f28]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_4,plain,
% 0.90/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.90/0.97      | v1_relat_1(X0) ),
% 0.90/0.97      inference(cnf_transformation,[],[f31]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_11,negated_conjecture,
% 0.90/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 0.90/0.97      inference(cnf_transformation,[],[f36]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_173,plain,
% 0.90/0.97      ( v1_relat_1(X0)
% 0.90/0.97      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.97      | sK3 != X0 ),
% 0.90/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_11]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_174,plain,
% 0.90/0.97      ( v1_relat_1(sK3)
% 0.90/0.97      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.97      inference(unflattening,[status(thm)],[c_173]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_217,plain,
% 0.90/0.97      ( ~ v4_relat_1(X0,X1)
% 0.90/0.97      | r1_tarski(k1_relat_1(X0),X1)
% 0.90/0.97      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.97      | sK3 != X0 ),
% 0.90/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_174]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_218,plain,
% 0.90/0.97      ( ~ v4_relat_1(sK3,X0)
% 0.90/0.97      | r1_tarski(k1_relat_1(sK3),X0)
% 0.90/0.97      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.97      inference(unflattening,[status(thm)],[c_217]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_408,plain,
% 0.90/0.97      ( ~ v4_relat_1(sK3,X0_43)
% 0.90/0.97      | r1_tarski(k1_relat_1(sK3),X0_43)
% 0.90/0.97      | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.97      inference(subtyping,[status(esa)],[c_218]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_417,plain,
% 0.90/0.97      ( ~ v4_relat_1(sK3,X0_43)
% 0.90/0.97      | r1_tarski(k1_relat_1(sK3),X0_43)
% 0.90/0.97      | ~ sP2_iProver_split ),
% 0.90/0.97      inference(splitting,
% 0.90/0.97                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 0.90/0.97                [c_408]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_647,plain,
% 0.90/0.97      ( v4_relat_1(sK3,X0_43) != iProver_top
% 0.90/0.97      | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
% 0.90/0.97      | sP2_iProver_split != iProver_top ),
% 0.90/0.97      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_432,plain,
% 0.90/0.97      ( k2_zfmisc_1(X0_43,X0_44) = k2_zfmisc_1(X1_43,X0_44)
% 0.90/0.97      | X0_43 != X1_43 ),
% 0.90/0.97      theory(equality) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_439,plain,
% 0.90/0.97      ( k2_zfmisc_1(sK1,sK0) = k2_zfmisc_1(sK1,sK0) | sK1 != sK1 ),
% 0.90/0.97      inference(instantiation,[status(thm)],[c_432]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_423,plain,( X0_43 = X0_43 ),theory(equality) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_444,plain,
% 0.90/0.97      ( sK1 = sK1 ),
% 0.90/0.97      inference(instantiation,[status(thm)],[c_423]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_3,plain,
% 0.90/0.97      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.90/0.97      inference(cnf_transformation,[],[f30]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_202,plain,
% 0.90/0.97      ( ~ v4_relat_1(X0,X1)
% 0.90/0.97      | k7_relat_1(X0,X1) = X0
% 0.90/0.97      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.97      | sK3 != X0 ),
% 0.90/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_174]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_203,plain,
% 0.90/0.97      ( ~ v4_relat_1(sK3,X0)
% 0.90/0.97      | k7_relat_1(sK3,X0) = sK3
% 0.90/0.97      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.97      inference(unflattening,[status(thm)],[c_202]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_409,plain,
% 0.90/0.97      ( ~ v4_relat_1(sK3,X0_43)
% 0.90/0.97      | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.97      | k7_relat_1(sK3,X0_43) = sK3 ),
% 0.90/0.97      inference(subtyping,[status(esa)],[c_203]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_414,plain,
% 0.90/0.97      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.97      | ~ sP0_iProver_split ),
% 0.90/0.97      inference(splitting,
% 0.90/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.90/0.97                [c_409]) ).
% 0.90/0.97  
% 0.90/0.97  cnf(c_457,plain,
% 0.90/0.97      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.98      | sP0_iProver_split != iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_459,plain,
% 0.90/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.98      | sP0_iProver_split != iProver_top ),
% 0.90/0.98      inference(instantiation,[status(thm)],[c_457]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_418,plain,
% 0.90/0.98      ( sP2_iProver_split | sP0_iProver_split ),
% 0.90/0.98      inference(splitting,
% 0.90/0.98                [splitting(split),new_symbols(definition,[])],
% 0.90/0.98                [c_408]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_460,plain,
% 0.90/0.98      ( sP2_iProver_split = iProver_top
% 0.90/0.98      | sP0_iProver_split = iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_461,plain,
% 0.90/0.98      ( v4_relat_1(sK3,X0_43) != iProver_top
% 0.90/0.98      | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
% 0.90/0.98      | sP2_iProver_split != iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_433,plain,
% 0.90/0.98      ( X0_46 != X1_46 | k1_zfmisc_1(X0_46) = k1_zfmisc_1(X1_46) ),
% 0.90/0.98      theory(equality) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_732,plain,
% 0.90/0.98      ( k2_zfmisc_1(X0_43,X0_44) != k2_zfmisc_1(sK1,sK0)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.98      inference(instantiation,[status(thm)],[c_433]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_733,plain,
% 0.90/0.98      ( k2_zfmisc_1(sK1,sK0) != k2_zfmisc_1(sK1,sK0)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.98      inference(instantiation,[status(thm)],[c_732]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_1015,plain,
% 0.90/0.98      ( r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top
% 0.90/0.98      | v4_relat_1(sK3,X0_43) != iProver_top ),
% 0.90/0.98      inference(global_propositional_subsumption,
% 0.90/0.98                [status(thm)],
% 0.90/0.98                [c_647,c_439,c_444,c_459,c_460,c_461,c_733]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_1016,plain,
% 0.90/0.98      ( v4_relat_1(sK3,X0_43) != iProver_top
% 0.90/0.98      | r1_tarski(k1_relat_1(sK3),X0_43) = iProver_top ),
% 0.90/0.98      inference(renaming,[status(thm)],[c_1015]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_10,negated_conjecture,
% 0.90/0.98      ( r1_tarski(sK1,sK2) ),
% 0.90/0.98      inference(cnf_transformation,[],[f37]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_412,negated_conjecture,
% 0.90/0.98      ( r1_tarski(sK1,sK2) ),
% 0.90/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_641,plain,
% 0.90/0.98      ( r1_tarski(sK1,sK2) = iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_0,plain,
% 0.90/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 0.90/0.98      inference(cnf_transformation,[],[f27]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_413,plain,
% 0.90/0.98      ( ~ r1_tarski(X0_43,X1_43)
% 0.90/0.98      | ~ r1_tarski(X2_43,X0_43)
% 0.90/0.98      | r1_tarski(X2_43,X1_43) ),
% 0.90/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_640,plain,
% 0.90/0.98      ( r1_tarski(X0_43,X1_43) != iProver_top
% 0.90/0.98      | r1_tarski(X2_43,X0_43) != iProver_top
% 0.90/0.98      | r1_tarski(X2_43,X1_43) = iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_814,plain,
% 0.90/0.98      ( r1_tarski(X0_43,sK2) = iProver_top
% 0.90/0.98      | r1_tarski(X0_43,sK1) != iProver_top ),
% 0.90/0.98      inference(superposition,[status(thm)],[c_641,c_640]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_1024,plain,
% 0.90/0.98      ( v4_relat_1(sK3,sK1) != iProver_top
% 0.90/0.98      | r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 0.90/0.98      inference(superposition,[status(thm)],[c_1016,c_814]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_1,plain,
% 0.90/0.98      ( v4_relat_1(X0,X1)
% 0.90/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 0.90/0.98      | ~ v1_relat_1(X0) ),
% 0.90/0.98      inference(cnf_transformation,[],[f29]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_232,plain,
% 0.90/0.98      ( v4_relat_1(X0,X1)
% 0.90/0.98      | ~ r1_tarski(k1_relat_1(X0),X1)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.98      | sK3 != X0 ),
% 0.90/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_174]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_233,plain,
% 0.90/0.98      ( v4_relat_1(sK3,X0)
% 0.90/0.98      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.98      inference(unflattening,[status(thm)],[c_232]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_407,plain,
% 0.90/0.98      ( v4_relat_1(sK3,X0_43)
% 0.90/0.98      | ~ r1_tarski(k1_relat_1(sK3),X0_43)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.98      inference(subtyping,[status(esa)],[c_233]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_419,plain,
% 0.90/0.98      ( v4_relat_1(sK3,X0_43)
% 0.90/0.98      | ~ r1_tarski(k1_relat_1(sK3),X0_43)
% 0.90/0.98      | ~ sP3_iProver_split ),
% 0.90/0.98      inference(splitting,
% 0.90/0.98                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 0.90/0.98                [c_407]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_896,plain,
% 0.90/0.98      ( v4_relat_1(sK3,sK2)
% 0.90/0.98      | ~ r1_tarski(k1_relat_1(sK3),sK2)
% 0.90/0.98      | ~ sP3_iProver_split ),
% 0.90/0.98      inference(instantiation,[status(thm)],[c_419]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_902,plain,
% 0.90/0.98      ( v4_relat_1(sK3,sK2) = iProver_top
% 0.90/0.98      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top
% 0.90/0.98      | sP3_iProver_split != iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_896]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_415,plain,
% 0.90/0.98      ( ~ v4_relat_1(sK3,X0_43)
% 0.90/0.98      | k7_relat_1(sK3,X0_43) = sK3
% 0.90/0.98      | ~ sP1_iProver_split ),
% 0.90/0.98      inference(splitting,
% 0.90/0.98                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 0.90/0.98                [c_409]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_839,plain,
% 0.90/0.98      ( ~ v4_relat_1(sK3,sK2)
% 0.90/0.98      | ~ sP1_iProver_split
% 0.90/0.98      | k7_relat_1(sK3,sK2) = sK3 ),
% 0.90/0.98      inference(instantiation,[status(thm)],[c_415]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_840,plain,
% 0.90/0.98      ( k7_relat_1(sK3,sK2) = sK3
% 0.90/0.98      | v4_relat_1(sK3,sK2) != iProver_top
% 0.90/0.98      | sP1_iProver_split != iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_6,plain,
% 0.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.90/0.98      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 0.90/0.98      inference(cnf_transformation,[],[f33]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_152,plain,
% 0.90/0.98      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.98      | sK3 != X2 ),
% 0.90/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_11]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_153,plain,
% 0.90/0.98      ( k5_relset_1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.98      inference(unflattening,[status(thm)],[c_152]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_411,plain,
% 0.90/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.98      | k5_relset_1(X0_43,X0_44,sK3,X1_43) = k7_relat_1(sK3,X1_43) ),
% 0.90/0.98      inference(subtyping,[status(esa)],[c_153]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_730,plain,
% 0.90/0.98      ( k5_relset_1(sK1,sK0,sK3,X0_43) = k7_relat_1(sK3,X0_43) ),
% 0.90/0.98      inference(equality_resolution,[status(thm)],[c_411]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_7,plain,
% 0.90/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 0.90/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.90/0.98      inference(cnf_transformation,[],[f39]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_9,negated_conjecture,
% 0.90/0.98      ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
% 0.90/0.98      inference(cnf_transformation,[],[f38]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_139,plain,
% 0.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.90/0.98      | k5_relset_1(sK1,sK0,sK3,sK2) != X0
% 0.90/0.98      | sK3 != X0
% 0.90/0.98      | sK0 != X2
% 0.90/0.98      | sK1 != X1 ),
% 0.90/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_140,plain,
% 0.90/0.98      ( ~ m1_subset_1(k5_relset_1(sK1,sK0,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 0.90/0.98      | sK3 != k5_relset_1(sK1,sK0,sK3,sK2) ),
% 0.90/0.98      inference(unflattening,[status(thm)],[c_139]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_185,plain,
% 0.90/0.98      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_140]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_319,plain,
% 0.90/0.98      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
% 0.90/0.98      inference(equality_resolution_simp,[status(thm)],[c_185]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_406,plain,
% 0.90/0.98      ( k5_relset_1(sK1,sK0,sK3,sK2) != sK3 ),
% 0.90/0.98      inference(subtyping,[status(esa)],[c_319]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_752,plain,
% 0.90/0.98      ( k7_relat_1(sK3,sK2) != sK3 ),
% 0.90/0.98      inference(demodulation,[status(thm)],[c_730,c_406]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_420,plain,
% 0.90/0.98      ( sP3_iProver_split | sP0_iProver_split ),
% 0.90/0.98      inference(splitting,
% 0.90/0.98                [splitting(split),new_symbols(definition,[])],
% 0.90/0.98                [c_407]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_465,plain,
% 0.90/0.98      ( sP3_iProver_split = iProver_top
% 0.90/0.98      | sP0_iProver_split = iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_416,plain,
% 0.90/0.98      ( sP1_iProver_split | sP0_iProver_split ),
% 0.90/0.98      inference(splitting,
% 0.90/0.98                [splitting(split),new_symbols(definition,[])],
% 0.90/0.98                [c_409]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_453,plain,
% 0.90/0.98      ( sP1_iProver_split = iProver_top
% 0.90/0.98      | sP0_iProver_split = iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_5,plain,
% 0.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.90/0.98      | v4_relat_1(X0,X1) ),
% 0.90/0.98      inference(cnf_transformation,[],[f32]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_161,plain,
% 0.90/0.98      ( v4_relat_1(X0,X1)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.98      | sK3 != X0 ),
% 0.90/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_162,plain,
% 0.90/0.98      ( v4_relat_1(sK3,X0)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.98      inference(unflattening,[status(thm)],[c_161]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_410,plain,
% 0.90/0.98      ( v4_relat_1(sK3,X0_43)
% 0.90/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.90/0.98      inference(subtyping,[status(esa)],[c_162]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_450,plain,
% 0.90/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.98      | v4_relat_1(sK3,X0_43) = iProver_top ),
% 0.90/0.98      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(c_452,plain,
% 0.90/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.90/0.98      | v4_relat_1(sK3,sK1) = iProver_top ),
% 0.90/0.98      inference(instantiation,[status(thm)],[c_450]) ).
% 0.90/0.98  
% 0.90/0.98  cnf(contradiction,plain,
% 0.90/0.98      ( $false ),
% 0.90/0.98      inference(minisat,
% 0.90/0.98                [status(thm)],
% 0.90/0.98                [c_1024,c_902,c_840,c_752,c_733,c_465,c_459,c_453,c_452,
% 0.90/0.98                 c_444,c_439]) ).
% 0.90/0.98  
% 0.90/0.98  
% 0.90/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.90/0.98  
% 0.90/0.98  ------                               Statistics
% 0.90/0.98  
% 0.90/0.98  ------ General
% 0.90/0.98  
% 0.90/0.98  abstr_ref_over_cycles:                  0
% 0.90/0.98  abstr_ref_under_cycles:                 0
% 0.90/0.98  gc_basic_clause_elim:                   0
% 0.90/0.98  forced_gc_time:                         0
% 0.90/0.98  parsing_time:                           0.019
% 0.90/0.98  unif_index_cands_time:                  0.
% 0.90/0.98  unif_index_add_time:                    0.
% 0.90/0.98  orderings_time:                         0.
% 0.90/0.98  out_proof_time:                         0.009
% 0.90/0.98  total_time:                             0.073
% 0.90/0.98  num_of_symbols:                         51
% 0.90/0.98  num_of_terms:                           935
% 0.90/0.98  
% 0.90/0.98  ------ Preprocessing
% 0.90/0.98  
% 0.90/0.98  num_of_splits:                          6
% 0.90/0.98  num_of_split_atoms:                     4
% 0.90/0.98  num_of_reused_defs:                     2
% 0.90/0.98  num_eq_ax_congr_red:                    12
% 0.90/0.98  num_of_sem_filtered_clauses:            1
% 0.90/0.98  num_of_subtypes:                        5
% 0.90/0.98  monotx_restored_types:                  0
% 0.90/0.98  sat_num_of_epr_types:                   0
% 0.90/0.98  sat_num_of_non_cyclic_types:            0
% 0.90/0.98  sat_guarded_non_collapsed_types:        0
% 0.90/0.98  num_pure_diseq_elim:                    0
% 0.90/0.98  simp_replaced_by:                       0
% 0.90/0.98  res_preprocessed:                       71
% 0.90/0.98  prep_upred:                             0
% 0.90/0.98  prep_unflattend:                        13
% 0.90/0.98  smt_new_axioms:                         0
% 0.90/0.98  pred_elim_cands:                        2
% 0.90/0.98  pred_elim:                              3
% 0.90/0.98  pred_elim_cl:                           4
% 0.90/0.98  pred_elim_cycles:                       5
% 0.90/0.98  merged_defs:                            0
% 0.90/0.98  merged_defs_ncl:                        0
% 0.90/0.98  bin_hyper_res:                          0
% 0.90/0.98  prep_cycles:                            4
% 0.90/0.98  pred_elim_time:                         0.005
% 0.90/0.98  splitting_time:                         0.
% 0.90/0.98  sem_filter_time:                        0.
% 0.90/0.98  monotx_time:                            0.
% 0.90/0.98  subtype_inf_time:                       0.
% 0.90/0.98  
% 0.90/0.98  ------ Problem properties
% 0.90/0.98  
% 0.90/0.98  clauses:                                14
% 0.90/0.98  conjectures:                            1
% 0.90/0.98  epr:                                    5
% 0.90/0.98  horn:                                   11
% 0.90/0.98  ground:                                 5
% 0.90/0.98  unary:                                  2
% 0.90/0.98  binary:                                 8
% 0.90/0.98  lits:                                   30
% 0.90/0.98  lits_eq:                                8
% 0.90/0.98  fd_pure:                                0
% 0.90/0.98  fd_pseudo:                              0
% 0.90/0.98  fd_cond:                                0
% 0.90/0.98  fd_pseudo_cond:                         0
% 0.90/0.98  ac_symbols:                             0
% 0.90/0.98  
% 0.90/0.98  ------ Propositional Solver
% 0.90/0.98  
% 0.90/0.98  prop_solver_calls:                      26
% 0.90/0.98  prop_fast_solver_calls:                 397
% 0.90/0.98  smt_solver_calls:                       0
% 0.90/0.98  smt_fast_solver_calls:                  0
% 0.90/0.98  prop_num_of_clauses:                    279
% 0.90/0.98  prop_preprocess_simplified:             1933
% 0.90/0.98  prop_fo_subsumed:                       8
% 0.90/0.98  prop_solver_time:                       0.
% 0.90/0.98  smt_solver_time:                        0.
% 0.90/0.98  smt_fast_solver_time:                   0.
% 0.90/0.98  prop_fast_solver_time:                  0.
% 0.90/0.98  prop_unsat_core_time:                   0.
% 0.90/0.98  
% 0.90/0.98  ------ QBF
% 0.90/0.98  
% 0.90/0.98  qbf_q_res:                              0
% 0.90/0.98  qbf_num_tautologies:                    0
% 0.90/0.98  qbf_prep_cycles:                        0
% 0.90/0.98  
% 0.90/0.98  ------ BMC1
% 0.90/0.98  
% 0.90/0.98  bmc1_current_bound:                     -1
% 0.90/0.98  bmc1_last_solved_bound:                 -1
% 0.90/0.98  bmc1_unsat_core_size:                   -1
% 0.90/0.98  bmc1_unsat_core_parents_size:           -1
% 0.90/0.98  bmc1_merge_next_fun:                    0
% 0.90/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.90/0.98  
% 0.90/0.98  ------ Instantiation
% 0.90/0.98  
% 0.90/0.98  inst_num_of_clauses:                    100
% 0.90/0.98  inst_num_in_passive:                    0
% 0.90/0.98  inst_num_in_active:                     67
% 0.90/0.98  inst_num_in_unprocessed:                33
% 0.90/0.98  inst_num_of_loops:                      80
% 0.90/0.98  inst_num_of_learning_restarts:          0
% 0.90/0.98  inst_num_moves_active_passive:          10
% 0.90/0.98  inst_lit_activity:                      0
% 0.90/0.98  inst_lit_activity_moves:                0
% 0.90/0.98  inst_num_tautologies:                   0
% 0.90/0.98  inst_num_prop_implied:                  0
% 0.90/0.98  inst_num_existing_simplified:           0
% 0.90/0.98  inst_num_eq_res_simplified:             0
% 0.90/0.98  inst_num_child_elim:                    0
% 0.90/0.98  inst_num_of_dismatching_blockings:      6
% 0.90/0.98  inst_num_of_non_proper_insts:           45
% 0.90/0.98  inst_num_of_duplicates:                 0
% 0.90/0.98  inst_inst_num_from_inst_to_res:         0
% 0.90/0.98  inst_dismatching_checking_time:         0.
% 0.90/0.98  
% 0.90/0.98  ------ Resolution
% 0.90/0.98  
% 0.90/0.98  res_num_of_clauses:                     0
% 0.90/0.98  res_num_in_passive:                     0
% 0.90/0.98  res_num_in_active:                      0
% 0.90/0.98  res_num_of_loops:                       75
% 0.90/0.98  res_forward_subset_subsumed:            5
% 0.90/0.98  res_backward_subset_subsumed:           0
% 0.90/0.98  res_forward_subsumed:                   0
% 0.90/0.98  res_backward_subsumed:                  0
% 0.90/0.98  res_forward_subsumption_resolution:     0
% 0.90/0.98  res_backward_subsumption_resolution:    0
% 0.90/0.98  res_clause_to_clause_subsumption:       22
% 0.90/0.98  res_orphan_elimination:                 0
% 0.90/0.98  res_tautology_del:                      13
% 0.90/0.98  res_num_eq_res_simplified:              1
% 0.90/0.98  res_num_sel_changes:                    0
% 0.90/0.98  res_moves_from_active_to_pass:          0
% 0.90/0.98  
% 0.90/0.98  ------ Superposition
% 0.90/0.98  
% 0.90/0.98  sup_time_total:                         0.
% 0.90/0.98  sup_time_generating:                    0.
% 0.90/0.98  sup_time_sim_full:                      0.
% 0.90/0.98  sup_time_sim_immed:                     0.
% 0.90/0.98  
% 0.90/0.98  sup_num_of_clauses:                     18
% 0.90/0.98  sup_num_in_active:                      14
% 0.90/0.98  sup_num_in_passive:                     4
% 0.90/0.98  sup_num_of_loops:                       14
% 0.90/0.98  sup_fw_superposition:                   2
% 0.90/0.98  sup_bw_superposition:                   2
% 0.90/0.98  sup_immediate_simplified:               0
% 0.90/0.98  sup_given_eliminated:                   0
% 0.90/0.98  comparisons_done:                       0
% 0.90/0.98  comparisons_avoided:                    0
% 0.90/0.98  
% 0.90/0.98  ------ Simplifications
% 0.90/0.98  
% 0.90/0.98  
% 0.90/0.98  sim_fw_subset_subsumed:                 0
% 0.90/0.98  sim_bw_subset_subsumed:                 0
% 0.90/0.98  sim_fw_subsumed:                        0
% 0.90/0.98  sim_bw_subsumed:                        0
% 0.90/0.98  sim_fw_subsumption_res:                 0
% 0.90/0.98  sim_bw_subsumption_res:                 0
% 0.90/0.98  sim_tautology_del:                      0
% 0.90/0.98  sim_eq_tautology_del:                   0
% 0.90/0.98  sim_eq_res_simp:                        0
% 0.90/0.98  sim_fw_demodulated:                     0
% 0.90/0.98  sim_bw_demodulated:                     1
% 0.90/0.98  sim_light_normalised:                   0
% 0.90/0.98  sim_joinable_taut:                      0
% 0.90/0.98  sim_joinable_simp:                      0
% 0.90/0.98  sim_ac_normalised:                      0
% 0.90/0.98  sim_smt_subsumption:                    0
% 0.90/0.98  
%------------------------------------------------------------------------------
