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
% DateTime   : Thu Dec  3 12:04:06 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 180 expanded)
%              Number of clauses        :   46 (  65 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  210 ( 569 expanded)
%              Number of equality atoms :   87 ( 114 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f24,plain,
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

fof(f25,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    & r1_tarski(sK0,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f24])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f31])).

fof(f36,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_266,plain,
    ( X0_42 != X1_42
    | X2_42 != X1_42
    | X2_42 = X0_42 ),
    theory(equality)).

cnf(c_318,plain,
    ( k7_relat_1(sK3,sK2) != X0_42
    | sK3 != X0_42
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_319,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK3 = k7_relat_1(sK3,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_157,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_1])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_161,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_157,c_3,c_2,c_1])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_215,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_161,c_9])).

cnf(c_216,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_262,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k7_relat_1(sK3,X0_43) = sK3 ),
    inference(subtyping,[status(esa)],[c_216])).

cnf(c_301,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_262])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_127,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X1)
    | sK2 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_128,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_127])).

cnf(c_177,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK0) ),
    inference(resolution,[status(thm)],[c_2,c_128])).

cnf(c_206,plain,
    ( k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_177,c_9])).

cnf(c_207,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_263,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_207])).

cnf(c_274,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_265,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_291,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_302,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_263,c_274,c_291])).

cnf(c_314,plain,
    ( k7_relat_1(sK3,sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_301,c_302])).

cnf(c_297,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0_42
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0_42 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_311,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_10,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_143,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_224,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_143])).

cnf(c_252,plain,
    ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_224])).

cnf(c_260,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k2_partfun1(X0_43,X0_44,sK3,X1_43) = k7_relat_1(sK3,X1_43) ),
    inference(subtyping,[status(esa)],[c_252])).

cnf(c_310,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_260])).

cnf(c_4,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_7])).

cnf(c_194,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK3 != k2_partfun1(sK0,sK1,sK3,sK2) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_235,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution_lifted,[status(thm)],[c_9,c_194])).

cnf(c_251,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_235])).

cnf(c_261,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_251])).

cnf(c_264,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_272,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_319,c_314,c_311,c_310,c_291,c_261,c_272])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n025.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 16:59:20 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 0.88/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.88/0.97  
% 0.88/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.88/0.97  
% 0.88/0.97  ------  iProver source info
% 0.88/0.97  
% 0.88/0.97  git: date: 2020-06-30 10:37:57 +0100
% 0.88/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.88/0.97  git: non_committed_changes: false
% 0.88/0.97  git: last_make_outside_of_git: false
% 0.88/0.97  
% 0.88/0.97  ------ 
% 0.88/0.97  
% 0.88/0.97  ------ Input Options
% 0.88/0.97  
% 0.88/0.97  --out_options                           all
% 0.88/0.97  --tptp_safe_out                         true
% 0.88/0.97  --problem_path                          ""
% 0.88/0.97  --include_path                          ""
% 0.88/0.97  --clausifier                            res/vclausify_rel
% 0.88/0.97  --clausifier_options                    --mode clausify
% 0.88/0.97  --stdin                                 false
% 0.88/0.97  --stats_out                             all
% 0.88/0.97  
% 0.88/0.97  ------ General Options
% 0.88/0.97  
% 0.88/0.97  --fof                                   false
% 0.88/0.97  --time_out_real                         305.
% 0.88/0.97  --time_out_virtual                      -1.
% 0.88/0.97  --symbol_type_check                     false
% 0.88/0.97  --clausify_out                          false
% 0.88/0.97  --sig_cnt_out                           false
% 0.88/0.97  --trig_cnt_out                          false
% 0.88/0.97  --trig_cnt_out_tolerance                1.
% 0.88/0.97  --trig_cnt_out_sk_spl                   false
% 0.88/0.97  --abstr_cl_out                          false
% 0.88/0.97  
% 0.88/0.97  ------ Global Options
% 0.88/0.97  
% 0.88/0.97  --schedule                              default
% 0.88/0.97  --add_important_lit                     false
% 0.88/0.97  --prop_solver_per_cl                    1000
% 0.88/0.97  --min_unsat_core                        false
% 0.88/0.97  --soft_assumptions                      false
% 0.88/0.97  --soft_lemma_size                       3
% 0.88/0.97  --prop_impl_unit_size                   0
% 0.88/0.97  --prop_impl_unit                        []
% 0.88/0.97  --share_sel_clauses                     true
% 0.88/0.97  --reset_solvers                         false
% 0.88/0.97  --bc_imp_inh                            [conj_cone]
% 0.88/0.97  --conj_cone_tolerance                   3.
% 0.88/0.97  --extra_neg_conj                        none
% 0.88/0.97  --large_theory_mode                     true
% 0.88/0.97  --prolific_symb_bound                   200
% 0.88/0.97  --lt_threshold                          2000
% 0.88/0.97  --clause_weak_htbl                      true
% 0.88/0.97  --gc_record_bc_elim                     false
% 0.88/0.97  
% 0.88/0.97  ------ Preprocessing Options
% 0.88/0.97  
% 0.88/0.97  --preprocessing_flag                    true
% 0.88/0.97  --time_out_prep_mult                    0.1
% 0.88/0.97  --splitting_mode                        input
% 0.88/0.97  --splitting_grd                         true
% 0.88/0.97  --splitting_cvd                         false
% 0.88/0.97  --splitting_cvd_svl                     false
% 0.88/0.97  --splitting_nvd                         32
% 0.88/0.97  --sub_typing                            true
% 0.88/0.97  --prep_gs_sim                           true
% 0.88/0.97  --prep_unflatten                        true
% 0.88/0.97  --prep_res_sim                          true
% 0.88/0.97  --prep_upred                            true
% 0.88/0.97  --prep_sem_filter                       exhaustive
% 0.88/0.97  --prep_sem_filter_out                   false
% 0.88/0.97  --pred_elim                             true
% 0.88/0.97  --res_sim_input                         true
% 0.88/0.97  --eq_ax_congr_red                       true
% 0.88/0.97  --pure_diseq_elim                       true
% 0.88/0.97  --brand_transform                       false
% 0.88/0.97  --non_eq_to_eq                          false
% 0.88/0.97  --prep_def_merge                        true
% 0.88/0.97  --prep_def_merge_prop_impl              false
% 0.88/0.97  --prep_def_merge_mbd                    true
% 0.88/0.97  --prep_def_merge_tr_red                 false
% 0.88/0.97  --prep_def_merge_tr_cl                  false
% 0.88/0.97  --smt_preprocessing                     true
% 0.88/0.97  --smt_ac_axioms                         fast
% 0.88/0.97  --preprocessed_out                      false
% 0.88/0.97  --preprocessed_stats                    false
% 0.88/0.97  
% 0.88/0.97  ------ Abstraction refinement Options
% 0.88/0.97  
% 0.88/0.97  --abstr_ref                             []
% 0.88/0.97  --abstr_ref_prep                        false
% 0.88/0.97  --abstr_ref_until_sat                   false
% 0.88/0.97  --abstr_ref_sig_restrict                funpre
% 0.88/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/0.97  --abstr_ref_under                       []
% 0.88/0.97  
% 0.88/0.97  ------ SAT Options
% 0.88/0.97  
% 0.88/0.97  --sat_mode                              false
% 0.88/0.97  --sat_fm_restart_options                ""
% 0.88/0.97  --sat_gr_def                            false
% 0.88/0.97  --sat_epr_types                         true
% 0.88/0.97  --sat_non_cyclic_types                  false
% 0.88/0.97  --sat_finite_models                     false
% 0.88/0.97  --sat_fm_lemmas                         false
% 0.88/0.97  --sat_fm_prep                           false
% 0.88/0.97  --sat_fm_uc_incr                        true
% 0.88/0.97  --sat_out_model                         small
% 0.88/0.97  --sat_out_clauses                       false
% 0.88/0.97  
% 0.88/0.97  ------ QBF Options
% 0.88/0.97  
% 0.88/0.97  --qbf_mode                              false
% 0.88/0.97  --qbf_elim_univ                         false
% 0.88/0.97  --qbf_dom_inst                          none
% 0.88/0.97  --qbf_dom_pre_inst                      false
% 0.88/0.97  --qbf_sk_in                             false
% 0.88/0.97  --qbf_pred_elim                         true
% 0.88/0.97  --qbf_split                             512
% 0.88/0.97  
% 0.88/0.97  ------ BMC1 Options
% 0.88/0.97  
% 0.88/0.97  --bmc1_incremental                      false
% 0.88/0.97  --bmc1_axioms                           reachable_all
% 0.88/0.97  --bmc1_min_bound                        0
% 0.88/0.97  --bmc1_max_bound                        -1
% 0.88/0.97  --bmc1_max_bound_default                -1
% 0.88/0.97  --bmc1_symbol_reachability              true
% 0.88/0.97  --bmc1_property_lemmas                  false
% 0.88/0.97  --bmc1_k_induction                      false
% 0.88/0.97  --bmc1_non_equiv_states                 false
% 0.88/0.97  --bmc1_deadlock                         false
% 0.88/0.97  --bmc1_ucm                              false
% 0.88/0.97  --bmc1_add_unsat_core                   none
% 0.88/0.97  --bmc1_unsat_core_children              false
% 0.88/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/0.97  --bmc1_out_stat                         full
% 0.88/0.97  --bmc1_ground_init                      false
% 0.88/0.97  --bmc1_pre_inst_next_state              false
% 0.88/0.97  --bmc1_pre_inst_state                   false
% 0.88/0.97  --bmc1_pre_inst_reach_state             false
% 0.88/0.97  --bmc1_out_unsat_core                   false
% 0.88/0.97  --bmc1_aig_witness_out                  false
% 0.88/0.97  --bmc1_verbose                          false
% 0.88/0.97  --bmc1_dump_clauses_tptp                false
% 0.88/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.88/0.97  --bmc1_dump_file                        -
% 0.88/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.88/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.88/0.97  --bmc1_ucm_extend_mode                  1
% 0.88/0.97  --bmc1_ucm_init_mode                    2
% 0.88/0.97  --bmc1_ucm_cone_mode                    none
% 0.88/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.88/0.97  --bmc1_ucm_relax_model                  4
% 0.88/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.88/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/0.97  --bmc1_ucm_layered_model                none
% 0.88/0.97  --bmc1_ucm_max_lemma_size               10
% 0.88/0.97  
% 0.88/0.97  ------ AIG Options
% 0.88/0.97  
% 0.88/0.97  --aig_mode                              false
% 0.88/0.97  
% 0.88/0.97  ------ Instantiation Options
% 0.88/0.97  
% 0.88/0.97  --instantiation_flag                    true
% 0.88/0.97  --inst_sos_flag                         false
% 0.88/0.97  --inst_sos_phase                        true
% 0.88/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/0.97  --inst_lit_sel_side                     num_symb
% 0.88/0.97  --inst_solver_per_active                1400
% 0.88/0.97  --inst_solver_calls_frac                1.
% 0.88/0.97  --inst_passive_queue_type               priority_queues
% 0.88/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.88/0.97  --inst_passive_queues_freq              [25;2]
% 0.88/0.97  --inst_dismatching                      true
% 0.88/0.97  --inst_eager_unprocessed_to_passive     true
% 0.88/0.97  --inst_prop_sim_given                   true
% 0.88/0.97  --inst_prop_sim_new                     false
% 0.88/0.97  --inst_subs_new                         false
% 0.88/0.97  --inst_eq_res_simp                      false
% 0.88/0.97  --inst_subs_given                       false
% 0.88/0.97  --inst_orphan_elimination               true
% 0.88/0.97  --inst_learning_loop_flag               true
% 0.88/0.97  --inst_learning_start                   3000
% 0.88/0.97  --inst_learning_factor                  2
% 0.88/0.97  --inst_start_prop_sim_after_learn       3
% 0.88/0.97  --inst_sel_renew                        solver
% 0.88/0.97  --inst_lit_activity_flag                true
% 0.88/0.97  --inst_restr_to_given                   false
% 0.88/0.97  --inst_activity_threshold               500
% 0.88/0.97  --inst_out_proof                        true
% 0.88/0.97  
% 0.88/0.97  ------ Resolution Options
% 0.88/0.97  
% 0.88/0.97  --resolution_flag                       true
% 0.88/0.97  --res_lit_sel                           adaptive
% 0.88/0.97  --res_lit_sel_side                      none
% 0.88/0.97  --res_ordering                          kbo
% 0.88/0.97  --res_to_prop_solver                    active
% 0.88/0.97  --res_prop_simpl_new                    false
% 0.88/0.97  --res_prop_simpl_given                  true
% 0.88/0.97  --res_passive_queue_type                priority_queues
% 0.88/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.88/0.97  --res_passive_queues_freq               [15;5]
% 0.88/0.97  --res_forward_subs                      full
% 0.88/0.97  --res_backward_subs                     full
% 0.88/0.97  --res_forward_subs_resolution           true
% 0.88/0.97  --res_backward_subs_resolution          true
% 0.88/0.97  --res_orphan_elimination                true
% 0.88/0.97  --res_time_limit                        2.
% 0.88/0.97  --res_out_proof                         true
% 0.88/0.97  
% 0.88/0.97  ------ Superposition Options
% 0.88/0.97  
% 0.88/0.97  --superposition_flag                    true
% 0.88/0.97  --sup_passive_queue_type                priority_queues
% 0.88/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.88/0.97  --demod_completeness_check              fast
% 0.88/0.97  --demod_use_ground                      true
% 0.88/0.97  --sup_to_prop_solver                    passive
% 0.88/0.97  --sup_prop_simpl_new                    true
% 0.88/0.97  --sup_prop_simpl_given                  true
% 0.88/0.97  --sup_fun_splitting                     false
% 0.88/0.97  --sup_smt_interval                      50000
% 0.88/0.97  
% 0.88/0.97  ------ Superposition Simplification Setup
% 0.88/0.97  
% 0.88/0.97  --sup_indices_passive                   []
% 0.88/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.97  --sup_full_bw                           [BwDemod]
% 0.88/0.97  --sup_immed_triv                        [TrivRules]
% 0.88/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.97  --sup_immed_bw_main                     []
% 0.88/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.97  
% 0.88/0.97  ------ Combination Options
% 0.88/0.97  
% 0.88/0.97  --comb_res_mult                         3
% 0.88/0.97  --comb_sup_mult                         2
% 0.88/0.97  --comb_inst_mult                        10
% 0.88/0.97  
% 0.88/0.97  ------ Debug Options
% 0.88/0.97  
% 0.88/0.97  --dbg_backtrace                         false
% 0.88/0.97  --dbg_dump_prop_clauses                 false
% 0.88/0.97  --dbg_dump_prop_clauses_file            -
% 0.88/0.97  --dbg_out_stat                          false
% 0.88/0.97  ------ Parsing...
% 0.88/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.88/0.97  
% 0.88/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.88/0.97  
% 0.88/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.88/0.97  
% 0.88/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.88/0.97  ------ Proving...
% 0.88/0.97  ------ Problem Properties 
% 0.88/0.97  
% 0.88/0.97  
% 0.88/0.97  clauses                                 4
% 0.88/0.97  conjectures                             0
% 0.88/0.97  EPR                                     0
% 0.88/0.97  Horn                                    4
% 0.88/0.97  unary                                   1
% 0.88/0.97  binary                                  3
% 0.88/0.97  lits                                    7
% 0.88/0.97  lits eq                                 7
% 0.88/0.97  fd_pure                                 0
% 0.88/0.97  fd_pseudo                               0
% 0.88/0.97  fd_cond                                 0
% 0.88/0.97  fd_pseudo_cond                          0
% 0.88/0.97  AC symbols                              0
% 0.88/0.97  
% 0.88/0.97  ------ Schedule dynamic 5 is on 
% 0.88/0.97  
% 0.88/0.97  ------ no conjectures: strip conj schedule 
% 0.88/0.97  
% 0.88/0.97  ------ pure equality problem: resolution off 
% 0.88/0.97  
% 0.88/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.88/0.97  
% 0.88/0.97  
% 0.88/0.97  ------ 
% 0.88/0.97  Current options:
% 0.88/0.97  ------ 
% 0.88/0.97  
% 0.88/0.97  ------ Input Options
% 0.88/0.97  
% 0.88/0.97  --out_options                           all
% 0.88/0.97  --tptp_safe_out                         true
% 0.88/0.97  --problem_path                          ""
% 0.88/0.97  --include_path                          ""
% 0.88/0.97  --clausifier                            res/vclausify_rel
% 0.88/0.97  --clausifier_options                    --mode clausify
% 0.88/0.97  --stdin                                 false
% 0.88/0.97  --stats_out                             all
% 0.88/0.97  
% 0.88/0.97  ------ General Options
% 0.88/0.97  
% 0.88/0.97  --fof                                   false
% 0.88/0.97  --time_out_real                         305.
% 0.88/0.97  --time_out_virtual                      -1.
% 0.88/0.97  --symbol_type_check                     false
% 0.88/0.97  --clausify_out                          false
% 0.88/0.97  --sig_cnt_out                           false
% 0.88/0.97  --trig_cnt_out                          false
% 0.88/0.97  --trig_cnt_out_tolerance                1.
% 0.88/0.97  --trig_cnt_out_sk_spl                   false
% 0.88/0.97  --abstr_cl_out                          false
% 0.88/0.97  
% 0.88/0.97  ------ Global Options
% 0.88/0.97  
% 0.88/0.97  --schedule                              default
% 0.88/0.97  --add_important_lit                     false
% 0.88/0.97  --prop_solver_per_cl                    1000
% 0.88/0.97  --min_unsat_core                        false
% 0.88/0.97  --soft_assumptions                      false
% 0.88/0.97  --soft_lemma_size                       3
% 0.88/0.97  --prop_impl_unit_size                   0
% 0.88/0.97  --prop_impl_unit                        []
% 0.88/0.97  --share_sel_clauses                     true
% 0.88/0.97  --reset_solvers                         false
% 0.88/0.97  --bc_imp_inh                            [conj_cone]
% 0.88/0.97  --conj_cone_tolerance                   3.
% 0.88/0.97  --extra_neg_conj                        none
% 0.88/0.97  --large_theory_mode                     true
% 0.88/0.97  --prolific_symb_bound                   200
% 0.88/0.97  --lt_threshold                          2000
% 0.88/0.97  --clause_weak_htbl                      true
% 0.88/0.97  --gc_record_bc_elim                     false
% 0.88/0.97  
% 0.88/0.97  ------ Preprocessing Options
% 0.88/0.97  
% 0.88/0.97  --preprocessing_flag                    true
% 0.88/0.97  --time_out_prep_mult                    0.1
% 0.88/0.97  --splitting_mode                        input
% 0.88/0.97  --splitting_grd                         true
% 0.88/0.97  --splitting_cvd                         false
% 0.88/0.97  --splitting_cvd_svl                     false
% 0.88/0.97  --splitting_nvd                         32
% 0.88/0.97  --sub_typing                            true
% 0.88/0.97  --prep_gs_sim                           true
% 0.88/0.97  --prep_unflatten                        true
% 0.88/0.97  --prep_res_sim                          true
% 0.88/0.97  --prep_upred                            true
% 0.88/0.97  --prep_sem_filter                       exhaustive
% 0.88/0.97  --prep_sem_filter_out                   false
% 0.88/0.97  --pred_elim                             true
% 0.88/0.97  --res_sim_input                         true
% 0.88/0.97  --eq_ax_congr_red                       true
% 0.88/0.97  --pure_diseq_elim                       true
% 0.88/0.97  --brand_transform                       false
% 0.88/0.97  --non_eq_to_eq                          false
% 0.88/0.97  --prep_def_merge                        true
% 0.88/0.97  --prep_def_merge_prop_impl              false
% 0.88/0.97  --prep_def_merge_mbd                    true
% 0.88/0.97  --prep_def_merge_tr_red                 false
% 0.88/0.97  --prep_def_merge_tr_cl                  false
% 0.88/0.97  --smt_preprocessing                     true
% 0.88/0.97  --smt_ac_axioms                         fast
% 0.88/0.97  --preprocessed_out                      false
% 0.88/0.97  --preprocessed_stats                    false
% 0.88/0.97  
% 0.88/0.97  ------ Abstraction refinement Options
% 0.88/0.97  
% 0.88/0.97  --abstr_ref                             []
% 0.88/0.97  --abstr_ref_prep                        false
% 0.88/0.97  --abstr_ref_until_sat                   false
% 0.88/0.97  --abstr_ref_sig_restrict                funpre
% 0.88/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.88/0.97  --abstr_ref_under                       []
% 0.88/0.97  
% 0.88/0.97  ------ SAT Options
% 0.88/0.97  
% 0.88/0.97  --sat_mode                              false
% 0.88/0.97  --sat_fm_restart_options                ""
% 0.88/0.97  --sat_gr_def                            false
% 0.88/0.97  --sat_epr_types                         true
% 0.88/0.97  --sat_non_cyclic_types                  false
% 0.88/0.97  --sat_finite_models                     false
% 0.88/0.97  --sat_fm_lemmas                         false
% 0.88/0.97  --sat_fm_prep                           false
% 0.88/0.97  --sat_fm_uc_incr                        true
% 0.88/0.97  --sat_out_model                         small
% 0.88/0.97  --sat_out_clauses                       false
% 0.88/0.97  
% 0.88/0.97  ------ QBF Options
% 0.88/0.97  
% 0.88/0.97  --qbf_mode                              false
% 0.88/0.97  --qbf_elim_univ                         false
% 0.88/0.97  --qbf_dom_inst                          none
% 0.88/0.97  --qbf_dom_pre_inst                      false
% 0.88/0.97  --qbf_sk_in                             false
% 0.88/0.97  --qbf_pred_elim                         true
% 0.88/0.97  --qbf_split                             512
% 0.88/0.97  
% 0.88/0.97  ------ BMC1 Options
% 0.88/0.97  
% 0.88/0.97  --bmc1_incremental                      false
% 0.88/0.97  --bmc1_axioms                           reachable_all
% 0.88/0.97  --bmc1_min_bound                        0
% 0.88/0.97  --bmc1_max_bound                        -1
% 0.88/0.97  --bmc1_max_bound_default                -1
% 0.88/0.97  --bmc1_symbol_reachability              true
% 0.88/0.97  --bmc1_property_lemmas                  false
% 0.88/0.97  --bmc1_k_induction                      false
% 0.88/0.97  --bmc1_non_equiv_states                 false
% 0.88/0.97  --bmc1_deadlock                         false
% 0.88/0.97  --bmc1_ucm                              false
% 0.88/0.97  --bmc1_add_unsat_core                   none
% 0.88/0.97  --bmc1_unsat_core_children              false
% 0.88/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.88/0.97  --bmc1_out_stat                         full
% 0.88/0.97  --bmc1_ground_init                      false
% 0.88/0.97  --bmc1_pre_inst_next_state              false
% 0.88/0.97  --bmc1_pre_inst_state                   false
% 0.88/0.97  --bmc1_pre_inst_reach_state             false
% 0.88/0.97  --bmc1_out_unsat_core                   false
% 0.88/0.97  --bmc1_aig_witness_out                  false
% 0.88/0.97  --bmc1_verbose                          false
% 0.88/0.97  --bmc1_dump_clauses_tptp                false
% 0.88/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.88/0.97  --bmc1_dump_file                        -
% 0.88/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.88/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.88/0.97  --bmc1_ucm_extend_mode                  1
% 0.88/0.97  --bmc1_ucm_init_mode                    2
% 0.88/0.97  --bmc1_ucm_cone_mode                    none
% 0.88/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.88/0.97  --bmc1_ucm_relax_model                  4
% 0.88/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.88/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.88/0.97  --bmc1_ucm_layered_model                none
% 0.88/0.97  --bmc1_ucm_max_lemma_size               10
% 0.88/0.97  
% 0.88/0.97  ------ AIG Options
% 0.88/0.97  
% 0.88/0.97  --aig_mode                              false
% 0.88/0.97  
% 0.88/0.97  ------ Instantiation Options
% 0.88/0.97  
% 0.88/0.97  --instantiation_flag                    true
% 0.88/0.97  --inst_sos_flag                         false
% 0.88/0.97  --inst_sos_phase                        true
% 0.88/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.88/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.88/0.97  --inst_lit_sel_side                     none
% 0.88/0.97  --inst_solver_per_active                1400
% 0.88/0.97  --inst_solver_calls_frac                1.
% 0.88/0.97  --inst_passive_queue_type               priority_queues
% 0.88/0.97  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.88/0.97  --inst_passive_queues_freq              [25;2]
% 0.88/0.97  --inst_dismatching                      true
% 0.88/0.97  --inst_eager_unprocessed_to_passive     true
% 0.88/0.97  --inst_prop_sim_given                   true
% 0.88/0.97  --inst_prop_sim_new                     false
% 0.88/0.97  --inst_subs_new                         false
% 0.88/0.97  --inst_eq_res_simp                      false
% 0.88/0.97  --inst_subs_given                       false
% 0.88/0.97  --inst_orphan_elimination               true
% 0.88/0.97  --inst_learning_loop_flag               true
% 0.88/0.97  --inst_learning_start                   3000
% 0.88/0.97  --inst_learning_factor                  2
% 0.88/0.97  --inst_start_prop_sim_after_learn       3
% 0.88/0.97  --inst_sel_renew                        solver
% 0.88/0.97  --inst_lit_activity_flag                true
% 0.88/0.97  --inst_restr_to_given                   false
% 0.88/0.97  --inst_activity_threshold               500
% 0.88/0.97  --inst_out_proof                        true
% 0.88/0.97  
% 0.88/0.97  ------ Resolution Options
% 0.88/0.97  
% 0.88/0.97  --resolution_flag                       false
% 0.88/0.97  --res_lit_sel                           adaptive
% 0.88/0.97  --res_lit_sel_side                      none
% 0.88/0.97  --res_ordering                          kbo
% 0.88/0.97  --res_to_prop_solver                    active
% 0.88/0.97  --res_prop_simpl_new                    false
% 0.88/0.97  --res_prop_simpl_given                  true
% 0.88/0.97  --res_passive_queue_type                priority_queues
% 0.88/0.97  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.88/0.97  --res_passive_queues_freq               [15;5]
% 0.88/0.97  --res_forward_subs                      full
% 0.88/0.97  --res_backward_subs                     full
% 0.88/0.97  --res_forward_subs_resolution           true
% 0.88/0.97  --res_backward_subs_resolution          true
% 0.88/0.97  --res_orphan_elimination                true
% 0.88/0.97  --res_time_limit                        2.
% 0.88/0.97  --res_out_proof                         true
% 0.88/0.97  
% 0.88/0.97  ------ Superposition Options
% 0.88/0.97  
% 0.88/0.97  --superposition_flag                    true
% 0.88/0.97  --sup_passive_queue_type                priority_queues
% 0.88/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.88/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.88/0.97  --demod_completeness_check              fast
% 0.88/0.97  --demod_use_ground                      true
% 0.88/0.97  --sup_to_prop_solver                    passive
% 0.88/0.97  --sup_prop_simpl_new                    true
% 0.88/0.97  --sup_prop_simpl_given                  true
% 0.88/0.97  --sup_fun_splitting                     false
% 0.88/0.97  --sup_smt_interval                      50000
% 0.88/0.97  
% 0.88/0.97  ------ Superposition Simplification Setup
% 0.88/0.97  
% 0.88/0.97  --sup_indices_passive                   []
% 0.88/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.88/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.88/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.97  --sup_full_bw                           [BwDemod]
% 0.88/0.97  --sup_immed_triv                        [TrivRules]
% 0.88/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.88/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.97  --sup_immed_bw_main                     []
% 0.88/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.88/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.88/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.88/0.97  
% 0.88/0.97  ------ Combination Options
% 0.88/0.97  
% 0.88/0.97  --comb_res_mult                         3
% 0.88/0.97  --comb_sup_mult                         2
% 0.88/0.97  --comb_inst_mult                        10
% 0.88/0.97  
% 0.88/0.97  ------ Debug Options
% 0.88/0.97  
% 0.88/0.97  --dbg_backtrace                         false
% 0.88/0.97  --dbg_dump_prop_clauses                 false
% 0.88/0.97  --dbg_dump_prop_clauses_file            -
% 0.88/0.97  --dbg_out_stat                          false
% 0.88/0.97  
% 0.88/0.97  
% 0.88/0.97  
% 0.88/0.97  
% 0.88/0.97  ------ Proving...
% 0.88/0.97  
% 0.88/0.97  
% 0.88/0.97  % SZS status Theorem for theBenchmark.p
% 0.88/0.97  
% 0.88/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 0.88/0.97  
% 0.88/0.97  fof(f4,axiom,(
% 0.88/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.97  
% 0.88/0.97  fof(f10,plain,(
% 0.88/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.88/0.97    inference(pure_predicate_removal,[],[f4])).
% 0.88/0.97  
% 0.88/0.97  fof(f16,plain,(
% 0.88/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.97    inference(ennf_transformation,[],[f10])).
% 0.88/0.97  
% 0.88/0.97  fof(f29,plain,(
% 0.88/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.88/0.97    inference(cnf_transformation,[],[f16])).
% 0.88/0.97  
% 0.88/0.97  fof(f2,axiom,(
% 0.88/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.97  
% 0.88/0.97  fof(f13,plain,(
% 0.88/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.88/0.97    inference(ennf_transformation,[],[f2])).
% 0.88/0.97  
% 0.88/0.97  fof(f14,plain,(
% 0.88/0.97    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.88/0.97    inference(flattening,[],[f13])).
% 0.88/0.97  
% 0.88/0.97  fof(f27,plain,(
% 0.88/0.97    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.88/0.97    inference(cnf_transformation,[],[f14])).
% 0.88/0.97  
% 0.88/0.97  fof(f3,axiom,(
% 0.88/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.97  
% 0.88/0.97  fof(f15,plain,(
% 0.88/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.97    inference(ennf_transformation,[],[f3])).
% 0.88/0.97  
% 0.88/0.97  fof(f28,plain,(
% 0.88/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.88/0.97    inference(cnf_transformation,[],[f15])).
% 0.88/0.97  
% 0.88/0.97  fof(f7,conjecture,(
% 0.88/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.88/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.97  
% 0.88/0.97  fof(f8,negated_conjecture,(
% 0.88/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.88/0.98    inference(negated_conjecture,[],[f7])).
% 0.88/0.98  
% 0.88/0.98  fof(f9,plain,(
% 0.88/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.88/0.98    inference(pure_predicate_removal,[],[f8])).
% 0.88/0.98  
% 0.88/0.98  fof(f21,plain,(
% 0.88/0.98    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.88/0.98    inference(ennf_transformation,[],[f9])).
% 0.88/0.98  
% 0.88/0.98  fof(f22,plain,(
% 0.88/0.98    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.88/0.98    inference(flattening,[],[f21])).
% 0.88/0.98  
% 0.88/0.98  fof(f24,plain,(
% 0.88/0.98    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.88/0.98    introduced(choice_axiom,[])).
% 0.88/0.98  
% 0.88/0.98  fof(f25,plain,(
% 0.88/0.98    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f24])).
% 0.88/0.98  
% 0.88/0.98  fof(f34,plain,(
% 0.88/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.88/0.98    inference(cnf_transformation,[],[f25])).
% 0.88/0.98  
% 0.88/0.98  fof(f1,axiom,(
% 0.88/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f11,plain,(
% 0.88/0.98    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.88/0.98    inference(ennf_transformation,[],[f1])).
% 0.88/0.98  
% 0.88/0.98  fof(f12,plain,(
% 0.88/0.98    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.88/0.98    inference(flattening,[],[f11])).
% 0.88/0.98  
% 0.88/0.98  fof(f26,plain,(
% 0.88/0.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.88/0.98    inference(cnf_transformation,[],[f12])).
% 0.88/0.98  
% 0.88/0.98  fof(f35,plain,(
% 0.88/0.98    r1_tarski(sK0,sK2)),
% 0.88/0.98    inference(cnf_transformation,[],[f25])).
% 0.88/0.98  
% 0.88/0.98  fof(f6,axiom,(
% 0.88/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f19,plain,(
% 0.88/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.88/0.98    inference(ennf_transformation,[],[f6])).
% 0.88/0.98  
% 0.88/0.98  fof(f20,plain,(
% 0.88/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.88/0.98    inference(flattening,[],[f19])).
% 0.88/0.98  
% 0.88/0.98  fof(f32,plain,(
% 0.88/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.88/0.98    inference(cnf_transformation,[],[f20])).
% 0.88/0.98  
% 0.88/0.98  fof(f33,plain,(
% 0.88/0.98    v1_funct_1(sK3)),
% 0.88/0.98    inference(cnf_transformation,[],[f25])).
% 0.88/0.98  
% 0.88/0.98  fof(f5,axiom,(
% 0.88/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.88/0.98  
% 0.88/0.98  fof(f17,plain,(
% 0.88/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.88/0.98    inference(ennf_transformation,[],[f5])).
% 0.88/0.98  
% 0.88/0.98  fof(f18,plain,(
% 0.88/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.98    inference(flattening,[],[f17])).
% 0.88/0.98  
% 0.88/0.98  fof(f23,plain,(
% 0.88/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.88/0.98    inference(nnf_transformation,[],[f18])).
% 0.88/0.98  
% 0.88/0.98  fof(f31,plain,(
% 0.88/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.88/0.98    inference(cnf_transformation,[],[f23])).
% 0.88/0.98  
% 0.88/0.98  fof(f37,plain,(
% 0.88/0.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.88/0.98    inference(equality_resolution,[],[f31])).
% 0.88/0.98  
% 0.88/0.98  fof(f36,plain,(
% 0.88/0.98    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.88/0.98    inference(cnf_transformation,[],[f25])).
% 0.88/0.98  
% 0.88/0.98  cnf(c_266,plain,
% 0.88/0.98      ( X0_42 != X1_42 | X2_42 != X1_42 | X2_42 = X0_42 ),
% 0.88/0.98      theory(equality) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_318,plain,
% 0.88/0.98      ( k7_relat_1(sK3,sK2) != X0_42
% 0.88/0.98      | sK3 != X0_42
% 0.88/0.98      | sK3 = k7_relat_1(sK3,sK2) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_266]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_319,plain,
% 0.88/0.98      ( k7_relat_1(sK3,sK2) != sK3
% 0.88/0.98      | sK3 = k7_relat_1(sK3,sK2)
% 0.88/0.98      | sK3 != sK3 ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_318]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_3,plain,
% 0.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.88/0.98      | v4_relat_1(X0,X1) ),
% 0.88/0.98      inference(cnf_transformation,[],[f29]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_1,plain,
% 0.88/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.88/0.98      inference(cnf_transformation,[],[f27]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_157,plain,
% 0.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.88/0.98      | ~ v1_relat_1(X0)
% 0.88/0.98      | k7_relat_1(X0,X1) = X0 ),
% 0.88/0.98      inference(resolution,[status(thm)],[c_3,c_1]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_2,plain,
% 0.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.88/0.98      | v1_relat_1(X0) ),
% 0.88/0.98      inference(cnf_transformation,[],[f28]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_161,plain,
% 0.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.88/0.98      | k7_relat_1(X0,X1) = X0 ),
% 0.88/0.98      inference(global_propositional_subsumption,
% 0.88/0.98                [status(thm)],
% 0.88/0.98                [c_157,c_3,c_2,c_1]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_9,negated_conjecture,
% 0.88/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 0.88/0.98      inference(cnf_transformation,[],[f34]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_215,plain,
% 0.88/0.98      ( k7_relat_1(X0,X1) = X0
% 0.88/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.88/0.98      | sK3 != X0 ),
% 0.88/0.98      inference(resolution_lifted,[status(thm)],[c_161,c_9]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_216,plain,
% 0.88/0.98      ( k7_relat_1(sK3,X0) = sK3
% 0.88/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.88/0.98      inference(unflattening,[status(thm)],[c_215]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_262,plain,
% 0.88/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.88/0.98      | k7_relat_1(sK3,X0_43) = sK3 ),
% 0.88/0.98      inference(subtyping,[status(esa)],[c_216]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_301,plain,
% 0.88/0.98      ( k7_relat_1(sK3,sK0) = sK3 ),
% 0.88/0.98      inference(equality_resolution,[status(thm)],[c_262]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_0,plain,
% 0.88/0.98      ( ~ r1_tarski(X0,X1)
% 0.88/0.98      | ~ v1_relat_1(X2)
% 0.88/0.98      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
% 0.88/0.98      inference(cnf_transformation,[],[f26]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_8,negated_conjecture,
% 0.88/0.98      ( r1_tarski(sK0,sK2) ),
% 0.88/0.98      inference(cnf_transformation,[],[f35]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_127,plain,
% 0.88/0.98      ( ~ v1_relat_1(X0)
% 0.88/0.98      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X1)
% 0.88/0.98      | sK2 != X2
% 0.88/0.98      | sK0 != X1 ),
% 0.88/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_128,plain,
% 0.88/0.98      ( ~ v1_relat_1(X0)
% 0.88/0.98      | k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK0) ),
% 0.88/0.98      inference(unflattening,[status(thm)],[c_127]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_177,plain,
% 0.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.88/0.98      | k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK0) ),
% 0.88/0.98      inference(resolution,[status(thm)],[c_2,c_128]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_206,plain,
% 0.88/0.98      ( k7_relat_1(k7_relat_1(X0,sK0),sK2) = k7_relat_1(X0,sK0)
% 0.88/0.98      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.88/0.98      | sK3 != X0 ),
% 0.88/0.98      inference(resolution_lifted,[status(thm)],[c_177,c_9]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_207,plain,
% 0.88/0.98      ( k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK0)
% 0.88/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.88/0.98      inference(unflattening,[status(thm)],[c_206]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_263,plain,
% 0.88/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.88/0.98      | k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK0) ),
% 0.88/0.98      inference(subtyping,[status(esa)],[c_207]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_274,plain,
% 0.88/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.88/0.98      | k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK0) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_263]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_265,plain,( X0_45 = X0_45 ),theory(equality) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_291,plain,
% 0.88/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_265]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_302,plain,
% 0.88/0.98      ( k7_relat_1(k7_relat_1(sK3,sK0),sK2) = k7_relat_1(sK3,sK0) ),
% 0.88/0.98      inference(global_propositional_subsumption,
% 0.88/0.98                [status(thm)],
% 0.88/0.98                [c_263,c_274,c_291]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_314,plain,
% 0.88/0.98      ( k7_relat_1(sK3,sK2) = sK3 ),
% 0.88/0.98      inference(demodulation,[status(thm)],[c_301,c_302]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_297,plain,
% 0.88/0.98      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0_42
% 0.88/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 0.88/0.98      | sK3 != X0_42 ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_266]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_311,plain,
% 0.88/0.98      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 0.88/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 0.88/0.98      | sK3 != k7_relat_1(sK3,sK2) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_297]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_6,plain,
% 0.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.88/0.98      | ~ v1_funct_1(X0)
% 0.88/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 0.88/0.98      inference(cnf_transformation,[],[f32]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_10,negated_conjecture,
% 0.88/0.98      ( v1_funct_1(sK3) ),
% 0.88/0.98      inference(cnf_transformation,[],[f33]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_142,plain,
% 0.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.88/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3)
% 0.88/0.98      | sK3 != X0 ),
% 0.88/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_143,plain,
% 0.88/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.88/0.98      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 0.88/0.98      inference(unflattening,[status(thm)],[c_142]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_224,plain,
% 0.88/0.98      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 0.88/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.88/0.98      | sK3 != sK3 ),
% 0.88/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_143]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_252,plain,
% 0.88/0.98      ( k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)
% 0.88/0.98      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.88/0.98      inference(equality_resolution_simp,[status(thm)],[c_224]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_260,plain,
% 0.88/0.98      ( k1_zfmisc_1(k2_zfmisc_1(X0_43,X0_44)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.88/0.98      | k2_partfun1(X0_43,X0_44,sK3,X1_43) = k7_relat_1(sK3,X1_43) ),
% 0.88/0.98      inference(subtyping,[status(esa)],[c_252]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_310,plain,
% 0.88/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 0.88/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_260]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_4,plain,
% 0.88/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 0.88/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.88/0.98      inference(cnf_transformation,[],[f37]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_7,negated_conjecture,
% 0.88/0.98      ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
% 0.88/0.98      inference(cnf_transformation,[],[f36]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_193,plain,
% 0.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.88/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 0.88/0.98      | sK3 != X0
% 0.88/0.98      | sK1 != X2
% 0.88/0.98      | sK0 != X1 ),
% 0.88/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_7]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_194,plain,
% 0.88/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 0.88/0.98      | sK3 != k2_partfun1(sK0,sK1,sK3,sK2) ),
% 0.88/0.98      inference(unflattening,[status(thm)],[c_193]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_235,plain,
% 0.88/0.98      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 0.88/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 0.88/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_194]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_251,plain,
% 0.88/0.98      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
% 0.88/0.98      inference(equality_resolution_simp,[status(thm)],[c_235]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_261,plain,
% 0.88/0.98      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3 ),
% 0.88/0.98      inference(subtyping,[status(esa)],[c_251]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_264,plain,( X0_42 = X0_42 ),theory(equality) ).
% 0.88/0.98  
% 0.88/0.98  cnf(c_272,plain,
% 0.88/0.98      ( sK3 = sK3 ),
% 0.88/0.98      inference(instantiation,[status(thm)],[c_264]) ).
% 0.88/0.98  
% 0.88/0.98  cnf(contradiction,plain,
% 0.88/0.98      ( $false ),
% 0.88/0.98      inference(minisat,
% 0.88/0.98                [status(thm)],
% 0.88/0.98                [c_319,c_314,c_311,c_310,c_291,c_261,c_272]) ).
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.88/0.98  
% 0.88/0.98  ------                               Statistics
% 0.88/0.98  
% 0.88/0.98  ------ General
% 0.88/0.98  
% 0.88/0.98  abstr_ref_over_cycles:                  0
% 0.88/0.98  abstr_ref_under_cycles:                 0
% 0.88/0.98  gc_basic_clause_elim:                   0
% 0.88/0.98  forced_gc_time:                         0
% 0.88/0.98  parsing_time:                           0.015
% 0.88/0.98  unif_index_cands_time:                  0.
% 0.88/0.98  unif_index_add_time:                    0.
% 0.88/0.98  orderings_time:                         0.
% 0.88/0.98  out_proof_time:                         0.007
% 0.88/0.98  total_time:                             0.057
% 0.88/0.98  num_of_symbols:                         47
% 0.88/0.98  num_of_terms:                           544
% 0.88/0.98  
% 0.88/0.98  ------ Preprocessing
% 0.88/0.98  
% 0.88/0.98  num_of_splits:                          0
% 0.88/0.98  num_of_split_atoms:                     0
% 0.88/0.98  num_of_reused_defs:                     0
% 0.88/0.98  num_eq_ax_congr_red:                    11
% 0.88/0.98  num_of_sem_filtered_clauses:            0
% 0.88/0.98  num_of_subtypes:                        5
% 0.88/0.98  monotx_restored_types:                  0
% 0.88/0.98  sat_num_of_epr_types:                   0
% 0.88/0.98  sat_num_of_non_cyclic_types:            0
% 0.88/0.98  sat_guarded_non_collapsed_types:        0
% 0.88/0.98  num_pure_diseq_elim:                    0
% 0.88/0.98  simp_replaced_by:                       0
% 0.88/0.98  res_preprocessed:                       25
% 0.88/0.98  prep_upred:                             0
% 0.88/0.98  prep_unflattend:                        12
% 0.88/0.98  smt_new_axioms:                         0
% 0.88/0.98  pred_elim_cands:                        0
% 0.88/0.98  pred_elim:                              6
% 0.88/0.98  pred_elim_cl:                           7
% 0.88/0.98  pred_elim_cycles:                       7
% 0.88/0.98  merged_defs:                            0
% 0.88/0.98  merged_defs_ncl:                        0
% 0.88/0.98  bin_hyper_res:                          0
% 0.88/0.98  prep_cycles:                            3
% 0.88/0.98  pred_elim_time:                         0.004
% 0.88/0.98  splitting_time:                         0.
% 0.88/0.98  sem_filter_time:                        0.
% 0.88/0.98  monotx_time:                            0.
% 0.88/0.98  subtype_inf_time:                       0.
% 0.88/0.98  
% 0.88/0.98  ------ Problem properties
% 0.88/0.98  
% 0.88/0.98  clauses:                                4
% 0.88/0.98  conjectures:                            0
% 0.88/0.98  epr:                                    0
% 0.88/0.98  horn:                                   4
% 0.88/0.98  ground:                                 1
% 0.88/0.98  unary:                                  1
% 0.88/0.98  binary:                                 3
% 0.88/0.98  lits:                                   7
% 0.88/0.98  lits_eq:                                7
% 0.88/0.98  fd_pure:                                0
% 0.88/0.98  fd_pseudo:                              0
% 0.88/0.98  fd_cond:                                0
% 0.88/0.98  fd_pseudo_cond:                         0
% 0.88/0.98  ac_symbols:                             0
% 0.88/0.98  
% 0.88/0.98  ------ Propositional Solver
% 0.88/0.98  
% 0.88/0.98  prop_solver_calls:                      21
% 0.88/0.98  prop_fast_solver_calls:                 127
% 0.88/0.98  smt_solver_calls:                       0
% 0.88/0.98  smt_fast_solver_calls:                  0
% 0.88/0.98  prop_num_of_clauses:                    100
% 0.88/0.98  prop_preprocess_simplified:             587
% 0.88/0.98  prop_fo_subsumed:                       2
% 0.88/0.98  prop_solver_time:                       0.
% 0.88/0.98  smt_solver_time:                        0.
% 0.88/0.98  smt_fast_solver_time:                   0.
% 0.88/0.98  prop_fast_solver_time:                  0.
% 0.88/0.98  prop_unsat_core_time:                   0.
% 0.88/0.98  
% 0.88/0.98  ------ QBF
% 0.88/0.98  
% 0.88/0.98  qbf_q_res:                              0
% 0.88/0.98  qbf_num_tautologies:                    0
% 0.88/0.98  qbf_prep_cycles:                        0
% 0.88/0.98  
% 0.88/0.98  ------ BMC1
% 0.88/0.98  
% 0.88/0.98  bmc1_current_bound:                     -1
% 0.88/0.98  bmc1_last_solved_bound:                 -1
% 0.88/0.98  bmc1_unsat_core_size:                   -1
% 0.88/0.98  bmc1_unsat_core_parents_size:           -1
% 0.88/0.98  bmc1_merge_next_fun:                    0
% 0.88/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.88/0.98  
% 0.88/0.98  ------ Instantiation
% 0.88/0.98  
% 0.88/0.98  inst_num_of_clauses:                    22
% 0.88/0.98  inst_num_in_passive:                    4
% 0.88/0.98  inst_num_in_active:                     17
% 0.88/0.98  inst_num_in_unprocessed:                0
% 0.88/0.98  inst_num_of_loops:                      23
% 0.88/0.98  inst_num_of_learning_restarts:          0
% 0.88/0.98  inst_num_moves_active_passive:          3
% 0.88/0.98  inst_lit_activity:                      0
% 0.88/0.98  inst_lit_activity_moves:                0
% 0.88/0.98  inst_num_tautologies:                   0
% 0.88/0.98  inst_num_prop_implied:                  0
% 0.88/0.98  inst_num_existing_simplified:           0
% 0.88/0.98  inst_num_eq_res_simplified:             0
% 0.88/0.98  inst_num_child_elim:                    0
% 0.88/0.98  inst_num_of_dismatching_blockings:      0
% 0.88/0.98  inst_num_of_non_proper_insts:           7
% 0.88/0.98  inst_num_of_duplicates:                 0
% 0.88/0.98  inst_inst_num_from_inst_to_res:         0
% 0.88/0.98  inst_dismatching_checking_time:         0.
% 0.88/0.98  
% 0.88/0.98  ------ Resolution
% 0.88/0.98  
% 0.88/0.98  res_num_of_clauses:                     0
% 0.88/0.98  res_num_in_passive:                     0
% 0.88/0.98  res_num_in_active:                      0
% 0.88/0.98  res_num_of_loops:                       28
% 0.88/0.98  res_forward_subset_subsumed:            0
% 0.88/0.98  res_backward_subset_subsumed:           0
% 0.88/0.98  res_forward_subsumed:                   0
% 0.88/0.98  res_backward_subsumed:                  0
% 0.88/0.98  res_forward_subsumption_resolution:     0
% 0.88/0.98  res_backward_subsumption_resolution:    0
% 0.88/0.98  res_clause_to_clause_subsumption:       7
% 0.88/0.98  res_orphan_elimination:                 0
% 0.88/0.98  res_tautology_del:                      1
% 0.88/0.98  res_num_eq_res_simplified:              2
% 0.88/0.98  res_num_sel_changes:                    0
% 0.88/0.98  res_moves_from_active_to_pass:          0
% 0.88/0.98  
% 0.88/0.98  ------ Superposition
% 0.88/0.98  
% 0.88/0.98  sup_time_total:                         0.
% 0.88/0.98  sup_time_generating:                    0.
% 0.88/0.98  sup_time_sim_full:                      0.
% 0.88/0.98  sup_time_sim_immed:                     0.
% 0.88/0.98  
% 0.88/0.98  sup_num_of_clauses:                     5
% 0.88/0.98  sup_num_in_active:                      3
% 0.88/0.98  sup_num_in_passive:                     2
% 0.88/0.98  sup_num_of_loops:                       4
% 0.88/0.98  sup_fw_superposition:                   0
% 0.88/0.98  sup_bw_superposition:                   0
% 0.88/0.98  sup_immediate_simplified:               0
% 0.88/0.98  sup_given_eliminated:                   0
% 0.88/0.98  comparisons_done:                       0
% 0.88/0.98  comparisons_avoided:                    0
% 0.88/0.98  
% 0.88/0.98  ------ Simplifications
% 0.88/0.98  
% 0.88/0.98  
% 0.88/0.98  sim_fw_subset_subsumed:                 0
% 0.88/0.98  sim_bw_subset_subsumed:                 0
% 0.88/0.98  sim_fw_subsumed:                        0
% 0.88/0.98  sim_bw_subsumed:                        0
% 0.88/0.98  sim_fw_subsumption_res:                 0
% 0.88/0.98  sim_bw_subsumption_res:                 0
% 0.88/0.98  sim_tautology_del:                      0
% 0.88/0.98  sim_eq_tautology_del:                   0
% 0.88/0.98  sim_eq_res_simp:                        0
% 0.88/0.98  sim_fw_demodulated:                     0
% 0.88/0.98  sim_bw_demodulated:                     1
% 0.88/0.98  sim_light_normalised:                   0
% 0.88/0.98  sim_joinable_taut:                      0
% 0.88/0.98  sim_joinable_simp:                      0
% 0.88/0.98  sim_ac_normalised:                      0
% 0.88/0.98  sim_smt_subsumption:                    0
% 0.88/0.98  
%------------------------------------------------------------------------------
