%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1054+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:47 EST 2020

% Result     : Theorem 1.16s
% Output     : CNFRefutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 180 expanded)
%              Number of clauses        :   60 (  77 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :   26
%              Number of atoms          :  332 ( 463 expanded)
%              Number of equality atoms :   89 ( 118 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0] : v1_partfun1(k6_relat_1(X0),X0) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ( ( v1_funct_2(X1,X0,X0)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v1_relat_2(X1) )
       => ( v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v8_relat_2(X0)
        & v3_relat_2(X0)
        & v1_relat_1(X0) )
     => ( v1_relat_2(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
        & v1_relat_1(X0) )
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v3_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( v8_relat_2(k6_relat_1(X0))
      & v4_relat_2(k6_relat_1(X0))
      & v3_relat_2(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v8_relat_2(k6_relat_1(X0))
      & v3_relat_2(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f43,plain,(
    ! [X0] : v8_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] : v3_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
        & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 )
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
        & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 )
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X2,X0,X0)
      | ~ v1_funct_2(X2,X0,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) != sK1 ),
    inference(definition_unfolding,[],[f51,f44])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_579,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_709,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_8,plain,
    ( v1_partfun1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( v3_funct_2(X0,X1,X1)
    | ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_relat_2(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v3_relat_2(X0)
    | ~ v8_relat_2(X0)
    | v1_relat_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_11,plain,
    ( v8_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_202,plain,
    ( ~ v1_relat_1(X0)
    | ~ v3_relat_2(X0)
    | v1_relat_2(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_203,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | ~ v3_relat_2(k6_relat_1(X0))
    | v1_relat_2(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_13,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,plain,
    ( v3_relat_2(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_207,plain,
    ( v1_relat_2(k6_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_203,c_13,c_12])).

cnf(c_219,plain,
    ( v3_funct_2(X0,X1,X1)
    | ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_207])).

cnf(c_220,plain,
    ( v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ v1_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_partfun1(k6_relat_1(X0),X1)
    | ~ v1_funct_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_9,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_224,plain,
    ( ~ v1_partfun1(k6_relat_1(X0),X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_2(k6_relat_1(X0),X1,X1)
    | v3_funct_2(k6_relat_1(X0),X1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_9])).

cnf(c_225,plain,
    ( v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ v1_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_partfun1(k6_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_266,plain,
    ( v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ v1_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X1 != X2
    | k6_relat_1(X2) != k6_relat_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_225])).

cnf(c_267,plain,
    ( v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ v1_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k6_relat_1(X1) != k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_266])).

cnf(c_0,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_248,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X1
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_249,plain,
    ( v1_funct_2(k6_relat_1(X0),X0,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_253,plain,
    ( ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(k6_relat_1(X0),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_9])).

cnf(c_254,plain,
    ( v1_funct_2(k6_relat_1(X0),X0,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_448,plain,
    ( v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X2 != X1
    | X3 != X1
    | k6_relat_1(X0) != k6_relat_1(X1)
    | k6_relat_1(X2) != k6_relat_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_267,c_254])).

cnf(c_449,plain,
    ( v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k6_relat_1(X0) != k6_relat_1(X1)
    | k6_relat_1(X1) != k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_7,plain,
    ( m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_463,plain,
    ( v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k6_relat_1(X0) != k6_relat_1(X1)
    | k6_relat_1(X1) != k6_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_449,c_7])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,plain,
    ( ~ v3_funct_2(X0,X1,X1)
    | ~ v1_funct_2(X0,X1,X1)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X1,X0,k7_relset_1(X1,X1,X0,X2)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_313,plain,
    ( ~ v3_funct_2(X0,X1,X1)
    | ~ v1_funct_2(X0,X1,X1)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k8_relset_1(X1,X1,X0,k7_relset_1(X1,X1,X0,X2)) = X2
    | k6_relat_1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_9])).

cnf(c_314,plain,
    ( ~ v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ v1_funct_2(k6_relat_1(X0),X1,X1)
    | ~ r1_tarski(X2,X1)
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k8_relset_1(X1,X1,k6_relat_1(X0),k7_relset_1(X1,X1,k6_relat_1(X0),X2)) = X2 ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_346,plain,
    ( ~ v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ v1_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X4 != X2
    | X1 != X3
    | k8_relset_1(X1,X1,k6_relat_1(X0),k7_relset_1(X1,X1,k6_relat_1(X0),X4)) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_314])).

cnf(c_347,plain,
    ( ~ v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ v1_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k8_relset_1(X1,X1,k6_relat_1(X0),k7_relset_1(X1,X1,k6_relat_1(X0),X2)) = X2 ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_424,plain,
    ( ~ v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(k6_relat_1(X3),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X3 != X1
    | X4 != X1
    | k8_relset_1(X1,X1,k6_relat_1(X0),k7_relset_1(X1,X1,k6_relat_1(X0),X2)) = X2
    | k6_relat_1(X3) != k6_relat_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_347,c_254])).

cnf(c_425,plain,
    ( ~ v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k8_relset_1(X1,X1,k6_relat_1(X0),k7_relset_1(X1,X1,k6_relat_1(X0),X2)) = X2
    | k6_relat_1(X1) != k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_441,plain,
    ( ~ v3_funct_2(k6_relat_1(X0),X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k8_relset_1(X1,X1,k6_relat_1(X0),k7_relset_1(X1,X1,k6_relat_1(X0),X2)) = X2
    | k6_relat_1(X1) != k6_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_425,c_7])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k6_relat_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | k8_relset_1(X1,X1,k6_relat_1(X2),k7_relset_1(X1,X1,k6_relat_1(X2),X0)) = X0
    | k6_relat_1(X2) != k6_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_463,c_441])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X0_48))
    | ~ m1_subset_1(k6_relat_1(X1_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48)))
    | k8_relset_1(X0_48,X0_48,k6_relat_1(X1_48),k7_relset_1(X0_48,X0_48,k6_relat_1(X1_48),X0_46)) = X0_46
    | k6_relat_1(X1_48) != k6_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_486])).

cnf(c_710,plain,
    ( k8_relset_1(X0_48,X0_48,k6_relat_1(X1_48),k7_relset_1(X0_48,X0_48,k6_relat_1(X1_48),X0_46)) = X0_46
    | k6_relat_1(X1_48) != k6_relat_1(X0_48)
    | m1_subset_1(X0_46,k1_zfmisc_1(X0_48)) != iProver_top
    | m1_subset_1(k6_relat_1(X1_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_1045,plain,
    ( k8_relset_1(X0_48,X0_48,k6_relat_1(X0_48),k7_relset_1(X0_48,X0_48,k6_relat_1(X0_48),X0_46)) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(X0_48)) != iProver_top
    | m1_subset_1(k6_relat_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_710])).

cnf(c_583,plain,
    ( m1_subset_1(k6_relat_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_706,plain,
    ( m1_subset_1(k6_relat_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | k7_relset_1(X0_48,X1_48,X0_46,X1_46) = k9_relat_1(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_707,plain,
    ( k7_relset_1(X0_48,X1_48,X0_46,X1_46) = k9_relat_1(X0_46,X1_46)
    | m1_subset_1(X0_46,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_942,plain,
    ( k7_relset_1(X0_48,X0_48,k6_relat_1(X0_48),X0_46) = k9_relat_1(k6_relat_1(X0_48),X0_46) ),
    inference(superposition,[status(thm)],[c_706,c_707])).

cnf(c_1046,plain,
    ( k8_relset_1(X0_48,X0_48,k6_relat_1(X0_48),k9_relat_1(k6_relat_1(X0_48),X0_46)) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(X0_48)) != iProver_top
    | m1_subset_1(k6_relat_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1045,c_942])).

cnf(c_597,plain,
    ( m1_subset_1(k6_relat_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_48,X0_48))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_1051,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X0_48)) != iProver_top
    | k8_relset_1(X0_48,X0_48,k6_relat_1(X0_48),k9_relat_1(k6_relat_1(X0_48),X0_46)) = X0_46 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1046,c_597])).

cnf(c_1052,plain,
    ( k8_relset_1(X0_48,X0_48,k6_relat_1(X0_48),k9_relat_1(k6_relat_1(X0_48),X0_46)) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1051])).

cnf(c_1059,plain,
    ( k8_relset_1(sK0,sK0,k6_relat_1(sK0),k9_relat_1(k6_relat_1(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_709,c_1052])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_relat_1(k6_relat_1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_581,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X0_48))
    | k9_relat_1(k6_relat_1(X0_48),X0_46) = X0_46 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_708,plain,
    ( k9_relat_1(k6_relat_1(X0_48),X0_46) = X0_46
    | m1_subset_1(X0_46,k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_814,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_709,c_708])).

cnf(c_1065,plain,
    ( k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1059,c_814])).

cnf(c_19,negated_conjecture,
    ( k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_580,negated_conjecture,
    ( k8_relset_1(sK0,sK0,k6_relat_1(sK0),sK1) != sK1 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1065,c_580])).


%------------------------------------------------------------------------------
