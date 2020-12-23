%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:29 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  192 (1680 expanded)
%              Number of clauses        :  127 ( 547 expanded)
%              Number of leaves         :   15 ( 317 expanded)
%              Depth                    :   22
%              Number of atoms          :  641 (7729 expanded)
%              Number of equality atoms :  264 ( 819 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
        | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f43])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f64])).

fof(f48,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_445,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_995,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_448,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_992,plain,
    ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_2821,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_992])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_556,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_3178,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2821,c_24,c_23,c_22,c_21,c_556])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_454,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_986,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_3191,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3178,c_986])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3395,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3191,c_25,c_26,c_27,c_28])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_447,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k1_relset_1(X0_49,X0_49,X0_48) = X0_49 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_993,plain,
    ( k1_relset_1(X0_49,X0_49,X0_48) = X0_49
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_3404,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_993])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_983,plain,
    ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_3407,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3395,c_983])).

cnf(c_3423,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3404,c_3407])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_463,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48))
    | ~ v2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_512,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(X0_48)) = iProver_top
    | v2_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_514,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_512])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_527,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_529,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_10,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_455,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | v2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_536,plain,
    ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_538,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_988,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_3021,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_988])).

cnf(c_545,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_547,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_3287,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3021,c_25,c_26,c_27,c_28,c_547])).

cnf(c_3291,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3287,c_3178])).

cnf(c_6803,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3423,c_25,c_27,c_28,c_514,c_529,c_538,c_3291])).

cnf(c_982,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_3408,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_982])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_460,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_980,plain,
    ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_3585,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3408,c_980])).

cnf(c_1251,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_982])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_459,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_981,plain,
    ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_1496,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_981])).

cnf(c_525,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_528,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_537,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_1566,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1496,c_24,c_22,c_21,c_525,c_528,c_537])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_461,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_979,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1819,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_979])).

cnf(c_519,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2350,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1819,c_24,c_22,c_21,c_519,c_528,c_537])).

cnf(c_3602,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3585,c_1566,c_2350])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_464,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | v2_funct_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_509,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_511,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_4907,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3602,c_25,c_27,c_28,c_511,c_514,c_529,c_538])).

cnf(c_6810,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_6803,c_4907])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_991,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_3618,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_991])).

cnf(c_5054,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3618,c_25,c_27,c_28,c_514,c_529,c_538])).

cnf(c_5055,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5054])).

cnf(c_5063,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_5055])).

cnf(c_5094,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5063,c_2350])).

cnf(c_5240,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5094,c_25])).

cnf(c_3614,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_991])).

cnf(c_3983,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_25])).

cnf(c_3984,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3983])).

cnf(c_3992,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_3984])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_451,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_548,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_4256,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3992,c_548])).

cnf(c_4257,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4256])).

cnf(c_4267,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_4257])).

cnf(c_1961,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1251,c_980])).

cnf(c_522,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_2420,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1961,c_24,c_22,c_21,c_522,c_528,c_537])).

cnf(c_2137,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_993])).

cnf(c_1367,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_995,c_983])).

cnf(c_2157,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2137,c_1367])).

cnf(c_2253,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2157,c_25,c_26])).

cnf(c_2422,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_2420,c_2253])).

cnf(c_4316,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4267,c_2422,c_3178])).

cnf(c_3994,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_3984])).

cnf(c_3997,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3994,c_2422])).

cnf(c_4333,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4316,c_25,c_27,c_28,c_514,c_529,c_538,c_3997])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_446,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_994,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_3182,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3178,c_994])).

cnf(c_4336,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4333,c_3182])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_450,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_990,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_456,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_984,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_2009,plain,
    ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_984])).

cnf(c_2025,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2009])).

cnf(c_4465,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4336,c_28,c_2025])).

cnf(c_5243,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5240,c_4465])).

cnf(c_6828,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6810,c_5243])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6828,c_2025,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.05/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.00  
% 3.05/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/1.00  
% 3.05/1.00  ------  iProver source info
% 3.05/1.00  
% 3.05/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.05/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/1.00  git: non_committed_changes: false
% 3.05/1.00  git: last_make_outside_of_git: false
% 3.05/1.00  
% 3.05/1.00  ------ 
% 3.05/1.00  
% 3.05/1.00  ------ Input Options
% 3.05/1.00  
% 3.05/1.00  --out_options                           all
% 3.05/1.00  --tptp_safe_out                         true
% 3.05/1.00  --problem_path                          ""
% 3.05/1.00  --include_path                          ""
% 3.05/1.00  --clausifier                            res/vclausify_rel
% 3.05/1.00  --clausifier_options                    --mode clausify
% 3.05/1.00  --stdin                                 false
% 3.05/1.00  --stats_out                             all
% 3.05/1.00  
% 3.05/1.00  ------ General Options
% 3.05/1.00  
% 3.05/1.00  --fof                                   false
% 3.05/1.00  --time_out_real                         305.
% 3.05/1.00  --time_out_virtual                      -1.
% 3.05/1.00  --symbol_type_check                     false
% 3.05/1.00  --clausify_out                          false
% 3.05/1.00  --sig_cnt_out                           false
% 3.05/1.01  --trig_cnt_out                          false
% 3.05/1.01  --trig_cnt_out_tolerance                1.
% 3.05/1.01  --trig_cnt_out_sk_spl                   false
% 3.05/1.01  --abstr_cl_out                          false
% 3.05/1.01  
% 3.05/1.01  ------ Global Options
% 3.05/1.01  
% 3.05/1.01  --schedule                              default
% 3.05/1.01  --add_important_lit                     false
% 3.05/1.01  --prop_solver_per_cl                    1000
% 3.05/1.01  --min_unsat_core                        false
% 3.05/1.01  --soft_assumptions                      false
% 3.05/1.01  --soft_lemma_size                       3
% 3.05/1.01  --prop_impl_unit_size                   0
% 3.05/1.01  --prop_impl_unit                        []
% 3.05/1.01  --share_sel_clauses                     true
% 3.05/1.01  --reset_solvers                         false
% 3.05/1.01  --bc_imp_inh                            [conj_cone]
% 3.05/1.01  --conj_cone_tolerance                   3.
% 3.05/1.01  --extra_neg_conj                        none
% 3.05/1.01  --large_theory_mode                     true
% 3.05/1.01  --prolific_symb_bound                   200
% 3.05/1.01  --lt_threshold                          2000
% 3.05/1.01  --clause_weak_htbl                      true
% 3.05/1.01  --gc_record_bc_elim                     false
% 3.05/1.01  
% 3.05/1.01  ------ Preprocessing Options
% 3.05/1.01  
% 3.05/1.01  --preprocessing_flag                    true
% 3.05/1.01  --time_out_prep_mult                    0.1
% 3.05/1.01  --splitting_mode                        input
% 3.05/1.01  --splitting_grd                         true
% 3.05/1.01  --splitting_cvd                         false
% 3.05/1.01  --splitting_cvd_svl                     false
% 3.05/1.01  --splitting_nvd                         32
% 3.05/1.01  --sub_typing                            true
% 3.05/1.01  --prep_gs_sim                           true
% 3.05/1.01  --prep_unflatten                        true
% 3.05/1.01  --prep_res_sim                          true
% 3.05/1.01  --prep_upred                            true
% 3.05/1.01  --prep_sem_filter                       exhaustive
% 3.05/1.01  --prep_sem_filter_out                   false
% 3.05/1.01  --pred_elim                             true
% 3.05/1.01  --res_sim_input                         true
% 3.05/1.01  --eq_ax_congr_red                       true
% 3.05/1.01  --pure_diseq_elim                       true
% 3.05/1.01  --brand_transform                       false
% 3.05/1.01  --non_eq_to_eq                          false
% 3.05/1.01  --prep_def_merge                        true
% 3.05/1.01  --prep_def_merge_prop_impl              false
% 3.05/1.01  --prep_def_merge_mbd                    true
% 3.05/1.01  --prep_def_merge_tr_red                 false
% 3.05/1.01  --prep_def_merge_tr_cl                  false
% 3.05/1.01  --smt_preprocessing                     true
% 3.05/1.01  --smt_ac_axioms                         fast
% 3.05/1.01  --preprocessed_out                      false
% 3.05/1.01  --preprocessed_stats                    false
% 3.05/1.01  
% 3.05/1.01  ------ Abstraction refinement Options
% 3.05/1.01  
% 3.05/1.01  --abstr_ref                             []
% 3.05/1.01  --abstr_ref_prep                        false
% 3.05/1.01  --abstr_ref_until_sat                   false
% 3.05/1.01  --abstr_ref_sig_restrict                funpre
% 3.05/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.01  --abstr_ref_under                       []
% 3.05/1.01  
% 3.05/1.01  ------ SAT Options
% 3.05/1.01  
% 3.05/1.01  --sat_mode                              false
% 3.05/1.01  --sat_fm_restart_options                ""
% 3.05/1.01  --sat_gr_def                            false
% 3.05/1.01  --sat_epr_types                         true
% 3.05/1.01  --sat_non_cyclic_types                  false
% 3.05/1.01  --sat_finite_models                     false
% 3.05/1.01  --sat_fm_lemmas                         false
% 3.05/1.01  --sat_fm_prep                           false
% 3.05/1.01  --sat_fm_uc_incr                        true
% 3.05/1.01  --sat_out_model                         small
% 3.05/1.01  --sat_out_clauses                       false
% 3.05/1.01  
% 3.05/1.01  ------ QBF Options
% 3.05/1.01  
% 3.05/1.01  --qbf_mode                              false
% 3.05/1.01  --qbf_elim_univ                         false
% 3.05/1.01  --qbf_dom_inst                          none
% 3.05/1.01  --qbf_dom_pre_inst                      false
% 3.05/1.01  --qbf_sk_in                             false
% 3.05/1.01  --qbf_pred_elim                         true
% 3.05/1.01  --qbf_split                             512
% 3.05/1.01  
% 3.05/1.01  ------ BMC1 Options
% 3.05/1.01  
% 3.05/1.01  --bmc1_incremental                      false
% 3.05/1.01  --bmc1_axioms                           reachable_all
% 3.05/1.01  --bmc1_min_bound                        0
% 3.05/1.01  --bmc1_max_bound                        -1
% 3.05/1.01  --bmc1_max_bound_default                -1
% 3.05/1.01  --bmc1_symbol_reachability              true
% 3.05/1.01  --bmc1_property_lemmas                  false
% 3.05/1.01  --bmc1_k_induction                      false
% 3.05/1.01  --bmc1_non_equiv_states                 false
% 3.05/1.01  --bmc1_deadlock                         false
% 3.05/1.01  --bmc1_ucm                              false
% 3.05/1.01  --bmc1_add_unsat_core                   none
% 3.05/1.01  --bmc1_unsat_core_children              false
% 3.05/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.01  --bmc1_out_stat                         full
% 3.05/1.01  --bmc1_ground_init                      false
% 3.05/1.01  --bmc1_pre_inst_next_state              false
% 3.05/1.01  --bmc1_pre_inst_state                   false
% 3.05/1.01  --bmc1_pre_inst_reach_state             false
% 3.05/1.01  --bmc1_out_unsat_core                   false
% 3.05/1.01  --bmc1_aig_witness_out                  false
% 3.05/1.01  --bmc1_verbose                          false
% 3.05/1.01  --bmc1_dump_clauses_tptp                false
% 3.05/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.01  --bmc1_dump_file                        -
% 3.05/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.01  --bmc1_ucm_extend_mode                  1
% 3.05/1.01  --bmc1_ucm_init_mode                    2
% 3.05/1.01  --bmc1_ucm_cone_mode                    none
% 3.05/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.01  --bmc1_ucm_relax_model                  4
% 3.05/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.01  --bmc1_ucm_layered_model                none
% 3.05/1.01  --bmc1_ucm_max_lemma_size               10
% 3.05/1.01  
% 3.05/1.01  ------ AIG Options
% 3.05/1.01  
% 3.05/1.01  --aig_mode                              false
% 3.05/1.01  
% 3.05/1.01  ------ Instantiation Options
% 3.05/1.01  
% 3.05/1.01  --instantiation_flag                    true
% 3.05/1.01  --inst_sos_flag                         false
% 3.05/1.01  --inst_sos_phase                        true
% 3.05/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.01  --inst_lit_sel_side                     num_symb
% 3.05/1.01  --inst_solver_per_active                1400
% 3.05/1.01  --inst_solver_calls_frac                1.
% 3.05/1.01  --inst_passive_queue_type               priority_queues
% 3.05/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.01  --inst_passive_queues_freq              [25;2]
% 3.05/1.01  --inst_dismatching                      true
% 3.05/1.01  --inst_eager_unprocessed_to_passive     true
% 3.05/1.01  --inst_prop_sim_given                   true
% 3.05/1.01  --inst_prop_sim_new                     false
% 3.05/1.01  --inst_subs_new                         false
% 3.05/1.01  --inst_eq_res_simp                      false
% 3.05/1.01  --inst_subs_given                       false
% 3.05/1.01  --inst_orphan_elimination               true
% 3.05/1.01  --inst_learning_loop_flag               true
% 3.05/1.01  --inst_learning_start                   3000
% 3.05/1.01  --inst_learning_factor                  2
% 3.05/1.01  --inst_start_prop_sim_after_learn       3
% 3.05/1.01  --inst_sel_renew                        solver
% 3.05/1.01  --inst_lit_activity_flag                true
% 3.05/1.01  --inst_restr_to_given                   false
% 3.05/1.01  --inst_activity_threshold               500
% 3.05/1.01  --inst_out_proof                        true
% 3.05/1.01  
% 3.05/1.01  ------ Resolution Options
% 3.05/1.01  
% 3.05/1.01  --resolution_flag                       true
% 3.05/1.01  --res_lit_sel                           adaptive
% 3.05/1.01  --res_lit_sel_side                      none
% 3.05/1.01  --res_ordering                          kbo
% 3.05/1.01  --res_to_prop_solver                    active
% 3.05/1.01  --res_prop_simpl_new                    false
% 3.05/1.01  --res_prop_simpl_given                  true
% 3.05/1.01  --res_passive_queue_type                priority_queues
% 3.05/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.01  --res_passive_queues_freq               [15;5]
% 3.05/1.01  --res_forward_subs                      full
% 3.05/1.01  --res_backward_subs                     full
% 3.05/1.01  --res_forward_subs_resolution           true
% 3.05/1.01  --res_backward_subs_resolution          true
% 3.05/1.01  --res_orphan_elimination                true
% 3.05/1.01  --res_time_limit                        2.
% 3.05/1.01  --res_out_proof                         true
% 3.05/1.01  
% 3.05/1.01  ------ Superposition Options
% 3.05/1.01  
% 3.05/1.01  --superposition_flag                    true
% 3.05/1.01  --sup_passive_queue_type                priority_queues
% 3.05/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.05/1.01  --demod_completeness_check              fast
% 3.05/1.01  --demod_use_ground                      true
% 3.05/1.01  --sup_to_prop_solver                    passive
% 3.05/1.01  --sup_prop_simpl_new                    true
% 3.05/1.01  --sup_prop_simpl_given                  true
% 3.05/1.01  --sup_fun_splitting                     false
% 3.05/1.01  --sup_smt_interval                      50000
% 3.05/1.01  
% 3.05/1.01  ------ Superposition Simplification Setup
% 3.05/1.01  
% 3.05/1.01  --sup_indices_passive                   []
% 3.05/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.01  --sup_full_bw                           [BwDemod]
% 3.05/1.01  --sup_immed_triv                        [TrivRules]
% 3.05/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.01  --sup_immed_bw_main                     []
% 3.05/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.01  
% 3.05/1.01  ------ Combination Options
% 3.05/1.01  
% 3.05/1.01  --comb_res_mult                         3
% 3.05/1.01  --comb_sup_mult                         2
% 3.05/1.01  --comb_inst_mult                        10
% 3.05/1.01  
% 3.05/1.01  ------ Debug Options
% 3.05/1.01  
% 3.05/1.01  --dbg_backtrace                         false
% 3.05/1.01  --dbg_dump_prop_clauses                 false
% 3.05/1.01  --dbg_dump_prop_clauses_file            -
% 3.05/1.01  --dbg_out_stat                          false
% 3.05/1.01  ------ Parsing...
% 3.05/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/1.01  
% 3.05/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.05/1.01  
% 3.05/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/1.01  
% 3.05/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.05/1.01  ------ Proving...
% 3.05/1.01  ------ Problem Properties 
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  clauses                                 24
% 3.05/1.01  conjectures                             5
% 3.05/1.01  EPR                                     3
% 3.05/1.01  Horn                                    24
% 3.05/1.01  unary                                   6
% 3.05/1.01  binary                                  3
% 3.05/1.01  lits                                    77
% 3.05/1.01  lits eq                                 7
% 3.05/1.01  fd_pure                                 0
% 3.05/1.01  fd_pseudo                               0
% 3.05/1.01  fd_cond                                 0
% 3.05/1.01  fd_pseudo_cond                          0
% 3.05/1.01  AC symbols                              0
% 3.05/1.01  
% 3.05/1.01  ------ Schedule dynamic 5 is on 
% 3.05/1.01  
% 3.05/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  ------ 
% 3.05/1.01  Current options:
% 3.05/1.01  ------ 
% 3.05/1.01  
% 3.05/1.01  ------ Input Options
% 3.05/1.01  
% 3.05/1.01  --out_options                           all
% 3.05/1.01  --tptp_safe_out                         true
% 3.05/1.01  --problem_path                          ""
% 3.05/1.01  --include_path                          ""
% 3.05/1.01  --clausifier                            res/vclausify_rel
% 3.05/1.01  --clausifier_options                    --mode clausify
% 3.05/1.01  --stdin                                 false
% 3.05/1.01  --stats_out                             all
% 3.05/1.01  
% 3.05/1.01  ------ General Options
% 3.05/1.01  
% 3.05/1.01  --fof                                   false
% 3.05/1.01  --time_out_real                         305.
% 3.05/1.01  --time_out_virtual                      -1.
% 3.05/1.01  --symbol_type_check                     false
% 3.05/1.01  --clausify_out                          false
% 3.05/1.01  --sig_cnt_out                           false
% 3.05/1.01  --trig_cnt_out                          false
% 3.05/1.01  --trig_cnt_out_tolerance                1.
% 3.05/1.01  --trig_cnt_out_sk_spl                   false
% 3.05/1.01  --abstr_cl_out                          false
% 3.05/1.01  
% 3.05/1.01  ------ Global Options
% 3.05/1.01  
% 3.05/1.01  --schedule                              default
% 3.05/1.01  --add_important_lit                     false
% 3.05/1.01  --prop_solver_per_cl                    1000
% 3.05/1.01  --min_unsat_core                        false
% 3.05/1.01  --soft_assumptions                      false
% 3.05/1.01  --soft_lemma_size                       3
% 3.05/1.01  --prop_impl_unit_size                   0
% 3.05/1.01  --prop_impl_unit                        []
% 3.05/1.01  --share_sel_clauses                     true
% 3.05/1.01  --reset_solvers                         false
% 3.05/1.01  --bc_imp_inh                            [conj_cone]
% 3.05/1.01  --conj_cone_tolerance                   3.
% 3.05/1.01  --extra_neg_conj                        none
% 3.05/1.01  --large_theory_mode                     true
% 3.05/1.01  --prolific_symb_bound                   200
% 3.05/1.01  --lt_threshold                          2000
% 3.05/1.01  --clause_weak_htbl                      true
% 3.05/1.01  --gc_record_bc_elim                     false
% 3.05/1.01  
% 3.05/1.01  ------ Preprocessing Options
% 3.05/1.01  
% 3.05/1.01  --preprocessing_flag                    true
% 3.05/1.01  --time_out_prep_mult                    0.1
% 3.05/1.01  --splitting_mode                        input
% 3.05/1.01  --splitting_grd                         true
% 3.05/1.01  --splitting_cvd                         false
% 3.05/1.01  --splitting_cvd_svl                     false
% 3.05/1.01  --splitting_nvd                         32
% 3.05/1.01  --sub_typing                            true
% 3.05/1.01  --prep_gs_sim                           true
% 3.05/1.01  --prep_unflatten                        true
% 3.05/1.01  --prep_res_sim                          true
% 3.05/1.01  --prep_upred                            true
% 3.05/1.01  --prep_sem_filter                       exhaustive
% 3.05/1.01  --prep_sem_filter_out                   false
% 3.05/1.01  --pred_elim                             true
% 3.05/1.01  --res_sim_input                         true
% 3.05/1.01  --eq_ax_congr_red                       true
% 3.05/1.01  --pure_diseq_elim                       true
% 3.05/1.01  --brand_transform                       false
% 3.05/1.01  --non_eq_to_eq                          false
% 3.05/1.01  --prep_def_merge                        true
% 3.05/1.01  --prep_def_merge_prop_impl              false
% 3.05/1.01  --prep_def_merge_mbd                    true
% 3.05/1.01  --prep_def_merge_tr_red                 false
% 3.05/1.01  --prep_def_merge_tr_cl                  false
% 3.05/1.01  --smt_preprocessing                     true
% 3.05/1.01  --smt_ac_axioms                         fast
% 3.05/1.01  --preprocessed_out                      false
% 3.05/1.01  --preprocessed_stats                    false
% 3.05/1.01  
% 3.05/1.01  ------ Abstraction refinement Options
% 3.05/1.01  
% 3.05/1.01  --abstr_ref                             []
% 3.05/1.01  --abstr_ref_prep                        false
% 3.05/1.01  --abstr_ref_until_sat                   false
% 3.05/1.01  --abstr_ref_sig_restrict                funpre
% 3.05/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.01  --abstr_ref_under                       []
% 3.05/1.01  
% 3.05/1.01  ------ SAT Options
% 3.05/1.01  
% 3.05/1.01  --sat_mode                              false
% 3.05/1.01  --sat_fm_restart_options                ""
% 3.05/1.01  --sat_gr_def                            false
% 3.05/1.01  --sat_epr_types                         true
% 3.05/1.01  --sat_non_cyclic_types                  false
% 3.05/1.01  --sat_finite_models                     false
% 3.05/1.01  --sat_fm_lemmas                         false
% 3.05/1.01  --sat_fm_prep                           false
% 3.05/1.01  --sat_fm_uc_incr                        true
% 3.05/1.01  --sat_out_model                         small
% 3.05/1.01  --sat_out_clauses                       false
% 3.05/1.01  
% 3.05/1.01  ------ QBF Options
% 3.05/1.01  
% 3.05/1.01  --qbf_mode                              false
% 3.05/1.01  --qbf_elim_univ                         false
% 3.05/1.01  --qbf_dom_inst                          none
% 3.05/1.01  --qbf_dom_pre_inst                      false
% 3.05/1.01  --qbf_sk_in                             false
% 3.05/1.01  --qbf_pred_elim                         true
% 3.05/1.01  --qbf_split                             512
% 3.05/1.01  
% 3.05/1.01  ------ BMC1 Options
% 3.05/1.01  
% 3.05/1.01  --bmc1_incremental                      false
% 3.05/1.01  --bmc1_axioms                           reachable_all
% 3.05/1.01  --bmc1_min_bound                        0
% 3.05/1.01  --bmc1_max_bound                        -1
% 3.05/1.01  --bmc1_max_bound_default                -1
% 3.05/1.01  --bmc1_symbol_reachability              true
% 3.05/1.01  --bmc1_property_lemmas                  false
% 3.05/1.01  --bmc1_k_induction                      false
% 3.05/1.01  --bmc1_non_equiv_states                 false
% 3.05/1.01  --bmc1_deadlock                         false
% 3.05/1.01  --bmc1_ucm                              false
% 3.05/1.01  --bmc1_add_unsat_core                   none
% 3.05/1.01  --bmc1_unsat_core_children              false
% 3.05/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.01  --bmc1_out_stat                         full
% 3.05/1.01  --bmc1_ground_init                      false
% 3.05/1.01  --bmc1_pre_inst_next_state              false
% 3.05/1.01  --bmc1_pre_inst_state                   false
% 3.05/1.01  --bmc1_pre_inst_reach_state             false
% 3.05/1.01  --bmc1_out_unsat_core                   false
% 3.05/1.01  --bmc1_aig_witness_out                  false
% 3.05/1.01  --bmc1_verbose                          false
% 3.05/1.01  --bmc1_dump_clauses_tptp                false
% 3.05/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.01  --bmc1_dump_file                        -
% 3.05/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.01  --bmc1_ucm_extend_mode                  1
% 3.05/1.01  --bmc1_ucm_init_mode                    2
% 3.05/1.01  --bmc1_ucm_cone_mode                    none
% 3.05/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.01  --bmc1_ucm_relax_model                  4
% 3.05/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.01  --bmc1_ucm_layered_model                none
% 3.05/1.01  --bmc1_ucm_max_lemma_size               10
% 3.05/1.01  
% 3.05/1.01  ------ AIG Options
% 3.05/1.01  
% 3.05/1.01  --aig_mode                              false
% 3.05/1.01  
% 3.05/1.01  ------ Instantiation Options
% 3.05/1.01  
% 3.05/1.01  --instantiation_flag                    true
% 3.05/1.01  --inst_sos_flag                         false
% 3.05/1.01  --inst_sos_phase                        true
% 3.05/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.01  --inst_lit_sel_side                     none
% 3.05/1.01  --inst_solver_per_active                1400
% 3.05/1.01  --inst_solver_calls_frac                1.
% 3.05/1.01  --inst_passive_queue_type               priority_queues
% 3.05/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.01  --inst_passive_queues_freq              [25;2]
% 3.05/1.01  --inst_dismatching                      true
% 3.05/1.01  --inst_eager_unprocessed_to_passive     true
% 3.05/1.01  --inst_prop_sim_given                   true
% 3.05/1.01  --inst_prop_sim_new                     false
% 3.05/1.01  --inst_subs_new                         false
% 3.05/1.01  --inst_eq_res_simp                      false
% 3.05/1.01  --inst_subs_given                       false
% 3.05/1.01  --inst_orphan_elimination               true
% 3.05/1.01  --inst_learning_loop_flag               true
% 3.05/1.01  --inst_learning_start                   3000
% 3.05/1.01  --inst_learning_factor                  2
% 3.05/1.01  --inst_start_prop_sim_after_learn       3
% 3.05/1.01  --inst_sel_renew                        solver
% 3.05/1.01  --inst_lit_activity_flag                true
% 3.05/1.01  --inst_restr_to_given                   false
% 3.05/1.01  --inst_activity_threshold               500
% 3.05/1.01  --inst_out_proof                        true
% 3.05/1.01  
% 3.05/1.01  ------ Resolution Options
% 3.05/1.01  
% 3.05/1.01  --resolution_flag                       false
% 3.05/1.01  --res_lit_sel                           adaptive
% 3.05/1.01  --res_lit_sel_side                      none
% 3.05/1.01  --res_ordering                          kbo
% 3.05/1.01  --res_to_prop_solver                    active
% 3.05/1.01  --res_prop_simpl_new                    false
% 3.05/1.01  --res_prop_simpl_given                  true
% 3.05/1.01  --res_passive_queue_type                priority_queues
% 3.05/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.01  --res_passive_queues_freq               [15;5]
% 3.05/1.01  --res_forward_subs                      full
% 3.05/1.01  --res_backward_subs                     full
% 3.05/1.01  --res_forward_subs_resolution           true
% 3.05/1.01  --res_backward_subs_resolution          true
% 3.05/1.01  --res_orphan_elimination                true
% 3.05/1.01  --res_time_limit                        2.
% 3.05/1.01  --res_out_proof                         true
% 3.05/1.01  
% 3.05/1.01  ------ Superposition Options
% 3.05/1.01  
% 3.05/1.01  --superposition_flag                    true
% 3.05/1.01  --sup_passive_queue_type                priority_queues
% 3.05/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.05/1.01  --demod_completeness_check              fast
% 3.05/1.01  --demod_use_ground                      true
% 3.05/1.01  --sup_to_prop_solver                    passive
% 3.05/1.01  --sup_prop_simpl_new                    true
% 3.05/1.01  --sup_prop_simpl_given                  true
% 3.05/1.01  --sup_fun_splitting                     false
% 3.05/1.01  --sup_smt_interval                      50000
% 3.05/1.01  
% 3.05/1.01  ------ Superposition Simplification Setup
% 3.05/1.01  
% 3.05/1.01  --sup_indices_passive                   []
% 3.05/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.01  --sup_full_bw                           [BwDemod]
% 3.05/1.01  --sup_immed_triv                        [TrivRules]
% 3.05/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.01  --sup_immed_bw_main                     []
% 3.05/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.01  
% 3.05/1.01  ------ Combination Options
% 3.05/1.01  
% 3.05/1.01  --comb_res_mult                         3
% 3.05/1.01  --comb_sup_mult                         2
% 3.05/1.01  --comb_inst_mult                        10
% 3.05/1.01  
% 3.05/1.01  ------ Debug Options
% 3.05/1.01  
% 3.05/1.01  --dbg_backtrace                         false
% 3.05/1.01  --dbg_dump_prop_clauses                 false
% 3.05/1.01  --dbg_dump_prop_clauses_file            -
% 3.05/1.01  --dbg_out_stat                          false
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  ------ Proving...
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  % SZS status Theorem for theBenchmark.p
% 3.05/1.01  
% 3.05/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/1.01  
% 3.05/1.01  fof(f15,conjecture,(
% 3.05/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f16,negated_conjecture,(
% 3.05/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.05/1.01    inference(negated_conjecture,[],[f15])).
% 3.05/1.01  
% 3.05/1.01  fof(f39,plain,(
% 3.05/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.05/1.01    inference(ennf_transformation,[],[f16])).
% 3.05/1.01  
% 3.05/1.01  fof(f40,plain,(
% 3.05/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.05/1.01    inference(flattening,[],[f39])).
% 3.05/1.01  
% 3.05/1.01  fof(f43,plain,(
% 3.05/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.05/1.01    introduced(choice_axiom,[])).
% 3.05/1.01  
% 3.05/1.01  fof(f44,plain,(
% 3.05/1.01    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.05/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f43])).
% 3.05/1.01  
% 3.05/1.01  fof(f69,plain,(
% 3.05/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.05/1.01    inference(cnf_transformation,[],[f44])).
% 3.05/1.01  
% 3.05/1.01  fof(f12,axiom,(
% 3.05/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f35,plain,(
% 3.05/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.05/1.01    inference(ennf_transformation,[],[f12])).
% 3.05/1.01  
% 3.05/1.01  fof(f36,plain,(
% 3.05/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.05/1.01    inference(flattening,[],[f35])).
% 3.05/1.01  
% 3.05/1.01  fof(f63,plain,(
% 3.05/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f36])).
% 3.05/1.01  
% 3.05/1.01  fof(f66,plain,(
% 3.05/1.01    v1_funct_1(sK2)),
% 3.05/1.01    inference(cnf_transformation,[],[f44])).
% 3.05/1.01  
% 3.05/1.01  fof(f67,plain,(
% 3.05/1.01    v1_funct_2(sK2,sK1,sK1)),
% 3.05/1.01    inference(cnf_transformation,[],[f44])).
% 3.05/1.01  
% 3.05/1.01  fof(f68,plain,(
% 3.05/1.01    v3_funct_2(sK2,sK1,sK1)),
% 3.05/1.01    inference(cnf_transformation,[],[f44])).
% 3.05/1.01  
% 3.05/1.01  fof(f9,axiom,(
% 3.05/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f31,plain,(
% 3.05/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.05/1.01    inference(ennf_transformation,[],[f9])).
% 3.05/1.01  
% 3.05/1.01  fof(f32,plain,(
% 3.05/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.05/1.01    inference(flattening,[],[f31])).
% 3.05/1.01  
% 3.05/1.01  fof(f60,plain,(
% 3.05/1.01    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f32])).
% 3.05/1.01  
% 3.05/1.01  fof(f14,axiom,(
% 3.05/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f37,plain,(
% 3.05/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.05/1.01    inference(ennf_transformation,[],[f14])).
% 3.05/1.01  
% 3.05/1.01  fof(f38,plain,(
% 3.05/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.05/1.01    inference(flattening,[],[f37])).
% 3.05/1.01  
% 3.05/1.01  fof(f65,plain,(
% 3.05/1.01    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f38])).
% 3.05/1.01  
% 3.05/1.01  fof(f6,axiom,(
% 3.05/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f26,plain,(
% 3.05/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.01    inference(ennf_transformation,[],[f6])).
% 3.05/1.01  
% 3.05/1.01  fof(f53,plain,(
% 3.05/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.01    inference(cnf_transformation,[],[f26])).
% 3.05/1.01  
% 3.05/1.01  fof(f2,axiom,(
% 3.05/1.01    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f19,plain,(
% 3.05/1.01    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/1.01    inference(ennf_transformation,[],[f2])).
% 3.05/1.01  
% 3.05/1.01  fof(f20,plain,(
% 3.05/1.01    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/1.01    inference(flattening,[],[f19])).
% 3.05/1.01  
% 3.05/1.01  fof(f47,plain,(
% 3.05/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f20])).
% 3.05/1.01  
% 3.05/1.01  fof(f5,axiom,(
% 3.05/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f25,plain,(
% 3.05/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.01    inference(ennf_transformation,[],[f5])).
% 3.05/1.01  
% 3.05/1.01  fof(f52,plain,(
% 3.05/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.01    inference(cnf_transformation,[],[f25])).
% 3.05/1.01  
% 3.05/1.01  fof(f8,axiom,(
% 3.05/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f18,plain,(
% 3.05/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.05/1.01    inference(pure_predicate_removal,[],[f8])).
% 3.05/1.01  
% 3.05/1.01  fof(f29,plain,(
% 3.05/1.01    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.01    inference(ennf_transformation,[],[f18])).
% 3.05/1.01  
% 3.05/1.01  fof(f30,plain,(
% 3.05/1.01    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.01    inference(flattening,[],[f29])).
% 3.05/1.01  
% 3.05/1.01  fof(f56,plain,(
% 3.05/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.01    inference(cnf_transformation,[],[f30])).
% 3.05/1.01  
% 3.05/1.01  fof(f58,plain,(
% 3.05/1.01    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f32])).
% 3.05/1.01  
% 3.05/1.01  fof(f3,axiom,(
% 3.05/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f21,plain,(
% 3.05/1.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/1.01    inference(ennf_transformation,[],[f3])).
% 3.05/1.01  
% 3.05/1.01  fof(f22,plain,(
% 3.05/1.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/1.01    inference(flattening,[],[f21])).
% 3.05/1.01  
% 3.05/1.01  fof(f49,plain,(
% 3.05/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f22])).
% 3.05/1.01  
% 3.05/1.01  fof(f13,axiom,(
% 3.05/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f64,plain,(
% 3.05/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f13])).
% 3.05/1.01  
% 3.05/1.01  fof(f72,plain,(
% 3.05/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/1.01    inference(definition_unfolding,[],[f49,f64])).
% 3.05/1.01  
% 3.05/1.01  fof(f4,axiom,(
% 3.05/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f23,plain,(
% 3.05/1.01    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.05/1.01    inference(ennf_transformation,[],[f4])).
% 3.05/1.01  
% 3.05/1.01  fof(f24,plain,(
% 3.05/1.01    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.05/1.01    inference(flattening,[],[f23])).
% 3.05/1.01  
% 3.05/1.01  fof(f51,plain,(
% 3.05/1.01    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f24])).
% 3.05/1.01  
% 3.05/1.01  fof(f50,plain,(
% 3.05/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f22])).
% 3.05/1.01  
% 3.05/1.01  fof(f71,plain,(
% 3.05/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/1.01    inference(definition_unfolding,[],[f50,f64])).
% 3.05/1.01  
% 3.05/1.01  fof(f48,plain,(
% 3.05/1.01    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f20])).
% 3.05/1.01  
% 3.05/1.01  fof(f11,axiom,(
% 3.05/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f33,plain,(
% 3.05/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.05/1.01    inference(ennf_transformation,[],[f11])).
% 3.05/1.01  
% 3.05/1.01  fof(f34,plain,(
% 3.05/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.05/1.01    inference(flattening,[],[f33])).
% 3.05/1.01  
% 3.05/1.01  fof(f62,plain,(
% 3.05/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f34])).
% 3.05/1.01  
% 3.05/1.01  fof(f57,plain,(
% 3.05/1.01    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.05/1.01    inference(cnf_transformation,[],[f32])).
% 3.05/1.01  
% 3.05/1.01  fof(f70,plain,(
% 3.05/1.01    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.05/1.01    inference(cnf_transformation,[],[f44])).
% 3.05/1.01  
% 3.05/1.01  fof(f10,axiom,(
% 3.05/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f17,plain,(
% 3.05/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.05/1.01    inference(pure_predicate_removal,[],[f10])).
% 3.05/1.01  
% 3.05/1.01  fof(f61,plain,(
% 3.05/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.05/1.01    inference(cnf_transformation,[],[f17])).
% 3.05/1.01  
% 3.05/1.01  fof(f7,axiom,(
% 3.05/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.05/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.01  
% 3.05/1.01  fof(f27,plain,(
% 3.05/1.01    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.05/1.01    inference(ennf_transformation,[],[f7])).
% 3.05/1.01  
% 3.05/1.01  fof(f28,plain,(
% 3.05/1.01    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.05/1.01    inference(flattening,[],[f27])).
% 3.05/1.01  
% 3.05/1.01  fof(f54,plain,(
% 3.05/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.05/1.01    inference(cnf_transformation,[],[f28])).
% 3.05/1.01  
% 3.05/1.01  cnf(c_21,negated_conjecture,
% 3.05/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.05/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_445,negated_conjecture,
% 3.05/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_995,plain,
% 3.05/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_18,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.05/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.05/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_448,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_992,plain,
% 3.05/1.01      ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
% 3.05/1.01      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2821,plain,
% 3.05/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.05/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_995,c_992]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_24,negated_conjecture,
% 3.05/1.01      ( v1_funct_1(sK2) ),
% 3.05/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_23,negated_conjecture,
% 3.05/1.01      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.05/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_22,negated_conjecture,
% 3.05/1.01      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.05/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_556,plain,
% 3.05/1.01      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.05/1.01      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.05/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.05/1.01      | ~ v1_funct_1(sK2)
% 3.05/1.01      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_448]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3178,plain,
% 3.05/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_2821,c_24,c_23,c_22,c_21,c_556]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_12,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.05/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.05/1.01      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.05/1.01      | ~ v1_funct_1(X0) ),
% 3.05/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_454,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.05/1.01      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.05/1.01      | ~ v1_funct_1(X0_48) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_986,plain,
% 3.05/1.01      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3191,plain,
% 3.05/1.01      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.05/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_3178,c_986]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_25,plain,
% 3.05/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_26,plain,
% 3.05/1.01      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_27,plain,
% 3.05/1.01      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_28,plain,
% 3.05/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3395,plain,
% 3.05/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_3191,c_25,c_26,c_27,c_28]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_19,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.05/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_447,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | k1_relset_1(X0_49,X0_49,X0_48) = X0_49 ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_993,plain,
% 3.05/1.01      ( k1_relset_1(X0_49,X0_49,X0_48) = X0_49
% 3.05/1.01      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3404,plain,
% 3.05/1.01      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
% 3.05/1.01      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.05/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_3395,c_993]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_8,plain,
% 3.05/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.05/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_457,plain,
% 3.05/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.05/1.01      | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_983,plain,
% 3.05/1.01      ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3407,plain,
% 3.05/1.01      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_3395,c_983]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3423,plain,
% 3.05/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.05/1.01      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.05/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/1.01      inference(demodulation,[status(thm)],[c_3404,c_3407]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0)
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.05/1.01      | ~ v2_funct_1(X0) ),
% 3.05/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_463,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0_48)
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | v1_funct_1(k2_funct_1(X0_48))
% 3.05/1.01      | ~ v2_funct_1(X0_48) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_512,plain,
% 3.05/1.01      ( v1_relat_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(k2_funct_1(X0_48)) = iProver_top
% 3.05/1.01      | v2_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_514,plain,
% 3.05/1.01      ( v1_relat_1(sK2) != iProver_top
% 3.05/1.01      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top
% 3.05/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_512]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_7,plain,
% 3.05/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.01      | v1_relat_1(X0) ),
% 3.05/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_458,plain,
% 3.05/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.05/1.01      | v1_relat_1(X0_48) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_527,plain,
% 3.05/1.01      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | v1_relat_1(X0_48) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_529,plain,
% 3.05/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.05/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_527]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_10,plain,
% 3.05/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | v2_funct_1(X0) ),
% 3.05/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_455,plain,
% 3.05/1.01      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.05/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | v2_funct_1(X0_48) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_536,plain,
% 3.05/1.01      ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v2_funct_1(X0_48) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_538,plain,
% 3.05/1.01      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top
% 3.05/1.01      | v2_funct_1(sK2) = iProver_top ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_536]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_14,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.05/1.01      | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.05/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.05/1.01      | ~ v1_funct_1(X0) ),
% 3.05/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_452,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.05/1.01      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.05/1.01      | ~ v1_funct_1(X0_48) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_988,plain,
% 3.05/1.01      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.05/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3021,plain,
% 3.05/1.01      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.05/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_995,c_988]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_545,plain,
% 3.05/1.01      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.05/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_547,plain,
% 3.05/1.01      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.05/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_545]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3287,plain,
% 3.05/1.01      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_3021,c_25,c_26,c_27,c_28,c_547]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3291,plain,
% 3.05/1.01      ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
% 3.05/1.01      inference(light_normalisation,[status(thm)],[c_3287,c_3178]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_6803,plain,
% 3.05/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_3423,c_25,c_27,c_28,c_514,c_529,c_538,c_3291]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_982,plain,
% 3.05/1.01      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | v1_relat_1(X0_48) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3408,plain,
% 3.05/1.01      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_3395,c_982]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_5,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0)
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | ~ v2_funct_1(X0)
% 3.05/1.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.05/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_460,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0_48)
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | ~ v2_funct_1(X0_48)
% 3.05/1.01      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_980,plain,
% 3.05/1.01      ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
% 3.05/1.01      | v1_relat_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v2_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3585,plain,
% 3.05/1.01      ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
% 3.05/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.05/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_3408,c_980]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_1251,plain,
% 3.05/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_995,c_982]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_6,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0)
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | ~ v2_funct_1(X0)
% 3.05/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.05/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_459,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0_48)
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | ~ v2_funct_1(X0_48)
% 3.05/1.01      | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_981,plain,
% 3.05/1.01      ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
% 3.05/1.01      | v1_relat_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v2_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_1496,plain,
% 3.05/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top
% 3.05/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_1251,c_981]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_525,plain,
% 3.05/1.01      ( ~ v1_relat_1(sK2)
% 3.05/1.01      | ~ v1_funct_1(sK2)
% 3.05/1.01      | ~ v2_funct_1(sK2)
% 3.05/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_459]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_528,plain,
% 3.05/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.05/1.01      | v1_relat_1(sK2) ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_458]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_537,plain,
% 3.05/1.01      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.05/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.05/1.01      | ~ v1_funct_1(sK2)
% 3.05/1.01      | v2_funct_1(sK2) ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_455]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_1566,plain,
% 3.05/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_1496,c_24,c_22,c_21,c_525,c_528,c_537]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0)
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | ~ v2_funct_1(X0)
% 3.05/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.05/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_461,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0_48)
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | ~ v2_funct_1(X0_48)
% 3.05/1.01      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_979,plain,
% 3.05/1.01      ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
% 3.05/1.01      | v1_relat_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v2_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_1819,plain,
% 3.05/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top
% 3.05/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_1251,c_979]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_519,plain,
% 3.05/1.01      ( ~ v1_relat_1(sK2)
% 3.05/1.01      | ~ v1_funct_1(sK2)
% 3.05/1.01      | ~ v2_funct_1(sK2)
% 3.05/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_461]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2350,plain,
% 3.05/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_1819,c_24,c_22,c_21,c_519,c_528,c_537]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3602,plain,
% 3.05/1.01      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2))
% 3.05/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.05/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/1.01      inference(light_normalisation,[status(thm)],[c_3585,c_1566,c_2350]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_1,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0)
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | ~ v2_funct_1(X0)
% 3.05/1.01      | v2_funct_1(k2_funct_1(X0)) ),
% 3.05/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_464,plain,
% 3.05/1.01      ( ~ v1_relat_1(X0_48)
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | ~ v2_funct_1(X0_48)
% 3.05/1.01      | v2_funct_1(k2_funct_1(X0_48)) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_509,plain,
% 3.05/1.01      ( v1_relat_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v2_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v2_funct_1(k2_funct_1(X0_48)) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_511,plain,
% 3.05/1.01      ( v1_relat_1(sK2) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top
% 3.05/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.05/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_509]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4907,plain,
% 3.05/1.01      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_3602,c_25,c_27,c_28,c_511,c_514,c_529,c_538]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_6810,plain,
% 3.05/1.01      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 3.05/1.01      inference(demodulation,[status(thm)],[c_6803,c_4907]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_17,plain,
% 3.05/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.05/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | ~ v1_funct_1(X3)
% 3.05/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.05/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_449,plain,
% 3.05/1.01      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.05/1.01      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | ~ v1_funct_1(X1_48)
% 3.05/1.01      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_991,plain,
% 3.05/1.01      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 3.05/1.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(X1_48) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3618,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_3395,c_991]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_5054,plain,
% 3.05/1.01      ( v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_3618,c_25,c_27,c_28,c_514,c_529,c_538]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_5055,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(renaming,[status(thm)],[c_5054]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_5063,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_995,c_5055]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_5094,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(light_normalisation,[status(thm)],[c_5063,c_2350]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_5240,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_5094,c_25]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3614,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_995,c_991]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3983,plain,
% 3.05/1.01      ( v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_3614,c_25]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3984,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(renaming,[status(thm)],[c_3983]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3992,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
% 3.05/1.01      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_986,c_3984]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_15,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.05/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.05/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.05/1.01      | ~ v1_funct_1(X0)
% 3.05/1.01      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.05/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_451,plain,
% 3.05/1.01      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.05/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.05/1.01      | ~ v1_funct_1(X0_48)
% 3.05/1.01      | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_548,plain,
% 3.05/1.01      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4256,plain,
% 3.05/1.01      ( v1_funct_1(X0_48) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48)) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_3992,c_548]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4257,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
% 3.05/1.01      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.05/1.01      | v1_funct_1(X0_48) != iProver_top ),
% 3.05/1.01      inference(renaming,[status(thm)],[c_4256]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4267,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
% 3.05/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_995,c_4257]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_1961,plain,
% 3.05/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top
% 3.05/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_1251,c_980]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_522,plain,
% 3.05/1.01      ( ~ v1_relat_1(sK2)
% 3.05/1.01      | ~ v1_funct_1(sK2)
% 3.05/1.01      | ~ v2_funct_1(sK2)
% 3.05/1.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_460]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2420,plain,
% 3.05/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_1961,c_24,c_22,c_21,c_522,c_528,c_537]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2137,plain,
% 3.05/1.01      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.05/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_995,c_993]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_1367,plain,
% 3.05/1.01      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_995,c_983]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2157,plain,
% 3.05/1.01      ( k1_relat_1(sK2) = sK1
% 3.05/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(demodulation,[status(thm)],[c_2137,c_1367]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2253,plain,
% 3.05/1.01      ( k1_relat_1(sK2) = sK1 ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_2157,c_25,c_26]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2422,plain,
% 3.05/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.05/1.01      inference(light_normalisation,[status(thm)],[c_2420,c_2253]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4316,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.05/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.05/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.05/1.01      inference(light_normalisation,[status(thm)],[c_4267,c_2422,c_3178]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3994,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.05/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_3395,c_3984]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3997,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.05/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.05/1.01      inference(light_normalisation,[status(thm)],[c_3994,c_2422]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4333,plain,
% 3.05/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_4316,c_25,c_27,c_28,c_514,c_529,c_538,c_3997]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_20,negated_conjecture,
% 3.05/1.01      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.05/1.01      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.05/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_446,negated_conjecture,
% 3.05/1.01      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.05/1.01      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_994,plain,
% 3.05/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.05/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_3182,plain,
% 3.05/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.05/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.05/1.01      inference(demodulation,[status(thm)],[c_3178,c_994]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4336,plain,
% 3.05/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.05/1.01      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.05/1.01      inference(demodulation,[status(thm)],[c_4333,c_3182]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_16,plain,
% 3.05/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.05/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_450,plain,
% 3.05/1.01      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_990,plain,
% 3.05/1.01      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_9,plain,
% 3.05/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.05/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.05/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.05/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_456,plain,
% 3.05/1.01      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
% 3.05/1.01      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.05/1.01      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
% 3.05/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_984,plain,
% 3.05/1.01      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.05/1.01      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.05/1.01      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2009,plain,
% 3.05/1.01      ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
% 3.05/1.01      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
% 3.05/1.01      inference(superposition,[status(thm)],[c_990,c_984]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_2025,plain,
% 3.05/1.01      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 3.05/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.05/1.01      inference(instantiation,[status(thm)],[c_2009]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_4465,plain,
% 3.05/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
% 3.05/1.01      inference(global_propositional_subsumption,
% 3.05/1.01                [status(thm)],
% 3.05/1.01                [c_4336,c_28,c_2025]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_5243,plain,
% 3.05/1.01      ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.05/1.01      inference(demodulation,[status(thm)],[c_5240,c_4465]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(c_6828,plain,
% 3.05/1.01      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.05/1.01      inference(demodulation,[status(thm)],[c_6810,c_5243]) ).
% 3.05/1.01  
% 3.05/1.01  cnf(contradiction,plain,
% 3.05/1.01      ( $false ),
% 3.05/1.01      inference(minisat,[status(thm)],[c_6828,c_2025,c_28]) ).
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/1.01  
% 3.05/1.01  ------                               Statistics
% 3.05/1.01  
% 3.05/1.01  ------ General
% 3.05/1.01  
% 3.05/1.01  abstr_ref_over_cycles:                  0
% 3.05/1.01  abstr_ref_under_cycles:                 0
% 3.05/1.01  gc_basic_clause_elim:                   0
% 3.05/1.01  forced_gc_time:                         0
% 3.05/1.01  parsing_time:                           0.015
% 3.05/1.01  unif_index_cands_time:                  0.
% 3.05/1.01  unif_index_add_time:                    0.
% 3.05/1.01  orderings_time:                         0.
% 3.05/1.01  out_proof_time:                         0.012
% 3.05/1.01  total_time:                             0.249
% 3.05/1.01  num_of_symbols:                         55
% 3.05/1.01  num_of_terms:                           6095
% 3.05/1.01  
% 3.05/1.01  ------ Preprocessing
% 3.05/1.01  
% 3.05/1.01  num_of_splits:                          0
% 3.05/1.01  num_of_split_atoms:                     0
% 3.05/1.01  num_of_reused_defs:                     0
% 3.05/1.01  num_eq_ax_congr_red:                    18
% 3.05/1.01  num_of_sem_filtered_clauses:            1
% 3.05/1.01  num_of_subtypes:                        4
% 3.05/1.01  monotx_restored_types:                  1
% 3.05/1.01  sat_num_of_epr_types:                   0
% 3.05/1.01  sat_num_of_non_cyclic_types:            0
% 3.05/1.01  sat_guarded_non_collapsed_types:        1
% 3.05/1.01  num_pure_diseq_elim:                    0
% 3.05/1.01  simp_replaced_by:                       0
% 3.05/1.01  res_preprocessed:                       137
% 3.05/1.01  prep_upred:                             0
% 3.05/1.01  prep_unflattend:                        0
% 3.05/1.01  smt_new_axioms:                         0
% 3.05/1.01  pred_elim_cands:                        7
% 3.05/1.01  pred_elim:                              0
% 3.05/1.01  pred_elim_cl:                           0
% 3.05/1.01  pred_elim_cycles:                       2
% 3.05/1.01  merged_defs:                            0
% 3.05/1.01  merged_defs_ncl:                        0
% 3.05/1.01  bin_hyper_res:                          0
% 3.05/1.01  prep_cycles:                            4
% 3.05/1.01  pred_elim_time:                         0.001
% 3.05/1.01  splitting_time:                         0.
% 3.05/1.01  sem_filter_time:                        0.
% 3.05/1.01  monotx_time:                            0.001
% 3.05/1.01  subtype_inf_time:                       0.001
% 3.05/1.01  
% 3.05/1.01  ------ Problem properties
% 3.05/1.01  
% 3.05/1.01  clauses:                                24
% 3.05/1.01  conjectures:                            5
% 3.05/1.01  epr:                                    3
% 3.05/1.01  horn:                                   24
% 3.05/1.01  ground:                                 5
% 3.05/1.01  unary:                                  6
% 3.05/1.01  binary:                                 3
% 3.05/1.01  lits:                                   77
% 3.05/1.01  lits_eq:                                7
% 3.05/1.01  fd_pure:                                0
% 3.05/1.01  fd_pseudo:                              0
% 3.05/1.01  fd_cond:                                0
% 3.05/1.01  fd_pseudo_cond:                         0
% 3.05/1.01  ac_symbols:                             0
% 3.05/1.01  
% 3.05/1.01  ------ Propositional Solver
% 3.05/1.01  
% 3.05/1.01  prop_solver_calls:                      30
% 3.05/1.01  prop_fast_solver_calls:                 1190
% 3.05/1.01  smt_solver_calls:                       0
% 3.05/1.01  smt_fast_solver_calls:                  0
% 3.05/1.01  prop_num_of_clauses:                    2152
% 3.05/1.01  prop_preprocess_simplified:             6869
% 3.05/1.01  prop_fo_subsumed:                       69
% 3.05/1.01  prop_solver_time:                       0.
% 3.05/1.01  smt_solver_time:                        0.
% 3.05/1.01  smt_fast_solver_time:                   0.
% 3.05/1.01  prop_fast_solver_time:                  0.
% 3.05/1.01  prop_unsat_core_time:                   0.
% 3.05/1.01  
% 3.05/1.01  ------ QBF
% 3.05/1.01  
% 3.05/1.01  qbf_q_res:                              0
% 3.05/1.01  qbf_num_tautologies:                    0
% 3.05/1.01  qbf_prep_cycles:                        0
% 3.05/1.01  
% 3.05/1.01  ------ BMC1
% 3.05/1.01  
% 3.05/1.01  bmc1_current_bound:                     -1
% 3.05/1.01  bmc1_last_solved_bound:                 -1
% 3.05/1.01  bmc1_unsat_core_size:                   -1
% 3.05/1.01  bmc1_unsat_core_parents_size:           -1
% 3.05/1.01  bmc1_merge_next_fun:                    0
% 3.05/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.05/1.01  
% 3.05/1.01  ------ Instantiation
% 3.05/1.01  
% 3.05/1.01  inst_num_of_clauses:                    776
% 3.05/1.01  inst_num_in_passive:                    300
% 3.05/1.01  inst_num_in_active:                     438
% 3.05/1.01  inst_num_in_unprocessed:                38
% 3.05/1.01  inst_num_of_loops:                      460
% 3.05/1.01  inst_num_of_learning_restarts:          0
% 3.05/1.01  inst_num_moves_active_passive:          17
% 3.05/1.01  inst_lit_activity:                      0
% 3.05/1.01  inst_lit_activity_moves:                0
% 3.05/1.01  inst_num_tautologies:                   0
% 3.05/1.01  inst_num_prop_implied:                  0
% 3.05/1.01  inst_num_existing_simplified:           0
% 3.05/1.01  inst_num_eq_res_simplified:             0
% 3.05/1.01  inst_num_child_elim:                    0
% 3.05/1.01  inst_num_of_dismatching_blockings:      629
% 3.05/1.01  inst_num_of_non_proper_insts:           1011
% 3.05/1.01  inst_num_of_duplicates:                 0
% 3.05/1.01  inst_inst_num_from_inst_to_res:         0
% 3.05/1.01  inst_dismatching_checking_time:         0.
% 3.05/1.01  
% 3.05/1.01  ------ Resolution
% 3.05/1.01  
% 3.05/1.01  res_num_of_clauses:                     0
% 3.05/1.01  res_num_in_passive:                     0
% 3.05/1.01  res_num_in_active:                      0
% 3.05/1.01  res_num_of_loops:                       141
% 3.05/1.01  res_forward_subset_subsumed:            117
% 3.05/1.01  res_backward_subset_subsumed:           4
% 3.05/1.01  res_forward_subsumed:                   0
% 3.05/1.01  res_backward_subsumed:                  0
% 3.05/1.01  res_forward_subsumption_resolution:     0
% 3.05/1.01  res_backward_subsumption_resolution:    0
% 3.05/1.01  res_clause_to_clause_subsumption:       335
% 3.05/1.01  res_orphan_elimination:                 0
% 3.05/1.01  res_tautology_del:                      120
% 3.05/1.01  res_num_eq_res_simplified:              0
% 3.05/1.01  res_num_sel_changes:                    0
% 3.05/1.01  res_moves_from_active_to_pass:          0
% 3.05/1.01  
% 3.05/1.01  ------ Superposition
% 3.05/1.01  
% 3.05/1.01  sup_time_total:                         0.
% 3.05/1.01  sup_time_generating:                    0.
% 3.05/1.01  sup_time_sim_full:                      0.
% 3.05/1.01  sup_time_sim_immed:                     0.
% 3.05/1.01  
% 3.05/1.01  sup_num_of_clauses:                     130
% 3.05/1.01  sup_num_in_active:                      74
% 3.05/1.01  sup_num_in_passive:                     56
% 3.05/1.01  sup_num_of_loops:                       91
% 3.05/1.01  sup_fw_superposition:                   93
% 3.05/1.01  sup_bw_superposition:                   71
% 3.05/1.01  sup_immediate_simplified:               68
% 3.05/1.01  sup_given_eliminated:                   0
% 3.05/1.01  comparisons_done:                       0
% 3.05/1.01  comparisons_avoided:                    0
% 3.05/1.01  
% 3.05/1.01  ------ Simplifications
% 3.05/1.01  
% 3.05/1.01  
% 3.05/1.01  sim_fw_subset_subsumed:                 6
% 3.05/1.01  sim_bw_subset_subsumed:                 5
% 3.05/1.01  sim_fw_subsumed:                        15
% 3.05/1.01  sim_bw_subsumed:                        1
% 3.05/1.01  sim_fw_subsumption_res:                 3
% 3.05/1.01  sim_bw_subsumption_res:                 0
% 3.05/1.01  sim_tautology_del:                      0
% 3.05/1.01  sim_eq_tautology_del:                   8
% 3.05/1.01  sim_eq_res_simp:                        0
% 3.05/1.01  sim_fw_demodulated:                     4
% 3.05/1.01  sim_bw_demodulated:                     15
% 3.05/1.01  sim_light_normalised:                   44
% 3.05/1.01  sim_joinable_taut:                      0
% 3.05/1.01  sim_joinable_simp:                      0
% 3.05/1.01  sim_ac_normalised:                      0
% 3.05/1.01  sim_smt_subsumption:                    0
% 3.05/1.01  
%------------------------------------------------------------------------------
