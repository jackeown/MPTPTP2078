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
% DateTime   : Thu Dec  3 12:07:18 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  197 (2099 expanded)
%              Number of clauses        :  136 ( 659 expanded)
%              Number of leaves         :   14 ( 402 expanded)
%              Depth                    :   22
%              Number of atoms          :  661 (10115 expanded)
%              Number of equality atoms :  304 (1027 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f47,plain,
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

fof(f48,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f47])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
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

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_443,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_987,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_978,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_445,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k1_relset_1(X0_49,X0_49,X0_48) = X0_49 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_985,plain,
    ( k1_relset_1(X0_49,X0_49,X0_48) = X0_49
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_2358,plain,
    ( k1_relset_1(X0_49,X0_49,k2_funct_2(X0_49,X0_48)) = X0_49
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_985])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_450,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_537,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_449,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_540,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_6652,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | k1_relset_1(X0_49,X0_49,k2_funct_2(X0_49,X0_48)) = X0_49
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2358,c_537,c_540])).

cnf(c_6653,plain,
    ( k1_relset_1(X0_49,X0_49,k2_funct_2(X0_49,X0_48)) = X0_49
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_6652])).

cnf(c_6663,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_2(sK1,sK2)) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_6653])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_446,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_984,plain,
    ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_2585,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_984])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_548,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_2948,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2585,c_24,c_23,c_22,c_21,c_548])).

cnf(c_2961,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2948,c_978])).

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

cnf(c_4037,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2961,c_25,c_26,c_27,c_28])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_975,plain,
    ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_4051,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4037,c_975])).

cnf(c_6727,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6663,c_2948,c_4051])).

cnf(c_981,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_2457,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_981])).

cnf(c_542,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_2848,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2457,c_25,c_26,c_27,c_28,c_542])).

cnf(c_2951,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2948,c_2848])).

cnf(c_980,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_2793,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_980])).

cnf(c_539,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_3070,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_25,c_26,c_27,c_28,c_539])).

cnf(c_3074,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3070,c_2948])).

cnf(c_4046,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4037,c_985])).

cnf(c_4085,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4046,c_4051])).

cnf(c_7091,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6727,c_2951,c_3074,c_4085])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_459,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_971,plain,
    ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_2853,plain,
    ( k5_relat_1(k2_funct_2(sK1,sK2),k2_funct_1(k2_funct_2(sK1,sK2))) = k6_partfun1(k1_relat_1(k2_funct_2(sK1,sK2)))
    | v2_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
    | v1_relat_1(k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2848,c_971])).

cnf(c_531,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_533,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_451,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_534,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_536,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_10,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_453,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | v2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1633,plain,
    ( ~ v3_funct_2(k2_funct_2(X0_49,X0_48),X1_49,X2_49)
    | ~ m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v1_funct_1(k2_funct_2(X0_49,X0_48))
    | v2_funct_1(k2_funct_2(X0_49,X0_48)) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_1634,plain,
    ( v3_funct_2(k2_funct_2(X0_49,X0_48),X1_49,X2_49) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top
    | v2_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1633])).

cnf(c_1636,plain,
    ( v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
    | v2_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2287,plain,
    ( ~ m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | v1_relat_1(k2_funct_2(X0_49,X0_48)) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_2288,plain,
    ( m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | v1_relat_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2287])).

cnf(c_2290,plain,
    ( m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2288])).

cnf(c_3896,plain,
    ( k5_relat_1(k2_funct_2(sK1,sK2),k2_funct_1(k2_funct_2(sK1,sK2))) = k6_partfun1(k1_relat_1(k2_funct_2(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2853,c_25,c_26,c_27,c_28,c_533,c_536,c_542,c_1636,c_2290])).

cnf(c_440,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_990,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_457,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_973,plain,
    ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1494,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_973])).

cnf(c_517,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_520,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_456])).

cnf(c_529,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_453])).

cnf(c_1575,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1494,c_24,c_22,c_21,c_517,c_520,c_529])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_460,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_970,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_1785,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_970])).

cnf(c_508,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_2124,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1785,c_24,c_22,c_21,c_508,c_520,c_529])).

cnf(c_3898,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3896,c_1575,c_2124,c_2948])).

cnf(c_7101,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_7091,c_3898])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_983,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_447])).

cnf(c_4048,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4037,c_983])).

cnf(c_6416,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4048,c_2951])).

cnf(c_6417,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_6416])).

cnf(c_6425,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_6417])).

cnf(c_6466,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6425,c_2124])).

cnf(c_6483,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6466,c_25])).

cnf(c_3303,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_983])).

cnf(c_3694,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3303,c_25])).

cnf(c_3695,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3694])).

cnf(c_3703,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_978,c_3695])).

cnf(c_4535,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3703,c_540])).

cnf(c_4536,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4535])).

cnf(c_4546,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_4536])).

cnf(c_2019,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_985])).

cnf(c_1404,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_987,c_975])).

cnf(c_2038,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2019,c_1404])).

cnf(c_2205,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2038,c_25,c_26])).

cnf(c_1792,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_971])).

cnf(c_511,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_2128,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1792,c_24,c_22,c_21,c_511,c_520,c_529])).

cnf(c_2208,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2205,c_2128])).

cnf(c_4601,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4546,c_2208,c_2948])).

cnf(c_4047,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4037,c_3695])).

cnf(c_4082,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4047,c_2208])).

cnf(c_4726,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4601,c_2951,c_4082])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_444,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_986,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_2952,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2948,c_986])).

cnf(c_4729,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4726,c_2952])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_448,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_982,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_454,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_976,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_1870,plain,
    ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_976])).

cnf(c_1886,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1870])).

cnf(c_4732,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4729,c_28,c_1886])).

cnf(c_6486,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6483,c_4732])).

cnf(c_7225,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7101,c_6486])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7225,c_1886,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.18/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.99  
% 3.18/0.99  ------  iProver source info
% 3.18/0.99  
% 3.18/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.99  git: non_committed_changes: false
% 3.18/0.99  git: last_make_outside_of_git: false
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     num_symb
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       true
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  ------ Parsing...
% 3.18/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.99  ------ Proving...
% 3.18/0.99  ------ Problem Properties 
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  clauses                                 24
% 3.18/0.99  conjectures                             5
% 3.18/0.99  EPR                                     3
% 3.18/0.99  Horn                                    24
% 3.18/0.99  unary                                   7
% 3.18/0.99  binary                                  3
% 3.18/0.99  lits                                    73
% 3.18/0.99  lits eq                                 7
% 3.18/0.99  fd_pure                                 0
% 3.18/0.99  fd_pseudo                               0
% 3.18/0.99  fd_cond                                 0
% 3.18/0.99  fd_pseudo_cond                          0
% 3.18/0.99  AC symbols                              0
% 3.18/0.99  
% 3.18/0.99  ------ Schedule dynamic 5 is on 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ 
% 3.18/0.99  Current options:
% 3.18/0.99  ------ 
% 3.18/0.99  
% 3.18/0.99  ------ Input Options
% 3.18/0.99  
% 3.18/0.99  --out_options                           all
% 3.18/0.99  --tptp_safe_out                         true
% 3.18/0.99  --problem_path                          ""
% 3.18/0.99  --include_path                          ""
% 3.18/0.99  --clausifier                            res/vclausify_rel
% 3.18/0.99  --clausifier_options                    --mode clausify
% 3.18/0.99  --stdin                                 false
% 3.18/0.99  --stats_out                             all
% 3.18/0.99  
% 3.18/0.99  ------ General Options
% 3.18/0.99  
% 3.18/0.99  --fof                                   false
% 3.18/0.99  --time_out_real                         305.
% 3.18/0.99  --time_out_virtual                      -1.
% 3.18/0.99  --symbol_type_check                     false
% 3.18/0.99  --clausify_out                          false
% 3.18/0.99  --sig_cnt_out                           false
% 3.18/0.99  --trig_cnt_out                          false
% 3.18/0.99  --trig_cnt_out_tolerance                1.
% 3.18/0.99  --trig_cnt_out_sk_spl                   false
% 3.18/0.99  --abstr_cl_out                          false
% 3.18/0.99  
% 3.18/0.99  ------ Global Options
% 3.18/0.99  
% 3.18/0.99  --schedule                              default
% 3.18/0.99  --add_important_lit                     false
% 3.18/0.99  --prop_solver_per_cl                    1000
% 3.18/0.99  --min_unsat_core                        false
% 3.18/0.99  --soft_assumptions                      false
% 3.18/0.99  --soft_lemma_size                       3
% 3.18/0.99  --prop_impl_unit_size                   0
% 3.18/0.99  --prop_impl_unit                        []
% 3.18/0.99  --share_sel_clauses                     true
% 3.18/0.99  --reset_solvers                         false
% 3.18/0.99  --bc_imp_inh                            [conj_cone]
% 3.18/0.99  --conj_cone_tolerance                   3.
% 3.18/0.99  --extra_neg_conj                        none
% 3.18/0.99  --large_theory_mode                     true
% 3.18/0.99  --prolific_symb_bound                   200
% 3.18/0.99  --lt_threshold                          2000
% 3.18/0.99  --clause_weak_htbl                      true
% 3.18/0.99  --gc_record_bc_elim                     false
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing Options
% 3.18/0.99  
% 3.18/0.99  --preprocessing_flag                    true
% 3.18/0.99  --time_out_prep_mult                    0.1
% 3.18/0.99  --splitting_mode                        input
% 3.18/0.99  --splitting_grd                         true
% 3.18/0.99  --splitting_cvd                         false
% 3.18/0.99  --splitting_cvd_svl                     false
% 3.18/0.99  --splitting_nvd                         32
% 3.18/0.99  --sub_typing                            true
% 3.18/0.99  --prep_gs_sim                           true
% 3.18/0.99  --prep_unflatten                        true
% 3.18/0.99  --prep_res_sim                          true
% 3.18/0.99  --prep_upred                            true
% 3.18/0.99  --prep_sem_filter                       exhaustive
% 3.18/0.99  --prep_sem_filter_out                   false
% 3.18/0.99  --pred_elim                             true
% 3.18/0.99  --res_sim_input                         true
% 3.18/0.99  --eq_ax_congr_red                       true
% 3.18/0.99  --pure_diseq_elim                       true
% 3.18/0.99  --brand_transform                       false
% 3.18/0.99  --non_eq_to_eq                          false
% 3.18/0.99  --prep_def_merge                        true
% 3.18/0.99  --prep_def_merge_prop_impl              false
% 3.18/0.99  --prep_def_merge_mbd                    true
% 3.18/0.99  --prep_def_merge_tr_red                 false
% 3.18/0.99  --prep_def_merge_tr_cl                  false
% 3.18/0.99  --smt_preprocessing                     true
% 3.18/0.99  --smt_ac_axioms                         fast
% 3.18/0.99  --preprocessed_out                      false
% 3.18/0.99  --preprocessed_stats                    false
% 3.18/0.99  
% 3.18/0.99  ------ Abstraction refinement Options
% 3.18/0.99  
% 3.18/0.99  --abstr_ref                             []
% 3.18/0.99  --abstr_ref_prep                        false
% 3.18/0.99  --abstr_ref_until_sat                   false
% 3.18/0.99  --abstr_ref_sig_restrict                funpre
% 3.18/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.99  --abstr_ref_under                       []
% 3.18/0.99  
% 3.18/0.99  ------ SAT Options
% 3.18/0.99  
% 3.18/0.99  --sat_mode                              false
% 3.18/0.99  --sat_fm_restart_options                ""
% 3.18/0.99  --sat_gr_def                            false
% 3.18/0.99  --sat_epr_types                         true
% 3.18/0.99  --sat_non_cyclic_types                  false
% 3.18/0.99  --sat_finite_models                     false
% 3.18/0.99  --sat_fm_lemmas                         false
% 3.18/0.99  --sat_fm_prep                           false
% 3.18/0.99  --sat_fm_uc_incr                        true
% 3.18/0.99  --sat_out_model                         small
% 3.18/0.99  --sat_out_clauses                       false
% 3.18/0.99  
% 3.18/0.99  ------ QBF Options
% 3.18/0.99  
% 3.18/0.99  --qbf_mode                              false
% 3.18/0.99  --qbf_elim_univ                         false
% 3.18/0.99  --qbf_dom_inst                          none
% 3.18/0.99  --qbf_dom_pre_inst                      false
% 3.18/0.99  --qbf_sk_in                             false
% 3.18/0.99  --qbf_pred_elim                         true
% 3.18/0.99  --qbf_split                             512
% 3.18/0.99  
% 3.18/0.99  ------ BMC1 Options
% 3.18/0.99  
% 3.18/0.99  --bmc1_incremental                      false
% 3.18/0.99  --bmc1_axioms                           reachable_all
% 3.18/0.99  --bmc1_min_bound                        0
% 3.18/0.99  --bmc1_max_bound                        -1
% 3.18/0.99  --bmc1_max_bound_default                -1
% 3.18/0.99  --bmc1_symbol_reachability              true
% 3.18/0.99  --bmc1_property_lemmas                  false
% 3.18/0.99  --bmc1_k_induction                      false
% 3.18/0.99  --bmc1_non_equiv_states                 false
% 3.18/0.99  --bmc1_deadlock                         false
% 3.18/0.99  --bmc1_ucm                              false
% 3.18/0.99  --bmc1_add_unsat_core                   none
% 3.18/0.99  --bmc1_unsat_core_children              false
% 3.18/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.99  --bmc1_out_stat                         full
% 3.18/0.99  --bmc1_ground_init                      false
% 3.18/0.99  --bmc1_pre_inst_next_state              false
% 3.18/0.99  --bmc1_pre_inst_state                   false
% 3.18/0.99  --bmc1_pre_inst_reach_state             false
% 3.18/0.99  --bmc1_out_unsat_core                   false
% 3.18/0.99  --bmc1_aig_witness_out                  false
% 3.18/0.99  --bmc1_verbose                          false
% 3.18/0.99  --bmc1_dump_clauses_tptp                false
% 3.18/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.99  --bmc1_dump_file                        -
% 3.18/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.99  --bmc1_ucm_extend_mode                  1
% 3.18/0.99  --bmc1_ucm_init_mode                    2
% 3.18/0.99  --bmc1_ucm_cone_mode                    none
% 3.18/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.99  --bmc1_ucm_relax_model                  4
% 3.18/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.99  --bmc1_ucm_layered_model                none
% 3.18/0.99  --bmc1_ucm_max_lemma_size               10
% 3.18/0.99  
% 3.18/0.99  ------ AIG Options
% 3.18/0.99  
% 3.18/0.99  --aig_mode                              false
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation Options
% 3.18/0.99  
% 3.18/0.99  --instantiation_flag                    true
% 3.18/0.99  --inst_sos_flag                         false
% 3.18/0.99  --inst_sos_phase                        true
% 3.18/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.99  --inst_lit_sel_side                     none
% 3.18/0.99  --inst_solver_per_active                1400
% 3.18/0.99  --inst_solver_calls_frac                1.
% 3.18/0.99  --inst_passive_queue_type               priority_queues
% 3.18/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.99  --inst_passive_queues_freq              [25;2]
% 3.18/0.99  --inst_dismatching                      true
% 3.18/0.99  --inst_eager_unprocessed_to_passive     true
% 3.18/0.99  --inst_prop_sim_given                   true
% 3.18/0.99  --inst_prop_sim_new                     false
% 3.18/0.99  --inst_subs_new                         false
% 3.18/0.99  --inst_eq_res_simp                      false
% 3.18/0.99  --inst_subs_given                       false
% 3.18/0.99  --inst_orphan_elimination               true
% 3.18/0.99  --inst_learning_loop_flag               true
% 3.18/0.99  --inst_learning_start                   3000
% 3.18/0.99  --inst_learning_factor                  2
% 3.18/0.99  --inst_start_prop_sim_after_learn       3
% 3.18/0.99  --inst_sel_renew                        solver
% 3.18/0.99  --inst_lit_activity_flag                true
% 3.18/0.99  --inst_restr_to_given                   false
% 3.18/0.99  --inst_activity_threshold               500
% 3.18/0.99  --inst_out_proof                        true
% 3.18/0.99  
% 3.18/0.99  ------ Resolution Options
% 3.18/0.99  
% 3.18/0.99  --resolution_flag                       false
% 3.18/0.99  --res_lit_sel                           adaptive
% 3.18/0.99  --res_lit_sel_side                      none
% 3.18/0.99  --res_ordering                          kbo
% 3.18/0.99  --res_to_prop_solver                    active
% 3.18/0.99  --res_prop_simpl_new                    false
% 3.18/0.99  --res_prop_simpl_given                  true
% 3.18/0.99  --res_passive_queue_type                priority_queues
% 3.18/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.99  --res_passive_queues_freq               [15;5]
% 3.18/0.99  --res_forward_subs                      full
% 3.18/0.99  --res_backward_subs                     full
% 3.18/0.99  --res_forward_subs_resolution           true
% 3.18/0.99  --res_backward_subs_resolution          true
% 3.18/0.99  --res_orphan_elimination                true
% 3.18/0.99  --res_time_limit                        2.
% 3.18/0.99  --res_out_proof                         true
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Options
% 3.18/0.99  
% 3.18/0.99  --superposition_flag                    true
% 3.18/0.99  --sup_passive_queue_type                priority_queues
% 3.18/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.99  --demod_completeness_check              fast
% 3.18/0.99  --demod_use_ground                      true
% 3.18/0.99  --sup_to_prop_solver                    passive
% 3.18/0.99  --sup_prop_simpl_new                    true
% 3.18/0.99  --sup_prop_simpl_given                  true
% 3.18/0.99  --sup_fun_splitting                     false
% 3.18/0.99  --sup_smt_interval                      50000
% 3.18/0.99  
% 3.18/0.99  ------ Superposition Simplification Setup
% 3.18/0.99  
% 3.18/0.99  --sup_indices_passive                   []
% 3.18/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_full_bw                           [BwDemod]
% 3.18/0.99  --sup_immed_triv                        [TrivRules]
% 3.18/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_immed_bw_main                     []
% 3.18/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.99  
% 3.18/0.99  ------ Combination Options
% 3.18/0.99  
% 3.18/0.99  --comb_res_mult                         3
% 3.18/0.99  --comb_sup_mult                         2
% 3.18/0.99  --comb_inst_mult                        10
% 3.18/0.99  
% 3.18/0.99  ------ Debug Options
% 3.18/0.99  
% 3.18/0.99  --dbg_backtrace                         false
% 3.18/0.99  --dbg_dump_prop_clauses                 false
% 3.18/0.99  --dbg_dump_prop_clauses_file            -
% 3.18/0.99  --dbg_out_stat                          false
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  ------ Proving...
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS status Theorem for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  fof(f17,conjecture,(
% 3.18/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f18,negated_conjecture,(
% 3.18/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.18/0.99    inference(negated_conjecture,[],[f17])).
% 3.18/0.99  
% 3.18/0.99  fof(f43,plain,(
% 3.18/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.18/0.99    inference(ennf_transformation,[],[f18])).
% 3.18/0.99  
% 3.18/0.99  fof(f44,plain,(
% 3.18/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.18/0.99    inference(flattening,[],[f43])).
% 3.18/0.99  
% 3.18/0.99  fof(f47,plain,(
% 3.18/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.18/0.99    introduced(choice_axiom,[])).
% 3.18/0.99  
% 3.18/0.99  fof(f48,plain,(
% 3.18/0.99    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.18/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f47])).
% 3.18/0.99  
% 3.18/0.99  fof(f73,plain,(
% 3.18/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.18/0.99    inference(cnf_transformation,[],[f48])).
% 3.18/0.99  
% 3.18/0.99  fof(f11,axiom,(
% 3.18/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f35,plain,(
% 3.18/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.18/0.99    inference(ennf_transformation,[],[f11])).
% 3.18/0.99  
% 3.18/0.99  fof(f36,plain,(
% 3.18/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.18/0.99    inference(flattening,[],[f35])).
% 3.18/0.99  
% 3.18/0.99  fof(f64,plain,(
% 3.18/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f36])).
% 3.18/0.99  
% 3.18/0.99  fof(f16,axiom,(
% 3.18/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f41,plain,(
% 3.18/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.18/0.99    inference(ennf_transformation,[],[f16])).
% 3.18/0.99  
% 3.18/0.99  fof(f42,plain,(
% 3.18/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.18/0.99    inference(flattening,[],[f41])).
% 3.18/0.99  
% 3.18/0.99  fof(f69,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f42])).
% 3.18/0.99  
% 3.18/0.99  fof(f62,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f36])).
% 3.18/0.99  
% 3.18/0.99  fof(f61,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f36])).
% 3.18/0.99  
% 3.18/0.99  fof(f14,axiom,(
% 3.18/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f39,plain,(
% 3.18/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.18/0.99    inference(ennf_transformation,[],[f14])).
% 3.18/0.99  
% 3.18/0.99  fof(f40,plain,(
% 3.18/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.18/0.99    inference(flattening,[],[f39])).
% 3.18/0.99  
% 3.18/0.99  fof(f67,plain,(
% 3.18/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f40])).
% 3.18/0.99  
% 3.18/0.99  fof(f70,plain,(
% 3.18/0.99    v1_funct_1(sK2)),
% 3.18/0.99    inference(cnf_transformation,[],[f48])).
% 3.18/0.99  
% 3.18/0.99  fof(f71,plain,(
% 3.18/0.99    v1_funct_2(sK2,sK1,sK1)),
% 3.18/0.99    inference(cnf_transformation,[],[f48])).
% 3.18/0.99  
% 3.18/0.99  fof(f72,plain,(
% 3.18/0.99    v3_funct_2(sK2,sK1,sK1)),
% 3.18/0.99    inference(cnf_transformation,[],[f48])).
% 3.18/0.99  
% 3.18/0.99  fof(f8,axiom,(
% 3.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f30,plain,(
% 3.18/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.99    inference(ennf_transformation,[],[f8])).
% 3.18/0.99  
% 3.18/0.99  fof(f57,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f30])).
% 3.18/0.99  
% 3.18/0.99  fof(f4,axiom,(
% 3.18/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f23,plain,(
% 3.18/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f4])).
% 3.18/0.99  
% 3.18/0.99  fof(f24,plain,(
% 3.18/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(flattening,[],[f23])).
% 3.18/0.99  
% 3.18/0.99  fof(f52,plain,(
% 3.18/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f24])).
% 3.18/0.99  
% 3.18/0.99  fof(f15,axiom,(
% 3.18/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f68,plain,(
% 3.18/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f15])).
% 3.18/0.99  
% 3.18/0.99  fof(f76,plain,(
% 3.18/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(definition_unfolding,[],[f52,f68])).
% 3.18/0.99  
% 3.18/0.99  fof(f63,plain,(
% 3.18/0.99    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f36])).
% 3.18/0.99  
% 3.18/0.99  fof(f10,axiom,(
% 3.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f20,plain,(
% 3.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.18/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.18/0.99  
% 3.18/0.99  fof(f33,plain,(
% 3.18/0.99    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.99    inference(ennf_transformation,[],[f20])).
% 3.18/0.99  
% 3.18/0.99  fof(f34,plain,(
% 3.18/0.99    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.99    inference(flattening,[],[f33])).
% 3.18/0.99  
% 3.18/0.99  fof(f60,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f34])).
% 3.18/0.99  
% 3.18/0.99  fof(f7,axiom,(
% 3.18/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f29,plain,(
% 3.18/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.99    inference(ennf_transformation,[],[f7])).
% 3.18/0.99  
% 3.18/0.99  fof(f56,plain,(
% 3.18/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f29])).
% 3.18/0.99  
% 3.18/0.99  fof(f6,axiom,(
% 3.18/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f27,plain,(
% 3.18/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.99    inference(ennf_transformation,[],[f6])).
% 3.18/0.99  
% 3.18/0.99  fof(f28,plain,(
% 3.18/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.99    inference(flattening,[],[f27])).
% 3.18/0.99  
% 3.18/0.99  fof(f55,plain,(
% 3.18/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f28])).
% 3.18/0.99  
% 3.18/0.99  fof(f53,plain,(
% 3.18/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f24])).
% 3.18/0.99  
% 3.18/0.99  fof(f75,plain,(
% 3.18/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.99    inference(definition_unfolding,[],[f53,f68])).
% 3.18/0.99  
% 3.18/0.99  fof(f13,axiom,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f37,plain,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.18/0.99    inference(ennf_transformation,[],[f13])).
% 3.18/0.99  
% 3.18/0.99  fof(f38,plain,(
% 3.18/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.18/0.99    inference(flattening,[],[f37])).
% 3.18/0.99  
% 3.18/0.99  fof(f66,plain,(
% 3.18/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.18/0.99    inference(cnf_transformation,[],[f38])).
% 3.18/0.99  
% 3.18/0.99  fof(f74,plain,(
% 3.18/0.99    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.18/0.99    inference(cnf_transformation,[],[f48])).
% 3.18/0.99  
% 3.18/0.99  fof(f12,axiom,(
% 3.18/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f19,plain,(
% 3.18/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.18/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.18/0.99  
% 3.18/0.99  fof(f65,plain,(
% 3.18/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f19])).
% 3.18/0.99  
% 3.18/0.99  fof(f9,axiom,(
% 3.18/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.18/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.99  
% 3.18/0.99  fof(f31,plain,(
% 3.18/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.18/0.99    inference(ennf_transformation,[],[f9])).
% 3.18/0.99  
% 3.18/0.99  fof(f32,plain,(
% 3.18/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.99    inference(flattening,[],[f31])).
% 3.18/0.99  
% 3.18/0.99  fof(f58,plain,(
% 3.18/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.99    inference(cnf_transformation,[],[f32])).
% 3.18/0.99  
% 3.18/0.99  cnf(c_21,negated_conjecture,
% 3.18/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_443,negated_conjecture,
% 3.18/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_987,plain,
% 3.18/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_12,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.99      | ~ v1_funct_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_452,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.99      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.99      | ~ v1_funct_1(X0_48) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_978,plain,
% 3.18/0.99      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_19,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.18/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_445,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.99      | ~ v1_funct_1(X0_48)
% 3.18/0.99      | k1_relset_1(X0_49,X0_49,X0_48) = X0_49 ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_985,plain,
% 3.18/0.99      ( k1_relset_1(X0_49,X0_49,X0_48) = X0_49
% 3.18/0.99      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2358,plain,
% 3.18/0.99      ( k1_relset_1(X0_49,X0_49,k2_funct_2(X0_49,X0_48)) = X0_49
% 3.18/0.99      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_978,c_985]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_14,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.99      | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.18/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.99      | ~ v1_funct_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_450,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.18/0.99      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.99      | ~ v1_funct_1(X0_48) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_537,plain,
% 3.18/0.99      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_15,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_449,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.99      | ~ v1_funct_1(X0_48)
% 3.18/0.99      | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_540,plain,
% 3.18/0.99      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6652,plain,
% 3.18/0.99      ( v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | k1_relset_1(X0_49,X0_49,k2_funct_2(X0_49,X0_48)) = X0_49
% 3.18/0.99      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2358,c_537,c_540]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6653,plain,
% 3.18/0.99      ( k1_relset_1(X0_49,X0_49,k2_funct_2(X0_49,X0_48)) = X0_49
% 3.18/0.99      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_6652]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6663,plain,
% 3.18/0.99      ( k1_relset_1(sK1,sK1,k2_funct_2(sK1,sK2)) = sK1
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_6653]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_18,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_446,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.99      | ~ v1_funct_1(X0_48)
% 3.18/0.99      | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_984,plain,
% 3.18/0.99      ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
% 3.18/0.99      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2585,plain,
% 3.18/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_984]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_24,negated_conjecture,
% 3.18/0.99      ( v1_funct_1(sK2) ),
% 3.18/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_23,negated_conjecture,
% 3.18/0.99      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_22,negated_conjecture,
% 3.18/0.99      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.18/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_548,plain,
% 3.18/0.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.18/0.99      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.18/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/0.99      | ~ v1_funct_1(sK2)
% 3.18/0.99      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_446]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2948,plain,
% 3.18/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2585,c_24,c_23,c_22,c_21,c_548]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2961,plain,
% 3.18/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.18/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_2948,c_978]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_25,plain,
% 3.18/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_26,plain,
% 3.18/0.99      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_27,plain,
% 3.18/0.99      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_28,plain,
% 3.18/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4037,plain,
% 3.18/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2961,c_25,c_26,c_27,c_28]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_8,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_455,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.99      | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_975,plain,
% 3.18/0.99      ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4051,plain,
% 3.18/0.99      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_4037,c_975]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6727,plain,
% 3.18/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_6663,c_2948,c_4051]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_981,plain,
% 3.18/0.99      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2457,plain,
% 3.18/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_981]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_542,plain,
% 3.18/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_540]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2848,plain,
% 3.18/0.99      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2457,c_25,c_26,c_27,c_28,c_542]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2951,plain,
% 3.18/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_2948,c_2848]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_980,plain,
% 3.18/0.99      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2793,plain,
% 3.18/0.99      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_980]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_539,plain,
% 3.18/0.99      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_537]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3070,plain,
% 3.18/0.99      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2793,c_25,c_26,c_27,c_28,c_539]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3074,plain,
% 3.18/0.99      ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_3070,c_2948]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4046,plain,
% 3.18/0.99      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
% 3.18/0.99      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_4037,c_985]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4085,plain,
% 3.18/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.18/0.99      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_4046,c_4051]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7091,plain,
% 3.18/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_6727,c_2951,c_3074,c_4085]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4,plain,
% 3.18/0.99      ( ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v2_funct_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_459,plain,
% 3.18/0.99      ( ~ v1_funct_1(X0_48)
% 3.18/0.99      | ~ v2_funct_1(X0_48)
% 3.18/0.99      | ~ v1_relat_1(X0_48)
% 3.18/0.99      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_971,plain,
% 3.18/0.99      ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v2_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2853,plain,
% 3.18/0.99      ( k5_relat_1(k2_funct_2(sK1,sK2),k2_funct_1(k2_funct_2(sK1,sK2))) = k6_partfun1(k1_relat_1(k2_funct_2(sK1,sK2)))
% 3.18/0.99      | v2_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
% 3.18/0.99      | v1_relat_1(k2_funct_2(sK1,sK2)) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_2848,c_971]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_531,plain,
% 3.18/0.99      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_533,plain,
% 3.18/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.18/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_531]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_13,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.99      | ~ v1_funct_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_451,plain,
% 3.18/0.99      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.99      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.18/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.99      | ~ v1_funct_1(X0_48) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_534,plain,
% 3.18/0.99      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_536,plain,
% 3.18/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_534]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_10,plain,
% 3.18/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.18/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | v2_funct_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_453,plain,
% 3.18/0.99      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.18/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.99      | ~ v1_funct_1(X0_48)
% 3.18/0.99      | v2_funct_1(X0_48) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1633,plain,
% 3.18/0.99      ( ~ v3_funct_2(k2_funct_2(X0_49,X0_48),X1_49,X2_49)
% 3.18/0.99      | ~ m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.18/0.99      | ~ v1_funct_1(k2_funct_2(X0_49,X0_48))
% 3.18/0.99      | v2_funct_1(k2_funct_2(X0_49,X0_48)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_453]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1634,plain,
% 3.18/0.99      ( v3_funct_2(k2_funct_2(X0_49,X0_48),X1_49,X2_49) != iProver_top
% 3.18/0.99      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top
% 3.18/0.99      | v2_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_1633]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1636,plain,
% 3.18/0.99      ( v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) != iProver_top
% 3.18/0.99      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
% 3.18/0.99      | v2_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1634]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | v1_relat_1(X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_456,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.99      | v1_relat_1(X0_48) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2287,plain,
% 3.18/0.99      ( ~ m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.18/0.99      | v1_relat_1(k2_funct_2(X0_49,X0_48)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_456]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2288,plain,
% 3.18/0.99      ( m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 3.18/0.99      | v1_relat_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_2287]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2290,plain,
% 3.18/0.99      ( m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.99      | v1_relat_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_2288]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3896,plain,
% 3.18/0.99      ( k5_relat_1(k2_funct_2(sK1,sK2),k2_funct_1(k2_funct_2(sK1,sK2))) = k6_partfun1(k1_relat_1(k2_funct_2(sK1,sK2))) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2853,c_25,c_26,c_27,c_28,c_533,c_536,c_542,c_1636,
% 3.18/0.99                 c_2290]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_440,negated_conjecture,
% 3.18/0.99      ( v1_funct_1(sK2) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_990,plain,
% 3.18/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6,plain,
% 3.18/0.99      ( ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v2_funct_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.18/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_457,plain,
% 3.18/0.99      ( ~ v1_funct_1(X0_48)
% 3.18/0.99      | ~ v2_funct_1(X0_48)
% 3.18/0.99      | ~ v1_relat_1(X0_48)
% 3.18/0.99      | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_973,plain,
% 3.18/0.99      ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v2_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1494,plain,
% 3.18/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.18/0.99      | v2_funct_1(sK2) != iProver_top
% 3.18/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_990,c_973]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_517,plain,
% 3.18/0.99      ( ~ v1_funct_1(sK2)
% 3.18/0.99      | ~ v2_funct_1(sK2)
% 3.18/0.99      | ~ v1_relat_1(sK2)
% 3.18/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_457]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_520,plain,
% 3.18/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/0.99      | v1_relat_1(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_456]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_529,plain,
% 3.18/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.18/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/0.99      | ~ v1_funct_1(sK2)
% 3.18/0.99      | v2_funct_1(sK2) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_453]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1575,plain,
% 3.18/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1494,c_24,c_22,c_21,c_517,c_520,c_529]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3,plain,
% 3.18/0.99      ( ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v2_funct_1(X0)
% 3.18/0.99      | ~ v1_relat_1(X0)
% 3.18/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_460,plain,
% 3.18/0.99      ( ~ v1_funct_1(X0_48)
% 3.18/0.99      | ~ v2_funct_1(X0_48)
% 3.18/0.99      | ~ v1_relat_1(X0_48)
% 3.18/0.99      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_970,plain,
% 3.18/0.99      ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v2_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_relat_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1785,plain,
% 3.18/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.18/0.99      | v2_funct_1(sK2) != iProver_top
% 3.18/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_990,c_970]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_508,plain,
% 3.18/0.99      ( ~ v1_funct_1(sK2)
% 3.18/0.99      | ~ v2_funct_1(sK2)
% 3.18/0.99      | ~ v1_relat_1(sK2)
% 3.18/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_460]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2124,plain,
% 3.18/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1785,c_24,c_22,c_21,c_508,c_520,c_529]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3898,plain,
% 3.18/0.99      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.18/0.99      inference(light_normalisation,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3896,c_1575,c_2124,c_2948]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7101,plain,
% 3.18/0.99      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_7091,c_3898]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_17,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.18/0.99      | ~ v1_funct_1(X0)
% 3.18/0.99      | ~ v1_funct_1(X3)
% 3.18/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.18/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_447,plain,
% 3.18/0.99      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.99      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.18/0.99      | ~ v1_funct_1(X0_48)
% 3.18/0.99      | ~ v1_funct_1(X1_48)
% 3.18/0.99      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_983,plain,
% 3.18/0.99      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 3.18/0.99      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_funct_1(X1_48) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_447]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4048,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_4037,c_983]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6416,plain,
% 3.18/0.99      ( v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.99      | k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_4048,c_2951]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6417,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_6416]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6425,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_6417]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6466,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_6425,c_2124]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6483,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_6466,c_25]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3303,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_983]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3694,plain,
% 3.18/0.99      ( v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.99      | k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3303,c_25]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3695,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_3694]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_3703,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
% 3.18/0.99      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_978,c_3695]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4535,plain,
% 3.18/0.99      ( v1_funct_1(X0_48) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48)) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_3703,c_540]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4536,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
% 3.18/0.99      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.99      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.99      inference(renaming,[status(thm)],[c_4535]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4546,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_4536]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2019,plain,
% 3.18/0.99      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_985]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1404,plain,
% 3.18/0.99      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_987,c_975]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2038,plain,
% 3.18/0.99      ( k1_relat_1(sK2) = sK1
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_2019,c_1404]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2205,plain,
% 3.18/0.99      ( k1_relat_1(sK2) = sK1 ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_2038,c_25,c_26]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1792,plain,
% 3.18/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.18/0.99      | v2_funct_1(sK2) != iProver_top
% 3.18/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_990,c_971]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_511,plain,
% 3.18/0.99      ( ~ v1_funct_1(sK2)
% 3.18/0.99      | ~ v2_funct_1(sK2)
% 3.18/0.99      | ~ v1_relat_1(sK2)
% 3.18/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_459]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2128,plain,
% 3.18/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_1792,c_24,c_22,c_21,c_511,c_520,c_529]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2208,plain,
% 3.18/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_2205,c_2128]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4601,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.18/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_4546,c_2208,c_2948]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4047,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.18/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_4037,c_3695]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4082,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.18/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.99      inference(light_normalisation,[status(thm)],[c_4047,c_2208]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4726,plain,
% 3.18/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_4601,c_2951,c_4082]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_20,negated_conjecture,
% 3.18/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.18/0.99      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.18/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_444,negated_conjecture,
% 3.18/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.18/0.99      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_986,plain,
% 3.18/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.18/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_2952,plain,
% 3.18/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.18/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_2948,c_986]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4729,plain,
% 3.18/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.18/0.99      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_4726,c_2952]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_16,plain,
% 3.18/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_448,plain,
% 3.18/0.99      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_982,plain,
% 3.18/0.99      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_9,plain,
% 3.18/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.18/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.18/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_454,plain,
% 3.18/0.99      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
% 3.18/0.99      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.99      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
% 3.18/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_976,plain,
% 3.18/0.99      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.99      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.18/0.99      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1870,plain,
% 3.18/0.99      ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
% 3.18/0.99      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
% 3.18/0.99      inference(superposition,[status(thm)],[c_982,c_976]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_1886,plain,
% 3.18/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 3.18/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.18/0.99      inference(instantiation,[status(thm)],[c_1870]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_4732,plain,
% 3.18/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.99      inference(global_propositional_subsumption,
% 3.18/0.99                [status(thm)],
% 3.18/0.99                [c_4729,c_28,c_1886]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_6486,plain,
% 3.18/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_6483,c_4732]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(c_7225,plain,
% 3.18/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.99      inference(demodulation,[status(thm)],[c_7101,c_6486]) ).
% 3.18/0.99  
% 3.18/0.99  cnf(contradiction,plain,
% 3.18/0.99      ( $false ),
% 3.18/0.99      inference(minisat,[status(thm)],[c_7225,c_1886,c_28]) ).
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/0.99  
% 3.18/0.99  ------                               Statistics
% 3.18/0.99  
% 3.18/0.99  ------ General
% 3.18/0.99  
% 3.18/0.99  abstr_ref_over_cycles:                  0
% 3.18/0.99  abstr_ref_under_cycles:                 0
% 3.18/0.99  gc_basic_clause_elim:                   0
% 3.18/0.99  forced_gc_time:                         0
% 3.18/0.99  parsing_time:                           0.011
% 3.18/0.99  unif_index_cands_time:                  0.
% 3.18/0.99  unif_index_add_time:                    0.
% 3.18/0.99  orderings_time:                         0.
% 3.18/0.99  out_proof_time:                         0.015
% 3.18/0.99  total_time:                             0.26
% 3.18/0.99  num_of_symbols:                         54
% 3.18/0.99  num_of_terms:                           6835
% 3.18/0.99  
% 3.18/0.99  ------ Preprocessing
% 3.18/0.99  
% 3.18/0.99  num_of_splits:                          0
% 3.18/0.99  num_of_split_atoms:                     0
% 3.18/0.99  num_of_reused_defs:                     0
% 3.18/0.99  num_eq_ax_congr_red:                    18
% 3.18/0.99  num_of_sem_filtered_clauses:            1
% 3.18/0.99  num_of_subtypes:                        3
% 3.18/0.99  monotx_restored_types:                  1
% 3.18/0.99  sat_num_of_epr_types:                   0
% 3.18/0.99  sat_num_of_non_cyclic_types:            0
% 3.18/0.99  sat_guarded_non_collapsed_types:        1
% 3.18/0.99  num_pure_diseq_elim:                    0
% 3.18/0.99  simp_replaced_by:                       0
% 3.18/0.99  res_preprocessed:                       135
% 3.18/0.99  prep_upred:                             0
% 3.18/0.99  prep_unflattend:                        0
% 3.18/0.99  smt_new_axioms:                         0
% 3.18/0.99  pred_elim_cands:                        7
% 3.18/0.99  pred_elim:                              0
% 3.18/0.99  pred_elim_cl:                           0
% 3.18/0.99  pred_elim_cycles:                       2
% 3.18/0.99  merged_defs:                            0
% 3.18/0.99  merged_defs_ncl:                        0
% 3.18/0.99  bin_hyper_res:                          0
% 3.18/0.99  prep_cycles:                            4
% 3.18/0.99  pred_elim_time:                         0.001
% 3.18/0.99  splitting_time:                         0.
% 3.18/0.99  sem_filter_time:                        0.
% 3.18/0.99  monotx_time:                            0.001
% 3.18/0.99  subtype_inf_time:                       0.001
% 3.18/0.99  
% 3.18/0.99  ------ Problem properties
% 3.18/0.99  
% 3.18/0.99  clauses:                                24
% 3.18/0.99  conjectures:                            5
% 3.18/0.99  epr:                                    3
% 3.18/0.99  horn:                                   24
% 3.18/0.99  ground:                                 5
% 3.18/0.99  unary:                                  7
% 3.18/0.99  binary:                                 3
% 3.18/0.99  lits:                                   73
% 3.18/0.99  lits_eq:                                7
% 3.18/0.99  fd_pure:                                0
% 3.18/0.99  fd_pseudo:                              0
% 3.18/0.99  fd_cond:                                0
% 3.18/0.99  fd_pseudo_cond:                         0
% 3.18/0.99  ac_symbols:                             0
% 3.18/0.99  
% 3.18/0.99  ------ Propositional Solver
% 3.18/0.99  
% 3.18/0.99  prop_solver_calls:                      31
% 3.18/0.99  prop_fast_solver_calls:                 1171
% 3.18/0.99  smt_solver_calls:                       0
% 3.18/0.99  smt_fast_solver_calls:                  0
% 3.18/0.99  prop_num_of_clauses:                    2254
% 3.18/0.99  prop_preprocess_simplified:             7370
% 3.18/0.99  prop_fo_subsumed:                       69
% 3.18/0.99  prop_solver_time:                       0.
% 3.18/0.99  smt_solver_time:                        0.
% 3.18/0.99  smt_fast_solver_time:                   0.
% 3.18/0.99  prop_fast_solver_time:                  0.
% 3.18/0.99  prop_unsat_core_time:                   0.
% 3.18/0.99  
% 3.18/0.99  ------ QBF
% 3.18/0.99  
% 3.18/0.99  qbf_q_res:                              0
% 3.18/0.99  qbf_num_tautologies:                    0
% 3.18/0.99  qbf_prep_cycles:                        0
% 3.18/0.99  
% 3.18/0.99  ------ BMC1
% 3.18/0.99  
% 3.18/0.99  bmc1_current_bound:                     -1
% 3.18/0.99  bmc1_last_solved_bound:                 -1
% 3.18/0.99  bmc1_unsat_core_size:                   -1
% 3.18/0.99  bmc1_unsat_core_parents_size:           -1
% 3.18/0.99  bmc1_merge_next_fun:                    0
% 3.18/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.18/0.99  
% 3.18/0.99  ------ Instantiation
% 3.18/0.99  
% 3.18/0.99  inst_num_of_clauses:                    869
% 3.18/0.99  inst_num_in_passive:                    276
% 3.18/0.99  inst_num_in_active:                     473
% 3.18/0.99  inst_num_in_unprocessed:                121
% 3.18/0.99  inst_num_of_loops:                      500
% 3.18/0.99  inst_num_of_learning_restarts:          0
% 3.18/0.99  inst_num_moves_active_passive:          22
% 3.18/0.99  inst_lit_activity:                      0
% 3.18/0.99  inst_lit_activity_moves:                0
% 3.18/0.99  inst_num_tautologies:                   0
% 3.18/0.99  inst_num_prop_implied:                  0
% 3.18/0.99  inst_num_existing_simplified:           0
% 3.18/0.99  inst_num_eq_res_simplified:             0
% 3.18/0.99  inst_num_child_elim:                    0
% 3.18/0.99  inst_num_of_dismatching_blockings:      700
% 3.18/0.99  inst_num_of_non_proper_insts:           1105
% 3.18/0.99  inst_num_of_duplicates:                 0
% 3.18/0.99  inst_inst_num_from_inst_to_res:         0
% 3.18/0.99  inst_dismatching_checking_time:         0.
% 3.18/0.99  
% 3.18/0.99  ------ Resolution
% 3.18/0.99  
% 3.18/0.99  res_num_of_clauses:                     0
% 3.18/0.99  res_num_in_passive:                     0
% 3.18/0.99  res_num_in_active:                      0
% 3.18/0.99  res_num_of_loops:                       139
% 3.18/0.99  res_forward_subset_subsumed:            162
% 3.18/0.99  res_backward_subset_subsumed:           6
% 3.18/0.99  res_forward_subsumed:                   0
% 3.18/0.99  res_backward_subsumed:                  0
% 3.18/0.99  res_forward_subsumption_resolution:     0
% 3.18/0.99  res_backward_subsumption_resolution:    0
% 3.18/0.99  res_clause_to_clause_subsumption:       339
% 3.18/0.99  res_orphan_elimination:                 0
% 3.18/0.99  res_tautology_del:                      142
% 3.18/0.99  res_num_eq_res_simplified:              0
% 3.18/0.99  res_num_sel_changes:                    0
% 3.18/0.99  res_moves_from_active_to_pass:          0
% 3.18/0.99  
% 3.18/0.99  ------ Superposition
% 3.18/0.99  
% 3.18/0.99  sup_time_total:                         0.
% 3.18/0.99  sup_time_generating:                    0.
% 3.18/0.99  sup_time_sim_full:                      0.
% 3.18/0.99  sup_time_sim_immed:                     0.
% 3.18/0.99  
% 3.18/0.99  sup_num_of_clauses:                     125
% 3.18/0.99  sup_num_in_active:                      77
% 3.18/0.99  sup_num_in_passive:                     48
% 3.18/0.99  sup_num_of_loops:                       98
% 3.18/0.99  sup_fw_superposition:                   99
% 3.18/0.99  sup_bw_superposition:                   66
% 3.18/0.99  sup_immediate_simplified:               69
% 3.18/0.99  sup_given_eliminated:                   0
% 3.18/0.99  comparisons_done:                       0
% 3.18/0.99  comparisons_avoided:                    0
% 3.18/0.99  
% 3.18/0.99  ------ Simplifications
% 3.18/0.99  
% 3.18/0.99  
% 3.18/0.99  sim_fw_subset_subsumed:                 5
% 3.18/0.99  sim_bw_subset_subsumed:                 9
% 3.18/0.99  sim_fw_subsumed:                        13
% 3.18/0.99  sim_bw_subsumed:                        2
% 3.18/0.99  sim_fw_subsumption_res:                 3
% 3.18/0.99  sim_bw_subsumption_res:                 0
% 3.18/0.99  sim_tautology_del:                      0
% 3.18/0.99  sim_eq_tautology_del:                   4
% 3.18/0.99  sim_eq_res_simp:                        0
% 3.18/0.99  sim_fw_demodulated:                     5
% 3.18/0.99  sim_bw_demodulated:                     17
% 3.18/0.99  sim_light_normalised:                   48
% 3.18/0.99  sim_joinable_taut:                      0
% 3.18/0.99  sim_joinable_simp:                      0
% 3.18/0.99  sim_ac_normalised:                      0
% 3.18/0.99  sim_smt_subsumption:                    0
% 3.18/0.99  
%------------------------------------------------------------------------------
