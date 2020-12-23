%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:28 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  202 (1861 expanded)
%              Number of clauses        :  133 ( 597 expanded)
%              Number of leaves         :   16 ( 351 expanded)
%              Depth                    :   22
%              Number of atoms          :  664 (8602 expanded)
%              Number of equality atoms :  276 ( 885 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

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

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
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
    inference(pure_predicate_removal,[],[f9])).

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

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f58,f70])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_479,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1059,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_482,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1056,plain,
    ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_2714,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1056])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_592,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_3125,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2714,c_26,c_25,c_24,c_23,c_592])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_490,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1048,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_3138,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3125,c_1048])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3862,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3138,c_27,c_28,c_29,c_30])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_481,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k1_relset_1(X0_49,X0_49,X0_48) = X0_49 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1057,plain,
    ( k1_relset_1(X0_49,X0_49,X0_48) = X0_49
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_3871,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3862,c_1057])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1044,plain,
    ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_3876,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3862,c_1044])).

cnf(c_3905,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3871,c_3876])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_501,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_542,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_544,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_542])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_495,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_560,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_562,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_488,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1050,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_2941,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1050])).

cnf(c_579,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_581,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(c_3234,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2941,c_27,c_28,c_29,c_30,c_581])).

cnf(c_3238,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3234,c_3125])).

cnf(c_6855,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3905,c_27,c_30,c_544,c_562,c_3238])).

cnf(c_10,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_491,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1047,plain,
    ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_3874,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3862,c_1047])).

cnf(c_4,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_497,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k2_funct_1(X0_48))
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_554,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_556,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_554])).

cnf(c_570,plain,
    ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_572,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_4674,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3874,c_27,c_29,c_30,c_556,c_562,c_572])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_498,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1040,plain,
    ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_4681,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4674,c_1040])).

cnf(c_1979,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1047])).

cnf(c_2264,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1979,c_27,c_29,c_30,c_572])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_496,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1042,plain,
    ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_2271,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_1042])).

cnf(c_558,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_561,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_495])).

cnf(c_571,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_2366,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2271,c_26,c_24,c_23,c_558,c_561,c_571])).

cnf(c_2,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_499,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1039,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_2270,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_1039])).

cnf(c_549,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_499])).

cnf(c_2509,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2270,c_26,c_24,c_23,c_549,c_561,c_571])).

cnf(c_4698,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4681,c_2366,c_2509])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_500,plain,
    ( ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_545,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_547,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_545])).

cnf(c_4850,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4698,c_27,c_30,c_544,c_547,c_562])).

cnf(c_6862,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_6855,c_4850])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1055,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_3873,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3862,c_1055])).

cnf(c_5062,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3873,c_27,c_30,c_544,c_562])).

cnf(c_5063,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5062])).

cnf(c_5071,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_5063])).

cnf(c_5102,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5071,c_2509])).

cnf(c_5719,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5102,c_27])).

cnf(c_3070,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1055])).

cnf(c_3277,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3070,c_27])).

cnf(c_3278,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3277])).

cnf(c_3286,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_3278])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_487,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_582,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_4138,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3286,c_582])).

cnf(c_4139,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4138])).

cnf(c_4149,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_4139])).

cnf(c_2269,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_1040])).

cnf(c_552,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_2504,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2269,c_26,c_24,c_23,c_552,c_561,c_571])).

cnf(c_2114,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1059,c_1057])).

cnf(c_1528,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1059,c_1044])).

cnf(c_2134,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2114,c_1528])).

cnf(c_2424,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2134,c_27,c_28])).

cnf(c_2506,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_2504,c_2424])).

cnf(c_4198,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4149,c_2506,c_3125])).

cnf(c_3872,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3862,c_3278])).

cnf(c_3902,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3872,c_2506])).

cnf(c_4215,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4198,c_27,c_30,c_544,c_562,c_3902])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_480,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1058,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_3129,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3125,c_1058])).

cnf(c_4218,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4215,c_3129])).

cnf(c_9,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_492,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1046,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_8,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_493,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1045,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_1954,plain,
    ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1045])).

cnf(c_1972,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_4315,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4218,c_30,c_1972])).

cnf(c_5722,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5719,c_4315])).

cnf(c_6880,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6862,c_5722])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6880,c_1972,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:20:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.18/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/0.98  
% 3.18/0.98  ------  iProver source info
% 3.18/0.98  
% 3.18/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.18/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/0.98  git: non_committed_changes: false
% 3.18/0.98  git: last_make_outside_of_git: false
% 3.18/0.98  
% 3.18/0.98  ------ 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options
% 3.18/0.98  
% 3.18/0.98  --out_options                           all
% 3.18/0.98  --tptp_safe_out                         true
% 3.18/0.98  --problem_path                          ""
% 3.18/0.98  --include_path                          ""
% 3.18/0.98  --clausifier                            res/vclausify_rel
% 3.18/0.98  --clausifier_options                    --mode clausify
% 3.18/0.98  --stdin                                 false
% 3.18/0.98  --stats_out                             all
% 3.18/0.98  
% 3.18/0.98  ------ General Options
% 3.18/0.98  
% 3.18/0.98  --fof                                   false
% 3.18/0.98  --time_out_real                         305.
% 3.18/0.98  --time_out_virtual                      -1.
% 3.18/0.98  --symbol_type_check                     false
% 3.18/0.98  --clausify_out                          false
% 3.18/0.98  --sig_cnt_out                           false
% 3.18/0.98  --trig_cnt_out                          false
% 3.18/0.98  --trig_cnt_out_tolerance                1.
% 3.18/0.98  --trig_cnt_out_sk_spl                   false
% 3.18/0.98  --abstr_cl_out                          false
% 3.18/0.98  
% 3.18/0.98  ------ Global Options
% 3.18/0.98  
% 3.18/0.98  --schedule                              default
% 3.18/0.98  --add_important_lit                     false
% 3.18/0.98  --prop_solver_per_cl                    1000
% 3.18/0.98  --min_unsat_core                        false
% 3.18/0.98  --soft_assumptions                      false
% 3.18/0.98  --soft_lemma_size                       3
% 3.18/0.98  --prop_impl_unit_size                   0
% 3.18/0.98  --prop_impl_unit                        []
% 3.18/0.98  --share_sel_clauses                     true
% 3.18/0.98  --reset_solvers                         false
% 3.18/0.98  --bc_imp_inh                            [conj_cone]
% 3.18/0.98  --conj_cone_tolerance                   3.
% 3.18/0.98  --extra_neg_conj                        none
% 3.18/0.98  --large_theory_mode                     true
% 3.18/0.98  --prolific_symb_bound                   200
% 3.18/0.98  --lt_threshold                          2000
% 3.18/0.98  --clause_weak_htbl                      true
% 3.18/0.98  --gc_record_bc_elim                     false
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing Options
% 3.18/0.98  
% 3.18/0.98  --preprocessing_flag                    true
% 3.18/0.98  --time_out_prep_mult                    0.1
% 3.18/0.98  --splitting_mode                        input
% 3.18/0.98  --splitting_grd                         true
% 3.18/0.98  --splitting_cvd                         false
% 3.18/0.98  --splitting_cvd_svl                     false
% 3.18/0.98  --splitting_nvd                         32
% 3.18/0.98  --sub_typing                            true
% 3.18/0.98  --prep_gs_sim                           true
% 3.18/0.98  --prep_unflatten                        true
% 3.18/0.98  --prep_res_sim                          true
% 3.18/0.98  --prep_upred                            true
% 3.18/0.98  --prep_sem_filter                       exhaustive
% 3.18/0.98  --prep_sem_filter_out                   false
% 3.18/0.98  --pred_elim                             true
% 3.18/0.98  --res_sim_input                         true
% 3.18/0.98  --eq_ax_congr_red                       true
% 3.18/0.98  --pure_diseq_elim                       true
% 3.18/0.98  --brand_transform                       false
% 3.18/0.98  --non_eq_to_eq                          false
% 3.18/0.98  --prep_def_merge                        true
% 3.18/0.98  --prep_def_merge_prop_impl              false
% 3.18/0.98  --prep_def_merge_mbd                    true
% 3.18/0.98  --prep_def_merge_tr_red                 false
% 3.18/0.98  --prep_def_merge_tr_cl                  false
% 3.18/0.98  --smt_preprocessing                     true
% 3.18/0.98  --smt_ac_axioms                         fast
% 3.18/0.98  --preprocessed_out                      false
% 3.18/0.98  --preprocessed_stats                    false
% 3.18/0.98  
% 3.18/0.98  ------ Abstraction refinement Options
% 3.18/0.98  
% 3.18/0.98  --abstr_ref                             []
% 3.18/0.98  --abstr_ref_prep                        false
% 3.18/0.98  --abstr_ref_until_sat                   false
% 3.18/0.98  --abstr_ref_sig_restrict                funpre
% 3.18/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.98  --abstr_ref_under                       []
% 3.18/0.98  
% 3.18/0.98  ------ SAT Options
% 3.18/0.98  
% 3.18/0.98  --sat_mode                              false
% 3.18/0.98  --sat_fm_restart_options                ""
% 3.18/0.98  --sat_gr_def                            false
% 3.18/0.98  --sat_epr_types                         true
% 3.18/0.98  --sat_non_cyclic_types                  false
% 3.18/0.98  --sat_finite_models                     false
% 3.18/0.98  --sat_fm_lemmas                         false
% 3.18/0.98  --sat_fm_prep                           false
% 3.18/0.98  --sat_fm_uc_incr                        true
% 3.18/0.98  --sat_out_model                         small
% 3.18/0.98  --sat_out_clauses                       false
% 3.18/0.98  
% 3.18/0.98  ------ QBF Options
% 3.18/0.98  
% 3.18/0.98  --qbf_mode                              false
% 3.18/0.98  --qbf_elim_univ                         false
% 3.18/0.98  --qbf_dom_inst                          none
% 3.18/0.98  --qbf_dom_pre_inst                      false
% 3.18/0.98  --qbf_sk_in                             false
% 3.18/0.98  --qbf_pred_elim                         true
% 3.18/0.98  --qbf_split                             512
% 3.18/0.98  
% 3.18/0.98  ------ BMC1 Options
% 3.18/0.98  
% 3.18/0.98  --bmc1_incremental                      false
% 3.18/0.98  --bmc1_axioms                           reachable_all
% 3.18/0.98  --bmc1_min_bound                        0
% 3.18/0.98  --bmc1_max_bound                        -1
% 3.18/0.98  --bmc1_max_bound_default                -1
% 3.18/0.98  --bmc1_symbol_reachability              true
% 3.18/0.98  --bmc1_property_lemmas                  false
% 3.18/0.98  --bmc1_k_induction                      false
% 3.18/0.98  --bmc1_non_equiv_states                 false
% 3.18/0.98  --bmc1_deadlock                         false
% 3.18/0.98  --bmc1_ucm                              false
% 3.18/0.98  --bmc1_add_unsat_core                   none
% 3.18/0.98  --bmc1_unsat_core_children              false
% 3.18/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.98  --bmc1_out_stat                         full
% 3.18/0.98  --bmc1_ground_init                      false
% 3.18/0.98  --bmc1_pre_inst_next_state              false
% 3.18/0.98  --bmc1_pre_inst_state                   false
% 3.18/0.98  --bmc1_pre_inst_reach_state             false
% 3.18/0.98  --bmc1_out_unsat_core                   false
% 3.18/0.98  --bmc1_aig_witness_out                  false
% 3.18/0.98  --bmc1_verbose                          false
% 3.18/0.98  --bmc1_dump_clauses_tptp                false
% 3.18/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.98  --bmc1_dump_file                        -
% 3.18/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.98  --bmc1_ucm_extend_mode                  1
% 3.18/0.98  --bmc1_ucm_init_mode                    2
% 3.18/0.98  --bmc1_ucm_cone_mode                    none
% 3.18/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.98  --bmc1_ucm_relax_model                  4
% 3.18/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.98  --bmc1_ucm_layered_model                none
% 3.18/0.98  --bmc1_ucm_max_lemma_size               10
% 3.18/0.98  
% 3.18/0.98  ------ AIG Options
% 3.18/0.98  
% 3.18/0.98  --aig_mode                              false
% 3.18/0.98  
% 3.18/0.98  ------ Instantiation Options
% 3.18/0.98  
% 3.18/0.98  --instantiation_flag                    true
% 3.18/0.98  --inst_sos_flag                         false
% 3.18/0.98  --inst_sos_phase                        true
% 3.18/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel_side                     num_symb
% 3.18/0.98  --inst_solver_per_active                1400
% 3.18/0.98  --inst_solver_calls_frac                1.
% 3.18/0.98  --inst_passive_queue_type               priority_queues
% 3.18/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.98  --inst_passive_queues_freq              [25;2]
% 3.18/0.98  --inst_dismatching                      true
% 3.18/0.98  --inst_eager_unprocessed_to_passive     true
% 3.18/0.98  --inst_prop_sim_given                   true
% 3.18/0.98  --inst_prop_sim_new                     false
% 3.18/0.98  --inst_subs_new                         false
% 3.18/0.98  --inst_eq_res_simp                      false
% 3.18/0.98  --inst_subs_given                       false
% 3.18/0.98  --inst_orphan_elimination               true
% 3.18/0.98  --inst_learning_loop_flag               true
% 3.18/0.98  --inst_learning_start                   3000
% 3.18/0.98  --inst_learning_factor                  2
% 3.18/0.98  --inst_start_prop_sim_after_learn       3
% 3.18/0.98  --inst_sel_renew                        solver
% 3.18/0.98  --inst_lit_activity_flag                true
% 3.18/0.98  --inst_restr_to_given                   false
% 3.18/0.98  --inst_activity_threshold               500
% 3.18/0.98  --inst_out_proof                        true
% 3.18/0.98  
% 3.18/0.98  ------ Resolution Options
% 3.18/0.98  
% 3.18/0.98  --resolution_flag                       true
% 3.18/0.98  --res_lit_sel                           adaptive
% 3.18/0.98  --res_lit_sel_side                      none
% 3.18/0.98  --res_ordering                          kbo
% 3.18/0.98  --res_to_prop_solver                    active
% 3.18/0.98  --res_prop_simpl_new                    false
% 3.18/0.98  --res_prop_simpl_given                  true
% 3.18/0.98  --res_passive_queue_type                priority_queues
% 3.18/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.98  --res_passive_queues_freq               [15;5]
% 3.18/0.98  --res_forward_subs                      full
% 3.18/0.98  --res_backward_subs                     full
% 3.18/0.98  --res_forward_subs_resolution           true
% 3.18/0.98  --res_backward_subs_resolution          true
% 3.18/0.98  --res_orphan_elimination                true
% 3.18/0.98  --res_time_limit                        2.
% 3.18/0.98  --res_out_proof                         true
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Options
% 3.18/0.98  
% 3.18/0.98  --superposition_flag                    true
% 3.18/0.98  --sup_passive_queue_type                priority_queues
% 3.18/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.98  --demod_completeness_check              fast
% 3.18/0.98  --demod_use_ground                      true
% 3.18/0.98  --sup_to_prop_solver                    passive
% 3.18/0.98  --sup_prop_simpl_new                    true
% 3.18/0.98  --sup_prop_simpl_given                  true
% 3.18/0.98  --sup_fun_splitting                     false
% 3.18/0.98  --sup_smt_interval                      50000
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Simplification Setup
% 3.18/0.98  
% 3.18/0.98  --sup_indices_passive                   []
% 3.18/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_full_bw                           [BwDemod]
% 3.18/0.98  --sup_immed_triv                        [TrivRules]
% 3.18/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_immed_bw_main                     []
% 3.18/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  
% 3.18/0.98  ------ Combination Options
% 3.18/0.98  
% 3.18/0.98  --comb_res_mult                         3
% 3.18/0.98  --comb_sup_mult                         2
% 3.18/0.98  --comb_inst_mult                        10
% 3.18/0.98  
% 3.18/0.98  ------ Debug Options
% 3.18/0.98  
% 3.18/0.98  --dbg_backtrace                         false
% 3.18/0.98  --dbg_dump_prop_clauses                 false
% 3.18/0.98  --dbg_dump_prop_clauses_file            -
% 3.18/0.98  --dbg_out_stat                          false
% 3.18/0.98  ------ Parsing...
% 3.18/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/0.98  ------ Proving...
% 3.18/0.98  ------ Problem Properties 
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  clauses                                 26
% 3.18/0.98  conjectures                             5
% 3.18/0.98  EPR                                     3
% 3.18/0.98  Horn                                    26
% 3.18/0.98  unary                                   8
% 3.18/0.98  binary                                  3
% 3.18/0.98  lits                                    77
% 3.18/0.98  lits eq                                 7
% 3.18/0.98  fd_pure                                 0
% 3.18/0.98  fd_pseudo                               0
% 3.18/0.98  fd_cond                                 0
% 3.18/0.98  fd_pseudo_cond                          0
% 3.18/0.98  AC symbols                              0
% 3.18/0.98  
% 3.18/0.98  ------ Schedule dynamic 5 is on 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  ------ 
% 3.18/0.98  Current options:
% 3.18/0.98  ------ 
% 3.18/0.98  
% 3.18/0.98  ------ Input Options
% 3.18/0.98  
% 3.18/0.98  --out_options                           all
% 3.18/0.98  --tptp_safe_out                         true
% 3.18/0.98  --problem_path                          ""
% 3.18/0.98  --include_path                          ""
% 3.18/0.98  --clausifier                            res/vclausify_rel
% 3.18/0.98  --clausifier_options                    --mode clausify
% 3.18/0.98  --stdin                                 false
% 3.18/0.98  --stats_out                             all
% 3.18/0.98  
% 3.18/0.98  ------ General Options
% 3.18/0.98  
% 3.18/0.98  --fof                                   false
% 3.18/0.98  --time_out_real                         305.
% 3.18/0.98  --time_out_virtual                      -1.
% 3.18/0.98  --symbol_type_check                     false
% 3.18/0.98  --clausify_out                          false
% 3.18/0.98  --sig_cnt_out                           false
% 3.18/0.98  --trig_cnt_out                          false
% 3.18/0.98  --trig_cnt_out_tolerance                1.
% 3.18/0.98  --trig_cnt_out_sk_spl                   false
% 3.18/0.98  --abstr_cl_out                          false
% 3.18/0.98  
% 3.18/0.98  ------ Global Options
% 3.18/0.98  
% 3.18/0.98  --schedule                              default
% 3.18/0.98  --add_important_lit                     false
% 3.18/0.98  --prop_solver_per_cl                    1000
% 3.18/0.98  --min_unsat_core                        false
% 3.18/0.98  --soft_assumptions                      false
% 3.18/0.98  --soft_lemma_size                       3
% 3.18/0.98  --prop_impl_unit_size                   0
% 3.18/0.98  --prop_impl_unit                        []
% 3.18/0.98  --share_sel_clauses                     true
% 3.18/0.98  --reset_solvers                         false
% 3.18/0.98  --bc_imp_inh                            [conj_cone]
% 3.18/0.98  --conj_cone_tolerance                   3.
% 3.18/0.98  --extra_neg_conj                        none
% 3.18/0.98  --large_theory_mode                     true
% 3.18/0.98  --prolific_symb_bound                   200
% 3.18/0.98  --lt_threshold                          2000
% 3.18/0.98  --clause_weak_htbl                      true
% 3.18/0.98  --gc_record_bc_elim                     false
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing Options
% 3.18/0.98  
% 3.18/0.98  --preprocessing_flag                    true
% 3.18/0.98  --time_out_prep_mult                    0.1
% 3.18/0.98  --splitting_mode                        input
% 3.18/0.98  --splitting_grd                         true
% 3.18/0.98  --splitting_cvd                         false
% 3.18/0.98  --splitting_cvd_svl                     false
% 3.18/0.98  --splitting_nvd                         32
% 3.18/0.98  --sub_typing                            true
% 3.18/0.98  --prep_gs_sim                           true
% 3.18/0.98  --prep_unflatten                        true
% 3.18/0.98  --prep_res_sim                          true
% 3.18/0.98  --prep_upred                            true
% 3.18/0.98  --prep_sem_filter                       exhaustive
% 3.18/0.98  --prep_sem_filter_out                   false
% 3.18/0.98  --pred_elim                             true
% 3.18/0.98  --res_sim_input                         true
% 3.18/0.98  --eq_ax_congr_red                       true
% 3.18/0.98  --pure_diseq_elim                       true
% 3.18/0.98  --brand_transform                       false
% 3.18/0.98  --non_eq_to_eq                          false
% 3.18/0.98  --prep_def_merge                        true
% 3.18/0.98  --prep_def_merge_prop_impl              false
% 3.18/0.98  --prep_def_merge_mbd                    true
% 3.18/0.98  --prep_def_merge_tr_red                 false
% 3.18/0.98  --prep_def_merge_tr_cl                  false
% 3.18/0.98  --smt_preprocessing                     true
% 3.18/0.98  --smt_ac_axioms                         fast
% 3.18/0.98  --preprocessed_out                      false
% 3.18/0.98  --preprocessed_stats                    false
% 3.18/0.98  
% 3.18/0.98  ------ Abstraction refinement Options
% 3.18/0.98  
% 3.18/0.98  --abstr_ref                             []
% 3.18/0.98  --abstr_ref_prep                        false
% 3.18/0.98  --abstr_ref_until_sat                   false
% 3.18/0.98  --abstr_ref_sig_restrict                funpre
% 3.18/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/0.98  --abstr_ref_under                       []
% 3.18/0.98  
% 3.18/0.98  ------ SAT Options
% 3.18/0.98  
% 3.18/0.98  --sat_mode                              false
% 3.18/0.98  --sat_fm_restart_options                ""
% 3.18/0.98  --sat_gr_def                            false
% 3.18/0.98  --sat_epr_types                         true
% 3.18/0.98  --sat_non_cyclic_types                  false
% 3.18/0.98  --sat_finite_models                     false
% 3.18/0.98  --sat_fm_lemmas                         false
% 3.18/0.98  --sat_fm_prep                           false
% 3.18/0.98  --sat_fm_uc_incr                        true
% 3.18/0.98  --sat_out_model                         small
% 3.18/0.98  --sat_out_clauses                       false
% 3.18/0.98  
% 3.18/0.98  ------ QBF Options
% 3.18/0.98  
% 3.18/0.98  --qbf_mode                              false
% 3.18/0.98  --qbf_elim_univ                         false
% 3.18/0.98  --qbf_dom_inst                          none
% 3.18/0.98  --qbf_dom_pre_inst                      false
% 3.18/0.98  --qbf_sk_in                             false
% 3.18/0.98  --qbf_pred_elim                         true
% 3.18/0.98  --qbf_split                             512
% 3.18/0.98  
% 3.18/0.98  ------ BMC1 Options
% 3.18/0.98  
% 3.18/0.98  --bmc1_incremental                      false
% 3.18/0.98  --bmc1_axioms                           reachable_all
% 3.18/0.98  --bmc1_min_bound                        0
% 3.18/0.98  --bmc1_max_bound                        -1
% 3.18/0.98  --bmc1_max_bound_default                -1
% 3.18/0.98  --bmc1_symbol_reachability              true
% 3.18/0.98  --bmc1_property_lemmas                  false
% 3.18/0.98  --bmc1_k_induction                      false
% 3.18/0.98  --bmc1_non_equiv_states                 false
% 3.18/0.98  --bmc1_deadlock                         false
% 3.18/0.98  --bmc1_ucm                              false
% 3.18/0.98  --bmc1_add_unsat_core                   none
% 3.18/0.98  --bmc1_unsat_core_children              false
% 3.18/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/0.98  --bmc1_out_stat                         full
% 3.18/0.98  --bmc1_ground_init                      false
% 3.18/0.98  --bmc1_pre_inst_next_state              false
% 3.18/0.98  --bmc1_pre_inst_state                   false
% 3.18/0.98  --bmc1_pre_inst_reach_state             false
% 3.18/0.98  --bmc1_out_unsat_core                   false
% 3.18/0.98  --bmc1_aig_witness_out                  false
% 3.18/0.98  --bmc1_verbose                          false
% 3.18/0.98  --bmc1_dump_clauses_tptp                false
% 3.18/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.18/0.98  --bmc1_dump_file                        -
% 3.18/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.18/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.18/0.98  --bmc1_ucm_extend_mode                  1
% 3.18/0.98  --bmc1_ucm_init_mode                    2
% 3.18/0.98  --bmc1_ucm_cone_mode                    none
% 3.18/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.18/0.98  --bmc1_ucm_relax_model                  4
% 3.18/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.18/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/0.98  --bmc1_ucm_layered_model                none
% 3.18/0.98  --bmc1_ucm_max_lemma_size               10
% 3.18/0.98  
% 3.18/0.98  ------ AIG Options
% 3.18/0.98  
% 3.18/0.98  --aig_mode                              false
% 3.18/0.98  
% 3.18/0.98  ------ Instantiation Options
% 3.18/0.98  
% 3.18/0.98  --instantiation_flag                    true
% 3.18/0.98  --inst_sos_flag                         false
% 3.18/0.98  --inst_sos_phase                        true
% 3.18/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/0.98  --inst_lit_sel_side                     none
% 3.18/0.98  --inst_solver_per_active                1400
% 3.18/0.98  --inst_solver_calls_frac                1.
% 3.18/0.98  --inst_passive_queue_type               priority_queues
% 3.18/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/0.98  --inst_passive_queues_freq              [25;2]
% 3.18/0.98  --inst_dismatching                      true
% 3.18/0.98  --inst_eager_unprocessed_to_passive     true
% 3.18/0.98  --inst_prop_sim_given                   true
% 3.18/0.98  --inst_prop_sim_new                     false
% 3.18/0.98  --inst_subs_new                         false
% 3.18/0.98  --inst_eq_res_simp                      false
% 3.18/0.98  --inst_subs_given                       false
% 3.18/0.98  --inst_orphan_elimination               true
% 3.18/0.98  --inst_learning_loop_flag               true
% 3.18/0.98  --inst_learning_start                   3000
% 3.18/0.98  --inst_learning_factor                  2
% 3.18/0.98  --inst_start_prop_sim_after_learn       3
% 3.18/0.98  --inst_sel_renew                        solver
% 3.18/0.98  --inst_lit_activity_flag                true
% 3.18/0.98  --inst_restr_to_given                   false
% 3.18/0.98  --inst_activity_threshold               500
% 3.18/0.98  --inst_out_proof                        true
% 3.18/0.98  
% 3.18/0.98  ------ Resolution Options
% 3.18/0.98  
% 3.18/0.98  --resolution_flag                       false
% 3.18/0.98  --res_lit_sel                           adaptive
% 3.18/0.98  --res_lit_sel_side                      none
% 3.18/0.98  --res_ordering                          kbo
% 3.18/0.98  --res_to_prop_solver                    active
% 3.18/0.98  --res_prop_simpl_new                    false
% 3.18/0.98  --res_prop_simpl_given                  true
% 3.18/0.98  --res_passive_queue_type                priority_queues
% 3.18/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/0.98  --res_passive_queues_freq               [15;5]
% 3.18/0.98  --res_forward_subs                      full
% 3.18/0.98  --res_backward_subs                     full
% 3.18/0.98  --res_forward_subs_resolution           true
% 3.18/0.98  --res_backward_subs_resolution          true
% 3.18/0.98  --res_orphan_elimination                true
% 3.18/0.98  --res_time_limit                        2.
% 3.18/0.98  --res_out_proof                         true
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Options
% 3.18/0.98  
% 3.18/0.98  --superposition_flag                    true
% 3.18/0.98  --sup_passive_queue_type                priority_queues
% 3.18/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.18/0.98  --demod_completeness_check              fast
% 3.18/0.98  --demod_use_ground                      true
% 3.18/0.98  --sup_to_prop_solver                    passive
% 3.18/0.98  --sup_prop_simpl_new                    true
% 3.18/0.98  --sup_prop_simpl_given                  true
% 3.18/0.98  --sup_fun_splitting                     false
% 3.18/0.98  --sup_smt_interval                      50000
% 3.18/0.98  
% 3.18/0.98  ------ Superposition Simplification Setup
% 3.18/0.98  
% 3.18/0.98  --sup_indices_passive                   []
% 3.18/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_full_bw                           [BwDemod]
% 3.18/0.98  --sup_immed_triv                        [TrivRules]
% 3.18/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_immed_bw_main                     []
% 3.18/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/0.98  
% 3.18/0.98  ------ Combination Options
% 3.18/0.98  
% 3.18/0.98  --comb_res_mult                         3
% 3.18/0.98  --comb_sup_mult                         2
% 3.18/0.98  --comb_inst_mult                        10
% 3.18/0.98  
% 3.18/0.98  ------ Debug Options
% 3.18/0.98  
% 3.18/0.98  --dbg_backtrace                         false
% 3.18/0.98  --dbg_dump_prop_clauses                 false
% 3.18/0.98  --dbg_dump_prop_clauses_file            -
% 3.18/0.98  --dbg_out_stat                          false
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  ------ Proving...
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  % SZS status Theorem for theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  fof(f16,conjecture,(
% 3.18/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f17,negated_conjecture,(
% 3.18/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.18/0.98    inference(negated_conjecture,[],[f16])).
% 3.18/0.98  
% 3.18/0.98  fof(f43,plain,(
% 3.18/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.18/0.98    inference(ennf_transformation,[],[f17])).
% 3.18/0.98  
% 3.18/0.98  fof(f44,plain,(
% 3.18/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.18/0.98    inference(flattening,[],[f43])).
% 3.18/0.98  
% 3.18/0.98  fof(f47,plain,(
% 3.18/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.18/0.98    introduced(choice_axiom,[])).
% 3.18/0.98  
% 3.18/0.98  fof(f48,plain,(
% 3.18/0.98    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.18/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f44,f47])).
% 3.18/0.98  
% 3.18/0.98  fof(f75,plain,(
% 3.18/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.18/0.98    inference(cnf_transformation,[],[f48])).
% 3.18/0.98  
% 3.18/0.98  fof(f13,axiom,(
% 3.18/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f39,plain,(
% 3.18/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.18/0.98    inference(ennf_transformation,[],[f13])).
% 3.18/0.98  
% 3.18/0.98  fof(f40,plain,(
% 3.18/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.18/0.98    inference(flattening,[],[f39])).
% 3.18/0.98  
% 3.18/0.98  fof(f69,plain,(
% 3.18/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f40])).
% 3.18/0.98  
% 3.18/0.98  fof(f72,plain,(
% 3.18/0.98    v1_funct_1(sK2)),
% 3.18/0.98    inference(cnf_transformation,[],[f48])).
% 3.18/0.98  
% 3.18/0.98  fof(f73,plain,(
% 3.18/0.98    v1_funct_2(sK2,sK1,sK1)),
% 3.18/0.98    inference(cnf_transformation,[],[f48])).
% 3.18/0.98  
% 3.18/0.98  fof(f74,plain,(
% 3.18/0.98    v3_funct_2(sK2,sK1,sK1)),
% 3.18/0.98    inference(cnf_transformation,[],[f48])).
% 3.18/0.98  
% 3.18/0.98  fof(f10,axiom,(
% 3.18/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f35,plain,(
% 3.18/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.18/0.98    inference(ennf_transformation,[],[f10])).
% 3.18/0.98  
% 3.18/0.98  fof(f36,plain,(
% 3.18/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.18/0.98    inference(flattening,[],[f35])).
% 3.18/0.98  
% 3.18/0.98  fof(f64,plain,(
% 3.18/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f36])).
% 3.18/0.98  
% 3.18/0.98  fof(f15,axiom,(
% 3.18/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f41,plain,(
% 3.18/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.18/0.98    inference(ennf_transformation,[],[f15])).
% 3.18/0.98  
% 3.18/0.98  fof(f42,plain,(
% 3.18/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.18/0.98    inference(flattening,[],[f41])).
% 3.18/0.98  
% 3.18/0.98  fof(f71,plain,(
% 3.18/0.98    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f42])).
% 3.18/0.98  
% 3.18/0.98  fof(f6,axiom,(
% 3.18/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f30,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.98    inference(ennf_transformation,[],[f6])).
% 3.18/0.98  
% 3.18/0.98  fof(f56,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f30])).
% 3.18/0.98  
% 3.18/0.98  fof(f1,axiom,(
% 3.18/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f21,plain,(
% 3.18/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f1])).
% 3.18/0.98  
% 3.18/0.98  fof(f22,plain,(
% 3.18/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.98    inference(flattening,[],[f21])).
% 3.18/0.98  
% 3.18/0.98  fof(f50,plain,(
% 3.18/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f22])).
% 3.18/0.98  
% 3.18/0.98  fof(f5,axiom,(
% 3.18/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f29,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.98    inference(ennf_transformation,[],[f5])).
% 3.18/0.98  
% 3.18/0.98  fof(f55,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f29])).
% 3.18/0.98  
% 3.18/0.98  fof(f62,plain,(
% 3.18/0.98    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f36])).
% 3.18/0.98  
% 3.18/0.98  fof(f9,axiom,(
% 3.18/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f20,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.18/0.98    inference(pure_predicate_removal,[],[f9])).
% 3.18/0.98  
% 3.18/0.98  fof(f33,plain,(
% 3.18/0.98    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.98    inference(ennf_transformation,[],[f20])).
% 3.18/0.98  
% 3.18/0.98  fof(f34,plain,(
% 3.18/0.98    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.98    inference(flattening,[],[f33])).
% 3.18/0.98  
% 3.18/0.98  fof(f60,plain,(
% 3.18/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f34])).
% 3.18/0.98  
% 3.18/0.98  fof(f3,axiom,(
% 3.18/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f25,plain,(
% 3.18/0.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f3])).
% 3.18/0.98  
% 3.18/0.98  fof(f26,plain,(
% 3.18/0.98    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.98    inference(flattening,[],[f25])).
% 3.18/0.98  
% 3.18/0.98  fof(f53,plain,(
% 3.18/0.98    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f26])).
% 3.18/0.98  
% 3.18/0.98  fof(f2,axiom,(
% 3.18/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f23,plain,(
% 3.18/0.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f2])).
% 3.18/0.98  
% 3.18/0.98  fof(f24,plain,(
% 3.18/0.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.98    inference(flattening,[],[f23])).
% 3.18/0.98  
% 3.18/0.98  fof(f51,plain,(
% 3.18/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f24])).
% 3.18/0.98  
% 3.18/0.98  fof(f14,axiom,(
% 3.18/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f70,plain,(
% 3.18/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f14])).
% 3.18/0.98  
% 3.18/0.98  fof(f78,plain,(
% 3.18/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(definition_unfolding,[],[f51,f70])).
% 3.18/0.98  
% 3.18/0.98  fof(f4,axiom,(
% 3.18/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f27,plain,(
% 3.18/0.98    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/0.98    inference(ennf_transformation,[],[f4])).
% 3.18/0.98  
% 3.18/0.98  fof(f28,plain,(
% 3.18/0.98    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/0.98    inference(flattening,[],[f27])).
% 3.18/0.98  
% 3.18/0.98  fof(f54,plain,(
% 3.18/0.98    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f28])).
% 3.18/0.98  
% 3.18/0.98  fof(f52,plain,(
% 3.18/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f24])).
% 3.18/0.98  
% 3.18/0.98  fof(f77,plain,(
% 3.18/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(definition_unfolding,[],[f52,f70])).
% 3.18/0.98  
% 3.18/0.98  fof(f49,plain,(
% 3.18/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f22])).
% 3.18/0.98  
% 3.18/0.98  fof(f12,axiom,(
% 3.18/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f37,plain,(
% 3.18/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.18/0.98    inference(ennf_transformation,[],[f12])).
% 3.18/0.98  
% 3.18/0.98  fof(f38,plain,(
% 3.18/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.18/0.98    inference(flattening,[],[f37])).
% 3.18/0.98  
% 3.18/0.98  fof(f68,plain,(
% 3.18/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f38])).
% 3.18/0.98  
% 3.18/0.98  fof(f61,plain,(
% 3.18/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/0.98    inference(cnf_transformation,[],[f36])).
% 3.18/0.98  
% 3.18/0.98  fof(f76,plain,(
% 3.18/0.98    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.18/0.98    inference(cnf_transformation,[],[f48])).
% 3.18/0.98  
% 3.18/0.98  fof(f8,axiom,(
% 3.18/0.98    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f58,plain,(
% 3.18/0.98    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f8])).
% 3.18/0.98  
% 3.18/0.98  fof(f79,plain,(
% 3.18/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.18/0.98    inference(definition_unfolding,[],[f58,f70])).
% 3.18/0.98  
% 3.18/0.98  fof(f7,axiom,(
% 3.18/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.18/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/0.98  
% 3.18/0.98  fof(f31,plain,(
% 3.18/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.18/0.98    inference(ennf_transformation,[],[f7])).
% 3.18/0.98  
% 3.18/0.98  fof(f32,plain,(
% 3.18/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/0.98    inference(flattening,[],[f31])).
% 3.18/0.98  
% 3.18/0.98  fof(f57,plain,(
% 3.18/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/0.98    inference(cnf_transformation,[],[f32])).
% 3.18/0.98  
% 3.18/0.98  cnf(c_23,negated_conjecture,
% 3.18/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.18/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_479,negated_conjecture,
% 3.18/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1059,plain,
% 3.18/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_20,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.98      | ~ v1_funct_1(X0)
% 3.18/0.98      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_482,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.98      | ~ v1_funct_1(X0_48)
% 3.18/0.98      | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1056,plain,
% 3.18/0.98      ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
% 3.18/0.98      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2714,plain,
% 3.18/0.98      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.18/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1059,c_1056]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_26,negated_conjecture,
% 3.18/0.98      ( v1_funct_1(sK2) ),
% 3.18/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_25,negated_conjecture,
% 3.18/0.98      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_24,negated_conjecture,
% 3.18/0.98      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.18/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_592,plain,
% 3.18/0.98      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.18/0.98      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.18/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/0.98      | ~ v1_funct_1(sK2)
% 3.18/0.98      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_482]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3125,plain,
% 3.18/0.98      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_2714,c_26,c_25,c_24,c_23,c_592]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_12,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.98      | ~ v1_funct_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_490,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.98      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.98      | ~ v1_funct_1(X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_12]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1048,plain,
% 3.18/0.98      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_490]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3138,plain,
% 3.18/0.98      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.18/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3125,c_1048]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_27,plain,
% 3.18/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_28,plain,
% 3.18/0.98      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_29,plain,
% 3.18/0.98      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_30,plain,
% 3.18/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3862,plain,
% 3.18/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_3138,c_27,c_28,c_29,c_30]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_21,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.98      | ~ v1_funct_1(X0)
% 3.18/0.98      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.18/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_481,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.98      | ~ v1_funct_1(X0_48)
% 3.18/0.98      | k1_relset_1(X0_49,X0_49,X0_48) = X0_49 ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1057,plain,
% 3.18/0.98      ( k1_relset_1(X0_49,X0_49,X0_48) = X0_49
% 3.18/0.98      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3871,plain,
% 3.18/0.98      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
% 3.18/0.98      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3862,c_1057]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_7,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_494,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.98      | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1044,plain,
% 3.18/0.98      ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3876,plain,
% 3.18/0.98      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3862,c_1044]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3905,plain,
% 3.18/0.98      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.18/0.98      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.98      inference(demodulation,[status(thm)],[c_3871,c_3876]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_0,plain,
% 3.18/0.98      ( ~ v1_relat_1(X0)
% 3.18/0.98      | ~ v1_funct_1(X0)
% 3.18/0.98      | v1_funct_1(k2_funct_1(X0)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_501,plain,
% 3.18/0.98      ( ~ v1_relat_1(X0_48)
% 3.18/0.98      | ~ v1_funct_1(X0_48)
% 3.18/0.98      | v1_funct_1(k2_funct_1(X0_48)) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_542,plain,
% 3.18/0.98      ( v1_relat_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_544,plain,
% 3.18/0.98      ( v1_relat_1(sK2) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_542]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_6,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.98      | v1_relat_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_495,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.98      | v1_relat_1(X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_560,plain,
% 3.18/0.98      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | v1_relat_1(X0_48) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_562,plain,
% 3.18/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_560]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_14,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.98      | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.18/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.98      | ~ v1_funct_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_488,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.18/0.98      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.98      | ~ v1_funct_1(X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1050,plain,
% 3.18/0.98      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.18/0.98      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2941,plain,
% 3.18/0.98      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.18/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1059,c_1050]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_579,plain,
% 3.18/0.98      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.18/0.98      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_581,plain,
% 3.18/0.98      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.18/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_579]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3234,plain,
% 3.18/0.98      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_2941,c_27,c_28,c_29,c_30,c_581]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3238,plain,
% 3.18/0.98      ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_3234,c_3125]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_6855,plain,
% 3.18/0.98      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_3905,c_27,c_30,c_544,c_562,c_3238]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_10,plain,
% 3.18/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.98      | v2_funct_1(X0)
% 3.18/0.98      | ~ v1_funct_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_491,plain,
% 3.18/0.98      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.18/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.98      | v2_funct_1(X0_48)
% 3.18/0.98      | ~ v1_funct_1(X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_10]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1047,plain,
% 3.18/0.98      ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | v2_funct_1(X0_48) = iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3874,plain,
% 3.18/0.98      ( v3_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.18/0.98      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3862,c_1047]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4,plain,
% 3.18/0.98      ( ~ v2_funct_1(X0)
% 3.18/0.98      | v2_funct_1(k2_funct_1(X0))
% 3.18/0.98      | ~ v1_relat_1(X0)
% 3.18/0.98      | ~ v1_funct_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_497,plain,
% 3.18/0.98      ( ~ v2_funct_1(X0_48)
% 3.18/0.98      | v2_funct_1(k2_funct_1(X0_48))
% 3.18/0.98      | ~ v1_relat_1(X0_48)
% 3.18/0.98      | ~ v1_funct_1(X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_554,plain,
% 3.18/0.98      ( v2_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
% 3.18/0.98      | v1_relat_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_556,plain,
% 3.18/0.98      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.18/0.98      | v2_funct_1(sK2) != iProver_top
% 3.18/0.98      | v1_relat_1(sK2) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_554]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_570,plain,
% 3.18/0.98      ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | v2_funct_1(X0_48) = iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_572,plain,
% 3.18/0.98      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/0.98      | v2_funct_1(sK2) = iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_570]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4674,plain,
% 3.18/0.98      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_3874,c_27,c_29,c_30,c_556,c_562,c_572]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3,plain,
% 3.18/0.98      ( ~ v2_funct_1(X0)
% 3.18/0.98      | ~ v1_relat_1(X0)
% 3.18/0.98      | ~ v1_funct_1(X0)
% 3.18/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_498,plain,
% 3.18/0.98      ( ~ v2_funct_1(X0_48)
% 3.18/0.98      | ~ v1_relat_1(X0_48)
% 3.18/0.98      | ~ v1_funct_1(X0_48)
% 3.18/0.98      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1040,plain,
% 3.18/0.98      ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
% 3.18/0.98      | v2_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_relat_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4681,plain,
% 3.18/0.98      ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
% 3.18/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_4674,c_1040]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1979,plain,
% 3.18/0.98      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v2_funct_1(sK2) = iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1059,c_1047]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2264,plain,
% 3.18/0.98      ( v2_funct_1(sK2) = iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_1979,c_27,c_29,c_30,c_572]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5,plain,
% 3.18/0.98      ( ~ v2_funct_1(X0)
% 3.18/0.98      | ~ v1_relat_1(X0)
% 3.18/0.98      | ~ v1_funct_1(X0)
% 3.18/0.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.18/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_496,plain,
% 3.18/0.98      ( ~ v2_funct_1(X0_48)
% 3.18/0.98      | ~ v1_relat_1(X0_48)
% 3.18/0.98      | ~ v1_funct_1(X0_48)
% 3.18/0.98      | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1042,plain,
% 3.18/0.98      ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
% 3.18/0.98      | v2_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_relat_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2271,plain,
% 3.18/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.18/0.98      | v1_relat_1(sK2) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_2264,c_1042]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_558,plain,
% 3.18/0.98      ( ~ v2_funct_1(sK2)
% 3.18/0.98      | ~ v1_relat_1(sK2)
% 3.18/0.98      | ~ v1_funct_1(sK2)
% 3.18/0.98      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_496]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_561,plain,
% 3.18/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/0.98      | v1_relat_1(sK2) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_495]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_571,plain,
% 3.18/0.98      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.18/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/0.98      | v2_funct_1(sK2)
% 3.18/0.98      | ~ v1_funct_1(sK2) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_491]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2366,plain,
% 3.18/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_2271,c_26,c_24,c_23,c_558,c_561,c_571]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2,plain,
% 3.18/0.98      ( ~ v2_funct_1(X0)
% 3.18/0.98      | ~ v1_relat_1(X0)
% 3.18/0.98      | ~ v1_funct_1(X0)
% 3.18/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_499,plain,
% 3.18/0.98      ( ~ v2_funct_1(X0_48)
% 3.18/0.98      | ~ v1_relat_1(X0_48)
% 3.18/0.98      | ~ v1_funct_1(X0_48)
% 3.18/0.98      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1039,plain,
% 3.18/0.98      ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
% 3.18/0.98      | v2_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_relat_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2270,plain,
% 3.18/0.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.18/0.98      | v1_relat_1(sK2) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_2264,c_1039]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_549,plain,
% 3.18/0.98      ( ~ v2_funct_1(sK2)
% 3.18/0.98      | ~ v1_relat_1(sK2)
% 3.18/0.98      | ~ v1_funct_1(sK2)
% 3.18/0.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_499]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2509,plain,
% 3.18/0.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_2270,c_26,c_24,c_23,c_549,c_561,c_571]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4698,plain,
% 3.18/0.98      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2))
% 3.18/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_4681,c_2366,c_2509]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1,plain,
% 3.18/0.98      ( ~ v1_relat_1(X0)
% 3.18/0.98      | v1_relat_1(k2_funct_1(X0))
% 3.18/0.98      | ~ v1_funct_1(X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_500,plain,
% 3.18/0.98      ( ~ v1_relat_1(X0_48)
% 3.18/0.98      | v1_relat_1(k2_funct_1(X0_48))
% 3.18/0.98      | ~ v1_funct_1(X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_545,plain,
% 3.18/0.98      ( v1_relat_1(X0_48) != iProver_top
% 3.18/0.98      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_547,plain,
% 3.18/0.98      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.18/0.98      | v1_relat_1(sK2) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_545]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4850,plain,
% 3.18/0.98      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_4698,c_27,c_30,c_544,c_547,c_562]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_6862,plain,
% 3.18/0.98      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 3.18/0.98      inference(demodulation,[status(thm)],[c_6855,c_4850]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_19,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.18/0.98      | ~ v1_funct_1(X0)
% 3.18/0.98      | ~ v1_funct_1(X3)
% 3.18/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.18/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_483,plain,
% 3.18/0.98      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.98      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.18/0.98      | ~ v1_funct_1(X0_48)
% 3.18/0.98      | ~ v1_funct_1(X1_48)
% 3.18/0.98      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1055,plain,
% 3.18/0.98      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 3.18/0.98      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(X1_48) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3873,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3862,c_1055]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5062,plain,
% 3.18/0.98      ( v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_3873,c_27,c_30,c_544,c_562]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5063,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_5062]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5071,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1059,c_5063]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5102,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_5071,c_2509]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5719,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_5102,c_27]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3070,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1059,c_1055]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3277,plain,
% 3.18/0.98      ( v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_3070,c_27]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3278,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_3277]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3286,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
% 3.18/0.98      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1048,c_3278]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_15,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.18/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/0.98      | ~ v1_funct_1(X0)
% 3.18/0.98      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_487,plain,
% 3.18/0.98      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.18/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.18/0.98      | ~ v1_funct_1(X0_48)
% 3.18/0.98      | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_582,plain,
% 3.18/0.98      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4138,plain,
% 3.18/0.98      ( v1_funct_1(X0_48) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48)) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_3286,c_582]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4139,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
% 3.18/0.98      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.18/0.98      | v1_funct_1(X0_48) != iProver_top ),
% 3.18/0.98      inference(renaming,[status(thm)],[c_4138]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4149,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
% 3.18/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1059,c_4139]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2269,plain,
% 3.18/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.18/0.98      | v1_relat_1(sK2) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_2264,c_1040]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_552,plain,
% 3.18/0.98      ( ~ v2_funct_1(sK2)
% 3.18/0.98      | ~ v1_relat_1(sK2)
% 3.18/0.98      | ~ v1_funct_1(sK2)
% 3.18/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_498]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2504,plain,
% 3.18/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_2269,c_26,c_24,c_23,c_552,c_561,c_571]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2114,plain,
% 3.18/0.98      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.18/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1059,c_1057]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1528,plain,
% 3.18/0.98      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1059,c_1044]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2134,plain,
% 3.18/0.98      ( k1_relat_1(sK2) = sK1
% 3.18/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(demodulation,[status(thm)],[c_2114,c_1528]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2424,plain,
% 3.18/0.98      ( k1_relat_1(sK2) = sK1 ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_2134,c_27,c_28]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_2506,plain,
% 3.18/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_2504,c_2424]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4198,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.18/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_4149,c_2506,c_3125]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3872,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_3862,c_3278]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3902,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.18/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/0.98      inference(light_normalisation,[status(thm)],[c_3872,c_2506]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4215,plain,
% 3.18/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_4198,c_27,c_30,c_544,c_562,c_3902]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_22,negated_conjecture,
% 3.18/0.98      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.18/0.98      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.18/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_480,negated_conjecture,
% 3.18/0.98      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.18/0.98      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1058,plain,
% 3.18/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.18/0.98      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_3129,plain,
% 3.18/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.18/0.98      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.98      inference(demodulation,[status(thm)],[c_3125,c_1058]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4218,plain,
% 3.18/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.18/0.98      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.98      inference(demodulation,[status(thm)],[c_4215,c_3129]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_9,plain,
% 3.18/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.18/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_492,plain,
% 3.18/0.98      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1046,plain,
% 3.18/0.98      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_8,plain,
% 3.18/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 3.18/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.18/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_493,plain,
% 3.18/0.98      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
% 3.18/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.18/0.98      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
% 3.18/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1045,plain,
% 3.18/0.98      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.18/0.98      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.18/0.98      inference(predicate_to_equality,[status(thm)],[c_493]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1954,plain,
% 3.18/0.98      ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
% 3.18/0.98      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
% 3.18/0.98      inference(superposition,[status(thm)],[c_1046,c_1045]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_1972,plain,
% 3.18/0.98      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 3.18/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.18/0.98      inference(instantiation,[status(thm)],[c_1954]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_4315,plain,
% 3.18/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.98      inference(global_propositional_subsumption,
% 3.18/0.98                [status(thm)],
% 3.18/0.98                [c_4218,c_30,c_1972]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_5722,plain,
% 3.18/0.98      ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.98      inference(demodulation,[status(thm)],[c_5719,c_4315]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(c_6880,plain,
% 3.18/0.98      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.18/0.98      inference(demodulation,[status(thm)],[c_6862,c_5722]) ).
% 3.18/0.98  
% 3.18/0.98  cnf(contradiction,plain,
% 3.18/0.98      ( $false ),
% 3.18/0.98      inference(minisat,[status(thm)],[c_6880,c_1972,c_30]) ).
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/0.98  
% 3.18/0.98  ------                               Statistics
% 3.18/0.98  
% 3.18/0.98  ------ General
% 3.18/0.98  
% 3.18/0.98  abstr_ref_over_cycles:                  0
% 3.18/0.98  abstr_ref_under_cycles:                 0
% 3.18/0.98  gc_basic_clause_elim:                   0
% 3.18/0.98  forced_gc_time:                         0
% 3.18/0.98  parsing_time:                           0.009
% 3.18/0.98  unif_index_cands_time:                  0.
% 3.18/0.98  unif_index_add_time:                    0.
% 3.18/0.98  orderings_time:                         0.
% 3.18/0.98  out_proof_time:                         0.018
% 3.18/0.98  total_time:                             0.256
% 3.18/0.98  num_of_symbols:                         55
% 3.18/0.98  num_of_terms:                           6425
% 3.18/0.98  
% 3.18/0.98  ------ Preprocessing
% 3.18/0.98  
% 3.18/0.98  num_of_splits:                          0
% 3.18/0.98  num_of_split_atoms:                     0
% 3.18/0.98  num_of_reused_defs:                     0
% 3.18/0.98  num_eq_ax_congr_red:                    21
% 3.18/0.98  num_of_sem_filtered_clauses:            1
% 3.18/0.98  num_of_subtypes:                        4
% 3.18/0.98  monotx_restored_types:                  1
% 3.18/0.98  sat_num_of_epr_types:                   0
% 3.18/0.98  sat_num_of_non_cyclic_types:            0
% 3.18/0.98  sat_guarded_non_collapsed_types:        1
% 3.18/0.98  num_pure_diseq_elim:                    0
% 3.18/0.98  simp_replaced_by:                       0
% 3.18/0.98  res_preprocessed:                       145
% 3.18/0.98  prep_upred:                             0
% 3.18/0.98  prep_unflattend:                        0
% 3.18/0.98  smt_new_axioms:                         0
% 3.18/0.98  pred_elim_cands:                        7
% 3.18/0.98  pred_elim:                              0
% 3.18/0.98  pred_elim_cl:                           0
% 3.18/0.98  pred_elim_cycles:                       2
% 3.18/0.98  merged_defs:                            0
% 3.18/0.98  merged_defs_ncl:                        0
% 3.18/0.98  bin_hyper_res:                          0
% 3.18/0.98  prep_cycles:                            4
% 3.18/0.98  pred_elim_time:                         0.001
% 3.18/0.98  splitting_time:                         0.
% 3.18/0.98  sem_filter_time:                        0.
% 3.18/0.98  monotx_time:                            0.001
% 3.18/0.98  subtype_inf_time:                       0.001
% 3.18/0.98  
% 3.18/0.98  ------ Problem properties
% 3.18/0.98  
% 3.18/0.98  clauses:                                26
% 3.18/0.98  conjectures:                            5
% 3.18/0.98  epr:                                    3
% 3.18/0.98  horn:                                   26
% 3.18/0.98  ground:                                 5
% 3.18/0.98  unary:                                  8
% 3.18/0.98  binary:                                 3
% 3.18/0.98  lits:                                   77
% 3.18/0.98  lits_eq:                                7
% 3.18/0.98  fd_pure:                                0
% 3.18/0.98  fd_pseudo:                              0
% 3.18/0.98  fd_cond:                                0
% 3.18/0.98  fd_pseudo_cond:                         0
% 3.18/0.98  ac_symbols:                             0
% 3.18/0.98  
% 3.18/0.98  ------ Propositional Solver
% 3.18/0.98  
% 3.18/0.98  prop_solver_calls:                      31
% 3.18/0.98  prop_fast_solver_calls:                 1200
% 3.18/0.98  smt_solver_calls:                       0
% 3.18/0.98  smt_fast_solver_calls:                  0
% 3.18/0.98  prop_num_of_clauses:                    2144
% 3.18/0.98  prop_preprocess_simplified:             6970
% 3.18/0.98  prop_fo_subsumed:                       73
% 3.18/0.98  prop_solver_time:                       0.
% 3.18/0.98  smt_solver_time:                        0.
% 3.18/0.98  smt_fast_solver_time:                   0.
% 3.18/0.98  prop_fast_solver_time:                  0.
% 3.18/0.98  prop_unsat_core_time:                   0.
% 3.18/0.98  
% 3.18/0.98  ------ QBF
% 3.18/0.98  
% 3.18/0.98  qbf_q_res:                              0
% 3.18/0.98  qbf_num_tautologies:                    0
% 3.18/0.98  qbf_prep_cycles:                        0
% 3.18/0.98  
% 3.18/0.98  ------ BMC1
% 3.18/0.98  
% 3.18/0.98  bmc1_current_bound:                     -1
% 3.18/0.98  bmc1_last_solved_bound:                 -1
% 3.18/0.98  bmc1_unsat_core_size:                   -1
% 3.18/0.98  bmc1_unsat_core_parents_size:           -1
% 3.18/0.98  bmc1_merge_next_fun:                    0
% 3.18/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.18/0.98  
% 3.18/0.98  ------ Instantiation
% 3.18/0.98  
% 3.18/0.98  inst_num_of_clauses:                    775
% 3.18/0.98  inst_num_in_passive:                    337
% 3.18/0.98  inst_num_in_active:                     438
% 3.18/0.98  inst_num_in_unprocessed:                0
% 3.18/0.98  inst_num_of_loops:                      460
% 3.18/0.98  inst_num_of_learning_restarts:          0
% 3.18/0.98  inst_num_moves_active_passive:          17
% 3.18/0.98  inst_lit_activity:                      0
% 3.18/0.98  inst_lit_activity_moves:                0
% 3.18/0.98  inst_num_tautologies:                   0
% 3.18/0.98  inst_num_prop_implied:                  0
% 3.18/0.98  inst_num_existing_simplified:           0
% 3.18/0.98  inst_num_eq_res_simplified:             0
% 3.18/0.98  inst_num_child_elim:                    0
% 3.18/0.98  inst_num_of_dismatching_blockings:      709
% 3.18/0.98  inst_num_of_non_proper_insts:           1057
% 3.18/0.98  inst_num_of_duplicates:                 0
% 3.18/0.98  inst_inst_num_from_inst_to_res:         0
% 3.18/0.98  inst_dismatching_checking_time:         0.
% 3.18/0.98  
% 3.18/0.98  ------ Resolution
% 3.18/0.98  
% 3.18/0.98  res_num_of_clauses:                     0
% 3.18/0.98  res_num_in_passive:                     0
% 3.18/0.98  res_num_in_active:                      0
% 3.18/0.98  res_num_of_loops:                       149
% 3.18/0.98  res_forward_subset_subsumed:            93
% 3.18/0.98  res_backward_subset_subsumed:           4
% 3.18/0.98  res_forward_subsumed:                   0
% 3.18/0.98  res_backward_subsumed:                  0
% 3.18/0.98  res_forward_subsumption_resolution:     0
% 3.18/0.98  res_backward_subsumption_resolution:    0
% 3.18/0.98  res_clause_to_clause_subsumption:       322
% 3.18/0.98  res_orphan_elimination:                 0
% 3.18/0.98  res_tautology_del:                      130
% 3.18/0.98  res_num_eq_res_simplified:              0
% 3.18/0.98  res_num_sel_changes:                    0
% 3.18/0.98  res_moves_from_active_to_pass:          0
% 3.18/0.98  
% 3.18/0.98  ------ Superposition
% 3.18/0.98  
% 3.18/0.98  sup_time_total:                         0.
% 3.18/0.98  sup_time_generating:                    0.
% 3.18/0.98  sup_time_sim_full:                      0.
% 3.18/0.98  sup_time_sim_immed:                     0.
% 3.18/0.98  
% 3.18/0.98  sup_num_of_clauses:                     123
% 3.18/0.98  sup_num_in_active:                      74
% 3.18/0.98  sup_num_in_passive:                     49
% 3.18/0.98  sup_num_of_loops:                       91
% 3.18/0.98  sup_fw_superposition:                   85
% 3.18/0.98  sup_bw_superposition:                   70
% 3.18/0.98  sup_immediate_simplified:               62
% 3.18/0.98  sup_given_eliminated:                   0
% 3.18/0.98  comparisons_done:                       0
% 3.18/0.98  comparisons_avoided:                    0
% 3.18/0.98  
% 3.18/0.98  ------ Simplifications
% 3.18/0.98  
% 3.18/0.98  
% 3.18/0.98  sim_fw_subset_subsumed:                 8
% 3.18/0.98  sim_bw_subset_subsumed:                 6
% 3.18/0.98  sim_fw_subsumed:                        8
% 3.18/0.98  sim_bw_subsumed:                        1
% 3.18/0.98  sim_fw_subsumption_res:                 3
% 3.18/0.98  sim_bw_subsumption_res:                 0
% 3.18/0.98  sim_tautology_del:                      0
% 3.18/0.98  sim_eq_tautology_del:                   9
% 3.18/0.98  sim_eq_res_simp:                        0
% 3.18/0.98  sim_fw_demodulated:                     4
% 3.18/0.98  sim_bw_demodulated:                     15
% 3.18/0.98  sim_light_normalised:                   44
% 3.18/0.98  sim_joinable_taut:                      0
% 3.18/0.98  sim_joinable_simp:                      0
% 3.18/0.98  sim_ac_normalised:                      0
% 3.18/0.98  sim_smt_subsumption:                    0
% 3.18/0.98  
%------------------------------------------------------------------------------
