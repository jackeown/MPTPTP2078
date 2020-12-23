%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:35 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  199 (2004 expanded)
%              Number of clauses        :  136 ( 657 expanded)
%              Number of leaves         :   15 ( 379 expanded)
%              Depth                    :   22
%              Number of atoms          :  667 (9461 expanded)
%              Number of equality atoms :  323 (1058 expanded)
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

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f46,plain,
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

fof(f47,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f46])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
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
    inference(definition_unfolding,[],[f51,f68])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_458,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_985,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_461,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_982,plain,
    ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_2321,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_982])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_23,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_561,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_461])).

cnf(c_2568,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2321,c_25,c_24,c_23,c_22,c_561])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_973,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_2574,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2568,c_973])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_28,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3600,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_26,c_27,c_28,c_29])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_460,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | k1_relset_1(X0_49,X0_49,X0_48) = X0_49 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_983,plain,
    ( k1_relset_1(X0_49,X0_49,X0_48) = X0_49
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_3608,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3600,c_983])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_970,plain,
    ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_3613,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3600,c_970])).

cnf(c_3616,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3608,c_3613])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_467,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_976,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_2306,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_976])).

cnf(c_550,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_552,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_2557,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2306,c_26,c_27,c_28,c_29,c_552])).

cnf(c_2570,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2568,c_2557])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_468,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_975,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_2384,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_975])).

cnf(c_547,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_549,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_2702,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2384,c_26,c_27,c_28,c_29,c_549])).

cnf(c_2706,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2702,c_2568])).

cnf(c_6533,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3616,c_2570,c_2706])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_476,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_967,plain,
    ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_2561,plain,
    ( k5_relat_1(k2_funct_2(sK1,sK2),k2_funct_1(k2_funct_2(sK1,sK2))) = k6_partfun1(k1_relat_1(k2_funct_2(sK1,sK2)))
    | v2_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
    | v1_relat_1(k2_funct_2(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_967])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_86,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_88,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_469,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X0_49)
    | ~ v3_funct_2(X0_48,X0_49,X0_49)
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_544,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_546,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_471,plain,
    ( ~ v3_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | v2_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_972,plain,
    ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_2217,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top
    | v2_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_972])).

cnf(c_2225,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ v1_relat_1(X1_48)
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_964,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_2220,plain,
    ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_2(X0_49,X0_48)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_49,X0_49)) != iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_964])).

cnf(c_2234,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2220])).

cnf(c_3477,plain,
    ( k5_relat_1(k2_funct_2(sK1,sK2),k2_funct_1(k2_funct_2(sK1,sK2))) = k6_partfun1(k1_relat_1(k2_funct_2(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2561,c_26,c_27,c_28,c_29,c_88,c_546,c_552,c_2225,c_2234])).

cnf(c_455,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_988,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_474,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_969,plain,
    ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_1661,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_969])).

cnf(c_529,plain,
    ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_531,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_529])).

cnf(c_538,plain,
    ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_540,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1277,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_964])).

cnf(c_1702,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1661,c_26,c_28,c_29,c_88,c_531,c_540,c_1277])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_477,plain,
    ( ~ v1_funct_1(X0_48)
    | ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_966,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_1707,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_966])).

cnf(c_520,plain,
    ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_522,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_2064,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1707,c_26,c_28,c_29,c_88,c_522,c_540,c_1277])).

cnf(c_3479,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3477,c_1702,c_2064,c_2568])).

cnf(c_6541,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_6533,c_3479])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_462,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_981,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_462])).

cnf(c_3610,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3600,c_981])).

cnf(c_5092,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3610,c_2570])).

cnf(c_5093,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5092])).

cnf(c_5098,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_5093])).

cnf(c_5105,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5098,c_2064])).

cnf(c_5120,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5105,c_26])).

cnf(c_2905,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_981])).

cnf(c_3196,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_26])).

cnf(c_3197,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3196])).

cnf(c_3203,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_973,c_3197])).

cnf(c_4160,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3203,c_550])).

cnf(c_4161,plain,
    ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
    | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4160])).

cnf(c_4166,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_4161])).

cnf(c_1913,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_983])).

cnf(c_1363,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_985,c_970])).

cnf(c_1918,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1913,c_1363])).

cnf(c_2146,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1918,c_26,c_27])).

cnf(c_1799,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_967])).

cnf(c_523,plain,
    ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
    | v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_525,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_2067,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1799,c_26,c_28,c_29,c_88,c_525,c_540,c_1277])).

cnf(c_2148,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2146,c_2067])).

cnf(c_4174,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4166,c_2148,c_2568])).

cnf(c_3609,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3600,c_3197])).

cnf(c_3615,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3609,c_2148])).

cnf(c_4188,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4174,c_2570,c_3615])).

cnf(c_21,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_459,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_984,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_2571,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2568,c_984])).

cnf(c_4190,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4188,c_2571])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_466,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_977,plain,
    ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_472,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_971,plain,
    ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_1808,plain,
    ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
    inference(superposition,[status(thm)],[c_977,c_971])).

cnf(c_1814,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_4290,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4190,c_29,c_1814])).

cnf(c_5122,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5120,c_4290])).

cnf(c_6712,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6541,c_5122])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6712,c_1814,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.01/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.02  
% 3.01/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.02  
% 3.01/1.02  ------  iProver source info
% 3.01/1.02  
% 3.01/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.02  git: non_committed_changes: false
% 3.01/1.02  git: last_make_outside_of_git: false
% 3.01/1.02  
% 3.01/1.02  ------ 
% 3.01/1.02  
% 3.01/1.02  ------ Input Options
% 3.01/1.02  
% 3.01/1.02  --out_options                           all
% 3.01/1.02  --tptp_safe_out                         true
% 3.01/1.02  --problem_path                          ""
% 3.01/1.02  --include_path                          ""
% 3.01/1.02  --clausifier                            res/vclausify_rel
% 3.01/1.02  --clausifier_options                    ""
% 3.01/1.02  --stdin                                 false
% 3.01/1.02  --stats_out                             all
% 3.01/1.02  
% 3.01/1.02  ------ General Options
% 3.01/1.02  
% 3.01/1.02  --fof                                   false
% 3.01/1.02  --time_out_real                         305.
% 3.01/1.02  --time_out_virtual                      -1.
% 3.01/1.02  --symbol_type_check                     false
% 3.01/1.02  --clausify_out                          false
% 3.01/1.02  --sig_cnt_out                           false
% 3.01/1.02  --trig_cnt_out                          false
% 3.01/1.02  --trig_cnt_out_tolerance                1.
% 3.01/1.02  --trig_cnt_out_sk_spl                   false
% 3.01/1.02  --abstr_cl_out                          false
% 3.01/1.02  
% 3.01/1.02  ------ Global Options
% 3.01/1.02  
% 3.01/1.02  --schedule                              default
% 3.01/1.02  --add_important_lit                     false
% 3.01/1.02  --prop_solver_per_cl                    1000
% 3.01/1.02  --min_unsat_core                        false
% 3.01/1.02  --soft_assumptions                      false
% 3.01/1.02  --soft_lemma_size                       3
% 3.01/1.02  --prop_impl_unit_size                   0
% 3.01/1.02  --prop_impl_unit                        []
% 3.01/1.02  --share_sel_clauses                     true
% 3.01/1.02  --reset_solvers                         false
% 3.01/1.02  --bc_imp_inh                            [conj_cone]
% 3.01/1.02  --conj_cone_tolerance                   3.
% 3.01/1.02  --extra_neg_conj                        none
% 3.01/1.02  --large_theory_mode                     true
% 3.01/1.02  --prolific_symb_bound                   200
% 3.01/1.02  --lt_threshold                          2000
% 3.01/1.02  --clause_weak_htbl                      true
% 3.01/1.02  --gc_record_bc_elim                     false
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing Options
% 3.01/1.03  
% 3.01/1.03  --preprocessing_flag                    true
% 3.01/1.03  --time_out_prep_mult                    0.1
% 3.01/1.03  --splitting_mode                        input
% 3.01/1.03  --splitting_grd                         true
% 3.01/1.03  --splitting_cvd                         false
% 3.01/1.03  --splitting_cvd_svl                     false
% 3.01/1.03  --splitting_nvd                         32
% 3.01/1.03  --sub_typing                            true
% 3.01/1.03  --prep_gs_sim                           true
% 3.01/1.03  --prep_unflatten                        true
% 3.01/1.03  --prep_res_sim                          true
% 3.01/1.03  --prep_upred                            true
% 3.01/1.03  --prep_sem_filter                       exhaustive
% 3.01/1.03  --prep_sem_filter_out                   false
% 3.01/1.03  --pred_elim                             true
% 3.01/1.03  --res_sim_input                         true
% 3.01/1.03  --eq_ax_congr_red                       true
% 3.01/1.03  --pure_diseq_elim                       true
% 3.01/1.03  --brand_transform                       false
% 3.01/1.03  --non_eq_to_eq                          false
% 3.01/1.03  --prep_def_merge                        true
% 3.01/1.03  --prep_def_merge_prop_impl              false
% 3.01/1.03  --prep_def_merge_mbd                    true
% 3.01/1.03  --prep_def_merge_tr_red                 false
% 3.01/1.03  --prep_def_merge_tr_cl                  false
% 3.01/1.03  --smt_preprocessing                     true
% 3.01/1.03  --smt_ac_axioms                         fast
% 3.01/1.03  --preprocessed_out                      false
% 3.01/1.03  --preprocessed_stats                    false
% 3.01/1.03  
% 3.01/1.03  ------ Abstraction refinement Options
% 3.01/1.03  
% 3.01/1.03  --abstr_ref                             []
% 3.01/1.03  --abstr_ref_prep                        false
% 3.01/1.03  --abstr_ref_until_sat                   false
% 3.01/1.03  --abstr_ref_sig_restrict                funpre
% 3.01/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.03  --abstr_ref_under                       []
% 3.01/1.03  
% 3.01/1.03  ------ SAT Options
% 3.01/1.03  
% 3.01/1.03  --sat_mode                              false
% 3.01/1.03  --sat_fm_restart_options                ""
% 3.01/1.03  --sat_gr_def                            false
% 3.01/1.03  --sat_epr_types                         true
% 3.01/1.03  --sat_non_cyclic_types                  false
% 3.01/1.03  --sat_finite_models                     false
% 3.01/1.03  --sat_fm_lemmas                         false
% 3.01/1.03  --sat_fm_prep                           false
% 3.01/1.03  --sat_fm_uc_incr                        true
% 3.01/1.03  --sat_out_model                         small
% 3.01/1.03  --sat_out_clauses                       false
% 3.01/1.03  
% 3.01/1.03  ------ QBF Options
% 3.01/1.03  
% 3.01/1.03  --qbf_mode                              false
% 3.01/1.03  --qbf_elim_univ                         false
% 3.01/1.03  --qbf_dom_inst                          none
% 3.01/1.03  --qbf_dom_pre_inst                      false
% 3.01/1.03  --qbf_sk_in                             false
% 3.01/1.03  --qbf_pred_elim                         true
% 3.01/1.03  --qbf_split                             512
% 3.01/1.03  
% 3.01/1.03  ------ BMC1 Options
% 3.01/1.03  
% 3.01/1.03  --bmc1_incremental                      false
% 3.01/1.03  --bmc1_axioms                           reachable_all
% 3.01/1.03  --bmc1_min_bound                        0
% 3.01/1.03  --bmc1_max_bound                        -1
% 3.01/1.03  --bmc1_max_bound_default                -1
% 3.01/1.03  --bmc1_symbol_reachability              true
% 3.01/1.03  --bmc1_property_lemmas                  false
% 3.01/1.03  --bmc1_k_induction                      false
% 3.01/1.03  --bmc1_non_equiv_states                 false
% 3.01/1.03  --bmc1_deadlock                         false
% 3.01/1.03  --bmc1_ucm                              false
% 3.01/1.03  --bmc1_add_unsat_core                   none
% 3.01/1.03  --bmc1_unsat_core_children              false
% 3.01/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.03  --bmc1_out_stat                         full
% 3.01/1.03  --bmc1_ground_init                      false
% 3.01/1.03  --bmc1_pre_inst_next_state              false
% 3.01/1.03  --bmc1_pre_inst_state                   false
% 3.01/1.03  --bmc1_pre_inst_reach_state             false
% 3.01/1.03  --bmc1_out_unsat_core                   false
% 3.01/1.03  --bmc1_aig_witness_out                  false
% 3.01/1.03  --bmc1_verbose                          false
% 3.01/1.03  --bmc1_dump_clauses_tptp                false
% 3.01/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.03  --bmc1_dump_file                        -
% 3.01/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.03  --bmc1_ucm_extend_mode                  1
% 3.01/1.03  --bmc1_ucm_init_mode                    2
% 3.01/1.03  --bmc1_ucm_cone_mode                    none
% 3.01/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.03  --bmc1_ucm_relax_model                  4
% 3.01/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.03  --bmc1_ucm_layered_model                none
% 3.01/1.03  --bmc1_ucm_max_lemma_size               10
% 3.01/1.03  
% 3.01/1.03  ------ AIG Options
% 3.01/1.03  
% 3.01/1.03  --aig_mode                              false
% 3.01/1.03  
% 3.01/1.03  ------ Instantiation Options
% 3.01/1.03  
% 3.01/1.03  --instantiation_flag                    true
% 3.01/1.03  --inst_sos_flag                         true
% 3.01/1.03  --inst_sos_phase                        true
% 3.01/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.03  --inst_lit_sel_side                     num_symb
% 3.01/1.03  --inst_solver_per_active                1400
% 3.01/1.03  --inst_solver_calls_frac                1.
% 3.01/1.03  --inst_passive_queue_type               priority_queues
% 3.01/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.03  --inst_passive_queues_freq              [25;2]
% 3.01/1.03  --inst_dismatching                      true
% 3.01/1.03  --inst_eager_unprocessed_to_passive     true
% 3.01/1.03  --inst_prop_sim_given                   true
% 3.01/1.03  --inst_prop_sim_new                     false
% 3.01/1.03  --inst_subs_new                         false
% 3.01/1.03  --inst_eq_res_simp                      false
% 3.01/1.03  --inst_subs_given                       false
% 3.01/1.03  --inst_orphan_elimination               true
% 3.01/1.03  --inst_learning_loop_flag               true
% 3.01/1.03  --inst_learning_start                   3000
% 3.01/1.03  --inst_learning_factor                  2
% 3.01/1.03  --inst_start_prop_sim_after_learn       3
% 3.01/1.03  --inst_sel_renew                        solver
% 3.01/1.03  --inst_lit_activity_flag                true
% 3.01/1.03  --inst_restr_to_given                   false
% 3.01/1.03  --inst_activity_threshold               500
% 3.01/1.03  --inst_out_proof                        true
% 3.01/1.03  
% 3.01/1.03  ------ Resolution Options
% 3.01/1.03  
% 3.01/1.03  --resolution_flag                       true
% 3.01/1.03  --res_lit_sel                           adaptive
% 3.01/1.03  --res_lit_sel_side                      none
% 3.01/1.03  --res_ordering                          kbo
% 3.01/1.03  --res_to_prop_solver                    active
% 3.01/1.03  --res_prop_simpl_new                    false
% 3.01/1.03  --res_prop_simpl_given                  true
% 3.01/1.03  --res_passive_queue_type                priority_queues
% 3.01/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.03  --res_passive_queues_freq               [15;5]
% 3.01/1.03  --res_forward_subs                      full
% 3.01/1.03  --res_backward_subs                     full
% 3.01/1.03  --res_forward_subs_resolution           true
% 3.01/1.03  --res_backward_subs_resolution          true
% 3.01/1.03  --res_orphan_elimination                true
% 3.01/1.03  --res_time_limit                        2.
% 3.01/1.03  --res_out_proof                         true
% 3.01/1.03  
% 3.01/1.03  ------ Superposition Options
% 3.01/1.03  
% 3.01/1.03  --superposition_flag                    true
% 3.01/1.03  --sup_passive_queue_type                priority_queues
% 3.01/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.03  --demod_completeness_check              fast
% 3.01/1.03  --demod_use_ground                      true
% 3.01/1.03  --sup_to_prop_solver                    passive
% 3.01/1.03  --sup_prop_simpl_new                    true
% 3.01/1.03  --sup_prop_simpl_given                  true
% 3.01/1.03  --sup_fun_splitting                     true
% 3.01/1.03  --sup_smt_interval                      50000
% 3.01/1.03  
% 3.01/1.03  ------ Superposition Simplification Setup
% 3.01/1.03  
% 3.01/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.01/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.01/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.01/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.01/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.01/1.03  --sup_immed_triv                        [TrivRules]
% 3.01/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.03  --sup_immed_bw_main                     []
% 3.01/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.01/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.03  --sup_input_bw                          []
% 3.01/1.03  
% 3.01/1.03  ------ Combination Options
% 3.01/1.03  
% 3.01/1.03  --comb_res_mult                         3
% 3.01/1.03  --comb_sup_mult                         2
% 3.01/1.03  --comb_inst_mult                        10
% 3.01/1.03  
% 3.01/1.03  ------ Debug Options
% 3.01/1.03  
% 3.01/1.03  --dbg_backtrace                         false
% 3.01/1.03  --dbg_dump_prop_clauses                 false
% 3.01/1.03  --dbg_dump_prop_clauses_file            -
% 3.01/1.03  --dbg_out_stat                          false
% 3.01/1.03  ------ Parsing...
% 3.01/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.03  
% 3.01/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.01/1.03  
% 3.01/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.03  
% 3.01/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.03  ------ Proving...
% 3.01/1.03  ------ Problem Properties 
% 3.01/1.03  
% 3.01/1.03  
% 3.01/1.03  clauses                                 25
% 3.01/1.03  conjectures                             5
% 3.01/1.03  EPR                                     3
% 3.01/1.03  Horn                                    25
% 3.01/1.03  unary                                   9
% 3.01/1.03  binary                                  2
% 3.01/1.03  lits                                    73
% 3.01/1.03  lits eq                                 7
% 3.01/1.03  fd_pure                                 0
% 3.01/1.03  fd_pseudo                               0
% 3.01/1.03  fd_cond                                 0
% 3.01/1.03  fd_pseudo_cond                          0
% 3.01/1.03  AC symbols                              0
% 3.01/1.03  
% 3.01/1.03  ------ Schedule dynamic 5 is on 
% 3.01/1.03  
% 3.01/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.03  
% 3.01/1.03  
% 3.01/1.03  ------ 
% 3.01/1.03  Current options:
% 3.01/1.03  ------ 
% 3.01/1.03  
% 3.01/1.03  ------ Input Options
% 3.01/1.03  
% 3.01/1.03  --out_options                           all
% 3.01/1.03  --tptp_safe_out                         true
% 3.01/1.03  --problem_path                          ""
% 3.01/1.03  --include_path                          ""
% 3.01/1.03  --clausifier                            res/vclausify_rel
% 3.01/1.03  --clausifier_options                    ""
% 3.01/1.03  --stdin                                 false
% 3.01/1.03  --stats_out                             all
% 3.01/1.03  
% 3.01/1.03  ------ General Options
% 3.01/1.03  
% 3.01/1.03  --fof                                   false
% 3.01/1.03  --time_out_real                         305.
% 3.01/1.03  --time_out_virtual                      -1.
% 3.01/1.03  --symbol_type_check                     false
% 3.01/1.03  --clausify_out                          false
% 3.01/1.03  --sig_cnt_out                           false
% 3.01/1.03  --trig_cnt_out                          false
% 3.01/1.03  --trig_cnt_out_tolerance                1.
% 3.01/1.03  --trig_cnt_out_sk_spl                   false
% 3.01/1.03  --abstr_cl_out                          false
% 3.01/1.03  
% 3.01/1.03  ------ Global Options
% 3.01/1.03  
% 3.01/1.03  --schedule                              default
% 3.01/1.03  --add_important_lit                     false
% 3.01/1.03  --prop_solver_per_cl                    1000
% 3.01/1.03  --min_unsat_core                        false
% 3.01/1.03  --soft_assumptions                      false
% 3.01/1.03  --soft_lemma_size                       3
% 3.01/1.03  --prop_impl_unit_size                   0
% 3.01/1.03  --prop_impl_unit                        []
% 3.01/1.03  --share_sel_clauses                     true
% 3.01/1.03  --reset_solvers                         false
% 3.01/1.03  --bc_imp_inh                            [conj_cone]
% 3.01/1.03  --conj_cone_tolerance                   3.
% 3.01/1.03  --extra_neg_conj                        none
% 3.01/1.03  --large_theory_mode                     true
% 3.01/1.03  --prolific_symb_bound                   200
% 3.01/1.03  --lt_threshold                          2000
% 3.01/1.03  --clause_weak_htbl                      true
% 3.01/1.03  --gc_record_bc_elim                     false
% 3.01/1.03  
% 3.01/1.03  ------ Preprocessing Options
% 3.01/1.03  
% 3.01/1.03  --preprocessing_flag                    true
% 3.01/1.03  --time_out_prep_mult                    0.1
% 3.01/1.03  --splitting_mode                        input
% 3.01/1.03  --splitting_grd                         true
% 3.01/1.03  --splitting_cvd                         false
% 3.01/1.03  --splitting_cvd_svl                     false
% 3.01/1.03  --splitting_nvd                         32
% 3.01/1.03  --sub_typing                            true
% 3.01/1.03  --prep_gs_sim                           true
% 3.01/1.03  --prep_unflatten                        true
% 3.01/1.03  --prep_res_sim                          true
% 3.01/1.03  --prep_upred                            true
% 3.01/1.03  --prep_sem_filter                       exhaustive
% 3.01/1.03  --prep_sem_filter_out                   false
% 3.01/1.03  --pred_elim                             true
% 3.01/1.03  --res_sim_input                         true
% 3.01/1.03  --eq_ax_congr_red                       true
% 3.01/1.03  --pure_diseq_elim                       true
% 3.01/1.03  --brand_transform                       false
% 3.01/1.03  --non_eq_to_eq                          false
% 3.01/1.03  --prep_def_merge                        true
% 3.01/1.03  --prep_def_merge_prop_impl              false
% 3.01/1.03  --prep_def_merge_mbd                    true
% 3.01/1.03  --prep_def_merge_tr_red                 false
% 3.01/1.03  --prep_def_merge_tr_cl                  false
% 3.01/1.03  --smt_preprocessing                     true
% 3.01/1.03  --smt_ac_axioms                         fast
% 3.01/1.03  --preprocessed_out                      false
% 3.01/1.03  --preprocessed_stats                    false
% 3.01/1.03  
% 3.01/1.03  ------ Abstraction refinement Options
% 3.01/1.03  
% 3.01/1.03  --abstr_ref                             []
% 3.01/1.03  --abstr_ref_prep                        false
% 3.01/1.03  --abstr_ref_until_sat                   false
% 3.01/1.03  --abstr_ref_sig_restrict                funpre
% 3.01/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.03  --abstr_ref_under                       []
% 3.01/1.03  
% 3.01/1.03  ------ SAT Options
% 3.01/1.03  
% 3.01/1.03  --sat_mode                              false
% 3.01/1.03  --sat_fm_restart_options                ""
% 3.01/1.03  --sat_gr_def                            false
% 3.01/1.03  --sat_epr_types                         true
% 3.01/1.03  --sat_non_cyclic_types                  false
% 3.01/1.03  --sat_finite_models                     false
% 3.01/1.03  --sat_fm_lemmas                         false
% 3.01/1.03  --sat_fm_prep                           false
% 3.01/1.03  --sat_fm_uc_incr                        true
% 3.01/1.03  --sat_out_model                         small
% 3.01/1.03  --sat_out_clauses                       false
% 3.01/1.03  
% 3.01/1.03  ------ QBF Options
% 3.01/1.03  
% 3.01/1.03  --qbf_mode                              false
% 3.01/1.03  --qbf_elim_univ                         false
% 3.01/1.03  --qbf_dom_inst                          none
% 3.01/1.03  --qbf_dom_pre_inst                      false
% 3.01/1.03  --qbf_sk_in                             false
% 3.01/1.03  --qbf_pred_elim                         true
% 3.01/1.03  --qbf_split                             512
% 3.01/1.03  
% 3.01/1.03  ------ BMC1 Options
% 3.01/1.03  
% 3.01/1.03  --bmc1_incremental                      false
% 3.01/1.03  --bmc1_axioms                           reachable_all
% 3.01/1.03  --bmc1_min_bound                        0
% 3.01/1.03  --bmc1_max_bound                        -1
% 3.01/1.03  --bmc1_max_bound_default                -1
% 3.01/1.03  --bmc1_symbol_reachability              true
% 3.01/1.03  --bmc1_property_lemmas                  false
% 3.01/1.03  --bmc1_k_induction                      false
% 3.01/1.03  --bmc1_non_equiv_states                 false
% 3.01/1.03  --bmc1_deadlock                         false
% 3.01/1.03  --bmc1_ucm                              false
% 3.01/1.03  --bmc1_add_unsat_core                   none
% 3.01/1.03  --bmc1_unsat_core_children              false
% 3.01/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.03  --bmc1_out_stat                         full
% 3.01/1.03  --bmc1_ground_init                      false
% 3.01/1.03  --bmc1_pre_inst_next_state              false
% 3.01/1.03  --bmc1_pre_inst_state                   false
% 3.01/1.03  --bmc1_pre_inst_reach_state             false
% 3.01/1.03  --bmc1_out_unsat_core                   false
% 3.01/1.03  --bmc1_aig_witness_out                  false
% 3.01/1.03  --bmc1_verbose                          false
% 3.01/1.03  --bmc1_dump_clauses_tptp                false
% 3.01/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.03  --bmc1_dump_file                        -
% 3.01/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.03  --bmc1_ucm_extend_mode                  1
% 3.01/1.03  --bmc1_ucm_init_mode                    2
% 3.01/1.03  --bmc1_ucm_cone_mode                    none
% 3.01/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.03  --bmc1_ucm_relax_model                  4
% 3.01/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.03  --bmc1_ucm_layered_model                none
% 3.01/1.03  --bmc1_ucm_max_lemma_size               10
% 3.01/1.03  
% 3.01/1.03  ------ AIG Options
% 3.01/1.03  
% 3.01/1.03  --aig_mode                              false
% 3.01/1.03  
% 3.01/1.03  ------ Instantiation Options
% 3.01/1.03  
% 3.01/1.03  --instantiation_flag                    true
% 3.01/1.03  --inst_sos_flag                         true
% 3.01/1.03  --inst_sos_phase                        true
% 3.01/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.03  --inst_lit_sel_side                     none
% 3.01/1.03  --inst_solver_per_active                1400
% 3.01/1.03  --inst_solver_calls_frac                1.
% 3.01/1.03  --inst_passive_queue_type               priority_queues
% 3.01/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.03  --inst_passive_queues_freq              [25;2]
% 3.01/1.03  --inst_dismatching                      true
% 3.01/1.03  --inst_eager_unprocessed_to_passive     true
% 3.01/1.03  --inst_prop_sim_given                   true
% 3.01/1.03  --inst_prop_sim_new                     false
% 3.01/1.03  --inst_subs_new                         false
% 3.01/1.03  --inst_eq_res_simp                      false
% 3.01/1.03  --inst_subs_given                       false
% 3.01/1.03  --inst_orphan_elimination               true
% 3.01/1.03  --inst_learning_loop_flag               true
% 3.01/1.03  --inst_learning_start                   3000
% 3.01/1.03  --inst_learning_factor                  2
% 3.01/1.03  --inst_start_prop_sim_after_learn       3
% 3.01/1.03  --inst_sel_renew                        solver
% 3.01/1.03  --inst_lit_activity_flag                true
% 3.01/1.03  --inst_restr_to_given                   false
% 3.01/1.03  --inst_activity_threshold               500
% 3.01/1.03  --inst_out_proof                        true
% 3.01/1.03  
% 3.01/1.03  ------ Resolution Options
% 3.01/1.03  
% 3.01/1.03  --resolution_flag                       false
% 3.01/1.03  --res_lit_sel                           adaptive
% 3.01/1.03  --res_lit_sel_side                      none
% 3.01/1.03  --res_ordering                          kbo
% 3.01/1.03  --res_to_prop_solver                    active
% 3.01/1.03  --res_prop_simpl_new                    false
% 3.01/1.03  --res_prop_simpl_given                  true
% 3.01/1.03  --res_passive_queue_type                priority_queues
% 3.01/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.03  --res_passive_queues_freq               [15;5]
% 3.01/1.03  --res_forward_subs                      full
% 3.01/1.03  --res_backward_subs                     full
% 3.01/1.03  --res_forward_subs_resolution           true
% 3.01/1.03  --res_backward_subs_resolution          true
% 3.01/1.03  --res_orphan_elimination                true
% 3.01/1.03  --res_time_limit                        2.
% 3.01/1.03  --res_out_proof                         true
% 3.01/1.03  
% 3.01/1.03  ------ Superposition Options
% 3.01/1.03  
% 3.01/1.03  --superposition_flag                    true
% 3.01/1.03  --sup_passive_queue_type                priority_queues
% 3.01/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.03  --demod_completeness_check              fast
% 3.01/1.03  --demod_use_ground                      true
% 3.01/1.03  --sup_to_prop_solver                    passive
% 3.01/1.03  --sup_prop_simpl_new                    true
% 3.01/1.03  --sup_prop_simpl_given                  true
% 3.01/1.03  --sup_fun_splitting                     true
% 3.01/1.03  --sup_smt_interval                      50000
% 3.01/1.03  
% 3.01/1.03  ------ Superposition Simplification Setup
% 3.01/1.03  
% 3.01/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.01/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.01/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.01/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.01/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.01/1.03  --sup_immed_triv                        [TrivRules]
% 3.01/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.03  --sup_immed_bw_main                     []
% 3.01/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.01/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.03  --sup_input_bw                          []
% 3.01/1.03  
% 3.01/1.03  ------ Combination Options
% 3.01/1.03  
% 3.01/1.03  --comb_res_mult                         3
% 3.01/1.03  --comb_sup_mult                         2
% 3.01/1.03  --comb_inst_mult                        10
% 3.01/1.03  
% 3.01/1.03  ------ Debug Options
% 3.01/1.03  
% 3.01/1.03  --dbg_backtrace                         false
% 3.01/1.03  --dbg_dump_prop_clauses                 false
% 3.01/1.03  --dbg_dump_prop_clauses_file            -
% 3.01/1.03  --dbg_out_stat                          false
% 3.01/1.03  
% 3.01/1.03  
% 3.01/1.03  
% 3.01/1.03  
% 3.01/1.03  ------ Proving...
% 3.01/1.03  
% 3.01/1.03  
% 3.01/1.03  % SZS status Theorem for theBenchmark.p
% 3.01/1.03  
% 3.01/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.03  
% 3.01/1.03  fof(f16,conjecture,(
% 3.01/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f17,negated_conjecture,(
% 3.01/1.03    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.01/1.03    inference(negated_conjecture,[],[f16])).
% 3.01/1.03  
% 3.01/1.03  fof(f42,plain,(
% 3.01/1.03    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.01/1.03    inference(ennf_transformation,[],[f17])).
% 3.01/1.03  
% 3.01/1.03  fof(f43,plain,(
% 3.01/1.03    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.01/1.03    inference(flattening,[],[f42])).
% 3.01/1.03  
% 3.01/1.03  fof(f46,plain,(
% 3.01/1.03    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.01/1.03    introduced(choice_axiom,[])).
% 3.01/1.03  
% 3.01/1.03  fof(f47,plain,(
% 3.01/1.03    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.01/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f43,f46])).
% 3.01/1.03  
% 3.01/1.03  fof(f73,plain,(
% 3.01/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.01/1.03    inference(cnf_transformation,[],[f47])).
% 3.01/1.03  
% 3.01/1.03  fof(f13,axiom,(
% 3.01/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f38,plain,(
% 3.01/1.03    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.01/1.03    inference(ennf_transformation,[],[f13])).
% 3.01/1.03  
% 3.01/1.03  fof(f39,plain,(
% 3.01/1.03    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.01/1.03    inference(flattening,[],[f38])).
% 3.01/1.03  
% 3.01/1.03  fof(f67,plain,(
% 3.01/1.03    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f39])).
% 3.01/1.03  
% 3.01/1.03  fof(f70,plain,(
% 3.01/1.03    v1_funct_1(sK2)),
% 3.01/1.03    inference(cnf_transformation,[],[f47])).
% 3.01/1.03  
% 3.01/1.03  fof(f71,plain,(
% 3.01/1.03    v1_funct_2(sK2,sK1,sK1)),
% 3.01/1.03    inference(cnf_transformation,[],[f47])).
% 3.01/1.03  
% 3.01/1.03  fof(f72,plain,(
% 3.01/1.03    v3_funct_2(sK2,sK1,sK1)),
% 3.01/1.03    inference(cnf_transformation,[],[f47])).
% 3.01/1.03  
% 3.01/1.03  fof(f9,axiom,(
% 3.01/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f34,plain,(
% 3.01/1.03    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.01/1.03    inference(ennf_transformation,[],[f9])).
% 3.01/1.03  
% 3.01/1.03  fof(f35,plain,(
% 3.01/1.03    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.01/1.03    inference(flattening,[],[f34])).
% 3.01/1.03  
% 3.01/1.03  fof(f61,plain,(
% 3.01/1.03    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f35])).
% 3.01/1.03  
% 3.01/1.03  fof(f15,axiom,(
% 3.01/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f40,plain,(
% 3.01/1.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.01/1.03    inference(ennf_transformation,[],[f15])).
% 3.01/1.03  
% 3.01/1.03  fof(f41,plain,(
% 3.01/1.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.01/1.03    inference(flattening,[],[f40])).
% 3.01/1.03  
% 3.01/1.03  fof(f69,plain,(
% 3.01/1.03    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f41])).
% 3.01/1.03  
% 3.01/1.03  fof(f6,axiom,(
% 3.01/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f29,plain,(
% 3.01/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.03    inference(ennf_transformation,[],[f6])).
% 3.01/1.03  
% 3.01/1.03  fof(f54,plain,(
% 3.01/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.03    inference(cnf_transformation,[],[f29])).
% 3.01/1.03  
% 3.01/1.03  fof(f58,plain,(
% 3.01/1.03    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f35])).
% 3.01/1.03  
% 3.01/1.03  fof(f59,plain,(
% 3.01/1.03    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f35])).
% 3.01/1.03  
% 3.01/1.03  fof(f3,axiom,(
% 3.01/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f23,plain,(
% 3.01/1.03    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.03    inference(ennf_transformation,[],[f3])).
% 3.01/1.03  
% 3.01/1.03  fof(f24,plain,(
% 3.01/1.03    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.03    inference(flattening,[],[f23])).
% 3.01/1.03  
% 3.01/1.03  fof(f50,plain,(
% 3.01/1.03    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f24])).
% 3.01/1.03  
% 3.01/1.03  fof(f14,axiom,(
% 3.01/1.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f68,plain,(
% 3.01/1.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f14])).
% 3.01/1.03  
% 3.01/1.03  fof(f76,plain,(
% 3.01/1.03    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.03    inference(definition_unfolding,[],[f50,f68])).
% 3.01/1.03  
% 3.01/1.03  fof(f2,axiom,(
% 3.01/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f49,plain,(
% 3.01/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.01/1.03    inference(cnf_transformation,[],[f2])).
% 3.01/1.03  
% 3.01/1.03  fof(f60,plain,(
% 3.01/1.03    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f35])).
% 3.01/1.03  
% 3.01/1.03  fof(f8,axiom,(
% 3.01/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f21,plain,(
% 3.01/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.01/1.03    inference(pure_predicate_removal,[],[f8])).
% 3.01/1.03  
% 3.01/1.03  fof(f32,plain,(
% 3.01/1.03    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.03    inference(ennf_transformation,[],[f21])).
% 3.01/1.03  
% 3.01/1.03  fof(f33,plain,(
% 3.01/1.03    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.03    inference(flattening,[],[f32])).
% 3.01/1.03  
% 3.01/1.03  fof(f57,plain,(
% 3.01/1.03    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.03    inference(cnf_transformation,[],[f33])).
% 3.01/1.03  
% 3.01/1.03  fof(f1,axiom,(
% 3.01/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f22,plain,(
% 3.01/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.01/1.03    inference(ennf_transformation,[],[f1])).
% 3.01/1.03  
% 3.01/1.03  fof(f48,plain,(
% 3.01/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f22])).
% 3.01/1.03  
% 3.01/1.03  fof(f5,axiom,(
% 3.01/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f27,plain,(
% 3.01/1.03    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.03    inference(ennf_transformation,[],[f5])).
% 3.01/1.03  
% 3.01/1.03  fof(f28,plain,(
% 3.01/1.03    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.03    inference(flattening,[],[f27])).
% 3.01/1.03  
% 3.01/1.03  fof(f53,plain,(
% 3.01/1.03    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f28])).
% 3.01/1.03  
% 3.01/1.03  fof(f51,plain,(
% 3.01/1.03    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f24])).
% 3.01/1.03  
% 3.01/1.03  fof(f75,plain,(
% 3.01/1.03    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.03    inference(definition_unfolding,[],[f51,f68])).
% 3.01/1.03  
% 3.01/1.03  fof(f12,axiom,(
% 3.01/1.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f36,plain,(
% 3.01/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.01/1.03    inference(ennf_transformation,[],[f12])).
% 3.01/1.03  
% 3.01/1.03  fof(f37,plain,(
% 3.01/1.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.01/1.03    inference(flattening,[],[f36])).
% 3.01/1.03  
% 3.01/1.03  fof(f66,plain,(
% 3.01/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.01/1.03    inference(cnf_transformation,[],[f37])).
% 3.01/1.03  
% 3.01/1.03  fof(f74,plain,(
% 3.01/1.03    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.01/1.03    inference(cnf_transformation,[],[f47])).
% 3.01/1.03  
% 3.01/1.03  fof(f10,axiom,(
% 3.01/1.03    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f20,plain,(
% 3.01/1.03    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.01/1.03    inference(pure_predicate_removal,[],[f10])).
% 3.01/1.03  
% 3.01/1.03  fof(f62,plain,(
% 3.01/1.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.01/1.03    inference(cnf_transformation,[],[f20])).
% 3.01/1.03  
% 3.01/1.03  fof(f7,axiom,(
% 3.01/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/1.03  
% 3.01/1.03  fof(f30,plain,(
% 3.01/1.03    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.01/1.03    inference(ennf_transformation,[],[f7])).
% 3.01/1.03  
% 3.01/1.03  fof(f31,plain,(
% 3.01/1.03    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.03    inference(flattening,[],[f30])).
% 3.01/1.03  
% 3.01/1.03  fof(f55,plain,(
% 3.01/1.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.03    inference(cnf_transformation,[],[f31])).
% 3.01/1.03  
% 3.01/1.03  cnf(c_22,negated_conjecture,
% 3.01/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.01/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_458,negated_conjecture,
% 3.01/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_22]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_985,plain,
% 3.01/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_19,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ v3_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.01/1.03      | ~ v1_funct_1(X0)
% 3.01/1.03      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.01/1.03      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_461,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.01/1.03      | ~ v1_funct_1(X0_48)
% 3.01/1.03      | k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_19]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_982,plain,
% 3.01/1.03      ( k2_funct_2(X0_49,X0_48) = k2_funct_1(X0_48)
% 3.01/1.03      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2321,plain,
% 3.01/1.03      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.01/1.03      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_982]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_25,negated_conjecture,
% 3.01/1.03      ( v1_funct_1(sK2) ),
% 3.01/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_24,negated_conjecture,
% 3.01/1.03      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.01/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_23,negated_conjecture,
% 3.01/1.03      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.01/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_561,plain,
% 3.01/1.03      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.01/1.03      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.01/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.01/1.03      | ~ v1_funct_1(sK2)
% 3.01/1.03      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_461]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2568,plain,
% 3.01/1.03      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_2321,c_25,c_24,c_23,c_22,c_561]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_10,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ v3_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.01/1.03      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.01/1.03      | ~ v1_funct_1(X0) ),
% 3.01/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_470,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.01/1.03      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.01/1.03      | ~ v1_funct_1(X0_48) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_973,plain,
% 3.01/1.03      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | m1_subset_1(k2_funct_2(X0_49,X0_48),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2574,plain,
% 3.01/1.03      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.01/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_2568,c_973]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_26,plain,
% 3.01/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_27,plain,
% 3.01/1.03      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_28,plain,
% 3.01/1.03      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_29,plain,
% 3.01/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3600,plain,
% 3.01/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_2574,c_26,c_27,c_28,c_29]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_20,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.01/1.03      | ~ v1_funct_1(X0)
% 3.01/1.03      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.01/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_460,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.01/1.03      | ~ v1_funct_1(X0_48)
% 3.01/1.03      | k1_relset_1(X0_49,X0_49,X0_48) = X0_49 ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_983,plain,
% 3.01/1.03      ( k1_relset_1(X0_49,X0_49,X0_48) = X0_49
% 3.01/1.03      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3608,plain,
% 3.01/1.03      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
% 3.01/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_3600,c_983]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_6,plain,
% 3.01/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.01/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_473,plain,
% 3.01/1.03      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.01/1.03      | k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_970,plain,
% 3.01/1.03      ( k1_relset_1(X0_49,X1_49,X0_48) = k1_relat_1(X0_48)
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3613,plain,
% 3.01/1.03      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_3600,c_970]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3616,plain,
% 3.01/1.03      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.01/1.03      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_3608,c_3613]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_13,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ v3_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.01/1.03      | ~ v1_funct_1(X0)
% 3.01/1.03      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.01/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_467,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.01/1.03      | ~ v1_funct_1(X0_48)
% 3.01/1.03      | v1_funct_1(k2_funct_2(X0_49,X0_48)) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_13]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_976,plain,
% 3.01/1.03      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2306,plain,
% 3.01/1.03      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_976]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_550,plain,
% 3.01/1.03      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_552,plain,
% 3.01/1.03      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_550]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2557,plain,
% 3.01/1.03      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_2306,c_26,c_27,c_28,c_29,c_552]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2570,plain,
% 3.01/1.03      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_2568,c_2557]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_12,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 3.01/1.03      | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.01/1.03      | ~ v3_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.01/1.03      | ~ v1_funct_1(X0) ),
% 3.01/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_468,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.01/1.03      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.01/1.03      | ~ v1_funct_1(X0_48) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_975,plain,
% 3.01/1.03      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2384,plain,
% 3.01/1.03      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.01/1.03      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_975]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_547,plain,
% 3.01/1.03      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v1_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_549,plain,
% 3.01/1.03      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.01/1.03      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_547]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2702,plain,
% 3.01/1.03      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_2384,c_26,c_27,c_28,c_29,c_549]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2706,plain,
% 3.01/1.03      ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
% 3.01/1.03      inference(light_normalisation,[status(thm)],[c_2702,c_2568]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_6533,plain,
% 3.01/1.03      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_3616,c_2570,c_2706]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3,plain,
% 3.01/1.03      ( ~ v1_funct_1(X0)
% 3.01/1.03      | ~ v2_funct_1(X0)
% 3.01/1.03      | ~ v1_relat_1(X0)
% 3.01/1.03      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.01/1.03      inference(cnf_transformation,[],[f76]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_476,plain,
% 3.01/1.03      ( ~ v1_funct_1(X0_48)
% 3.01/1.03      | ~ v2_funct_1(X0_48)
% 3.01/1.03      | ~ v1_relat_1(X0_48)
% 3.01/1.03      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48)) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_967,plain,
% 3.01/1.03      ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v2_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_relat_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2561,plain,
% 3.01/1.03      ( k5_relat_1(k2_funct_2(sK1,sK2),k2_funct_1(k2_funct_2(sK1,sK2))) = k6_partfun1(k1_relat_1(k2_funct_2(sK1,sK2)))
% 3.01/1.03      | v2_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
% 3.01/1.03      | v1_relat_1(k2_funct_2(sK1,sK2)) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_2557,c_967]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1,plain,
% 3.01/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_86,plain,
% 3.01/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_88,plain,
% 3.01/1.03      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) = iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_86]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_11,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0,X1,X1)
% 3.01/1.03      | ~ v3_funct_2(X0,X1,X1)
% 3.01/1.03      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.01/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.01/1.03      | ~ v1_funct_1(X0) ),
% 3.01/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_469,plain,
% 3.01/1.03      ( ~ v1_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | ~ v3_funct_2(X0_48,X0_49,X0_49)
% 3.01/1.03      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49)
% 3.01/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49)))
% 3.01/1.03      | ~ v1_funct_1(X0_48) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_544,plain,
% 3.01/1.03      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) = iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_546,plain,
% 3.01/1.03      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_544]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_8,plain,
% 3.01/1.03      ( ~ v3_funct_2(X0,X1,X2)
% 3.01/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.03      | ~ v1_funct_1(X0)
% 3.01/1.03      | v2_funct_1(X0) ),
% 3.01/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_471,plain,
% 3.01/1.03      ( ~ v3_funct_2(X0_48,X0_49,X1_49)
% 3.01/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.01/1.03      | ~ v1_funct_1(X0_48)
% 3.01/1.03      | v2_funct_1(X0_48) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_972,plain,
% 3.01/1.03      ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v2_funct_1(X0_48) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2217,plain,
% 3.01/1.03      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(k2_funct_2(X0_49,X0_48),X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top
% 3.01/1.03      | v2_funct_1(k2_funct_2(X0_49,X0_48)) = iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_973,c_972]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2225,plain,
% 3.01/1.03      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_2(sK1,sK2)) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top
% 3.01/1.03      | v2_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_2217]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_0,plain,
% 3.01/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.01/1.03      | ~ v1_relat_1(X1)
% 3.01/1.03      | v1_relat_1(X0) ),
% 3.01/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_479,plain,
% 3.01/1.03      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
% 3.01/1.03      | ~ v1_relat_1(X1_48)
% 3.01/1.03      | v1_relat_1(X0_48) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_964,plain,
% 3.01/1.03      ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
% 3.01/1.03      | v1_relat_1(X1_48) != iProver_top
% 3.01/1.03      | v1_relat_1(X0_48) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2220,plain,
% 3.01/1.03      ( v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_relat_1(k2_funct_2(X0_49,X0_48)) = iProver_top
% 3.01/1.03      | v1_relat_1(k2_zfmisc_1(X0_49,X0_49)) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_973,c_964]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2234,plain,
% 3.01/1.03      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top
% 3.01/1.03      | v1_relat_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.01/1.03      | v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_2220]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3477,plain,
% 3.01/1.03      ( k5_relat_1(k2_funct_2(sK1,sK2),k2_funct_1(k2_funct_2(sK1,sK2))) = k6_partfun1(k1_relat_1(k2_funct_2(sK1,sK2))) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_2561,c_26,c_27,c_28,c_29,c_88,c_546,c_552,c_2225,
% 3.01/1.03                 c_2234]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_455,negated_conjecture,
% 3.01/1.03      ( v1_funct_1(sK2) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_25]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_988,plain,
% 3.01/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_5,plain,
% 3.01/1.03      ( ~ v1_funct_1(X0)
% 3.01/1.03      | ~ v2_funct_1(X0)
% 3.01/1.03      | ~ v1_relat_1(X0)
% 3.01/1.03      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.01/1.03      inference(cnf_transformation,[],[f53]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_474,plain,
% 3.01/1.03      ( ~ v1_funct_1(X0_48)
% 3.01/1.03      | ~ v2_funct_1(X0_48)
% 3.01/1.03      | ~ v1_relat_1(X0_48)
% 3.01/1.03      | k2_funct_1(k2_funct_1(X0_48)) = X0_48 ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_969,plain,
% 3.01/1.03      ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v2_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_relat_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1661,plain,
% 3.01/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.01/1.03      | v2_funct_1(sK2) != iProver_top
% 3.01/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_988,c_969]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_529,plain,
% 3.01/1.03      ( k2_funct_1(k2_funct_1(X0_48)) = X0_48
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v2_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_relat_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_531,plain,
% 3.01/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top
% 3.01/1.03      | v2_funct_1(sK2) != iProver_top
% 3.01/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_529]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_538,plain,
% 3.01/1.03      ( v3_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v2_funct_1(X0_48) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_540,plain,
% 3.01/1.03      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top
% 3.01/1.03      | v2_funct_1(sK2) = iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_538]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1277,plain,
% 3.01/1.03      ( v1_relat_1(k2_zfmisc_1(sK1,sK1)) != iProver_top
% 3.01/1.03      | v1_relat_1(sK2) = iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_964]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1702,plain,
% 3.01/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_1661,c_26,c_28,c_29,c_88,c_531,c_540,c_1277]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2,plain,
% 3.01/1.03      ( ~ v1_funct_1(X0)
% 3.01/1.03      | ~ v2_funct_1(X0)
% 3.01/1.03      | ~ v1_relat_1(X0)
% 3.01/1.03      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.01/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_477,plain,
% 3.01/1.03      ( ~ v1_funct_1(X0_48)
% 3.01/1.03      | ~ v2_funct_1(X0_48)
% 3.01/1.03      | ~ v1_relat_1(X0_48)
% 3.01/1.03      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48)) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_966,plain,
% 3.01/1.03      ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v2_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_relat_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1707,plain,
% 3.01/1.03      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.01/1.03      | v2_funct_1(sK2) != iProver_top
% 3.01/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_988,c_966]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_520,plain,
% 3.01/1.03      ( k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(k2_relat_1(X0_48))
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v2_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_relat_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_522,plain,
% 3.01/1.03      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top
% 3.01/1.03      | v2_funct_1(sK2) != iProver_top
% 3.01/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_520]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2064,plain,
% 3.01/1.03      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_1707,c_26,c_28,c_29,c_88,c_522,c_540,c_1277]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3479,plain,
% 3.01/1.03      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.01/1.03      inference(light_normalisation,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_3477,c_1702,c_2064,c_2568]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_6541,plain,
% 3.01/1.03      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_6533,c_3479]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_18,plain,
% 3.01/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.01/1.03      | ~ v1_funct_1(X0)
% 3.01/1.03      | ~ v1_funct_1(X3)
% 3.01/1.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.01/1.03      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_462,plain,
% 3.01/1.03      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.01/1.03      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 3.01/1.03      | ~ v1_funct_1(X0_48)
% 3.01/1.03      | ~ v1_funct_1(X1_48)
% 3.01/1.03      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_18]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_981,plain,
% 3.01/1.03      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 3.01/1.03      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_funct_1(X1_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_462]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3610,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_3600,c_981]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_5092,plain,
% 3.01/1.03      ( v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_3610,c_2570]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_5093,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,X0_49,X1_49,k2_funct_1(sK2),X0_48) = k5_relat_1(k2_funct_1(sK2),X0_48)
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(renaming,[status(thm)],[c_5092]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_5098,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_5093]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_5105,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(light_normalisation,[status(thm)],[c_5098,c_2064]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_5120,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_5105,c_26]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2905,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_981]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3196,plain,
% 3.01/1.03      ( v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_2905,c_26]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3197,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,X0_49,X1_49,sK2,X0_48) = k5_relat_1(sK2,X0_48)
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(renaming,[status(thm)],[c_3196]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3203,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
% 3.01/1.03      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_funct_1(k2_funct_2(X0_49,X0_48)) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_973,c_3197]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_4160,plain,
% 3.01/1.03      ( v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48)) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_3203,c_550]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_4161,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,X0_49,X0_49,sK2,k2_funct_2(X0_49,X0_48)) = k5_relat_1(sK2,k2_funct_2(X0_49,X0_48))
% 3.01/1.03      | v1_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | v3_funct_2(X0_48,X0_49,X0_49) != iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(renaming,[status(thm)],[c_4160]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_4166,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
% 3.01/1.03      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_4161]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1913,plain,
% 3.01/1.03      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.01/1.03      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_983]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1363,plain,
% 3.01/1.03      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_985,c_970]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1918,plain,
% 3.01/1.03      ( k1_relat_1(sK2) = sK1
% 3.01/1.03      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_1913,c_1363]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2146,plain,
% 3.01/1.03      ( k1_relat_1(sK2) = sK1 ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_1918,c_26,c_27]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1799,plain,
% 3.01/1.03      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.01/1.03      | v2_funct_1(sK2) != iProver_top
% 3.01/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_988,c_967]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_523,plain,
% 3.01/1.03      ( k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(k1_relat_1(X0_48))
% 3.01/1.03      | v1_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v2_funct_1(X0_48) != iProver_top
% 3.01/1.03      | v1_relat_1(X0_48) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_525,plain,
% 3.01/1.03      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top
% 3.01/1.03      | v2_funct_1(sK2) != iProver_top
% 3.01/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_523]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2067,plain,
% 3.01/1.03      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_1799,c_26,c_28,c_29,c_88,c_525,c_540,c_1277]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2148,plain,
% 3.01/1.03      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_2146,c_2067]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_4174,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.01/1.03      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.01/1.03      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.03      inference(light_normalisation,[status(thm)],[c_4166,c_2148,c_2568]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3609,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.01/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_3600,c_3197]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_3615,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.01/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.03      inference(light_normalisation,[status(thm)],[c_3609,c_2148]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_4188,plain,
% 3.01/1.03      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_4174,c_2570,c_3615]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_21,negated_conjecture,
% 3.01/1.03      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.01/1.03      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.01/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_459,negated_conjecture,
% 3.01/1.03      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.01/1.03      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_21]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_984,plain,
% 3.01/1.03      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.01/1.03      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_2571,plain,
% 3.01/1.03      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.01/1.03      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_2568,c_984]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_4190,plain,
% 3.01/1.03      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.01/1.03      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_4188,c_2571]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_14,plain,
% 3.01/1.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.01/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_466,plain,
% 3.01/1.03      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_977,plain,
% 3.01/1.03      ( m1_subset_1(k6_partfun1(X0_49),k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) = iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_7,plain,
% 3.01/1.03      ( r2_relset_1(X0,X1,X2,X2)
% 3.01/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.01/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.01/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_472,plain,
% 3.01/1.03      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48)
% 3.01/1.03      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.01/1.03      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) ),
% 3.01/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_971,plain,
% 3.01/1.03      ( r2_relset_1(X0_49,X1_49,X0_48,X0_48) = iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.01/1.03      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.01/1.03      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1808,plain,
% 3.01/1.03      ( r2_relset_1(X0_49,X0_49,k6_partfun1(X0_49),k6_partfun1(X0_49)) = iProver_top
% 3.01/1.03      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X0_49))) != iProver_top ),
% 3.01/1.03      inference(superposition,[status(thm)],[c_977,c_971]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_1814,plain,
% 3.01/1.03      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 3.01/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.01/1.03      inference(instantiation,[status(thm)],[c_1808]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_4290,plain,
% 3.01/1.03      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
% 3.01/1.03      inference(global_propositional_subsumption,
% 3.01/1.03                [status(thm)],
% 3.01/1.03                [c_4190,c_29,c_1814]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_5122,plain,
% 3.01/1.03      ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_5120,c_4290]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(c_6712,plain,
% 3.01/1.03      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.01/1.03      inference(demodulation,[status(thm)],[c_6541,c_5122]) ).
% 3.01/1.03  
% 3.01/1.03  cnf(contradiction,plain,
% 3.01/1.03      ( $false ),
% 3.01/1.03      inference(minisat,[status(thm)],[c_6712,c_1814,c_29]) ).
% 3.01/1.03  
% 3.01/1.03  
% 3.01/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.03  
% 3.01/1.03  ------                               Statistics
% 3.01/1.03  
% 3.01/1.03  ------ General
% 3.01/1.03  
% 3.01/1.03  abstr_ref_over_cycles:                  0
% 3.01/1.03  abstr_ref_under_cycles:                 0
% 3.01/1.03  gc_basic_clause_elim:                   0
% 3.01/1.03  forced_gc_time:                         0
% 3.01/1.03  parsing_time:                           0.013
% 3.01/1.03  unif_index_cands_time:                  0.
% 3.01/1.03  unif_index_add_time:                    0.
% 3.01/1.03  orderings_time:                         0.
% 3.01/1.03  out_proof_time:                         0.021
% 3.01/1.03  total_time:                             0.421
% 3.01/1.03  num_of_symbols:                         54
% 3.01/1.03  num_of_terms:                           5682
% 3.01/1.03  
% 3.01/1.03  ------ Preprocessing
% 3.01/1.03  
% 3.01/1.03  num_of_splits:                          0
% 3.01/1.03  num_of_split_atoms:                     0
% 3.01/1.03  num_of_reused_defs:                     0
% 3.01/1.03  num_eq_ax_congr_red:                    21
% 3.01/1.03  num_of_sem_filtered_clauses:            1
% 3.01/1.03  num_of_subtypes:                        3
% 3.01/1.03  monotx_restored_types:                  1
% 3.01/1.03  sat_num_of_epr_types:                   0
% 3.01/1.03  sat_num_of_non_cyclic_types:            0
% 3.01/1.03  sat_guarded_non_collapsed_types:        1
% 3.01/1.03  num_pure_diseq_elim:                    0
% 3.01/1.03  simp_replaced_by:                       0
% 3.01/1.03  res_preprocessed:                       139
% 3.01/1.03  prep_upred:                             0
% 3.01/1.03  prep_unflattend:                        0
% 3.01/1.03  smt_new_axioms:                         0
% 3.01/1.03  pred_elim_cands:                        7
% 3.01/1.03  pred_elim:                              0
% 3.01/1.03  pred_elim_cl:                           0
% 3.01/1.03  pred_elim_cycles:                       2
% 3.01/1.03  merged_defs:                            0
% 3.01/1.03  merged_defs_ncl:                        0
% 3.01/1.03  bin_hyper_res:                          0
% 3.01/1.03  prep_cycles:                            4
% 3.01/1.03  pred_elim_time:                         0.001
% 3.01/1.03  splitting_time:                         0.
% 3.01/1.03  sem_filter_time:                        0.
% 3.01/1.03  monotx_time:                            0.001
% 3.01/1.03  subtype_inf_time:                       0.001
% 3.01/1.03  
% 3.01/1.03  ------ Problem properties
% 3.01/1.03  
% 3.01/1.03  clauses:                                25
% 3.01/1.03  conjectures:                            5
% 3.01/1.03  epr:                                    3
% 3.01/1.03  horn:                                   25
% 3.01/1.03  ground:                                 5
% 3.01/1.03  unary:                                  9
% 3.01/1.03  binary:                                 2
% 3.01/1.03  lits:                                   73
% 3.01/1.03  lits_eq:                                7
% 3.01/1.03  fd_pure:                                0
% 3.01/1.03  fd_pseudo:                              0
% 3.01/1.03  fd_cond:                                0
% 3.01/1.03  fd_pseudo_cond:                         0
% 3.01/1.03  ac_symbols:                             0
% 3.01/1.03  
% 3.01/1.03  ------ Propositional Solver
% 3.01/1.03  
% 3.01/1.03  prop_solver_calls:                      33
% 3.01/1.03  prop_fast_solver_calls:                 1174
% 3.01/1.03  smt_solver_calls:                       0
% 3.01/1.03  smt_fast_solver_calls:                  0
% 3.01/1.03  prop_num_of_clauses:                    2133
% 3.01/1.03  prop_preprocess_simplified:             6968
% 3.01/1.03  prop_fo_subsumed:                       76
% 3.01/1.03  prop_solver_time:                       0.
% 3.01/1.03  smt_solver_time:                        0.
% 3.01/1.03  smt_fast_solver_time:                   0.
% 3.01/1.03  prop_fast_solver_time:                  0.
% 3.01/1.03  prop_unsat_core_time:                   0.
% 3.01/1.03  
% 3.01/1.03  ------ QBF
% 3.01/1.03  
% 3.01/1.03  qbf_q_res:                              0
% 3.01/1.03  qbf_num_tautologies:                    0
% 3.01/1.03  qbf_prep_cycles:                        0
% 3.01/1.03  
% 3.01/1.03  ------ BMC1
% 3.01/1.03  
% 3.01/1.03  bmc1_current_bound:                     -1
% 3.01/1.03  bmc1_last_solved_bound:                 -1
% 3.01/1.03  bmc1_unsat_core_size:                   -1
% 3.01/1.03  bmc1_unsat_core_parents_size:           -1
% 3.01/1.03  bmc1_merge_next_fun:                    0
% 3.01/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.03  
% 3.01/1.03  ------ Instantiation
% 3.01/1.03  
% 3.01/1.03  inst_num_of_clauses:                    905
% 3.01/1.03  inst_num_in_passive:                    95
% 3.01/1.03  inst_num_in_active:                     461
% 3.01/1.03  inst_num_in_unprocessed:                349
% 3.01/1.03  inst_num_of_loops:                      490
% 3.01/1.03  inst_num_of_learning_restarts:          0
% 3.01/1.03  inst_num_moves_active_passive:          23
% 3.01/1.03  inst_lit_activity:                      0
% 3.01/1.03  inst_lit_activity_moves:                0
% 3.01/1.03  inst_num_tautologies:                   0
% 3.01/1.03  inst_num_prop_implied:                  0
% 3.01/1.03  inst_num_existing_simplified:           0
% 3.01/1.03  inst_num_eq_res_simplified:             0
% 3.01/1.03  inst_num_child_elim:                    0
% 3.01/1.03  inst_num_of_dismatching_blockings:      647
% 3.01/1.03  inst_num_of_non_proper_insts:           1717
% 3.01/1.03  inst_num_of_duplicates:                 0
% 3.01/1.03  inst_inst_num_from_inst_to_res:         0
% 3.01/1.03  inst_dismatching_checking_time:         0.
% 3.01/1.03  
% 3.01/1.03  ------ Resolution
% 3.01/1.03  
% 3.01/1.03  res_num_of_clauses:                     0
% 3.01/1.03  res_num_in_passive:                     0
% 3.01/1.03  res_num_in_active:                      0
% 3.01/1.03  res_num_of_loops:                       143
% 3.01/1.03  res_forward_subset_subsumed:            293
% 3.01/1.03  res_backward_subset_subsumed:           0
% 3.01/1.03  res_forward_subsumed:                   0
% 3.01/1.03  res_backward_subsumed:                  0
% 3.01/1.03  res_forward_subsumption_resolution:     0
% 3.01/1.03  res_backward_subsumption_resolution:    0
% 3.01/1.03  res_clause_to_clause_subsumption:       296
% 3.01/1.03  res_orphan_elimination:                 0
% 3.01/1.03  res_tautology_del:                      198
% 3.01/1.03  res_num_eq_res_simplified:              0
% 3.01/1.03  res_num_sel_changes:                    0
% 3.01/1.03  res_moves_from_active_to_pass:          0
% 3.01/1.03  
% 3.01/1.03  ------ Superposition
% 3.01/1.03  
% 3.01/1.03  sup_time_total:                         0.
% 3.01/1.03  sup_time_generating:                    0.
% 3.01/1.03  sup_time_sim_full:                      0.
% 3.01/1.03  sup_time_sim_immed:                     0.
% 3.01/1.03  
% 3.01/1.03  sup_num_of_clauses:                     117
% 3.01/1.03  sup_num_in_active:                      76
% 3.01/1.03  sup_num_in_passive:                     41
% 3.01/1.03  sup_num_of_loops:                       97
% 3.01/1.03  sup_fw_superposition:                   84
% 3.01/1.03  sup_bw_superposition:                   61
% 3.01/1.03  sup_immediate_simplified:               56
% 3.01/1.03  sup_given_eliminated:                   0
% 3.01/1.03  comparisons_done:                       0
% 3.01/1.03  comparisons_avoided:                    0
% 3.01/1.03  
% 3.01/1.03  ------ Simplifications
% 3.01/1.03  
% 3.01/1.03  
% 3.01/1.03  sim_fw_subset_subsumed:                 4
% 3.01/1.03  sim_bw_subset_subsumed:                 7
% 3.01/1.03  sim_fw_subsumed:                        14
% 3.01/1.03  sim_bw_subsumed:                        2
% 3.01/1.03  sim_fw_subsumption_res:                 0
% 3.01/1.03  sim_bw_subsumption_res:                 0
% 3.01/1.03  sim_tautology_del:                      0
% 3.01/1.03  sim_eq_tautology_del:                   5
% 3.01/1.03  sim_eq_res_simp:                        0
% 3.01/1.03  sim_fw_demodulated:                     15
% 3.01/1.03  sim_bw_demodulated:                     16
% 3.01/1.03  sim_light_normalised:                   30
% 3.01/1.03  sim_joinable_taut:                      0
% 3.01/1.03  sim_joinable_simp:                      0
% 3.01/1.03  sim_ac_normalised:                      0
% 3.01/1.03  sim_smt_subsumption:                    0
% 3.01/1.03  
%------------------------------------------------------------------------------
