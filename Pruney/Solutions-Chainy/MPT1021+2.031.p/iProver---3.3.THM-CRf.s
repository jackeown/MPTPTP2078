%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:24 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  165 (1127 expanded)
%              Number of clauses        :  101 ( 338 expanded)
%              Number of leaves         :   15 ( 220 expanded)
%              Depth                    :   21
%              Number of atoms          :  555 (5338 expanded)
%              Number of equality atoms :  220 ( 561 expanded)
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

fof(f44,plain,
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

fof(f45,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f44])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f67,plain,(
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

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1226,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1229,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3200,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1229])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1572,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1574,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1572])).

cnf(c_3685,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3200,c_28,c_27,c_26,c_25,c_1574])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1239,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3690,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3685,c_1239])).

cnf(c_29,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_31,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3839,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3690,c_29,c_30,c_31,c_32])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1230,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4032,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3839,c_1230])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1236,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3240,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1236])).

cnf(c_1541,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1542,plain,
    ( v1_funct_2(sK2,X0,X0) != iProver_top
    | v3_funct_2(sK2,X0,X0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(k2_funct_2(X0,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_1544,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1542])).

cnf(c_3713,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3240,c_29,c_30,c_31,c_32,c_1544])).

cnf(c_3717,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3713,c_3685])).

cnf(c_5754,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4032,c_3717])).

cnf(c_5755,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5754])).

cnf(c_5766,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_5755])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1883,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1243])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1244,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2377,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_1244])).

cnf(c_1441,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1477,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1479,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1628,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3088,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_28,c_26,c_25,c_1441,c_1479,c_1628])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1228,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2293,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1228])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1242,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1981,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1226,c_1242])).

cnf(c_2297,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2293,c_1981])).

cnf(c_2973,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2297,c_29,c_30])).

cnf(c_3090,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_3088,c_2973])).

cnf(c_5774,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5766,c_3090])).

cnf(c_5857,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5774,c_29])).

cnf(c_4031,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1230])).

cnf(c_4406,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4031,c_29])).

cnf(c_4407,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4406])).

cnf(c_4415,plain,
    ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1239,c_4407])).

cnf(c_4859,plain,
    ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4415,c_1236])).

cnf(c_4866,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2) = k5_relat_1(k2_funct_2(sK1,sK2),sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_4859])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1245,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2408,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_1245])).

cnf(c_6,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_323,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_324,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_2])).

cnf(c_329,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_3,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_344,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_329,c_3])).

cnf(c_1222,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_1769,plain,
    ( k2_relat_1(sK2) = sK1
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1222])).

cnf(c_1502,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = X1 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_1504,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_2076,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1769,c_28,c_26,c_25,c_1504])).

cnf(c_2412,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2408,c_2076])).

cnf(c_1478,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1477])).

cnf(c_1480,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_3084,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2412,c_29,c_31,c_32,c_1480])).

cnf(c_4880,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4866,c_3084,c_3685])).

cnf(c_4419,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3839,c_4407])).

cnf(c_4422,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4419,c_3084])).

cnf(c_4929,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4880,c_3717,c_4422])).

cnf(c_24,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1227,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3688,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3685,c_1227])).

cnf(c_4932,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4929,c_3688])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_58,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_60,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_5,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1511,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1934,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_1935,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_1937,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1935])).

cnf(c_5270,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4932,c_60,c_1937])).

cnf(c_5860,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5857,c_5270])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5860,c_1937,c_60])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.93/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/0.97  
% 2.93/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.93/0.97  
% 2.93/0.97  ------  iProver source info
% 2.93/0.97  
% 2.93/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.93/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.93/0.97  git: non_committed_changes: false
% 2.93/0.97  git: last_make_outside_of_git: false
% 2.93/0.97  
% 2.93/0.97  ------ 
% 2.93/0.97  
% 2.93/0.97  ------ Input Options
% 2.93/0.97  
% 2.93/0.97  --out_options                           all
% 2.93/0.97  --tptp_safe_out                         true
% 2.93/0.97  --problem_path                          ""
% 2.93/0.97  --include_path                          ""
% 2.93/0.97  --clausifier                            res/vclausify_rel
% 2.93/0.97  --clausifier_options                    --mode clausify
% 2.93/0.97  --stdin                                 false
% 2.93/0.97  --stats_out                             all
% 2.93/0.97  
% 2.93/0.97  ------ General Options
% 2.93/0.97  
% 2.93/0.97  --fof                                   false
% 2.93/0.97  --time_out_real                         305.
% 2.93/0.97  --time_out_virtual                      -1.
% 2.93/0.97  --symbol_type_check                     false
% 2.93/0.97  --clausify_out                          false
% 2.93/0.97  --sig_cnt_out                           false
% 2.93/0.97  --trig_cnt_out                          false
% 2.93/0.97  --trig_cnt_out_tolerance                1.
% 2.93/0.97  --trig_cnt_out_sk_spl                   false
% 2.93/0.97  --abstr_cl_out                          false
% 2.93/0.97  
% 2.93/0.97  ------ Global Options
% 2.93/0.97  
% 2.93/0.97  --schedule                              default
% 2.93/0.97  --add_important_lit                     false
% 2.93/0.97  --prop_solver_per_cl                    1000
% 2.93/0.97  --min_unsat_core                        false
% 2.93/0.97  --soft_assumptions                      false
% 2.93/0.97  --soft_lemma_size                       3
% 2.93/0.97  --prop_impl_unit_size                   0
% 2.93/0.97  --prop_impl_unit                        []
% 2.93/0.97  --share_sel_clauses                     true
% 2.93/0.97  --reset_solvers                         false
% 2.93/0.97  --bc_imp_inh                            [conj_cone]
% 2.93/0.97  --conj_cone_tolerance                   3.
% 2.93/0.97  --extra_neg_conj                        none
% 2.93/0.97  --large_theory_mode                     true
% 2.93/0.97  --prolific_symb_bound                   200
% 2.93/0.97  --lt_threshold                          2000
% 2.93/0.97  --clause_weak_htbl                      true
% 2.93/0.97  --gc_record_bc_elim                     false
% 2.93/0.97  
% 2.93/0.97  ------ Preprocessing Options
% 2.93/0.97  
% 2.93/0.97  --preprocessing_flag                    true
% 2.93/0.97  --time_out_prep_mult                    0.1
% 2.93/0.97  --splitting_mode                        input
% 2.93/0.97  --splitting_grd                         true
% 2.93/0.97  --splitting_cvd                         false
% 2.93/0.97  --splitting_cvd_svl                     false
% 2.93/0.97  --splitting_nvd                         32
% 2.93/0.97  --sub_typing                            true
% 2.93/0.97  --prep_gs_sim                           true
% 2.93/0.97  --prep_unflatten                        true
% 2.93/0.97  --prep_res_sim                          true
% 2.93/0.97  --prep_upred                            true
% 2.93/0.97  --prep_sem_filter                       exhaustive
% 2.93/0.97  --prep_sem_filter_out                   false
% 2.93/0.97  --pred_elim                             true
% 2.93/0.97  --res_sim_input                         true
% 2.93/0.97  --eq_ax_congr_red                       true
% 2.93/0.97  --pure_diseq_elim                       true
% 2.93/0.97  --brand_transform                       false
% 2.93/0.97  --non_eq_to_eq                          false
% 2.93/0.97  --prep_def_merge                        true
% 2.93/0.97  --prep_def_merge_prop_impl              false
% 2.93/0.97  --prep_def_merge_mbd                    true
% 2.93/0.97  --prep_def_merge_tr_red                 false
% 2.93/0.97  --prep_def_merge_tr_cl                  false
% 2.93/0.97  --smt_preprocessing                     true
% 2.93/0.97  --smt_ac_axioms                         fast
% 2.93/0.97  --preprocessed_out                      false
% 2.93/0.97  --preprocessed_stats                    false
% 2.93/0.97  
% 2.93/0.97  ------ Abstraction refinement Options
% 2.93/0.97  
% 2.93/0.97  --abstr_ref                             []
% 2.93/0.97  --abstr_ref_prep                        false
% 2.93/0.97  --abstr_ref_until_sat                   false
% 2.93/0.97  --abstr_ref_sig_restrict                funpre
% 2.93/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/0.97  --abstr_ref_under                       []
% 2.93/0.97  
% 2.93/0.97  ------ SAT Options
% 2.93/0.97  
% 2.93/0.97  --sat_mode                              false
% 2.93/0.97  --sat_fm_restart_options                ""
% 2.93/0.97  --sat_gr_def                            false
% 2.93/0.97  --sat_epr_types                         true
% 2.93/0.97  --sat_non_cyclic_types                  false
% 2.93/0.97  --sat_finite_models                     false
% 2.93/0.97  --sat_fm_lemmas                         false
% 2.93/0.97  --sat_fm_prep                           false
% 2.93/0.97  --sat_fm_uc_incr                        true
% 2.93/0.97  --sat_out_model                         small
% 2.93/0.97  --sat_out_clauses                       false
% 2.93/0.97  
% 2.93/0.97  ------ QBF Options
% 2.93/0.97  
% 2.93/0.97  --qbf_mode                              false
% 2.93/0.97  --qbf_elim_univ                         false
% 2.93/0.97  --qbf_dom_inst                          none
% 2.93/0.97  --qbf_dom_pre_inst                      false
% 2.93/0.97  --qbf_sk_in                             false
% 2.93/0.97  --qbf_pred_elim                         true
% 2.93/0.97  --qbf_split                             512
% 2.93/0.97  
% 2.93/0.97  ------ BMC1 Options
% 2.93/0.97  
% 2.93/0.97  --bmc1_incremental                      false
% 2.93/0.97  --bmc1_axioms                           reachable_all
% 2.93/0.97  --bmc1_min_bound                        0
% 2.93/0.97  --bmc1_max_bound                        -1
% 2.93/0.97  --bmc1_max_bound_default                -1
% 2.93/0.97  --bmc1_symbol_reachability              true
% 2.93/0.97  --bmc1_property_lemmas                  false
% 2.93/0.97  --bmc1_k_induction                      false
% 2.93/0.97  --bmc1_non_equiv_states                 false
% 2.93/0.97  --bmc1_deadlock                         false
% 2.93/0.97  --bmc1_ucm                              false
% 2.93/0.97  --bmc1_add_unsat_core                   none
% 2.93/0.97  --bmc1_unsat_core_children              false
% 2.93/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/0.97  --bmc1_out_stat                         full
% 2.93/0.97  --bmc1_ground_init                      false
% 2.93/0.97  --bmc1_pre_inst_next_state              false
% 2.93/0.97  --bmc1_pre_inst_state                   false
% 2.93/0.97  --bmc1_pre_inst_reach_state             false
% 2.93/0.97  --bmc1_out_unsat_core                   false
% 2.93/0.97  --bmc1_aig_witness_out                  false
% 2.93/0.97  --bmc1_verbose                          false
% 2.93/0.97  --bmc1_dump_clauses_tptp                false
% 2.93/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.93/0.97  --bmc1_dump_file                        -
% 2.93/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.93/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.93/0.97  --bmc1_ucm_extend_mode                  1
% 2.93/0.97  --bmc1_ucm_init_mode                    2
% 2.93/0.97  --bmc1_ucm_cone_mode                    none
% 2.93/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.93/0.97  --bmc1_ucm_relax_model                  4
% 2.93/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.93/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/0.97  --bmc1_ucm_layered_model                none
% 2.93/0.97  --bmc1_ucm_max_lemma_size               10
% 2.93/0.97  
% 2.93/0.97  ------ AIG Options
% 2.93/0.97  
% 2.93/0.97  --aig_mode                              false
% 2.93/0.97  
% 2.93/0.97  ------ Instantiation Options
% 2.93/0.97  
% 2.93/0.97  --instantiation_flag                    true
% 2.93/0.97  --inst_sos_flag                         false
% 2.93/0.97  --inst_sos_phase                        true
% 2.93/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/0.97  --inst_lit_sel_side                     num_symb
% 2.93/0.97  --inst_solver_per_active                1400
% 2.93/0.97  --inst_solver_calls_frac                1.
% 2.93/0.97  --inst_passive_queue_type               priority_queues
% 2.93/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/0.97  --inst_passive_queues_freq              [25;2]
% 2.93/0.97  --inst_dismatching                      true
% 2.93/0.97  --inst_eager_unprocessed_to_passive     true
% 2.93/0.97  --inst_prop_sim_given                   true
% 2.93/0.97  --inst_prop_sim_new                     false
% 2.93/0.97  --inst_subs_new                         false
% 2.93/0.97  --inst_eq_res_simp                      false
% 2.93/0.97  --inst_subs_given                       false
% 2.93/0.97  --inst_orphan_elimination               true
% 2.93/0.97  --inst_learning_loop_flag               true
% 2.93/0.97  --inst_learning_start                   3000
% 2.93/0.97  --inst_learning_factor                  2
% 2.93/0.97  --inst_start_prop_sim_after_learn       3
% 2.93/0.97  --inst_sel_renew                        solver
% 2.93/0.97  --inst_lit_activity_flag                true
% 2.93/0.97  --inst_restr_to_given                   false
% 2.93/0.97  --inst_activity_threshold               500
% 2.93/0.97  --inst_out_proof                        true
% 2.93/0.97  
% 2.93/0.97  ------ Resolution Options
% 2.93/0.97  
% 2.93/0.97  --resolution_flag                       true
% 2.93/0.97  --res_lit_sel                           adaptive
% 2.93/0.97  --res_lit_sel_side                      none
% 2.93/0.97  --res_ordering                          kbo
% 2.93/0.97  --res_to_prop_solver                    active
% 2.93/0.97  --res_prop_simpl_new                    false
% 2.93/0.97  --res_prop_simpl_given                  true
% 2.93/0.97  --res_passive_queue_type                priority_queues
% 2.93/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/0.97  --res_passive_queues_freq               [15;5]
% 2.93/0.97  --res_forward_subs                      full
% 2.93/0.97  --res_backward_subs                     full
% 2.93/0.97  --res_forward_subs_resolution           true
% 2.93/0.97  --res_backward_subs_resolution          true
% 2.93/0.97  --res_orphan_elimination                true
% 2.93/0.97  --res_time_limit                        2.
% 2.93/0.97  --res_out_proof                         true
% 2.93/0.97  
% 2.93/0.97  ------ Superposition Options
% 2.93/0.97  
% 2.93/0.97  --superposition_flag                    true
% 2.93/0.97  --sup_passive_queue_type                priority_queues
% 2.93/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.93/0.97  --demod_completeness_check              fast
% 2.93/0.97  --demod_use_ground                      true
% 2.93/0.97  --sup_to_prop_solver                    passive
% 2.93/0.97  --sup_prop_simpl_new                    true
% 2.93/0.97  --sup_prop_simpl_given                  true
% 2.93/0.97  --sup_fun_splitting                     false
% 2.93/0.97  --sup_smt_interval                      50000
% 2.93/0.97  
% 2.93/0.97  ------ Superposition Simplification Setup
% 2.93/0.97  
% 2.93/0.97  --sup_indices_passive                   []
% 2.93/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.97  --sup_full_bw                           [BwDemod]
% 2.93/0.97  --sup_immed_triv                        [TrivRules]
% 2.93/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.97  --sup_immed_bw_main                     []
% 2.93/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.97  
% 2.93/0.97  ------ Combination Options
% 2.93/0.97  
% 2.93/0.97  --comb_res_mult                         3
% 2.93/0.97  --comb_sup_mult                         2
% 2.93/0.97  --comb_inst_mult                        10
% 2.93/0.97  
% 2.93/0.97  ------ Debug Options
% 2.93/0.97  
% 2.93/0.97  --dbg_backtrace                         false
% 2.93/0.97  --dbg_dump_prop_clauses                 false
% 2.93/0.97  --dbg_dump_prop_clauses_file            -
% 2.93/0.97  --dbg_out_stat                          false
% 2.93/0.97  ------ Parsing...
% 2.93/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.93/0.97  
% 2.93/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.93/0.97  
% 2.93/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.93/0.97  
% 2.93/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.93/0.97  ------ Proving...
% 2.93/0.97  ------ Problem Properties 
% 2.93/0.97  
% 2.93/0.97  
% 2.93/0.97  clauses                                 24
% 2.93/0.97  conjectures                             5
% 2.93/0.97  EPR                                     3
% 2.93/0.97  Horn                                    24
% 2.93/0.97  unary                                   9
% 2.93/0.97  binary                                  3
% 2.93/0.97  lits                                    68
% 2.93/0.97  lits eq                                 7
% 2.93/0.97  fd_pure                                 0
% 2.93/0.97  fd_pseudo                               0
% 2.93/0.97  fd_cond                                 0
% 2.93/0.97  fd_pseudo_cond                          1
% 2.93/0.97  AC symbols                              0
% 2.93/0.97  
% 2.93/0.97  ------ Schedule dynamic 5 is on 
% 2.93/0.97  
% 2.93/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.93/0.97  
% 2.93/0.97  
% 2.93/0.97  ------ 
% 2.93/0.97  Current options:
% 2.93/0.97  ------ 
% 2.93/0.97  
% 2.93/0.97  ------ Input Options
% 2.93/0.97  
% 2.93/0.97  --out_options                           all
% 2.93/0.97  --tptp_safe_out                         true
% 2.93/0.97  --problem_path                          ""
% 2.93/0.97  --include_path                          ""
% 2.93/0.97  --clausifier                            res/vclausify_rel
% 2.93/0.97  --clausifier_options                    --mode clausify
% 2.93/0.97  --stdin                                 false
% 2.93/0.97  --stats_out                             all
% 2.93/0.97  
% 2.93/0.97  ------ General Options
% 2.93/0.97  
% 2.93/0.97  --fof                                   false
% 2.93/0.97  --time_out_real                         305.
% 2.93/0.97  --time_out_virtual                      -1.
% 2.93/0.97  --symbol_type_check                     false
% 2.93/0.97  --clausify_out                          false
% 2.93/0.97  --sig_cnt_out                           false
% 2.93/0.97  --trig_cnt_out                          false
% 2.93/0.97  --trig_cnt_out_tolerance                1.
% 2.93/0.97  --trig_cnt_out_sk_spl                   false
% 2.93/0.97  --abstr_cl_out                          false
% 2.93/0.97  
% 2.93/0.97  ------ Global Options
% 2.93/0.97  
% 2.93/0.97  --schedule                              default
% 2.93/0.97  --add_important_lit                     false
% 2.93/0.97  --prop_solver_per_cl                    1000
% 2.93/0.97  --min_unsat_core                        false
% 2.93/0.97  --soft_assumptions                      false
% 2.93/0.97  --soft_lemma_size                       3
% 2.93/0.97  --prop_impl_unit_size                   0
% 2.93/0.97  --prop_impl_unit                        []
% 2.93/0.97  --share_sel_clauses                     true
% 2.93/0.97  --reset_solvers                         false
% 2.93/0.97  --bc_imp_inh                            [conj_cone]
% 2.93/0.97  --conj_cone_tolerance                   3.
% 2.93/0.97  --extra_neg_conj                        none
% 2.93/0.97  --large_theory_mode                     true
% 2.93/0.97  --prolific_symb_bound                   200
% 2.93/0.97  --lt_threshold                          2000
% 2.93/0.97  --clause_weak_htbl                      true
% 2.93/0.97  --gc_record_bc_elim                     false
% 2.93/0.97  
% 2.93/0.97  ------ Preprocessing Options
% 2.93/0.97  
% 2.93/0.97  --preprocessing_flag                    true
% 2.93/0.97  --time_out_prep_mult                    0.1
% 2.93/0.97  --splitting_mode                        input
% 2.93/0.97  --splitting_grd                         true
% 2.93/0.97  --splitting_cvd                         false
% 2.93/0.97  --splitting_cvd_svl                     false
% 2.93/0.97  --splitting_nvd                         32
% 2.93/0.97  --sub_typing                            true
% 2.93/0.97  --prep_gs_sim                           true
% 2.93/0.97  --prep_unflatten                        true
% 2.93/0.97  --prep_res_sim                          true
% 2.93/0.97  --prep_upred                            true
% 2.93/0.97  --prep_sem_filter                       exhaustive
% 2.93/0.97  --prep_sem_filter_out                   false
% 2.93/0.97  --pred_elim                             true
% 2.93/0.97  --res_sim_input                         true
% 2.93/0.97  --eq_ax_congr_red                       true
% 2.93/0.97  --pure_diseq_elim                       true
% 2.93/0.97  --brand_transform                       false
% 2.93/0.97  --non_eq_to_eq                          false
% 2.93/0.97  --prep_def_merge                        true
% 2.93/0.97  --prep_def_merge_prop_impl              false
% 2.93/0.97  --prep_def_merge_mbd                    true
% 2.93/0.97  --prep_def_merge_tr_red                 false
% 2.93/0.97  --prep_def_merge_tr_cl                  false
% 2.93/0.97  --smt_preprocessing                     true
% 2.93/0.97  --smt_ac_axioms                         fast
% 2.93/0.97  --preprocessed_out                      false
% 2.93/0.97  --preprocessed_stats                    false
% 2.93/0.97  
% 2.93/0.97  ------ Abstraction refinement Options
% 2.93/0.97  
% 2.93/0.97  --abstr_ref                             []
% 2.93/0.97  --abstr_ref_prep                        false
% 2.93/0.97  --abstr_ref_until_sat                   false
% 2.93/0.97  --abstr_ref_sig_restrict                funpre
% 2.93/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.93/0.97  --abstr_ref_under                       []
% 2.93/0.97  
% 2.93/0.97  ------ SAT Options
% 2.93/0.97  
% 2.93/0.97  --sat_mode                              false
% 2.93/0.97  --sat_fm_restart_options                ""
% 2.93/0.97  --sat_gr_def                            false
% 2.93/0.97  --sat_epr_types                         true
% 2.93/0.97  --sat_non_cyclic_types                  false
% 2.93/0.97  --sat_finite_models                     false
% 2.93/0.97  --sat_fm_lemmas                         false
% 2.93/0.97  --sat_fm_prep                           false
% 2.93/0.97  --sat_fm_uc_incr                        true
% 2.93/0.97  --sat_out_model                         small
% 2.93/0.97  --sat_out_clauses                       false
% 2.93/0.97  
% 2.93/0.97  ------ QBF Options
% 2.93/0.97  
% 2.93/0.97  --qbf_mode                              false
% 2.93/0.97  --qbf_elim_univ                         false
% 2.93/0.97  --qbf_dom_inst                          none
% 2.93/0.97  --qbf_dom_pre_inst                      false
% 2.93/0.97  --qbf_sk_in                             false
% 2.93/0.97  --qbf_pred_elim                         true
% 2.93/0.97  --qbf_split                             512
% 2.93/0.97  
% 2.93/0.97  ------ BMC1 Options
% 2.93/0.97  
% 2.93/0.97  --bmc1_incremental                      false
% 2.93/0.97  --bmc1_axioms                           reachable_all
% 2.93/0.97  --bmc1_min_bound                        0
% 2.93/0.97  --bmc1_max_bound                        -1
% 2.93/0.97  --bmc1_max_bound_default                -1
% 2.93/0.97  --bmc1_symbol_reachability              true
% 2.93/0.97  --bmc1_property_lemmas                  false
% 2.93/0.97  --bmc1_k_induction                      false
% 2.93/0.97  --bmc1_non_equiv_states                 false
% 2.93/0.97  --bmc1_deadlock                         false
% 2.93/0.97  --bmc1_ucm                              false
% 2.93/0.97  --bmc1_add_unsat_core                   none
% 2.93/0.97  --bmc1_unsat_core_children              false
% 2.93/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.93/0.97  --bmc1_out_stat                         full
% 2.93/0.97  --bmc1_ground_init                      false
% 2.93/0.97  --bmc1_pre_inst_next_state              false
% 2.93/0.97  --bmc1_pre_inst_state                   false
% 2.93/0.97  --bmc1_pre_inst_reach_state             false
% 2.93/0.97  --bmc1_out_unsat_core                   false
% 2.93/0.97  --bmc1_aig_witness_out                  false
% 2.93/0.97  --bmc1_verbose                          false
% 2.93/0.97  --bmc1_dump_clauses_tptp                false
% 2.93/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.93/0.97  --bmc1_dump_file                        -
% 2.93/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.93/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.93/0.97  --bmc1_ucm_extend_mode                  1
% 2.93/0.97  --bmc1_ucm_init_mode                    2
% 2.93/0.97  --bmc1_ucm_cone_mode                    none
% 2.93/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.93/0.97  --bmc1_ucm_relax_model                  4
% 2.93/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.93/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.93/0.97  --bmc1_ucm_layered_model                none
% 2.93/0.97  --bmc1_ucm_max_lemma_size               10
% 2.93/0.97  
% 2.93/0.97  ------ AIG Options
% 2.93/0.97  
% 2.93/0.97  --aig_mode                              false
% 2.93/0.97  
% 2.93/0.97  ------ Instantiation Options
% 2.93/0.97  
% 2.93/0.97  --instantiation_flag                    true
% 2.93/0.97  --inst_sos_flag                         false
% 2.93/0.97  --inst_sos_phase                        true
% 2.93/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.93/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.93/0.97  --inst_lit_sel_side                     none
% 2.93/0.97  --inst_solver_per_active                1400
% 2.93/0.97  --inst_solver_calls_frac                1.
% 2.93/0.97  --inst_passive_queue_type               priority_queues
% 2.93/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.93/0.97  --inst_passive_queues_freq              [25;2]
% 2.93/0.97  --inst_dismatching                      true
% 2.93/0.97  --inst_eager_unprocessed_to_passive     true
% 2.93/0.97  --inst_prop_sim_given                   true
% 2.93/0.97  --inst_prop_sim_new                     false
% 2.93/0.97  --inst_subs_new                         false
% 2.93/0.97  --inst_eq_res_simp                      false
% 2.93/0.97  --inst_subs_given                       false
% 2.93/0.97  --inst_orphan_elimination               true
% 2.93/0.97  --inst_learning_loop_flag               true
% 2.93/0.97  --inst_learning_start                   3000
% 2.93/0.97  --inst_learning_factor                  2
% 2.93/0.97  --inst_start_prop_sim_after_learn       3
% 2.93/0.97  --inst_sel_renew                        solver
% 2.93/0.97  --inst_lit_activity_flag                true
% 2.93/0.97  --inst_restr_to_given                   false
% 2.93/0.97  --inst_activity_threshold               500
% 2.93/0.97  --inst_out_proof                        true
% 2.93/0.97  
% 2.93/0.97  ------ Resolution Options
% 2.93/0.97  
% 2.93/0.97  --resolution_flag                       false
% 2.93/0.97  --res_lit_sel                           adaptive
% 2.93/0.97  --res_lit_sel_side                      none
% 2.93/0.97  --res_ordering                          kbo
% 2.93/0.97  --res_to_prop_solver                    active
% 2.93/0.97  --res_prop_simpl_new                    false
% 2.93/0.97  --res_prop_simpl_given                  true
% 2.93/0.97  --res_passive_queue_type                priority_queues
% 2.93/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.93/0.97  --res_passive_queues_freq               [15;5]
% 2.93/0.97  --res_forward_subs                      full
% 2.93/0.97  --res_backward_subs                     full
% 2.93/0.97  --res_forward_subs_resolution           true
% 2.93/0.97  --res_backward_subs_resolution          true
% 2.93/0.97  --res_orphan_elimination                true
% 2.93/0.97  --res_time_limit                        2.
% 2.93/0.97  --res_out_proof                         true
% 2.93/0.97  
% 2.93/0.97  ------ Superposition Options
% 2.93/0.97  
% 2.93/0.97  --superposition_flag                    true
% 2.93/0.97  --sup_passive_queue_type                priority_queues
% 2.93/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.93/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.93/0.97  --demod_completeness_check              fast
% 2.93/0.97  --demod_use_ground                      true
% 2.93/0.97  --sup_to_prop_solver                    passive
% 2.93/0.97  --sup_prop_simpl_new                    true
% 2.93/0.97  --sup_prop_simpl_given                  true
% 2.93/0.97  --sup_fun_splitting                     false
% 2.93/0.97  --sup_smt_interval                      50000
% 2.93/0.97  
% 2.93/0.97  ------ Superposition Simplification Setup
% 2.93/0.97  
% 2.93/0.97  --sup_indices_passive                   []
% 2.93/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.93/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.93/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.97  --sup_full_bw                           [BwDemod]
% 2.93/0.97  --sup_immed_triv                        [TrivRules]
% 2.93/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.93/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.97  --sup_immed_bw_main                     []
% 2.93/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.93/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.93/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.93/0.97  
% 2.93/0.97  ------ Combination Options
% 2.93/0.97  
% 2.93/0.97  --comb_res_mult                         3
% 2.93/0.97  --comb_sup_mult                         2
% 2.93/0.97  --comb_inst_mult                        10
% 2.93/0.97  
% 2.93/0.97  ------ Debug Options
% 2.93/0.97  
% 2.93/0.97  --dbg_backtrace                         false
% 2.93/0.97  --dbg_dump_prop_clauses                 false
% 2.93/0.97  --dbg_dump_prop_clauses_file            -
% 2.93/0.97  --dbg_out_stat                          false
% 2.93/0.97  
% 2.93/0.97  
% 2.93/0.97  
% 2.93/0.97  
% 2.93/0.97  ------ Proving...
% 2.93/0.97  
% 2.93/0.97  
% 2.93/0.97  % SZS status Theorem for theBenchmark.p
% 2.93/0.97  
% 2.93/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.93/0.97  
% 2.93/0.97  fof(f15,conjecture,(
% 2.93/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f16,negated_conjecture,(
% 2.93/0.97    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.93/0.97    inference(negated_conjecture,[],[f15])).
% 2.93/0.97  
% 2.93/0.97  fof(f39,plain,(
% 2.93/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.93/0.97    inference(ennf_transformation,[],[f16])).
% 2.93/0.97  
% 2.93/0.97  fof(f40,plain,(
% 2.93/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.93/0.97    inference(flattening,[],[f39])).
% 2.93/0.97  
% 2.93/0.97  fof(f44,plain,(
% 2.93/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 2.93/0.97    introduced(choice_axiom,[])).
% 2.93/0.97  
% 2.93/0.97  fof(f45,plain,(
% 2.93/0.97    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 2.93/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f44])).
% 2.93/0.97  
% 2.93/0.97  fof(f74,plain,(
% 2.93/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.93/0.97    inference(cnf_transformation,[],[f45])).
% 2.93/0.97  
% 2.93/0.97  fof(f12,axiom,(
% 2.93/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f35,plain,(
% 2.93/0.97    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.93/0.97    inference(ennf_transformation,[],[f12])).
% 2.93/0.97  
% 2.93/0.97  fof(f36,plain,(
% 2.93/0.97    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.93/0.97    inference(flattening,[],[f35])).
% 2.93/0.97  
% 2.93/0.97  fof(f68,plain,(
% 2.93/0.97    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f36])).
% 2.93/0.97  
% 2.93/0.97  fof(f71,plain,(
% 2.93/0.97    v1_funct_1(sK2)),
% 2.93/0.97    inference(cnf_transformation,[],[f45])).
% 2.93/0.97  
% 2.93/0.97  fof(f72,plain,(
% 2.93/0.97    v1_funct_2(sK2,sK1,sK1)),
% 2.93/0.97    inference(cnf_transformation,[],[f45])).
% 2.93/0.97  
% 2.93/0.97  fof(f73,plain,(
% 2.93/0.97    v3_funct_2(sK2,sK1,sK1)),
% 2.93/0.97    inference(cnf_transformation,[],[f45])).
% 2.93/0.97  
% 2.93/0.97  fof(f8,axiom,(
% 2.93/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f31,plain,(
% 2.93/0.97    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.93/0.97    inference(ennf_transformation,[],[f8])).
% 2.93/0.97  
% 2.93/0.97  fof(f32,plain,(
% 2.93/0.97    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.93/0.97    inference(flattening,[],[f31])).
% 2.93/0.97  
% 2.93/0.97  fof(f60,plain,(
% 2.93/0.97    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f32])).
% 2.93/0.97  
% 2.93/0.97  fof(f11,axiom,(
% 2.93/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f33,plain,(
% 2.93/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.93/0.97    inference(ennf_transformation,[],[f11])).
% 2.93/0.97  
% 2.93/0.97  fof(f34,plain,(
% 2.93/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.93/0.97    inference(flattening,[],[f33])).
% 2.93/0.97  
% 2.93/0.97  fof(f67,plain,(
% 2.93/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f34])).
% 2.93/0.97  
% 2.93/0.97  fof(f57,plain,(
% 2.93/0.97    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f32])).
% 2.93/0.97  
% 2.93/0.97  fof(f2,axiom,(
% 2.93/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f22,plain,(
% 2.93/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.97    inference(ennf_transformation,[],[f2])).
% 2.93/0.97  
% 2.93/0.97  fof(f48,plain,(
% 2.93/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.97    inference(cnf_transformation,[],[f22])).
% 2.93/0.97  
% 2.93/0.97  fof(f1,axiom,(
% 2.93/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f20,plain,(
% 2.93/0.97    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.93/0.97    inference(ennf_transformation,[],[f1])).
% 2.93/0.97  
% 2.93/0.97  fof(f21,plain,(
% 2.93/0.97    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.93/0.97    inference(flattening,[],[f20])).
% 2.93/0.97  
% 2.93/0.97  fof(f46,plain,(
% 2.93/0.97    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f21])).
% 2.93/0.97  
% 2.93/0.97  fof(f13,axiom,(
% 2.93/0.97    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f69,plain,(
% 2.93/0.97    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f13])).
% 2.93/0.97  
% 2.93/0.97  fof(f77,plain,(
% 2.93/0.97    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.97    inference(definition_unfolding,[],[f46,f69])).
% 2.93/0.97  
% 2.93/0.97  fof(f6,axiom,(
% 2.93/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f27,plain,(
% 2.93/0.97    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.97    inference(ennf_transformation,[],[f6])).
% 2.93/0.97  
% 2.93/0.97  fof(f28,plain,(
% 2.93/0.97    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.97    inference(flattening,[],[f27])).
% 2.93/0.97  
% 2.93/0.97  fof(f53,plain,(
% 2.93/0.97    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.97    inference(cnf_transformation,[],[f28])).
% 2.93/0.97  
% 2.93/0.97  fof(f14,axiom,(
% 2.93/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f37,plain,(
% 2.93/0.97    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.93/0.97    inference(ennf_transformation,[],[f14])).
% 2.93/0.97  
% 2.93/0.97  fof(f38,plain,(
% 2.93/0.97    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.93/0.97    inference(flattening,[],[f37])).
% 2.93/0.97  
% 2.93/0.97  fof(f70,plain,(
% 2.93/0.97    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f38])).
% 2.93/0.97  
% 2.93/0.97  fof(f4,axiom,(
% 2.93/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f24,plain,(
% 2.93/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.97    inference(ennf_transformation,[],[f4])).
% 2.93/0.97  
% 2.93/0.97  fof(f50,plain,(
% 2.93/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.97    inference(cnf_transformation,[],[f24])).
% 2.93/0.97  
% 2.93/0.97  fof(f47,plain,(
% 2.93/0.97    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f21])).
% 2.93/0.97  
% 2.93/0.97  fof(f76,plain,(
% 2.93/0.97    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.93/0.97    inference(definition_unfolding,[],[f47,f69])).
% 2.93/0.97  
% 2.93/0.97  fof(f54,plain,(
% 2.93/0.97    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.97    inference(cnf_transformation,[],[f28])).
% 2.93/0.97  
% 2.93/0.97  fof(f7,axiom,(
% 2.93/0.97    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f29,plain,(
% 2.93/0.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.93/0.97    inference(ennf_transformation,[],[f7])).
% 2.93/0.97  
% 2.93/0.97  fof(f30,plain,(
% 2.93/0.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.93/0.97    inference(flattening,[],[f29])).
% 2.93/0.97  
% 2.93/0.97  fof(f41,plain,(
% 2.93/0.97    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.93/0.97    inference(nnf_transformation,[],[f30])).
% 2.93/0.97  
% 2.93/0.97  fof(f55,plain,(
% 2.93/0.97    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.93/0.97    inference(cnf_transformation,[],[f41])).
% 2.93/0.97  
% 2.93/0.97  fof(f3,axiom,(
% 2.93/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f19,plain,(
% 2.93/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.93/0.97    inference(pure_predicate_removal,[],[f3])).
% 2.93/0.97  
% 2.93/0.97  fof(f23,plain,(
% 2.93/0.97    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.97    inference(ennf_transformation,[],[f19])).
% 2.93/0.97  
% 2.93/0.97  fof(f49,plain,(
% 2.93/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.97    inference(cnf_transformation,[],[f23])).
% 2.93/0.97  
% 2.93/0.97  fof(f75,plain,(
% 2.93/0.97    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 2.93/0.97    inference(cnf_transformation,[],[f45])).
% 2.93/0.97  
% 2.93/0.97  fof(f9,axiom,(
% 2.93/0.97    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f17,plain,(
% 2.93/0.97    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.93/0.97    inference(pure_predicate_removal,[],[f9])).
% 2.93/0.97  
% 2.93/0.97  fof(f61,plain,(
% 2.93/0.97    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.93/0.97    inference(cnf_transformation,[],[f17])).
% 2.93/0.97  
% 2.93/0.97  fof(f5,axiom,(
% 2.93/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.93/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.93/0.97  
% 2.93/0.97  fof(f25,plain,(
% 2.93/0.97    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.93/0.97    inference(ennf_transformation,[],[f5])).
% 2.93/0.97  
% 2.93/0.97  fof(f26,plain,(
% 2.93/0.97    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.93/0.97    inference(flattening,[],[f25])).
% 2.93/0.97  
% 2.93/0.97  fof(f51,plain,(
% 2.93/0.97    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.93/0.97    inference(cnf_transformation,[],[f26])).
% 2.93/0.97  
% 2.93/0.97  cnf(c_25,negated_conjecture,
% 2.93/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.93/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1226,plain,
% 2.93/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_22,plain,
% 2.93/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 2.93/0.97      | ~ v3_funct_2(X0,X1,X1)
% 2.93/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.93/0.97      | ~ v1_funct_1(X0)
% 2.93/0.97      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.93/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1229,plain,
% 2.93/0.97      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 2.93/0.97      | v1_funct_2(X1,X0,X0) != iProver_top
% 2.93/0.97      | v3_funct_2(X1,X0,X0) != iProver_top
% 2.93/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.93/0.97      | v1_funct_1(X1) != iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_3200,plain,
% 2.93/0.97      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 2.93/0.97      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.97      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.97      inference(superposition,[status(thm)],[c_1226,c_1229]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_28,negated_conjecture,
% 2.93/0.97      ( v1_funct_1(sK2) ),
% 2.93/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_27,negated_conjecture,
% 2.93/0.97      ( v1_funct_2(sK2,sK1,sK1) ),
% 2.93/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_26,negated_conjecture,
% 2.93/0.97      ( v3_funct_2(sK2,sK1,sK1) ),
% 2.93/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1572,plain,
% 2.93/0.97      ( ~ v1_funct_2(sK2,X0,X0)
% 2.93/0.97      | ~ v3_funct_2(sK2,X0,X0)
% 2.93/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 2.93/0.97      | ~ v1_funct_1(sK2)
% 2.93/0.97      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 2.93/0.97      inference(instantiation,[status(thm)],[c_22]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1574,plain,
% 2.93/0.97      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.93/0.97      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.93/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.93/0.97      | ~ v1_funct_1(sK2)
% 2.93/0.97      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.93/0.97      inference(instantiation,[status(thm)],[c_1572]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_3685,plain,
% 2.93/0.97      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.93/0.97      inference(global_propositional_subsumption,
% 2.93/0.97                [status(thm)],
% 2.93/0.97                [c_3200,c_28,c_27,c_26,c_25,c_1574]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_11,plain,
% 2.93/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 2.93/0.97      | ~ v3_funct_2(X0,X1,X1)
% 2.93/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.93/0.97      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.93/0.97      | ~ v1_funct_1(X0) ),
% 2.93/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1239,plain,
% 2.93/0.97      ( v1_funct_2(X0,X1,X1) != iProver_top
% 2.93/0.97      | v3_funct_2(X0,X1,X1) != iProver_top
% 2.93/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 2.93/0.97      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 2.93/0.97      | v1_funct_1(X0) != iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_3690,plain,
% 2.93/0.97      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.97      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.93/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.93/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.97      inference(superposition,[status(thm)],[c_3685,c_1239]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_29,plain,
% 2.93/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_30,plain,
% 2.93/0.97      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_31,plain,
% 2.93/0.97      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_32,plain,
% 2.93/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_3839,plain,
% 2.93/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.93/0.97      inference(global_propositional_subsumption,
% 2.93/0.97                [status(thm)],
% 2.93/0.97                [c_3690,c_29,c_30,c_31,c_32]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_21,plain,
% 2.93/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.93/0.97      | ~ v1_funct_1(X0)
% 2.93/0.97      | ~ v1_funct_1(X3)
% 2.93/0.97      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.93/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1230,plain,
% 2.93/0.97      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.93/0.97      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.93/0.97      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.93/0.97      | v1_funct_1(X5) != iProver_top
% 2.93/0.97      | v1_funct_1(X4) != iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_4032,plain,
% 2.93/0.97      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 2.93/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.93/0.97      | v1_funct_1(X2) != iProver_top
% 2.93/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.93/0.97      inference(superposition,[status(thm)],[c_3839,c_1230]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_14,plain,
% 2.93/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 2.93/0.97      | ~ v3_funct_2(X0,X1,X1)
% 2.93/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.93/0.97      | ~ v1_funct_1(X0)
% 2.93/0.97      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.93/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1236,plain,
% 2.93/0.97      ( v1_funct_2(X0,X1,X1) != iProver_top
% 2.93/0.97      | v3_funct_2(X0,X1,X1) != iProver_top
% 2.93/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 2.93/0.97      | v1_funct_1(X0) != iProver_top
% 2.93/0.97      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_3240,plain,
% 2.93/0.97      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.97      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.97      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.93/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.97      inference(superposition,[status(thm)],[c_1226,c_1236]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1541,plain,
% 2.93/0.97      ( ~ v1_funct_2(sK2,X0,X0)
% 2.93/0.97      | ~ v3_funct_2(sK2,X0,X0)
% 2.93/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 2.93/0.97      | v1_funct_1(k2_funct_2(X0,sK2))
% 2.93/0.97      | ~ v1_funct_1(sK2) ),
% 2.93/0.97      inference(instantiation,[status(thm)],[c_14]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1542,plain,
% 2.93/0.97      ( v1_funct_2(sK2,X0,X0) != iProver_top
% 2.93/0.97      | v3_funct_2(sK2,X0,X0) != iProver_top
% 2.93/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.93/0.97      | v1_funct_1(k2_funct_2(X0,sK2)) = iProver_top
% 2.93/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_1541]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1544,plain,
% 2.93/0.97      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.97      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.93/0.97      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.93/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.97      inference(instantiation,[status(thm)],[c_1542]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_3713,plain,
% 2.93/0.97      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 2.93/0.97      inference(global_propositional_subsumption,
% 2.93/0.97                [status(thm)],
% 2.93/0.97                [c_3240,c_29,c_30,c_31,c_32,c_1544]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_3717,plain,
% 2.93/0.97      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.93/0.97      inference(light_normalisation,[status(thm)],[c_3713,c_3685]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_5754,plain,
% 2.93/0.97      ( v1_funct_1(X2) != iProver_top
% 2.93/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.93/0.97      | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 2.93/0.97      inference(global_propositional_subsumption,
% 2.93/0.97                [status(thm)],
% 2.93/0.97                [c_4032,c_3717]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_5755,plain,
% 2.93/0.97      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 2.93/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.93/0.97      | v1_funct_1(X2) != iProver_top ),
% 2.93/0.97      inference(renaming,[status(thm)],[c_5754]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_5766,plain,
% 2.93/0.97      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 2.93/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.97      inference(superposition,[status(thm)],[c_1226,c_5755]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_2,plain,
% 2.93/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.97      | v1_relat_1(X0) ),
% 2.93/0.97      inference(cnf_transformation,[],[f48]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1243,plain,
% 2.93/0.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.93/0.97      | v1_relat_1(X0) = iProver_top ),
% 2.93/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.93/0.97  
% 2.93/0.97  cnf(c_1883,plain,
% 2.93/0.97      ( v1_relat_1(sK2) = iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1226,c_1243]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1,plain,
% 2.93/0.98      ( ~ v1_relat_1(X0)
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v2_funct_1(X0)
% 2.93/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.93/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1244,plain,
% 2.93/0.98      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 2.93/0.98      | v1_relat_1(X0) != iProver_top
% 2.93/0.98      | v1_funct_1(X0) != iProver_top
% 2.93/0.98      | v2_funct_1(X0) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2377,plain,
% 2.93/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top
% 2.93/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1883,c_1244]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1441,plain,
% 2.93/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.93/0.98      | v1_relat_1(sK2) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_7,plain,
% 2.93/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | v2_funct_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1477,plain,
% 2.93/0.98      ( ~ v3_funct_2(sK2,X0,X1)
% 2.93/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/0.98      | ~ v1_funct_1(sK2)
% 2.93/0.98      | v2_funct_1(sK2) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1479,plain,
% 2.93/0.98      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.93/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.93/0.98      | ~ v1_funct_1(sK2)
% 2.93/0.98      | v2_funct_1(sK2) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_1477]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1628,plain,
% 2.93/0.98      ( ~ v1_relat_1(sK2)
% 2.93/0.98      | ~ v1_funct_1(sK2)
% 2.93/0.98      | ~ v2_funct_1(sK2)
% 2.93/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3088,plain,
% 2.93/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_2377,c_28,c_26,c_25,c_1441,c_1479,c_1628]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_23,plain,
% 2.93/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.93/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1228,plain,
% 2.93/0.98      ( k1_relset_1(X0,X0,X1) = X0
% 2.93/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 2.93/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.93/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2293,plain,
% 2.93/0.98      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 2.93/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1226,c_1228]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1242,plain,
% 2.93/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.93/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1981,plain,
% 2.93/0.98      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1226,c_1242]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2297,plain,
% 2.93/0.98      ( k1_relat_1(sK2) = sK1
% 2.93/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_2293,c_1981]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2973,plain,
% 2.93/0.98      ( k1_relat_1(sK2) = sK1 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_2297,c_29,c_30]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3090,plain,
% 2.93/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_3088,c_2973]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5774,plain,
% 2.93/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_5766,c_3090]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5857,plain,
% 2.93/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_5774,c_29]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4031,plain,
% 2.93/0.98      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 2.93/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.93/0.98      | v1_funct_1(X2) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1226,c_1230]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4406,plain,
% 2.93/0.98      ( v1_funct_1(X2) != iProver_top
% 2.93/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.93/0.98      | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_4031,c_29]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4407,plain,
% 2.93/0.98      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 2.93/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.93/0.98      | v1_funct_1(X2) != iProver_top ),
% 2.93/0.98      inference(renaming,[status(thm)],[c_4406]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4415,plain,
% 2.93/0.98      ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
% 2.93/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 2.93/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 2.93/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.93/0.98      | v1_funct_1(X1) != iProver_top
% 2.93/0.98      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1239,c_4407]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4859,plain,
% 2.93/0.98      ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
% 2.93/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 2.93/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 2.93/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 2.93/0.98      | v1_funct_1(X1) != iProver_top ),
% 2.93/0.98      inference(forward_subsumption_resolution,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_4415,c_1236]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4866,plain,
% 2.93/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2) = k5_relat_1(k2_funct_2(sK1,sK2),sK2)
% 2.93/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1226,c_4859]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_0,plain,
% 2.93/0.98      ( ~ v1_relat_1(X0)
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | ~ v2_funct_1(X0)
% 2.93/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.93/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1245,plain,
% 2.93/0.98      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 2.93/0.98      | v1_relat_1(X0) != iProver_top
% 2.93/0.98      | v1_funct_1(X0) != iProver_top
% 2.93/0.98      | v2_funct_1(X0) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2408,plain,
% 2.93/0.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top
% 2.93/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1883,c_1245]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_6,plain,
% 2.93/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 2.93/0.98      | v2_funct_2(X0,X2)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ v1_funct_1(X0) ),
% 2.93/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_10,plain,
% 2.93/0.98      ( ~ v2_funct_2(X0,X1)
% 2.93/0.98      | ~ v5_relat_1(X0,X1)
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | k2_relat_1(X0) = X1 ),
% 2.93/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_323,plain,
% 2.93/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 2.93/0.98      | ~ v5_relat_1(X3,X4)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ v1_relat_1(X3)
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | X3 != X0
% 2.93/0.98      | X4 != X2
% 2.93/0.98      | k2_relat_1(X3) = X4 ),
% 2.93/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_324,plain,
% 2.93/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 2.93/0.98      | ~ v5_relat_1(X0,X2)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ v1_relat_1(X0)
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | k2_relat_1(X0) = X2 ),
% 2.93/0.98      inference(unflattening,[status(thm)],[c_323]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_328,plain,
% 2.93/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ v5_relat_1(X0,X2)
% 2.93/0.98      | ~ v3_funct_2(X0,X1,X2)
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | k2_relat_1(X0) = X2 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_324,c_2]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_329,plain,
% 2.93/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 2.93/0.98      | ~ v5_relat_1(X0,X2)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | k2_relat_1(X0) = X2 ),
% 2.93/0.98      inference(renaming,[status(thm)],[c_328]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3,plain,
% 2.93/0.98      ( v5_relat_1(X0,X1)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.93/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_344,plain,
% 2.93/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 2.93/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.93/0.98      | ~ v1_funct_1(X0)
% 2.93/0.98      | k2_relat_1(X0) = X2 ),
% 2.93/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_329,c_3]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1222,plain,
% 2.93/0.98      ( k2_relat_1(X0) = X1
% 2.93/0.98      | v3_funct_2(X0,X2,X1) != iProver_top
% 2.93/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.93/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1769,plain,
% 2.93/0.98      ( k2_relat_1(sK2) = sK1
% 2.93/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_1226,c_1222]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1502,plain,
% 2.93/0.98      ( ~ v3_funct_2(sK2,X0,X1)
% 2.93/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/0.98      | ~ v1_funct_1(sK2)
% 2.93/0.98      | k2_relat_1(sK2) = X1 ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_344]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1504,plain,
% 2.93/0.98      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.93/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.93/0.98      | ~ v1_funct_1(sK2)
% 2.93/0.98      | k2_relat_1(sK2) = sK1 ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_1502]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2076,plain,
% 2.93/0.98      ( k2_relat_1(sK2) = sK1 ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_1769,c_28,c_26,c_25,c_1504]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_2412,plain,
% 2.93/0.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top
% 2.93/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_2408,c_2076]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1478,plain,
% 2.93/0.98      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 2.93/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top
% 2.93/0.98      | v2_funct_1(sK2) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1477]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1480,plain,
% 2.93/0.98      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top
% 2.93/0.98      | v2_funct_1(sK2) = iProver_top ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_1478]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3084,plain,
% 2.93/0.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_2412,c_29,c_31,c_32,c_1480]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4880,plain,
% 2.93/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.93/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.93/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_4866,c_3084,c_3685]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4419,plain,
% 2.93/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.93/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.93/0.98      inference(superposition,[status(thm)],[c_3839,c_4407]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4422,plain,
% 2.93/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.93/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.93/0.98      inference(light_normalisation,[status(thm)],[c_4419,c_3084]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4929,plain,
% 2.93/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_4880,c_3717,c_4422]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_24,negated_conjecture,
% 2.93/0.98      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.93/0.98      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.93/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1227,plain,
% 2.93/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.93/0.98      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_3688,plain,
% 2.93/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.93/0.98      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_3685,c_1227]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_4932,plain,
% 2.93/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
% 2.93/0.98      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_4929,c_3688]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_15,plain,
% 2.93/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.93/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_58,plain,
% 2.93/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_60,plain,
% 2.93/0.98      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_58]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5,plain,
% 2.93/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 2.93/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.93/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.93/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1511,plain,
% 2.93/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 2.93/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 2.93/0.98      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1934,plain,
% 2.93/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 2.93/0.98      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_1511]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1935,plain,
% 2.93/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 2.93/0.98      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 2.93/0.98      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_1937,plain,
% 2.93/0.98      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 2.93/0.98      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.93/0.98      inference(instantiation,[status(thm)],[c_1935]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5270,plain,
% 2.93/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.93/0.98      inference(global_propositional_subsumption,
% 2.93/0.98                [status(thm)],
% 2.93/0.98                [c_4932,c_60,c_1937]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(c_5860,plain,
% 2.93/0.98      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.93/0.98      inference(demodulation,[status(thm)],[c_5857,c_5270]) ).
% 2.93/0.98  
% 2.93/0.98  cnf(contradiction,plain,
% 2.93/0.98      ( $false ),
% 2.93/0.98      inference(minisat,[status(thm)],[c_5860,c_1937,c_60]) ).
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.93/0.98  
% 2.93/0.98  ------                               Statistics
% 2.93/0.98  
% 2.93/0.98  ------ General
% 2.93/0.98  
% 2.93/0.98  abstr_ref_over_cycles:                  0
% 2.93/0.98  abstr_ref_under_cycles:                 0
% 2.93/0.98  gc_basic_clause_elim:                   0
% 2.93/0.98  forced_gc_time:                         0
% 2.93/0.98  parsing_time:                           0.011
% 2.93/0.98  unif_index_cands_time:                  0.
% 2.93/0.98  unif_index_add_time:                    0.
% 2.93/0.98  orderings_time:                         0.
% 2.93/0.98  out_proof_time:                         0.014
% 2.93/0.98  total_time:                             0.283
% 2.93/0.98  num_of_symbols:                         53
% 2.93/0.98  num_of_terms:                           8432
% 2.93/0.98  
% 2.93/0.98  ------ Preprocessing
% 2.93/0.98  
% 2.93/0.98  num_of_splits:                          0
% 2.93/0.98  num_of_split_atoms:                     0
% 2.93/0.98  num_of_reused_defs:                     0
% 2.93/0.98  num_eq_ax_congr_red:                    28
% 2.93/0.98  num_of_sem_filtered_clauses:            1
% 2.93/0.98  num_of_subtypes:                        0
% 2.93/0.98  monotx_restored_types:                  0
% 2.93/0.98  sat_num_of_epr_types:                   0
% 2.93/0.98  sat_num_of_non_cyclic_types:            0
% 2.93/0.98  sat_guarded_non_collapsed_types:        0
% 2.93/0.98  num_pure_diseq_elim:                    0
% 2.93/0.98  simp_replaced_by:                       0
% 2.93/0.98  res_preprocessed:                       129
% 2.93/0.98  prep_upred:                             0
% 2.93/0.98  prep_unflattend:                        8
% 2.93/0.98  smt_new_axioms:                         0
% 2.93/0.98  pred_elim_cands:                        7
% 2.93/0.98  pred_elim:                              2
% 2.93/0.98  pred_elim_cl:                           4
% 2.93/0.98  pred_elim_cycles:                       6
% 2.93/0.98  merged_defs:                            0
% 2.93/0.98  merged_defs_ncl:                        0
% 2.93/0.98  bin_hyper_res:                          0
% 2.93/0.98  prep_cycles:                            4
% 2.93/0.98  pred_elim_time:                         0.007
% 2.93/0.98  splitting_time:                         0.
% 2.93/0.98  sem_filter_time:                        0.
% 2.93/0.98  monotx_time:                            0.001
% 2.93/0.98  subtype_inf_time:                       0.
% 2.93/0.98  
% 2.93/0.98  ------ Problem properties
% 2.93/0.98  
% 2.93/0.98  clauses:                                24
% 2.93/0.98  conjectures:                            5
% 2.93/0.98  epr:                                    3
% 2.93/0.98  horn:                                   24
% 2.93/0.98  ground:                                 5
% 2.93/0.98  unary:                                  9
% 2.93/0.98  binary:                                 3
% 2.93/0.98  lits:                                   68
% 2.93/0.98  lits_eq:                                7
% 2.93/0.98  fd_pure:                                0
% 2.93/0.98  fd_pseudo:                              0
% 2.93/0.98  fd_cond:                                0
% 2.93/0.98  fd_pseudo_cond:                         1
% 2.93/0.98  ac_symbols:                             0
% 2.93/0.98  
% 2.93/0.98  ------ Propositional Solver
% 2.93/0.98  
% 2.93/0.98  prop_solver_calls:                      28
% 2.93/0.98  prop_fast_solver_calls:                 1092
% 2.93/0.98  smt_solver_calls:                       0
% 2.93/0.98  smt_fast_solver_calls:                  0
% 2.93/0.98  prop_num_of_clauses:                    2290
% 2.93/0.98  prop_preprocess_simplified:             6080
% 2.93/0.98  prop_fo_subsumed:                       65
% 2.93/0.98  prop_solver_time:                       0.
% 2.93/0.98  smt_solver_time:                        0.
% 2.93/0.98  smt_fast_solver_time:                   0.
% 2.93/0.98  prop_fast_solver_time:                  0.
% 2.93/0.98  prop_unsat_core_time:                   0.
% 2.93/0.98  
% 2.93/0.98  ------ QBF
% 2.93/0.98  
% 2.93/0.98  qbf_q_res:                              0
% 2.93/0.98  qbf_num_tautologies:                    0
% 2.93/0.98  qbf_prep_cycles:                        0
% 2.93/0.98  
% 2.93/0.98  ------ BMC1
% 2.93/0.98  
% 2.93/0.98  bmc1_current_bound:                     -1
% 2.93/0.98  bmc1_last_solved_bound:                 -1
% 2.93/0.98  bmc1_unsat_core_size:                   -1
% 2.93/0.98  bmc1_unsat_core_parents_size:           -1
% 2.93/0.98  bmc1_merge_next_fun:                    0
% 2.93/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.93/0.98  
% 2.93/0.98  ------ Instantiation
% 2.93/0.98  
% 2.93/0.98  inst_num_of_clauses:                    628
% 2.93/0.98  inst_num_in_passive:                    243
% 2.93/0.98  inst_num_in_active:                     352
% 2.93/0.98  inst_num_in_unprocessed:                33
% 2.93/0.98  inst_num_of_loops:                      360
% 2.93/0.98  inst_num_of_learning_restarts:          0
% 2.93/0.98  inst_num_moves_active_passive:          4
% 2.93/0.98  inst_lit_activity:                      0
% 2.93/0.98  inst_lit_activity_moves:                0
% 2.93/0.98  inst_num_tautologies:                   0
% 2.93/0.98  inst_num_prop_implied:                  0
% 2.93/0.98  inst_num_existing_simplified:           0
% 2.93/0.98  inst_num_eq_res_simplified:             0
% 2.93/0.98  inst_num_child_elim:                    0
% 2.93/0.98  inst_num_of_dismatching_blockings:      243
% 2.93/0.98  inst_num_of_non_proper_insts:           498
% 2.93/0.98  inst_num_of_duplicates:                 0
% 2.93/0.98  inst_inst_num_from_inst_to_res:         0
% 2.93/0.98  inst_dismatching_checking_time:         0.
% 2.93/0.98  
% 2.93/0.98  ------ Resolution
% 2.93/0.98  
% 2.93/0.98  res_num_of_clauses:                     0
% 2.93/0.98  res_num_in_passive:                     0
% 2.93/0.98  res_num_in_active:                      0
% 2.93/0.98  res_num_of_loops:                       133
% 2.93/0.98  res_forward_subset_subsumed:            21
% 2.93/0.98  res_backward_subset_subsumed:           2
% 2.93/0.98  res_forward_subsumed:                   0
% 2.93/0.98  res_backward_subsumed:                  0
% 2.93/0.98  res_forward_subsumption_resolution:     1
% 2.93/0.98  res_backward_subsumption_resolution:    0
% 2.93/0.98  res_clause_to_clause_subsumption:       170
% 2.93/0.98  res_orphan_elimination:                 0
% 2.93/0.98  res_tautology_del:                      38
% 2.93/0.98  res_num_eq_res_simplified:              0
% 2.93/0.98  res_num_sel_changes:                    0
% 2.93/0.98  res_moves_from_active_to_pass:          0
% 2.93/0.98  
% 2.93/0.98  ------ Superposition
% 2.93/0.98  
% 2.93/0.98  sup_time_total:                         0.
% 2.93/0.98  sup_time_generating:                    0.
% 2.93/0.98  sup_time_sim_full:                      0.
% 2.93/0.98  sup_time_sim_immed:                     0.
% 2.93/0.98  
% 2.93/0.98  sup_num_of_clauses:                     102
% 2.93/0.98  sup_num_in_active:                      64
% 2.93/0.98  sup_num_in_passive:                     38
% 2.93/0.98  sup_num_of_loops:                       70
% 2.93/0.98  sup_fw_superposition:                   59
% 2.93/0.98  sup_bw_superposition:                   26
% 2.93/0.98  sup_immediate_simplified:               10
% 2.93/0.98  sup_given_eliminated:                   0
% 2.93/0.98  comparisons_done:                       0
% 2.93/0.98  comparisons_avoided:                    0
% 2.93/0.98  
% 2.93/0.98  ------ Simplifications
% 2.93/0.98  
% 2.93/0.98  
% 2.93/0.98  sim_fw_subset_subsumed:                 1
% 2.93/0.98  sim_bw_subset_subsumed:                 3
% 2.93/0.98  sim_fw_subsumed:                        0
% 2.93/0.98  sim_bw_subsumed:                        0
% 2.93/0.98  sim_fw_subsumption_res:                 3
% 2.93/0.98  sim_bw_subsumption_res:                 0
% 2.93/0.98  sim_tautology_del:                      0
% 2.93/0.98  sim_eq_tautology_del:                   0
% 2.93/0.98  sim_eq_res_simp:                        0
% 2.93/0.98  sim_fw_demodulated:                     3
% 2.93/0.98  sim_bw_demodulated:                     6
% 2.93/0.98  sim_light_normalised:                   10
% 2.93/0.98  sim_joinable_taut:                      0
% 2.93/0.98  sim_joinable_simp:                      0
% 2.93/0.98  sim_ac_normalised:                      0
% 2.93/0.98  sim_smt_subsumption:                    0
% 2.93/0.98  
%------------------------------------------------------------------------------
