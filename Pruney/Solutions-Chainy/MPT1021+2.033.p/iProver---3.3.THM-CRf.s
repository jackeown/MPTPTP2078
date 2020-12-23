%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:24 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 886 expanded)
%              Number of clauses        :  139 ( 324 expanded)
%              Number of leaves         :   23 ( 176 expanded)
%              Depth                    :   17
%              Number of atoms          :  690 (4141 expanded)
%              Number of equality atoms :  289 ( 525 expanded)
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

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f45,plain,
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

fof(f46,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f45])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f72,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f68])).

cnf(c_762,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1497,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_partfun1(X0_51)
    | k6_partfun1(X0_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_3178,plain,
    ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
    | X0_50 = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_4652,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3178])).

cnf(c_4656,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_4652])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_739,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1230,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_741,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1228,plain,
    ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_2198,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1228])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_753,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1216,plain,
    ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_1608,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1230,c_1216])).

cnf(c_2218,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2198,c_1608])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_28,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2821,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2218,c_27,c_28])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_754,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1215,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_1541,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1215])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_755,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1214,plain,
    ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_1722,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1214])).

cnf(c_24,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_797,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_800,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_751,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_809,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1872,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1722,c_26,c_24,c_23,c_797,c_800,c_809])).

cnf(c_2824,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2821,c_1872])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_742,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1227,plain,
    ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_2328,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1227])).

cnf(c_830,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_2554,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2328,c_26,c_25,c_24,c_23,c_830])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_750,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1219,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_2896,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2554,c_1219])).

cnf(c_29,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_811,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_813,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_760,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1460,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_1518,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_funct_2(X0_51,X2_50)
    | k2_funct_2(X0_51,X2_50) != X1_50 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1628,plain,
    ( X0_50 = k2_funct_2(X0_51,X1_50)
    | X0_50 != k2_funct_1(X1_50)
    | k2_funct_2(X0_51,X1_50) != k2_funct_1(X1_50) ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_1780,plain,
    ( k2_funct_2(X0_51,X0_50) != k2_funct_1(X0_50)
    | k2_funct_1(X0_50) = k2_funct_2(X0_51,X0_50)
    | k2_funct_1(X0_50) != k2_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_1782,plain,
    ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_funct_2(sK1,sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_758,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1781,plain,
    ( k2_funct_1(X0_50) = k2_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_1783,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1781])).

cnf(c_770,plain,
    ( ~ m1_subset_1(X0_50,X0_52)
    | m1_subset_1(X1_50,X1_52)
    | X1_52 != X0_52
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1440,plain,
    ( m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(k2_funct_2(X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
    | X0_50 != k2_funct_2(X0_51,X1_50) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_2129,plain,
    ( ~ m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_1(X0_50),X0_52)
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
    | k2_funct_1(X0_50) != k2_funct_2(X0_51,X0_50) ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_2787,plain,
    ( ~ m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_2788,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50)
    | m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2787])).

cnf(c_2790,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(sK2) != k2_funct_2(sK1,sK2)
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2788])).

cnf(c_3779,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2896,c_26,c_27,c_25,c_28,c_24,c_29,c_23,c_30,c_813,c_830,c_1460,c_1782,c_1783,c_2790])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1226,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_3190,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1226])).

cnf(c_3346,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3190,c_27])).

cnf(c_3347,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3346])).

cnf(c_3784,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3779,c_3347])).

cnf(c_812,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_747,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1222,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_2235,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1222])).

cnf(c_820,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_822,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_2471,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2235,c_27,c_28,c_29,c_30,c_822])).

cnf(c_2557,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2554,c_2471])).

cnf(c_2565,plain,
    ( v1_funct_1(k2_funct_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2557])).

cnf(c_2789,plain,
    ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(sK2) != k2_funct_2(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2787])).

cnf(c_3751,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_funct_1(X0_50))
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,k2_funct_1(X0_50)) = k5_relat_1(X0_50,k2_funct_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_3754,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3751])).

cnf(c_3881,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3784,c_26,c_25,c_24,c_23,c_812,c_830,c_1460,c_1782,c_1783,c_2565,c_2789,c_3754])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_740,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1229,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_2558,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2554,c_1229])).

cnf(c_3884,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3881,c_2558])).

cnf(c_4494,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2824,c_3884])).

cnf(c_771,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
    | X2_51 != X0_51
    | X3_51 != X1_51
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_2293,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
    | X2_51 != X0_51
    | X3_51 != X1_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
    | k6_partfun1(X8_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_3398,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
    | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
    | X3_51 != X0_51
    | X4_51 != X1_51
    | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
    | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_4285,plain,
    ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
    | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
    | X0_51 != X7_51
    | X1_51 != X8_51
    | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
    | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
    inference(instantiation,[status(thm)],[c_3398])).

cnf(c_4287,plain,
    ( X0_51 != X1_51
    | X2_51 != X3_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X8_51)
    | k6_partfun1(X9_51) != k6_partfun1(X8_51)
    | r2_relset_1(X0_51,X2_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50),k6_partfun1(X9_51)) = iProver_top
    | r2_relset_1(X1_51,X3_51,k6_partfun1(X8_51),k6_partfun1(X8_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4285])).

cnf(c_4289,plain,
    ( sK1 != sK1
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) = iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4287])).

cnf(c_3539,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_3542,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3539])).

cnf(c_763,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2156,plain,
    ( k2_relat_1(X0_50) != X0_51
    | sK1 != X0_51
    | sK1 = k2_relat_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_2157,plain,
    ( k2_relat_1(sK2) != sK1
    | sK1 = k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2156])).

cnf(c_765,plain,
    ( X0_51 != X1_51
    | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
    theory(equality)).

cnf(c_1478,plain,
    ( sK1 != X0_51
    | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_1974,plain,
    ( sK1 != k2_relat_1(X0_50)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_1975,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_746,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1223,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_5,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_752,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1217,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_1700,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1217])).

cnf(c_1718,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_1476,plain,
    ( X0_50 != X1_50
    | k6_partfun1(sK1) != X1_50
    | k6_partfun1(sK1) = X0_50 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1567,plain,
    ( X0_50 != k6_partfun1(X0_51)
    | k6_partfun1(sK1) = X0_50
    | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_1657,plain,
    ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_1658,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_6,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_301,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_302,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_2])).

cnf(c_307,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_306])).

cnf(c_3,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_322,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_307,c_3])).

cnf(c_735,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | k2_relat_1(X0_50) = X1_51 ),
    inference(subtyping,[status(esa)],[c_322])).

cnf(c_841,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_756,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_794,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_759,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_790,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_777,plain,
    ( sK1 != sK1
    | k6_partfun1(sK1) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4656,c_4494,c_4289,c_3542,c_2789,c_2565,c_2157,c_1975,c_1783,c_1782,c_1718,c_1658,c_1460,c_841,c_830,c_812,c_809,c_800,c_794,c_790,c_777,c_30,c_23,c_24,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.84/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/0.98  
% 2.84/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/0.98  
% 2.84/0.98  ------  iProver source info
% 2.84/0.98  
% 2.84/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.84/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/0.98  git: non_committed_changes: false
% 2.84/0.98  git: last_make_outside_of_git: false
% 2.84/0.98  
% 2.84/0.98  ------ 
% 2.84/0.98  
% 2.84/0.98  ------ Input Options
% 2.84/0.98  
% 2.84/0.98  --out_options                           all
% 2.84/0.98  --tptp_safe_out                         true
% 2.84/0.98  --problem_path                          ""
% 2.84/0.98  --include_path                          ""
% 2.84/0.98  --clausifier                            res/vclausify_rel
% 2.84/0.98  --clausifier_options                    --mode clausify
% 2.84/0.98  --stdin                                 false
% 2.84/0.98  --stats_out                             all
% 2.84/0.98  
% 2.84/0.98  ------ General Options
% 2.84/0.98  
% 2.84/0.98  --fof                                   false
% 2.84/0.98  --time_out_real                         305.
% 2.84/0.98  --time_out_virtual                      -1.
% 2.84/0.98  --symbol_type_check                     false
% 2.84/0.98  --clausify_out                          false
% 2.84/0.98  --sig_cnt_out                           false
% 2.84/0.98  --trig_cnt_out                          false
% 2.84/0.98  --trig_cnt_out_tolerance                1.
% 2.84/0.98  --trig_cnt_out_sk_spl                   false
% 2.84/0.98  --abstr_cl_out                          false
% 2.84/0.98  
% 2.84/0.98  ------ Global Options
% 2.84/0.98  
% 2.84/0.98  --schedule                              default
% 2.84/0.98  --add_important_lit                     false
% 2.84/0.98  --prop_solver_per_cl                    1000
% 2.84/0.98  --min_unsat_core                        false
% 2.84/0.98  --soft_assumptions                      false
% 2.84/0.98  --soft_lemma_size                       3
% 2.84/0.98  --prop_impl_unit_size                   0
% 2.84/0.98  --prop_impl_unit                        []
% 2.84/0.98  --share_sel_clauses                     true
% 2.84/0.98  --reset_solvers                         false
% 2.84/0.98  --bc_imp_inh                            [conj_cone]
% 2.84/0.98  --conj_cone_tolerance                   3.
% 2.84/0.98  --extra_neg_conj                        none
% 2.84/0.98  --large_theory_mode                     true
% 2.84/0.98  --prolific_symb_bound                   200
% 2.84/0.98  --lt_threshold                          2000
% 2.84/0.98  --clause_weak_htbl                      true
% 2.84/0.98  --gc_record_bc_elim                     false
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing Options
% 2.84/0.98  
% 2.84/0.98  --preprocessing_flag                    true
% 2.84/0.98  --time_out_prep_mult                    0.1
% 2.84/0.98  --splitting_mode                        input
% 2.84/0.98  --splitting_grd                         true
% 2.84/0.98  --splitting_cvd                         false
% 2.84/0.98  --splitting_cvd_svl                     false
% 2.84/0.98  --splitting_nvd                         32
% 2.84/0.98  --sub_typing                            true
% 2.84/0.98  --prep_gs_sim                           true
% 2.84/0.98  --prep_unflatten                        true
% 2.84/0.98  --prep_res_sim                          true
% 2.84/0.98  --prep_upred                            true
% 2.84/0.98  --prep_sem_filter                       exhaustive
% 2.84/0.98  --prep_sem_filter_out                   false
% 2.84/0.98  --pred_elim                             true
% 2.84/0.98  --res_sim_input                         true
% 2.84/0.98  --eq_ax_congr_red                       true
% 2.84/0.98  --pure_diseq_elim                       true
% 2.84/0.98  --brand_transform                       false
% 2.84/0.98  --non_eq_to_eq                          false
% 2.84/0.98  --prep_def_merge                        true
% 2.84/0.98  --prep_def_merge_prop_impl              false
% 2.84/0.98  --prep_def_merge_mbd                    true
% 2.84/0.98  --prep_def_merge_tr_red                 false
% 2.84/0.98  --prep_def_merge_tr_cl                  false
% 2.84/0.98  --smt_preprocessing                     true
% 2.84/0.98  --smt_ac_axioms                         fast
% 2.84/0.98  --preprocessed_out                      false
% 2.84/0.98  --preprocessed_stats                    false
% 2.84/0.98  
% 2.84/0.98  ------ Abstraction refinement Options
% 2.84/0.98  
% 2.84/0.98  --abstr_ref                             []
% 2.84/0.98  --abstr_ref_prep                        false
% 2.84/0.98  --abstr_ref_until_sat                   false
% 2.84/0.98  --abstr_ref_sig_restrict                funpre
% 2.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/0.98  --abstr_ref_under                       []
% 2.84/0.98  
% 2.84/0.98  ------ SAT Options
% 2.84/0.98  
% 2.84/0.98  --sat_mode                              false
% 2.84/0.98  --sat_fm_restart_options                ""
% 2.84/0.98  --sat_gr_def                            false
% 2.84/0.98  --sat_epr_types                         true
% 2.84/0.98  --sat_non_cyclic_types                  false
% 2.84/0.98  --sat_finite_models                     false
% 2.84/0.98  --sat_fm_lemmas                         false
% 2.84/0.98  --sat_fm_prep                           false
% 2.84/0.98  --sat_fm_uc_incr                        true
% 2.84/0.98  --sat_out_model                         small
% 2.84/0.98  --sat_out_clauses                       false
% 2.84/0.98  
% 2.84/0.98  ------ QBF Options
% 2.84/0.98  
% 2.84/0.98  --qbf_mode                              false
% 2.84/0.98  --qbf_elim_univ                         false
% 2.84/0.98  --qbf_dom_inst                          none
% 2.84/0.98  --qbf_dom_pre_inst                      false
% 2.84/0.98  --qbf_sk_in                             false
% 2.84/0.98  --qbf_pred_elim                         true
% 2.84/0.98  --qbf_split                             512
% 2.84/0.98  
% 2.84/0.98  ------ BMC1 Options
% 2.84/0.98  
% 2.84/0.98  --bmc1_incremental                      false
% 2.84/0.98  --bmc1_axioms                           reachable_all
% 2.84/0.98  --bmc1_min_bound                        0
% 2.84/0.98  --bmc1_max_bound                        -1
% 2.84/0.98  --bmc1_max_bound_default                -1
% 2.84/0.98  --bmc1_symbol_reachability              true
% 2.84/0.98  --bmc1_property_lemmas                  false
% 2.84/0.98  --bmc1_k_induction                      false
% 2.84/0.98  --bmc1_non_equiv_states                 false
% 2.84/0.98  --bmc1_deadlock                         false
% 2.84/0.98  --bmc1_ucm                              false
% 2.84/0.98  --bmc1_add_unsat_core                   none
% 2.84/0.98  --bmc1_unsat_core_children              false
% 2.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/0.98  --bmc1_out_stat                         full
% 2.84/0.98  --bmc1_ground_init                      false
% 2.84/0.98  --bmc1_pre_inst_next_state              false
% 2.84/0.98  --bmc1_pre_inst_state                   false
% 2.84/0.98  --bmc1_pre_inst_reach_state             false
% 2.84/0.98  --bmc1_out_unsat_core                   false
% 2.84/0.98  --bmc1_aig_witness_out                  false
% 2.84/0.98  --bmc1_verbose                          false
% 2.84/0.98  --bmc1_dump_clauses_tptp                false
% 2.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.84/0.98  --bmc1_dump_file                        -
% 2.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.84/0.98  --bmc1_ucm_extend_mode                  1
% 2.84/0.98  --bmc1_ucm_init_mode                    2
% 2.84/0.98  --bmc1_ucm_cone_mode                    none
% 2.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.84/0.98  --bmc1_ucm_relax_model                  4
% 2.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/0.98  --bmc1_ucm_layered_model                none
% 2.84/0.98  --bmc1_ucm_max_lemma_size               10
% 2.84/0.98  
% 2.84/0.98  ------ AIG Options
% 2.84/0.98  
% 2.84/0.98  --aig_mode                              false
% 2.84/0.98  
% 2.84/0.98  ------ Instantiation Options
% 2.84/0.98  
% 2.84/0.98  --instantiation_flag                    true
% 2.84/0.98  --inst_sos_flag                         false
% 2.84/0.98  --inst_sos_phase                        true
% 2.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel_side                     num_symb
% 2.84/0.98  --inst_solver_per_active                1400
% 2.84/0.98  --inst_solver_calls_frac                1.
% 2.84/0.98  --inst_passive_queue_type               priority_queues
% 2.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/0.98  --inst_passive_queues_freq              [25;2]
% 2.84/0.98  --inst_dismatching                      true
% 2.84/0.98  --inst_eager_unprocessed_to_passive     true
% 2.84/0.98  --inst_prop_sim_given                   true
% 2.84/0.98  --inst_prop_sim_new                     false
% 2.84/0.98  --inst_subs_new                         false
% 2.84/0.98  --inst_eq_res_simp                      false
% 2.84/0.98  --inst_subs_given                       false
% 2.84/0.98  --inst_orphan_elimination               true
% 2.84/0.98  --inst_learning_loop_flag               true
% 2.84/0.98  --inst_learning_start                   3000
% 2.84/0.98  --inst_learning_factor                  2
% 2.84/0.98  --inst_start_prop_sim_after_learn       3
% 2.84/0.98  --inst_sel_renew                        solver
% 2.84/0.98  --inst_lit_activity_flag                true
% 2.84/0.98  --inst_restr_to_given                   false
% 2.84/0.98  --inst_activity_threshold               500
% 2.84/0.98  --inst_out_proof                        true
% 2.84/0.98  
% 2.84/0.98  ------ Resolution Options
% 2.84/0.98  
% 2.84/0.98  --resolution_flag                       true
% 2.84/0.98  --res_lit_sel                           adaptive
% 2.84/0.98  --res_lit_sel_side                      none
% 2.84/0.98  --res_ordering                          kbo
% 2.84/0.98  --res_to_prop_solver                    active
% 2.84/0.98  --res_prop_simpl_new                    false
% 2.84/0.98  --res_prop_simpl_given                  true
% 2.84/0.98  --res_passive_queue_type                priority_queues
% 2.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/0.98  --res_passive_queues_freq               [15;5]
% 2.84/0.98  --res_forward_subs                      full
% 2.84/0.98  --res_backward_subs                     full
% 2.84/0.98  --res_forward_subs_resolution           true
% 2.84/0.98  --res_backward_subs_resolution          true
% 2.84/0.98  --res_orphan_elimination                true
% 2.84/0.98  --res_time_limit                        2.
% 2.84/0.98  --res_out_proof                         true
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Options
% 2.84/0.98  
% 2.84/0.98  --superposition_flag                    true
% 2.84/0.98  --sup_passive_queue_type                priority_queues
% 2.84/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.84/0.98  --demod_completeness_check              fast
% 2.84/0.98  --demod_use_ground                      true
% 2.84/0.98  --sup_to_prop_solver                    passive
% 2.84/0.98  --sup_prop_simpl_new                    true
% 2.84/0.98  --sup_prop_simpl_given                  true
% 2.84/0.98  --sup_fun_splitting                     false
% 2.84/0.98  --sup_smt_interval                      50000
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Simplification Setup
% 2.84/0.98  
% 2.84/0.98  --sup_indices_passive                   []
% 2.84/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_full_bw                           [BwDemod]
% 2.84/0.98  --sup_immed_triv                        [TrivRules]
% 2.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_immed_bw_main                     []
% 2.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  
% 2.84/0.98  ------ Combination Options
% 2.84/0.98  
% 2.84/0.98  --comb_res_mult                         3
% 2.84/0.98  --comb_sup_mult                         2
% 2.84/0.98  --comb_inst_mult                        10
% 2.84/0.98  
% 2.84/0.98  ------ Debug Options
% 2.84/0.98  
% 2.84/0.98  --dbg_backtrace                         false
% 2.84/0.98  --dbg_dump_prop_clauses                 false
% 2.84/0.98  --dbg_dump_prop_clauses_file            -
% 2.84/0.98  --dbg_out_stat                          false
% 2.84/0.98  ------ Parsing...
% 2.84/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.84/0.98  ------ Proving...
% 2.84/0.98  ------ Problem Properties 
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  clauses                                 22
% 2.84/0.98  conjectures                             5
% 2.84/0.98  EPR                                     3
% 2.84/0.98  Horn                                    22
% 2.84/0.98  unary                                   7
% 2.84/0.98  binary                                  3
% 2.84/0.98  lits                                    66
% 2.84/0.98  lits eq                                 7
% 2.84/0.98  fd_pure                                 0
% 2.84/0.98  fd_pseudo                               0
% 2.84/0.98  fd_cond                                 0
% 2.84/0.98  fd_pseudo_cond                          1
% 2.84/0.98  AC symbols                              0
% 2.84/0.98  
% 2.84/0.98  ------ Schedule dynamic 5 is on 
% 2.84/0.98  
% 2.84/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  ------ 
% 2.84/0.98  Current options:
% 2.84/0.98  ------ 
% 2.84/0.98  
% 2.84/0.98  ------ Input Options
% 2.84/0.98  
% 2.84/0.98  --out_options                           all
% 2.84/0.98  --tptp_safe_out                         true
% 2.84/0.98  --problem_path                          ""
% 2.84/0.98  --include_path                          ""
% 2.84/0.98  --clausifier                            res/vclausify_rel
% 2.84/0.98  --clausifier_options                    --mode clausify
% 2.84/0.98  --stdin                                 false
% 2.84/0.98  --stats_out                             all
% 2.84/0.98  
% 2.84/0.98  ------ General Options
% 2.84/0.98  
% 2.84/0.98  --fof                                   false
% 2.84/0.98  --time_out_real                         305.
% 2.84/0.98  --time_out_virtual                      -1.
% 2.84/0.98  --symbol_type_check                     false
% 2.84/0.98  --clausify_out                          false
% 2.84/0.98  --sig_cnt_out                           false
% 2.84/0.98  --trig_cnt_out                          false
% 2.84/0.98  --trig_cnt_out_tolerance                1.
% 2.84/0.98  --trig_cnt_out_sk_spl                   false
% 2.84/0.98  --abstr_cl_out                          false
% 2.84/0.98  
% 2.84/0.98  ------ Global Options
% 2.84/0.98  
% 2.84/0.98  --schedule                              default
% 2.84/0.98  --add_important_lit                     false
% 2.84/0.98  --prop_solver_per_cl                    1000
% 2.84/0.98  --min_unsat_core                        false
% 2.84/0.98  --soft_assumptions                      false
% 2.84/0.98  --soft_lemma_size                       3
% 2.84/0.98  --prop_impl_unit_size                   0
% 2.84/0.98  --prop_impl_unit                        []
% 2.84/0.98  --share_sel_clauses                     true
% 2.84/0.98  --reset_solvers                         false
% 2.84/0.98  --bc_imp_inh                            [conj_cone]
% 2.84/0.98  --conj_cone_tolerance                   3.
% 2.84/0.98  --extra_neg_conj                        none
% 2.84/0.98  --large_theory_mode                     true
% 2.84/0.98  --prolific_symb_bound                   200
% 2.84/0.98  --lt_threshold                          2000
% 2.84/0.98  --clause_weak_htbl                      true
% 2.84/0.98  --gc_record_bc_elim                     false
% 2.84/0.98  
% 2.84/0.98  ------ Preprocessing Options
% 2.84/0.98  
% 2.84/0.98  --preprocessing_flag                    true
% 2.84/0.98  --time_out_prep_mult                    0.1
% 2.84/0.98  --splitting_mode                        input
% 2.84/0.98  --splitting_grd                         true
% 2.84/0.98  --splitting_cvd                         false
% 2.84/0.98  --splitting_cvd_svl                     false
% 2.84/0.98  --splitting_nvd                         32
% 2.84/0.98  --sub_typing                            true
% 2.84/0.98  --prep_gs_sim                           true
% 2.84/0.98  --prep_unflatten                        true
% 2.84/0.98  --prep_res_sim                          true
% 2.84/0.98  --prep_upred                            true
% 2.84/0.98  --prep_sem_filter                       exhaustive
% 2.84/0.98  --prep_sem_filter_out                   false
% 2.84/0.98  --pred_elim                             true
% 2.84/0.98  --res_sim_input                         true
% 2.84/0.98  --eq_ax_congr_red                       true
% 2.84/0.98  --pure_diseq_elim                       true
% 2.84/0.98  --brand_transform                       false
% 2.84/0.98  --non_eq_to_eq                          false
% 2.84/0.98  --prep_def_merge                        true
% 2.84/0.98  --prep_def_merge_prop_impl              false
% 2.84/0.98  --prep_def_merge_mbd                    true
% 2.84/0.98  --prep_def_merge_tr_red                 false
% 2.84/0.98  --prep_def_merge_tr_cl                  false
% 2.84/0.98  --smt_preprocessing                     true
% 2.84/0.98  --smt_ac_axioms                         fast
% 2.84/0.98  --preprocessed_out                      false
% 2.84/0.98  --preprocessed_stats                    false
% 2.84/0.98  
% 2.84/0.98  ------ Abstraction refinement Options
% 2.84/0.98  
% 2.84/0.98  --abstr_ref                             []
% 2.84/0.98  --abstr_ref_prep                        false
% 2.84/0.98  --abstr_ref_until_sat                   false
% 2.84/0.98  --abstr_ref_sig_restrict                funpre
% 2.84/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/0.98  --abstr_ref_under                       []
% 2.84/0.98  
% 2.84/0.98  ------ SAT Options
% 2.84/0.98  
% 2.84/0.98  --sat_mode                              false
% 2.84/0.98  --sat_fm_restart_options                ""
% 2.84/0.98  --sat_gr_def                            false
% 2.84/0.98  --sat_epr_types                         true
% 2.84/0.98  --sat_non_cyclic_types                  false
% 2.84/0.98  --sat_finite_models                     false
% 2.84/0.98  --sat_fm_lemmas                         false
% 2.84/0.98  --sat_fm_prep                           false
% 2.84/0.98  --sat_fm_uc_incr                        true
% 2.84/0.98  --sat_out_model                         small
% 2.84/0.98  --sat_out_clauses                       false
% 2.84/0.98  
% 2.84/0.98  ------ QBF Options
% 2.84/0.98  
% 2.84/0.98  --qbf_mode                              false
% 2.84/0.98  --qbf_elim_univ                         false
% 2.84/0.98  --qbf_dom_inst                          none
% 2.84/0.98  --qbf_dom_pre_inst                      false
% 2.84/0.98  --qbf_sk_in                             false
% 2.84/0.98  --qbf_pred_elim                         true
% 2.84/0.98  --qbf_split                             512
% 2.84/0.98  
% 2.84/0.98  ------ BMC1 Options
% 2.84/0.98  
% 2.84/0.98  --bmc1_incremental                      false
% 2.84/0.98  --bmc1_axioms                           reachable_all
% 2.84/0.98  --bmc1_min_bound                        0
% 2.84/0.98  --bmc1_max_bound                        -1
% 2.84/0.98  --bmc1_max_bound_default                -1
% 2.84/0.98  --bmc1_symbol_reachability              true
% 2.84/0.98  --bmc1_property_lemmas                  false
% 2.84/0.98  --bmc1_k_induction                      false
% 2.84/0.98  --bmc1_non_equiv_states                 false
% 2.84/0.98  --bmc1_deadlock                         false
% 2.84/0.98  --bmc1_ucm                              false
% 2.84/0.98  --bmc1_add_unsat_core                   none
% 2.84/0.98  --bmc1_unsat_core_children              false
% 2.84/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/0.98  --bmc1_out_stat                         full
% 2.84/0.98  --bmc1_ground_init                      false
% 2.84/0.98  --bmc1_pre_inst_next_state              false
% 2.84/0.98  --bmc1_pre_inst_state                   false
% 2.84/0.98  --bmc1_pre_inst_reach_state             false
% 2.84/0.98  --bmc1_out_unsat_core                   false
% 2.84/0.98  --bmc1_aig_witness_out                  false
% 2.84/0.98  --bmc1_verbose                          false
% 2.84/0.98  --bmc1_dump_clauses_tptp                false
% 2.84/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.84/0.98  --bmc1_dump_file                        -
% 2.84/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.84/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.84/0.98  --bmc1_ucm_extend_mode                  1
% 2.84/0.98  --bmc1_ucm_init_mode                    2
% 2.84/0.98  --bmc1_ucm_cone_mode                    none
% 2.84/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.84/0.98  --bmc1_ucm_relax_model                  4
% 2.84/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.84/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/0.98  --bmc1_ucm_layered_model                none
% 2.84/0.98  --bmc1_ucm_max_lemma_size               10
% 2.84/0.98  
% 2.84/0.98  ------ AIG Options
% 2.84/0.98  
% 2.84/0.98  --aig_mode                              false
% 2.84/0.98  
% 2.84/0.98  ------ Instantiation Options
% 2.84/0.98  
% 2.84/0.98  --instantiation_flag                    true
% 2.84/0.98  --inst_sos_flag                         false
% 2.84/0.98  --inst_sos_phase                        true
% 2.84/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/0.98  --inst_lit_sel_side                     none
% 2.84/0.98  --inst_solver_per_active                1400
% 2.84/0.98  --inst_solver_calls_frac                1.
% 2.84/0.98  --inst_passive_queue_type               priority_queues
% 2.84/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/0.98  --inst_passive_queues_freq              [25;2]
% 2.84/0.98  --inst_dismatching                      true
% 2.84/0.98  --inst_eager_unprocessed_to_passive     true
% 2.84/0.98  --inst_prop_sim_given                   true
% 2.84/0.98  --inst_prop_sim_new                     false
% 2.84/0.98  --inst_subs_new                         false
% 2.84/0.98  --inst_eq_res_simp                      false
% 2.84/0.98  --inst_subs_given                       false
% 2.84/0.98  --inst_orphan_elimination               true
% 2.84/0.98  --inst_learning_loop_flag               true
% 2.84/0.98  --inst_learning_start                   3000
% 2.84/0.98  --inst_learning_factor                  2
% 2.84/0.98  --inst_start_prop_sim_after_learn       3
% 2.84/0.98  --inst_sel_renew                        solver
% 2.84/0.98  --inst_lit_activity_flag                true
% 2.84/0.98  --inst_restr_to_given                   false
% 2.84/0.98  --inst_activity_threshold               500
% 2.84/0.98  --inst_out_proof                        true
% 2.84/0.98  
% 2.84/0.98  ------ Resolution Options
% 2.84/0.98  
% 2.84/0.98  --resolution_flag                       false
% 2.84/0.98  --res_lit_sel                           adaptive
% 2.84/0.98  --res_lit_sel_side                      none
% 2.84/0.98  --res_ordering                          kbo
% 2.84/0.98  --res_to_prop_solver                    active
% 2.84/0.98  --res_prop_simpl_new                    false
% 2.84/0.98  --res_prop_simpl_given                  true
% 2.84/0.98  --res_passive_queue_type                priority_queues
% 2.84/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/0.98  --res_passive_queues_freq               [15;5]
% 2.84/0.98  --res_forward_subs                      full
% 2.84/0.98  --res_backward_subs                     full
% 2.84/0.98  --res_forward_subs_resolution           true
% 2.84/0.98  --res_backward_subs_resolution          true
% 2.84/0.98  --res_orphan_elimination                true
% 2.84/0.98  --res_time_limit                        2.
% 2.84/0.98  --res_out_proof                         true
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Options
% 2.84/0.98  
% 2.84/0.98  --superposition_flag                    true
% 2.84/0.98  --sup_passive_queue_type                priority_queues
% 2.84/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.84/0.98  --demod_completeness_check              fast
% 2.84/0.98  --demod_use_ground                      true
% 2.84/0.98  --sup_to_prop_solver                    passive
% 2.84/0.98  --sup_prop_simpl_new                    true
% 2.84/0.98  --sup_prop_simpl_given                  true
% 2.84/0.98  --sup_fun_splitting                     false
% 2.84/0.98  --sup_smt_interval                      50000
% 2.84/0.98  
% 2.84/0.98  ------ Superposition Simplification Setup
% 2.84/0.98  
% 2.84/0.98  --sup_indices_passive                   []
% 2.84/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_full_bw                           [BwDemod]
% 2.84/0.98  --sup_immed_triv                        [TrivRules]
% 2.84/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_immed_bw_main                     []
% 2.84/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/0.98  
% 2.84/0.98  ------ Combination Options
% 2.84/0.98  
% 2.84/0.98  --comb_res_mult                         3
% 2.84/0.98  --comb_sup_mult                         2
% 2.84/0.98  --comb_inst_mult                        10
% 2.84/0.98  
% 2.84/0.98  ------ Debug Options
% 2.84/0.98  
% 2.84/0.98  --dbg_backtrace                         false
% 2.84/0.98  --dbg_dump_prop_clauses                 false
% 2.84/0.98  --dbg_dump_prop_clauses_file            -
% 2.84/0.98  --dbg_out_stat                          false
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  ------ Proving...
% 2.84/0.98  
% 2.84/0.98  
% 2.84/0.98  % SZS status Theorem for theBenchmark.p
% 2.84/0.98  
% 2.84/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.84/0.98  
% 2.84/0.98  fof(f15,conjecture,(
% 2.84/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f16,negated_conjecture,(
% 2.84/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.84/0.98    inference(negated_conjecture,[],[f15])).
% 2.84/0.98  
% 2.84/0.98  fof(f40,plain,(
% 2.84/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.84/0.98    inference(ennf_transformation,[],[f16])).
% 2.84/0.98  
% 2.84/0.98  fof(f41,plain,(
% 2.84/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.84/0.98    inference(flattening,[],[f40])).
% 2.84/0.98  
% 2.84/0.98  fof(f45,plain,(
% 2.84/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 2.84/0.98    introduced(choice_axiom,[])).
% 2.84/0.98  
% 2.84/0.98  fof(f46,plain,(
% 2.84/0.98    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 2.84/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f45])).
% 2.84/0.98  
% 2.84/0.98  fof(f73,plain,(
% 2.84/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.84/0.98    inference(cnf_transformation,[],[f46])).
% 2.84/0.98  
% 2.84/0.98  fof(f14,axiom,(
% 2.84/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f38,plain,(
% 2.84/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.84/0.98    inference(ennf_transformation,[],[f14])).
% 2.84/0.98  
% 2.84/0.98  fof(f39,plain,(
% 2.84/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.84/0.98    inference(flattening,[],[f38])).
% 2.84/0.98  
% 2.84/0.98  fof(f69,plain,(
% 2.84/0.98    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f39])).
% 2.84/0.98  
% 2.84/0.98  fof(f4,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f25,plain,(
% 2.84/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.98    inference(ennf_transformation,[],[f4])).
% 2.84/0.98  
% 2.84/0.98  fof(f51,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f25])).
% 2.84/0.98  
% 2.84/0.98  fof(f70,plain,(
% 2.84/0.98    v1_funct_1(sK2)),
% 2.84/0.98    inference(cnf_transformation,[],[f46])).
% 2.84/0.98  
% 2.84/0.98  fof(f71,plain,(
% 2.84/0.98    v1_funct_2(sK2,sK1,sK1)),
% 2.84/0.98    inference(cnf_transformation,[],[f46])).
% 2.84/0.98  
% 2.84/0.98  fof(f2,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f23,plain,(
% 2.84/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.98    inference(ennf_transformation,[],[f2])).
% 2.84/0.98  
% 2.84/0.98  fof(f49,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f23])).
% 2.84/0.98  
% 2.84/0.98  fof(f1,axiom,(
% 2.84/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f21,plain,(
% 2.84/0.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.84/0.98    inference(ennf_transformation,[],[f1])).
% 2.84/0.98  
% 2.84/0.98  fof(f22,plain,(
% 2.84/0.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.84/0.98    inference(flattening,[],[f21])).
% 2.84/0.98  
% 2.84/0.98  fof(f47,plain,(
% 2.84/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f22])).
% 2.84/0.98  
% 2.84/0.98  fof(f13,axiom,(
% 2.84/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f68,plain,(
% 2.84/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f13])).
% 2.84/0.98  
% 2.84/0.98  fof(f76,plain,(
% 2.84/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/0.98    inference(definition_unfolding,[],[f47,f68])).
% 2.84/0.98  
% 2.84/0.98  fof(f72,plain,(
% 2.84/0.98    v3_funct_2(sK2,sK1,sK1)),
% 2.84/0.98    inference(cnf_transformation,[],[f46])).
% 2.84/0.98  
% 2.84/0.98  fof(f6,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f28,plain,(
% 2.84/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.98    inference(ennf_transformation,[],[f6])).
% 2.84/0.98  
% 2.84/0.98  fof(f29,plain,(
% 2.84/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.98    inference(flattening,[],[f28])).
% 2.84/0.98  
% 2.84/0.98  fof(f54,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f29])).
% 2.84/0.98  
% 2.84/0.98  fof(f12,axiom,(
% 2.84/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f36,plain,(
% 2.84/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.84/0.98    inference(ennf_transformation,[],[f12])).
% 2.84/0.98  
% 2.84/0.98  fof(f37,plain,(
% 2.84/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.84/0.98    inference(flattening,[],[f36])).
% 2.84/0.98  
% 2.84/0.98  fof(f67,plain,(
% 2.84/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f37])).
% 2.84/0.98  
% 2.84/0.98  fof(f8,axiom,(
% 2.84/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f32,plain,(
% 2.84/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.84/0.98    inference(ennf_transformation,[],[f8])).
% 2.84/0.98  
% 2.84/0.98  fof(f33,plain,(
% 2.84/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.84/0.98    inference(flattening,[],[f32])).
% 2.84/0.98  
% 2.84/0.98  fof(f61,plain,(
% 2.84/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f33])).
% 2.84/0.98  
% 2.84/0.98  fof(f11,axiom,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f34,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.84/0.98    inference(ennf_transformation,[],[f11])).
% 2.84/0.98  
% 2.84/0.98  fof(f35,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.84/0.98    inference(flattening,[],[f34])).
% 2.84/0.98  
% 2.84/0.98  fof(f66,plain,(
% 2.84/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f35])).
% 2.84/0.98  
% 2.84/0.98  fof(f58,plain,(
% 2.84/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f33])).
% 2.84/0.98  
% 2.84/0.98  fof(f74,plain,(
% 2.84/0.98    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 2.84/0.98    inference(cnf_transformation,[],[f46])).
% 2.84/0.98  
% 2.84/0.98  fof(f9,axiom,(
% 2.84/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f18,plain,(
% 2.84/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.84/0.98    inference(pure_predicate_removal,[],[f9])).
% 2.84/0.98  
% 2.84/0.98  fof(f62,plain,(
% 2.84/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f18])).
% 2.84/0.98  
% 2.84/0.98  fof(f5,axiom,(
% 2.84/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f26,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.84/0.98    inference(ennf_transformation,[],[f5])).
% 2.84/0.98  
% 2.84/0.98  fof(f27,plain,(
% 2.84/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.98    inference(flattening,[],[f26])).
% 2.84/0.98  
% 2.84/0.98  fof(f52,plain,(
% 2.84/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f27])).
% 2.84/0.98  
% 2.84/0.98  fof(f55,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f29])).
% 2.84/0.98  
% 2.84/0.98  fof(f7,axiom,(
% 2.84/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f30,plain,(
% 2.84/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.84/0.98    inference(ennf_transformation,[],[f7])).
% 2.84/0.98  
% 2.84/0.98  fof(f31,plain,(
% 2.84/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.84/0.98    inference(flattening,[],[f30])).
% 2.84/0.98  
% 2.84/0.98  fof(f42,plain,(
% 2.84/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.84/0.98    inference(nnf_transformation,[],[f31])).
% 2.84/0.98  
% 2.84/0.98  fof(f56,plain,(
% 2.84/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f42])).
% 2.84/0.98  
% 2.84/0.98  fof(f3,axiom,(
% 2.84/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.84/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.84/0.98  
% 2.84/0.98  fof(f20,plain,(
% 2.84/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.84/0.98    inference(pure_predicate_removal,[],[f3])).
% 2.84/0.98  
% 2.84/0.98  fof(f24,plain,(
% 2.84/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.84/0.98    inference(ennf_transformation,[],[f20])).
% 2.84/0.98  
% 2.84/0.98  fof(f50,plain,(
% 2.84/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.84/0.98    inference(cnf_transformation,[],[f24])).
% 2.84/0.98  
% 2.84/0.98  fof(f48,plain,(
% 2.84/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/0.98    inference(cnf_transformation,[],[f22])).
% 2.84/0.98  
% 2.84/0.98  fof(f75,plain,(
% 2.84/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.84/0.98    inference(definition_unfolding,[],[f48,f68])).
% 2.84/0.98  
% 2.84/0.98  cnf(c_762,plain,
% 2.84/0.98      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 2.84/0.98      theory(equality) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1497,plain,
% 2.84/0.98      ( X0_50 != X1_50
% 2.84/0.98      | X0_50 = k6_partfun1(X0_51)
% 2.84/0.98      | k6_partfun1(X0_51) != X1_50 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_762]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3178,plain,
% 2.84/0.98      ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
% 2.84/0.98      | X0_50 = k6_partfun1(sK1)
% 2.84/0.98      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_1497]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4652,plain,
% 2.84/0.98      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 2.84/0.98      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.84/0.98      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_3178]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4656,plain,
% 2.84/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 2.84/0.98      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.84/0.98      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_4652]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_23,negated_conjecture,
% 2.84/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.84/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_739,negated_conjecture,
% 2.84/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1230,plain,
% 2.84/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_21,plain,
% 2.84/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.84/0.98      | ~ v1_funct_1(X0)
% 2.84/0.98      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.84/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_741,plain,
% 2.84/0.98      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.84/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.84/0.98      | ~ v1_funct_1(X0_50)
% 2.84/0.98      | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_21]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1228,plain,
% 2.84/0.98      ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
% 2.84/0.98      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2198,plain,
% 2.84/0.98      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 2.84/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_1230,c_1228]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_753,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.84/0.98      | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1216,plain,
% 2.84/0.98      ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1608,plain,
% 2.84/0.98      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_1230,c_1216]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2218,plain,
% 2.84/0.98      ( k1_relat_1(sK2) = sK1
% 2.84/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_2198,c_1608]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_26,negated_conjecture,
% 2.84/0.98      ( v1_funct_1(sK2) ),
% 2.84/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_27,plain,
% 2.84/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_25,negated_conjecture,
% 2.84/0.98      ( v1_funct_2(sK2,sK1,sK1) ),
% 2.84/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_28,plain,
% 2.84/0.98      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2821,plain,
% 2.84/0.98      ( k1_relat_1(sK2) = sK1 ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_2218,c_27,c_28]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.98      | v1_relat_1(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_754,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.84/0.98      | v1_relat_1(X0_50) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1215,plain,
% 2.84/0.98      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.84/0.98      | v1_relat_1(X0_50) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1541,plain,
% 2.84/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_1230,c_1215]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1,plain,
% 2.84/0.98      ( ~ v1_relat_1(X0)
% 2.84/0.98      | ~ v1_funct_1(X0)
% 2.84/0.98      | ~ v2_funct_1(X0)
% 2.84/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.84/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_755,plain,
% 2.84/0.98      ( ~ v1_relat_1(X0_50)
% 2.84/0.98      | ~ v1_funct_1(X0_50)
% 2.84/0.98      | ~ v2_funct_1(X0_50)
% 2.84/0.98      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1214,plain,
% 2.84/0.98      ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
% 2.84/0.98      | v1_relat_1(X0_50) != iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.84/0.98      | v2_funct_1(X0_50) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1722,plain,
% 2.84/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top
% 2.84/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_1541,c_1214]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_24,negated_conjecture,
% 2.84/0.98      ( v3_funct_2(sK2,sK1,sK1) ),
% 2.84/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_797,plain,
% 2.84/0.98      ( ~ v1_relat_1(sK2)
% 2.84/0.98      | ~ v1_funct_1(sK2)
% 2.84/0.98      | ~ v2_funct_1(sK2)
% 2.84/0.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_755]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_800,plain,
% 2.84/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | v1_relat_1(sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_754]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_7,plain,
% 2.84/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.98      | ~ v1_funct_1(X0)
% 2.84/0.98      | v2_funct_1(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_751,plain,
% 2.84/0.98      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.84/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.84/0.98      | ~ v1_funct_1(X0_50)
% 2.84/0.98      | v2_funct_1(X0_50) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_809,plain,
% 2.84/0.98      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.84/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | ~ v1_funct_1(sK2)
% 2.84/0.98      | v2_funct_1(sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_751]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1872,plain,
% 2.84/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_1722,c_26,c_24,c_23,c_797,c_800,c_809]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2824,plain,
% 2.84/0.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_2821,c_1872]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_20,plain,
% 2.84/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 2.84/0.98      | ~ v3_funct_2(X0,X1,X1)
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.84/0.98      | ~ v1_funct_1(X0)
% 2.84/0.98      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_742,plain,
% 2.84/0.98      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.84/0.98      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.84/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.84/0.98      | ~ v1_funct_1(X0_50)
% 2.84/0.98      | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1227,plain,
% 2.84/0.98      ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
% 2.84/0.98      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2328,plain,
% 2.84/0.98      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 2.84/0.98      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_1230,c_1227]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_830,plain,
% 2.84/0.98      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.84/0.98      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.84/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | ~ v1_funct_1(sK2)
% 2.84/0.98      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_742]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2554,plain,
% 2.84/0.98      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_2328,c_26,c_25,c_24,c_23,c_830]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_11,plain,
% 2.84/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 2.84/0.98      | ~ v3_funct_2(X0,X1,X1)
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.84/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.84/0.98      | ~ v1_funct_1(X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_750,plain,
% 2.84/0.98      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.84/0.98      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.84/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.84/0.98      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.84/0.98      | ~ v1_funct_1(X0_50) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1219,plain,
% 2.84/0.98      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.84/0.98      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2896,plain,
% 2.84/0.98      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.84/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_2554,c_1219]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_29,plain,
% 2.84/0.98      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_30,plain,
% 2.84/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_811,plain,
% 2.84/0.98      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.84/0.98      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_813,plain,
% 2.84/0.98      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.84/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_811]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_760,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1460,plain,
% 2.84/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_760]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1518,plain,
% 2.84/0.98      ( X0_50 != X1_50
% 2.84/0.98      | X0_50 = k2_funct_2(X0_51,X2_50)
% 2.84/0.98      | k2_funct_2(X0_51,X2_50) != X1_50 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_762]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1628,plain,
% 2.84/0.98      ( X0_50 = k2_funct_2(X0_51,X1_50)
% 2.84/0.98      | X0_50 != k2_funct_1(X1_50)
% 2.84/0.98      | k2_funct_2(X0_51,X1_50) != k2_funct_1(X1_50) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_1518]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1780,plain,
% 2.84/0.98      ( k2_funct_2(X0_51,X0_50) != k2_funct_1(X0_50)
% 2.84/0.98      | k2_funct_1(X0_50) = k2_funct_2(X0_51,X0_50)
% 2.84/0.98      | k2_funct_1(X0_50) != k2_funct_1(X0_50) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_1628]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1782,plain,
% 2.84/0.98      ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
% 2.84/0.98      | k2_funct_1(sK2) = k2_funct_2(sK1,sK2)
% 2.84/0.98      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_1780]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_758,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1781,plain,
% 2.84/0.98      ( k2_funct_1(X0_50) = k2_funct_1(X0_50) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_758]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1783,plain,
% 2.84/0.98      ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_1781]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_770,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0_50,X0_52)
% 2.84/0.98      | m1_subset_1(X1_50,X1_52)
% 2.84/0.98      | X1_52 != X0_52
% 2.84/0.98      | X1_50 != X0_50 ),
% 2.84/0.98      theory(equality) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1440,plain,
% 2.84/0.98      ( m1_subset_1(X0_50,X0_52)
% 2.84/0.98      | ~ m1_subset_1(k2_funct_2(X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.84/0.98      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
% 2.84/0.98      | X0_50 != k2_funct_2(X0_51,X1_50) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_770]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2129,plain,
% 2.84/0.98      ( ~ m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.84/0.98      | m1_subset_1(k2_funct_1(X0_50),X0_52)
% 2.84/0.98      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
% 2.84/0.98      | k2_funct_1(X0_50) != k2_funct_2(X0_51,X0_50) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_1440]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2787,plain,
% 2.84/0.98      ( ~ m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 2.84/0.98      | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_2129]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2788,plain,
% 2.84/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 2.84/0.98      | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50)
% 2.84/0.98      | m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.84/0.98      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2790,plain,
% 2.84/0.98      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 2.84/0.98      | k2_funct_1(sK2) != k2_funct_2(sK1,sK2)
% 2.84/0.98      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.84/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_2788]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3779,plain,
% 2.84/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_2896,c_26,c_27,c_25,c_28,c_24,c_29,c_23,c_30,c_813,
% 2.84/0.98                 c_830,c_1460,c_1782,c_1783,c_2790]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_19,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.84/0.98      | ~ v1_funct_1(X0)
% 2.84/0.98      | ~ v1_funct_1(X3)
% 2.84/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.84/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_743,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.84/0.98      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.84/0.98      | ~ v1_funct_1(X0_50)
% 2.84/0.98      | ~ v1_funct_1(X1_50)
% 2.84/0.98      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_19]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1226,plain,
% 2.84/0.98      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 2.84/0.98      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.84/0.98      | v1_funct_1(X1_50) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3190,plain,
% 2.84/0.98      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_1230,c_1226]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3346,plain,
% 2.84/0.98      ( v1_funct_1(X0_50) != iProver_top
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.84/0.98      | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_3190,c_27]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3347,plain,
% 2.84/0.98      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top ),
% 2.84/0.98      inference(renaming,[status(thm)],[c_3346]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3784,plain,
% 2.84/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 2.84/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_3779,c_3347]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_812,plain,
% 2.84/0.98      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.84/0.98      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.84/0.98      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | ~ v1_funct_1(sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_750]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_14,plain,
% 2.84/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 2.84/0.98      | ~ v3_funct_2(X0,X1,X1)
% 2.84/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.84/0.98      | ~ v1_funct_1(X0)
% 2.84/0.98      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.84/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_747,plain,
% 2.84/0.98      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.84/0.98      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.84/0.98      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.84/0.98      | ~ v1_funct_1(X0_50)
% 2.84/0.98      | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_14]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1222,plain,
% 2.84/0.98      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.84/0.98      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2235,plain,
% 2.84/0.98      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(superposition,[status(thm)],[c_1230,c_1222]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_820,plain,
% 2.84/0.98      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.84/0.98      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.84/0.98      | v1_funct_1(X0_50) != iProver_top
% 2.84/0.98      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_822,plain,
% 2.84/0.98      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.84/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.84/0.98      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.84/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_820]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2471,plain,
% 2.84/0.98      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_2235,c_27,c_28,c_29,c_30,c_822]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2557,plain,
% 2.84/0.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_2554,c_2471]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2565,plain,
% 2.84/0.98      ( v1_funct_1(k2_funct_1(sK2)) ),
% 2.84/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2557]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2789,plain,
% 2.84/0.98      ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 2.84/0.98      | k2_funct_1(sK2) != k2_funct_2(sK1,sK2) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_2787]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3751,plain,
% 2.84/0.98      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.84/0.98      | ~ m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.84/0.98      | ~ v1_funct_1(X0_50)
% 2.84/0.98      | ~ v1_funct_1(k2_funct_1(X0_50))
% 2.84/0.98      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,k2_funct_1(X0_50)) = k5_relat_1(X0_50,k2_funct_1(X0_50)) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_743]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3754,plain,
% 2.84/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.98      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/0.98      | ~ v1_funct_1(sK2)
% 2.84/0.98      | k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_3751]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3881,plain,
% 2.84/0.98      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 2.84/0.98      inference(global_propositional_subsumption,
% 2.84/0.98                [status(thm)],
% 2.84/0.98                [c_3784,c_26,c_25,c_24,c_23,c_812,c_830,c_1460,c_1782,
% 2.84/0.98                 c_1783,c_2565,c_2789,c_3754]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_22,negated_conjecture,
% 2.84/0.98      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.84/0.98      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.84/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_740,negated_conjecture,
% 2.84/0.98      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.84/0.98      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.84/0.98      inference(subtyping,[status(esa)],[c_22]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_1229,plain,
% 2.84/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.84/0.98      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2558,plain,
% 2.84/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.84/0.98      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_2554,c_1229]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3884,plain,
% 2.84/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.84/0.98      | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_3881,c_2558]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4494,plain,
% 2.84/0.98      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.84/0.98      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.84/0.98      inference(demodulation,[status(thm)],[c_2824,c_3884]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_771,plain,
% 2.84/0.98      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 2.84/0.98      | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
% 2.84/0.98      | X2_51 != X0_51
% 2.84/0.98      | X3_51 != X1_51
% 2.84/0.98      | X2_50 != X0_50
% 2.84/0.98      | X3_50 != X1_50 ),
% 2.84/0.98      theory(equality) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_2293,plain,
% 2.84/0.98      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 2.84/0.98      | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
% 2.84/0.98      | X2_51 != X0_51
% 2.84/0.98      | X3_51 != X1_51
% 2.84/0.98      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
% 2.84/0.98      | k6_partfun1(X8_51) != X1_50 ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_771]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_3398,plain,
% 2.84/0.98      ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
% 2.84/0.98      | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
% 2.84/0.98      | X3_51 != X0_51
% 2.84/0.98      | X4_51 != X1_51
% 2.84/0.98      | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
% 2.84/0.98      | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_2293]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4285,plain,
% 2.84/0.98      ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
% 2.84/0.98      | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
% 2.84/0.98      | X0_51 != X7_51
% 2.84/0.98      | X1_51 != X8_51
% 2.84/0.98      | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
% 2.84/0.98      | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
% 2.84/0.98      inference(instantiation,[status(thm)],[c_3398]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4287,plain,
% 2.84/0.98      ( X0_51 != X1_51
% 2.84/0.98      | X2_51 != X3_51
% 2.84/0.98      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X8_51)
% 2.84/0.98      | k6_partfun1(X9_51) != k6_partfun1(X8_51)
% 2.84/0.98      | r2_relset_1(X0_51,X2_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50),k6_partfun1(X9_51)) = iProver_top
% 2.84/0.98      | r2_relset_1(X1_51,X3_51,k6_partfun1(X8_51),k6_partfun1(X8_51)) != iProver_top ),
% 2.84/0.98      inference(predicate_to_equality,[status(thm)],[c_4285]) ).
% 2.84/0.98  
% 2.84/0.98  cnf(c_4289,plain,
% 2.84/0.98      ( sK1 != sK1
% 2.84/0.98      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 2.84/0.98      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 2.84/0.98      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) = iProver_top
% 2.84/0.98      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_4287]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_3539,plain,
% 2.84/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.84/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.84/0.99      | ~ v1_funct_1(X0_50)
% 2.84/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/0.99      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_743]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_3542,plain,
% 2.84/0.99      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.84/0.99      | ~ v1_funct_1(sK2)
% 2.84/0.99      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_3539]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_763,plain,
% 2.84/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.84/0.99      theory(equality) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_2156,plain,
% 2.84/0.99      ( k2_relat_1(X0_50) != X0_51
% 2.84/0.99      | sK1 != X0_51
% 2.84/0.99      | sK1 = k2_relat_1(X0_50) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_763]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_2157,plain,
% 2.84/0.99      ( k2_relat_1(sK2) != sK1 | sK1 = k2_relat_1(sK2) | sK1 != sK1 ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_2156]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_765,plain,
% 2.84/0.99      ( X0_51 != X1_51 | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
% 2.84/0.99      theory(equality) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1478,plain,
% 2.84/0.99      ( sK1 != X0_51 | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_765]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1974,plain,
% 2.84/0.99      ( sK1 != k2_relat_1(X0_50)
% 2.84/0.99      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_1478]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1975,plain,
% 2.84/0.99      ( sK1 != k2_relat_1(sK2)
% 2.84/0.99      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_15,plain,
% 2.84/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.84/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_746,plain,
% 2.84/0.99      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 2.84/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1223,plain,
% 2.84/0.99      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 2.84/0.99      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_5,plain,
% 2.84/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.84/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.84/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.84/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_752,plain,
% 2.84/0.99      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
% 2.84/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.84/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 2.84/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1217,plain,
% 2.84/0.99      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
% 2.84/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.84/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.84/0.99      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1700,plain,
% 2.84/0.99      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
% 2.84/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
% 2.84/0.99      inference(superposition,[status(thm)],[c_1223,c_1217]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1718,plain,
% 2.84/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 2.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_1700]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1476,plain,
% 2.84/0.99      ( X0_50 != X1_50
% 2.84/0.99      | k6_partfun1(sK1) != X1_50
% 2.84/0.99      | k6_partfun1(sK1) = X0_50 ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_762]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1567,plain,
% 2.84/0.99      ( X0_50 != k6_partfun1(X0_51)
% 2.84/0.99      | k6_partfun1(sK1) = X0_50
% 2.84/0.99      | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_1476]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1657,plain,
% 2.84/0.99      ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
% 2.84/0.99      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
% 2.84/0.99      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_1567]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_1658,plain,
% 2.84/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
% 2.84/0.99      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.84/0.99      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_1657]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_6,plain,
% 2.84/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.84/0.99      | v2_funct_2(X0,X2)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.99      | ~ v1_funct_1(X0) ),
% 2.84/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_10,plain,
% 2.84/0.99      ( ~ v2_funct_2(X0,X1)
% 2.84/0.99      | ~ v5_relat_1(X0,X1)
% 2.84/0.99      | ~ v1_relat_1(X0)
% 2.84/0.99      | k2_relat_1(X0) = X1 ),
% 2.84/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_301,plain,
% 2.84/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.84/0.99      | ~ v5_relat_1(X3,X4)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.99      | ~ v1_relat_1(X3)
% 2.84/0.99      | ~ v1_funct_1(X0)
% 2.84/0.99      | X3 != X0
% 2.84/0.99      | X4 != X2
% 2.84/0.99      | k2_relat_1(X3) = X4 ),
% 2.84/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_302,plain,
% 2.84/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.84/0.99      | ~ v5_relat_1(X0,X2)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.99      | ~ v1_relat_1(X0)
% 2.84/0.99      | ~ v1_funct_1(X0)
% 2.84/0.99      | k2_relat_1(X0) = X2 ),
% 2.84/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_306,plain,
% 2.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.99      | ~ v5_relat_1(X0,X2)
% 2.84/0.99      | ~ v3_funct_2(X0,X1,X2)
% 2.84/0.99      | ~ v1_funct_1(X0)
% 2.84/0.99      | k2_relat_1(X0) = X2 ),
% 2.84/0.99      inference(global_propositional_subsumption,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_302,c_2]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_307,plain,
% 2.84/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.84/0.99      | ~ v5_relat_1(X0,X2)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.99      | ~ v1_funct_1(X0)
% 2.84/0.99      | k2_relat_1(X0) = X2 ),
% 2.84/0.99      inference(renaming,[status(thm)],[c_306]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_3,plain,
% 2.84/0.99      ( v5_relat_1(X0,X1)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.84/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_322,plain,
% 2.84/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.84/0.99      | ~ v1_funct_1(X0)
% 2.84/0.99      | k2_relat_1(X0) = X2 ),
% 2.84/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_307,c_3]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_735,plain,
% 2.84/0.99      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.84/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.84/0.99      | ~ v1_funct_1(X0_50)
% 2.84/0.99      | k2_relat_1(X0_50) = X1_51 ),
% 2.84/0.99      inference(subtyping,[status(esa)],[c_322]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_841,plain,
% 2.84/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.84/0.99      | ~ v1_funct_1(sK2)
% 2.84/0.99      | k2_relat_1(sK2) = sK1 ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_735]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_0,plain,
% 2.84/0.99      ( ~ v1_relat_1(X0)
% 2.84/0.99      | ~ v1_funct_1(X0)
% 2.84/0.99      | ~ v2_funct_1(X0)
% 2.84/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.84/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_756,plain,
% 2.84/0.99      ( ~ v1_relat_1(X0_50)
% 2.84/0.99      | ~ v1_funct_1(X0_50)
% 2.84/0.99      | ~ v2_funct_1(X0_50)
% 2.84/0.99      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.84/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_794,plain,
% 2.84/0.99      ( ~ v1_relat_1(sK2)
% 2.84/0.99      | ~ v1_funct_1(sK2)
% 2.84/0.99      | ~ v2_funct_1(sK2)
% 2.84/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_756]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_759,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_790,plain,
% 2.84/0.99      ( sK1 = sK1 ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_759]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(c_777,plain,
% 2.84/0.99      ( sK1 != sK1 | k6_partfun1(sK1) = k6_partfun1(sK1) ),
% 2.84/0.99      inference(instantiation,[status(thm)],[c_765]) ).
% 2.84/0.99  
% 2.84/0.99  cnf(contradiction,plain,
% 2.84/0.99      ( $false ),
% 2.84/0.99      inference(minisat,
% 2.84/0.99                [status(thm)],
% 2.84/0.99                [c_4656,c_4494,c_4289,c_3542,c_2789,c_2565,c_2157,c_1975,
% 2.84/0.99                 c_1783,c_1782,c_1718,c_1658,c_1460,c_841,c_830,c_812,
% 2.84/0.99                 c_809,c_800,c_794,c_790,c_777,c_30,c_23,c_24,c_25,c_26]) ).
% 2.84/0.99  
% 2.84/0.99  
% 2.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.84/0.99  
% 2.84/0.99  ------                               Statistics
% 2.84/0.99  
% 2.84/0.99  ------ General
% 2.84/0.99  
% 2.84/0.99  abstr_ref_over_cycles:                  0
% 2.84/0.99  abstr_ref_under_cycles:                 0
% 2.84/0.99  gc_basic_clause_elim:                   0
% 2.84/0.99  forced_gc_time:                         0
% 2.84/0.99  parsing_time:                           0.009
% 2.84/0.99  unif_index_cands_time:                  0.
% 2.84/0.99  unif_index_add_time:                    0.
% 2.84/0.99  orderings_time:                         0.
% 2.84/0.99  out_proof_time:                         0.013
% 2.84/0.99  total_time:                             0.185
% 2.84/0.99  num_of_symbols:                         57
% 2.84/0.99  num_of_terms:                           4230
% 2.84/0.99  
% 2.84/0.99  ------ Preprocessing
% 2.84/0.99  
% 2.84/0.99  num_of_splits:                          0
% 2.84/0.99  num_of_split_atoms:                     0
% 2.84/0.99  num_of_reused_defs:                     0
% 2.84/0.99  num_eq_ax_congr_red:                    28
% 2.84/0.99  num_of_sem_filtered_clauses:            1
% 2.84/0.99  num_of_subtypes:                        4
% 2.84/0.99  monotx_restored_types:                  1
% 2.84/0.99  sat_num_of_epr_types:                   0
% 2.84/0.99  sat_num_of_non_cyclic_types:            0
% 2.84/0.99  sat_guarded_non_collapsed_types:        0
% 2.84/0.99  num_pure_diseq_elim:                    0
% 2.84/0.99  simp_replaced_by:                       0
% 2.84/0.99  res_preprocessed:                       129
% 2.84/0.99  prep_upred:                             0
% 2.84/0.99  prep_unflattend:                        8
% 2.84/0.99  smt_new_axioms:                         0
% 2.84/0.99  pred_elim_cands:                        7
% 2.84/0.99  pred_elim:                              2
% 2.84/0.99  pred_elim_cl:                           4
% 2.84/0.99  pred_elim_cycles:                       6
% 2.84/0.99  merged_defs:                            0
% 2.84/0.99  merged_defs_ncl:                        0
% 2.84/0.99  bin_hyper_res:                          0
% 2.84/0.99  prep_cycles:                            4
% 2.84/0.99  pred_elim_time:                         0.005
% 2.84/0.99  splitting_time:                         0.
% 2.84/0.99  sem_filter_time:                        0.
% 2.84/0.99  monotx_time:                            0.001
% 2.84/0.99  subtype_inf_time:                       0.002
% 2.84/0.99  
% 2.84/0.99  ------ Problem properties
% 2.84/0.99  
% 2.84/0.99  clauses:                                22
% 2.84/0.99  conjectures:                            5
% 2.84/0.99  epr:                                    3
% 2.84/0.99  horn:                                   22
% 2.84/0.99  ground:                                 5
% 2.84/0.99  unary:                                  7
% 2.84/0.99  binary:                                 3
% 2.84/0.99  lits:                                   66
% 2.84/0.99  lits_eq:                                7
% 2.84/0.99  fd_pure:                                0
% 2.84/0.99  fd_pseudo:                              0
% 2.84/0.99  fd_cond:                                0
% 2.84/0.99  fd_pseudo_cond:                         1
% 2.84/0.99  ac_symbols:                             0
% 2.84/0.99  
% 2.84/0.99  ------ Propositional Solver
% 2.84/0.99  
% 2.84/0.99  prop_solver_calls:                      29
% 2.84/0.99  prop_fast_solver_calls:                 1023
% 2.84/0.99  smt_solver_calls:                       0
% 2.84/0.99  smt_fast_solver_calls:                  0
% 2.84/0.99  prop_num_of_clauses:                    1327
% 2.84/0.99  prop_preprocess_simplified:             5155
% 2.84/0.99  prop_fo_subsumed:                       41
% 2.84/0.99  prop_solver_time:                       0.
% 2.84/0.99  smt_solver_time:                        0.
% 2.84/0.99  smt_fast_solver_time:                   0.
% 2.84/0.99  prop_fast_solver_time:                  0.
% 2.84/0.99  prop_unsat_core_time:                   0.
% 2.84/0.99  
% 2.84/0.99  ------ QBF
% 2.84/0.99  
% 2.84/0.99  qbf_q_res:                              0
% 2.84/0.99  qbf_num_tautologies:                    0
% 2.84/0.99  qbf_prep_cycles:                        0
% 2.84/0.99  
% 2.84/0.99  ------ BMC1
% 2.84/0.99  
% 2.84/0.99  bmc1_current_bound:                     -1
% 2.84/0.99  bmc1_last_solved_bound:                 -1
% 2.84/0.99  bmc1_unsat_core_size:                   -1
% 2.84/0.99  bmc1_unsat_core_parents_size:           -1
% 2.84/0.99  bmc1_merge_next_fun:                    0
% 2.84/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.84/0.99  
% 2.84/0.99  ------ Instantiation
% 2.84/0.99  
% 2.84/0.99  inst_num_of_clauses:                    425
% 2.84/0.99  inst_num_in_passive:                    69
% 2.84/0.99  inst_num_in_active:                     270
% 2.84/0.99  inst_num_in_unprocessed:                85
% 2.84/0.99  inst_num_of_loops:                      295
% 2.84/0.99  inst_num_of_learning_restarts:          0
% 2.84/0.99  inst_num_moves_active_passive:          20
% 2.84/0.99  inst_lit_activity:                      0
% 2.84/0.99  inst_lit_activity_moves:                0
% 2.84/0.99  inst_num_tautologies:                   0
% 2.84/0.99  inst_num_prop_implied:                  0
% 2.84/0.99  inst_num_existing_simplified:           0
% 2.84/0.99  inst_num_eq_res_simplified:             0
% 2.84/0.99  inst_num_child_elim:                    0
% 2.84/0.99  inst_num_of_dismatching_blockings:      420
% 2.84/0.99  inst_num_of_non_proper_insts:           632
% 2.84/0.99  inst_num_of_duplicates:                 0
% 2.84/0.99  inst_inst_num_from_inst_to_res:         0
% 2.84/0.99  inst_dismatching_checking_time:         0.
% 2.84/0.99  
% 2.84/0.99  ------ Resolution
% 2.84/0.99  
% 2.84/0.99  res_num_of_clauses:                     0
% 2.84/0.99  res_num_in_passive:                     0
% 2.84/0.99  res_num_in_active:                      0
% 2.84/0.99  res_num_of_loops:                       133
% 2.84/0.99  res_forward_subset_subsumed:            94
% 2.84/0.99  res_backward_subset_subsumed:           4
% 2.84/0.99  res_forward_subsumed:                   0
% 2.84/0.99  res_backward_subsumed:                  0
% 2.84/0.99  res_forward_subsumption_resolution:     1
% 2.84/0.99  res_backward_subsumption_resolution:    0
% 2.84/0.99  res_clause_to_clause_subsumption:       171
% 2.84/0.99  res_orphan_elimination:                 0
% 2.84/0.99  res_tautology_del:                      82
% 2.84/0.99  res_num_eq_res_simplified:              0
% 2.84/0.99  res_num_sel_changes:                    0
% 2.84/0.99  res_moves_from_active_to_pass:          0
% 2.84/0.99  
% 2.84/0.99  ------ Superposition
% 2.84/0.99  
% 2.84/0.99  sup_time_total:                         0.
% 2.84/0.99  sup_time_generating:                    0.
% 2.84/0.99  sup_time_sim_full:                      0.
% 2.84/0.99  sup_time_sim_immed:                     0.
% 2.84/0.99  
% 2.84/0.99  sup_num_of_clauses:                     94
% 2.84/0.99  sup_num_in_active:                      49
% 2.84/0.99  sup_num_in_passive:                     45
% 2.84/0.99  sup_num_of_loops:                       58
% 2.84/0.99  sup_fw_superposition:                   53
% 2.84/0.99  sup_bw_superposition:                   25
% 2.84/0.99  sup_immediate_simplified:               10
% 2.84/0.99  sup_given_eliminated:                   0
% 2.84/0.99  comparisons_done:                       0
% 2.84/0.99  comparisons_avoided:                    0
% 2.84/0.99  
% 2.84/0.99  ------ Simplifications
% 2.84/0.99  
% 2.84/0.99  
% 2.84/0.99  sim_fw_subset_subsumed:                 0
% 2.84/0.99  sim_bw_subset_subsumed:                 2
% 2.84/0.99  sim_fw_subsumed:                        2
% 2.84/0.99  sim_bw_subsumed:                        0
% 2.84/0.99  sim_fw_subsumption_res:                 1
% 2.84/0.99  sim_bw_subsumption_res:                 0
% 2.84/0.99  sim_tautology_del:                      0
% 2.84/0.99  sim_eq_tautology_del:                   1
% 2.84/0.99  sim_eq_res_simp:                        0
% 2.84/0.99  sim_fw_demodulated:                     3
% 2.84/0.99  sim_bw_demodulated:                     9
% 2.84/0.99  sim_light_normalised:                   3
% 2.84/0.99  sim_joinable_taut:                      0
% 2.84/0.99  sim_joinable_simp:                      0
% 2.84/0.99  sim_ac_normalised:                      0
% 2.84/0.99  sim_smt_subsumption:                    0
% 2.84/0.99  
%------------------------------------------------------------------------------
