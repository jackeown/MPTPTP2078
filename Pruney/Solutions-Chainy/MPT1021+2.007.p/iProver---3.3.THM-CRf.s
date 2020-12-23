%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:18 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  171 (2290 expanded)
%              Number of clauses        :  110 ( 617 expanded)
%              Number of leaves         :   14 ( 467 expanded)
%              Depth                    :   21
%              Number of atoms          :  552 (11274 expanded)
%              Number of equality atoms :  240 (1047 expanded)
%              Maximal formula depth    :   12 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f45])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
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
    inference(definition_unfolding,[],[f50,f68])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1107,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2200,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1107])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_24,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1484,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1486,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_2840,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2200,c_26,c_25,c_24,c_23,c_1486])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1117,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3733,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2840,c_1117])).

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

cnf(c_4623,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3733,c_27,c_28,c_29,c_30])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1120,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4633,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4623,c_1120])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1106,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4639,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4623,c_1106])).

cnf(c_4688,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4633,c_4639])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1114,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3187,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1114])).

cnf(c_3192,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3187,c_2840])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1115,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3228,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1115])).

cnf(c_3233,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3228,c_2840])).

cnf(c_6557,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4688,c_27,c_28,c_29,c_3192,c_3233])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1118,plain,
    ( v3_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4629,plain,
    ( v3_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4623,c_1118])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1116,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3295,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1116])).

cnf(c_3300,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3295,c_2840])).

cnf(c_5676,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4629,c_27,c_28,c_29,c_3192,c_3300])).

cnf(c_3668,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3192,c_27,c_28,c_29])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1123,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3674,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3668,c_1123])).

cnf(c_1101,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1122,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2309,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1122])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1335,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1358,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1395,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1397,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_2737,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2309,c_26,c_24,c_23,c_1335,c_1358,c_1397])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1124,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2419,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1124])).

cnf(c_1366,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2836,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2419,c_26,c_24,c_23,c_1335,c_1366,c_1397])).

cnf(c_3683,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3674,c_2737,c_2836])).

cnf(c_5681,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5676,c_3683])).

cnf(c_1121,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4630,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4623,c_1121])).

cnf(c_5784,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5681,c_27,c_28,c_29,c_3192,c_3300,c_3683,c_4629,c_4630])).

cnf(c_6563,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_6557,c_5784])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1108,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4637,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4623,c_1108])).

cnf(c_5846,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4637,c_27,c_28,c_29,c_3192])).

cnf(c_5847,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5846])).

cnf(c_5858,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_5847])).

cnf(c_2332,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1101,c_1123])).

cnf(c_2008,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1104,c_1120])).

cnf(c_1581,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1106])).

cnf(c_1439,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(X0,X0,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1441,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_1439])).

cnf(c_1959,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1581,c_26,c_25,c_23,c_1441])).

cnf(c_2010,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2008,c_1959])).

cnf(c_2336,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2332,c_2010])).

cnf(c_1336,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1335])).

cnf(c_1396,plain,
    ( v3_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1395])).

cnf(c_1398,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1396])).

cnf(c_2907,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2336,c_27,c_29,c_30,c_1336,c_1398])).

cnf(c_5866,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5858,c_2907])).

cnf(c_5991,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5866,c_27])).

cnf(c_3033,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1108])).

cnf(c_3462,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3033,c_27])).

cnf(c_3463,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3462])).

cnf(c_4631,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4623,c_3463])).

cnf(c_4702,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4631,c_2836])).

cnf(c_4728,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4702,c_27,c_28,c_29,c_3192])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1105,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2843,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2840,c_1105])).

cnf(c_4731,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4728,c_2843])).

cnf(c_5994,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5991,c_4731])).

cnf(c_14,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_53,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_55,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_7,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1419,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1851,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_1852,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1851])).

cnf(c_1854,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_6433,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5994,c_55,c_1854])).

cnf(c_6576,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6563,c_6433])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6576,c_1854,c_55])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:03:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.20/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.98  
% 3.20/0.98  ------  iProver source info
% 3.20/0.98  
% 3.20/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.98  git: non_committed_changes: false
% 3.20/0.98  git: last_make_outside_of_git: false
% 3.20/0.98  
% 3.20/0.98  ------ 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options
% 3.20/0.98  
% 3.20/0.98  --out_options                           all
% 3.20/0.98  --tptp_safe_out                         true
% 3.20/0.98  --problem_path                          ""
% 3.20/0.98  --include_path                          ""
% 3.20/0.98  --clausifier                            res/vclausify_rel
% 3.20/0.98  --clausifier_options                    --mode clausify
% 3.20/0.98  --stdin                                 false
% 3.20/0.98  --stats_out                             all
% 3.20/0.98  
% 3.20/0.98  ------ General Options
% 3.20/0.98  
% 3.20/0.98  --fof                                   false
% 3.20/0.98  --time_out_real                         305.
% 3.20/0.98  --time_out_virtual                      -1.
% 3.20/0.98  --symbol_type_check                     false
% 3.20/0.98  --clausify_out                          false
% 3.20/0.98  --sig_cnt_out                           false
% 3.20/0.98  --trig_cnt_out                          false
% 3.20/0.98  --trig_cnt_out_tolerance                1.
% 3.20/0.98  --trig_cnt_out_sk_spl                   false
% 3.20/0.98  --abstr_cl_out                          false
% 3.20/0.98  
% 3.20/0.98  ------ Global Options
% 3.20/0.98  
% 3.20/0.98  --schedule                              default
% 3.20/0.98  --add_important_lit                     false
% 3.20/0.98  --prop_solver_per_cl                    1000
% 3.20/0.98  --min_unsat_core                        false
% 3.20/0.98  --soft_assumptions                      false
% 3.20/0.98  --soft_lemma_size                       3
% 3.20/0.98  --prop_impl_unit_size                   0
% 3.20/0.98  --prop_impl_unit                        []
% 3.20/0.98  --share_sel_clauses                     true
% 3.20/0.98  --reset_solvers                         false
% 3.20/0.98  --bc_imp_inh                            [conj_cone]
% 3.20/0.98  --conj_cone_tolerance                   3.
% 3.20/0.98  --extra_neg_conj                        none
% 3.20/0.98  --large_theory_mode                     true
% 3.20/0.98  --prolific_symb_bound                   200
% 3.20/0.98  --lt_threshold                          2000
% 3.20/0.98  --clause_weak_htbl                      true
% 3.20/0.98  --gc_record_bc_elim                     false
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing Options
% 3.20/0.98  
% 3.20/0.98  --preprocessing_flag                    true
% 3.20/0.98  --time_out_prep_mult                    0.1
% 3.20/0.98  --splitting_mode                        input
% 3.20/0.98  --splitting_grd                         true
% 3.20/0.98  --splitting_cvd                         false
% 3.20/0.98  --splitting_cvd_svl                     false
% 3.20/0.98  --splitting_nvd                         32
% 3.20/0.98  --sub_typing                            true
% 3.20/0.98  --prep_gs_sim                           true
% 3.20/0.98  --prep_unflatten                        true
% 3.20/0.98  --prep_res_sim                          true
% 3.20/0.98  --prep_upred                            true
% 3.20/0.98  --prep_sem_filter                       exhaustive
% 3.20/0.98  --prep_sem_filter_out                   false
% 3.20/0.98  --pred_elim                             true
% 3.20/0.98  --res_sim_input                         true
% 3.20/0.98  --eq_ax_congr_red                       true
% 3.20/0.98  --pure_diseq_elim                       true
% 3.20/0.98  --brand_transform                       false
% 3.20/0.98  --non_eq_to_eq                          false
% 3.20/0.98  --prep_def_merge                        true
% 3.20/0.98  --prep_def_merge_prop_impl              false
% 3.20/0.98  --prep_def_merge_mbd                    true
% 3.20/0.98  --prep_def_merge_tr_red                 false
% 3.20/0.98  --prep_def_merge_tr_cl                  false
% 3.20/0.98  --smt_preprocessing                     true
% 3.20/0.98  --smt_ac_axioms                         fast
% 3.20/0.98  --preprocessed_out                      false
% 3.20/0.98  --preprocessed_stats                    false
% 3.20/0.98  
% 3.20/0.98  ------ Abstraction refinement Options
% 3.20/0.98  
% 3.20/0.98  --abstr_ref                             []
% 3.20/0.98  --abstr_ref_prep                        false
% 3.20/0.98  --abstr_ref_until_sat                   false
% 3.20/0.98  --abstr_ref_sig_restrict                funpre
% 3.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.98  --abstr_ref_under                       []
% 3.20/0.98  
% 3.20/0.98  ------ SAT Options
% 3.20/0.98  
% 3.20/0.98  --sat_mode                              false
% 3.20/0.98  --sat_fm_restart_options                ""
% 3.20/0.98  --sat_gr_def                            false
% 3.20/0.98  --sat_epr_types                         true
% 3.20/0.98  --sat_non_cyclic_types                  false
% 3.20/0.98  --sat_finite_models                     false
% 3.20/0.98  --sat_fm_lemmas                         false
% 3.20/0.98  --sat_fm_prep                           false
% 3.20/0.98  --sat_fm_uc_incr                        true
% 3.20/0.98  --sat_out_model                         small
% 3.20/0.98  --sat_out_clauses                       false
% 3.20/0.98  
% 3.20/0.98  ------ QBF Options
% 3.20/0.98  
% 3.20/0.98  --qbf_mode                              false
% 3.20/0.98  --qbf_elim_univ                         false
% 3.20/0.98  --qbf_dom_inst                          none
% 3.20/0.98  --qbf_dom_pre_inst                      false
% 3.20/0.98  --qbf_sk_in                             false
% 3.20/0.98  --qbf_pred_elim                         true
% 3.20/0.98  --qbf_split                             512
% 3.20/0.98  
% 3.20/0.98  ------ BMC1 Options
% 3.20/0.98  
% 3.20/0.98  --bmc1_incremental                      false
% 3.20/0.98  --bmc1_axioms                           reachable_all
% 3.20/0.98  --bmc1_min_bound                        0
% 3.20/0.98  --bmc1_max_bound                        -1
% 3.20/0.98  --bmc1_max_bound_default                -1
% 3.20/0.98  --bmc1_symbol_reachability              true
% 3.20/0.98  --bmc1_property_lemmas                  false
% 3.20/0.98  --bmc1_k_induction                      false
% 3.20/0.98  --bmc1_non_equiv_states                 false
% 3.20/0.98  --bmc1_deadlock                         false
% 3.20/0.98  --bmc1_ucm                              false
% 3.20/0.98  --bmc1_add_unsat_core                   none
% 3.20/0.98  --bmc1_unsat_core_children              false
% 3.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.98  --bmc1_out_stat                         full
% 3.20/0.98  --bmc1_ground_init                      false
% 3.20/0.98  --bmc1_pre_inst_next_state              false
% 3.20/0.98  --bmc1_pre_inst_state                   false
% 3.20/0.98  --bmc1_pre_inst_reach_state             false
% 3.20/0.98  --bmc1_out_unsat_core                   false
% 3.20/0.98  --bmc1_aig_witness_out                  false
% 3.20/0.98  --bmc1_verbose                          false
% 3.20/0.98  --bmc1_dump_clauses_tptp                false
% 3.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.98  --bmc1_dump_file                        -
% 3.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.98  --bmc1_ucm_extend_mode                  1
% 3.20/0.98  --bmc1_ucm_init_mode                    2
% 3.20/0.98  --bmc1_ucm_cone_mode                    none
% 3.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.98  --bmc1_ucm_relax_model                  4
% 3.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.98  --bmc1_ucm_layered_model                none
% 3.20/0.98  --bmc1_ucm_max_lemma_size               10
% 3.20/0.98  
% 3.20/0.98  ------ AIG Options
% 3.20/0.98  
% 3.20/0.98  --aig_mode                              false
% 3.20/0.98  
% 3.20/0.98  ------ Instantiation Options
% 3.20/0.98  
% 3.20/0.98  --instantiation_flag                    true
% 3.20/0.98  --inst_sos_flag                         false
% 3.20/0.98  --inst_sos_phase                        true
% 3.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel_side                     num_symb
% 3.20/0.98  --inst_solver_per_active                1400
% 3.20/0.98  --inst_solver_calls_frac                1.
% 3.20/0.98  --inst_passive_queue_type               priority_queues
% 3.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.98  --inst_passive_queues_freq              [25;2]
% 3.20/0.98  --inst_dismatching                      true
% 3.20/0.98  --inst_eager_unprocessed_to_passive     true
% 3.20/0.98  --inst_prop_sim_given                   true
% 3.20/0.98  --inst_prop_sim_new                     false
% 3.20/0.98  --inst_subs_new                         false
% 3.20/0.98  --inst_eq_res_simp                      false
% 3.20/0.98  --inst_subs_given                       false
% 3.20/0.98  --inst_orphan_elimination               true
% 3.20/0.98  --inst_learning_loop_flag               true
% 3.20/0.98  --inst_learning_start                   3000
% 3.20/0.98  --inst_learning_factor                  2
% 3.20/0.98  --inst_start_prop_sim_after_learn       3
% 3.20/0.98  --inst_sel_renew                        solver
% 3.20/0.98  --inst_lit_activity_flag                true
% 3.20/0.98  --inst_restr_to_given                   false
% 3.20/0.98  --inst_activity_threshold               500
% 3.20/0.98  --inst_out_proof                        true
% 3.20/0.98  
% 3.20/0.98  ------ Resolution Options
% 3.20/0.98  
% 3.20/0.98  --resolution_flag                       true
% 3.20/0.98  --res_lit_sel                           adaptive
% 3.20/0.98  --res_lit_sel_side                      none
% 3.20/0.98  --res_ordering                          kbo
% 3.20/0.98  --res_to_prop_solver                    active
% 3.20/0.98  --res_prop_simpl_new                    false
% 3.20/0.98  --res_prop_simpl_given                  true
% 3.20/0.98  --res_passive_queue_type                priority_queues
% 3.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.98  --res_passive_queues_freq               [15;5]
% 3.20/0.98  --res_forward_subs                      full
% 3.20/0.98  --res_backward_subs                     full
% 3.20/0.98  --res_forward_subs_resolution           true
% 3.20/0.98  --res_backward_subs_resolution          true
% 3.20/0.98  --res_orphan_elimination                true
% 3.20/0.98  --res_time_limit                        2.
% 3.20/0.98  --res_out_proof                         true
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Options
% 3.20/0.98  
% 3.20/0.98  --superposition_flag                    true
% 3.20/0.98  --sup_passive_queue_type                priority_queues
% 3.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.98  --demod_completeness_check              fast
% 3.20/0.98  --demod_use_ground                      true
% 3.20/0.98  --sup_to_prop_solver                    passive
% 3.20/0.98  --sup_prop_simpl_new                    true
% 3.20/0.98  --sup_prop_simpl_given                  true
% 3.20/0.98  --sup_fun_splitting                     false
% 3.20/0.98  --sup_smt_interval                      50000
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Simplification Setup
% 3.20/0.98  
% 3.20/0.98  --sup_indices_passive                   []
% 3.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_full_bw                           [BwDemod]
% 3.20/0.98  --sup_immed_triv                        [TrivRules]
% 3.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_immed_bw_main                     []
% 3.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  
% 3.20/0.98  ------ Combination Options
% 3.20/0.98  
% 3.20/0.98  --comb_res_mult                         3
% 3.20/0.98  --comb_sup_mult                         2
% 3.20/0.98  --comb_inst_mult                        10
% 3.20/0.98  
% 3.20/0.98  ------ Debug Options
% 3.20/0.98  
% 3.20/0.98  --dbg_backtrace                         false
% 3.20/0.98  --dbg_dump_prop_clauses                 false
% 3.20/0.98  --dbg_dump_prop_clauses_file            -
% 3.20/0.98  --dbg_out_stat                          false
% 3.20/0.98  ------ Parsing...
% 3.20/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.98  ------ Proving...
% 3.20/0.98  ------ Problem Properties 
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  clauses                                 26
% 3.20/0.98  conjectures                             5
% 3.20/0.98  EPR                                     3
% 3.20/0.98  Horn                                    26
% 3.20/0.98  unary                                   10
% 3.20/0.98  binary                                  3
% 3.20/0.98  lits                                    72
% 3.20/0.98  lits eq                                 7
% 3.20/0.98  fd_pure                                 0
% 3.20/0.98  fd_pseudo                               0
% 3.20/0.98  fd_cond                                 0
% 3.20/0.98  fd_pseudo_cond                          0
% 3.20/0.98  AC symbols                              0
% 3.20/0.98  
% 3.20/0.98  ------ Schedule dynamic 5 is on 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  ------ 
% 3.20/0.98  Current options:
% 3.20/0.98  ------ 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options
% 3.20/0.98  
% 3.20/0.98  --out_options                           all
% 3.20/0.98  --tptp_safe_out                         true
% 3.20/0.98  --problem_path                          ""
% 3.20/0.98  --include_path                          ""
% 3.20/0.98  --clausifier                            res/vclausify_rel
% 3.20/0.98  --clausifier_options                    --mode clausify
% 3.20/0.98  --stdin                                 false
% 3.20/0.98  --stats_out                             all
% 3.20/0.98  
% 3.20/0.98  ------ General Options
% 3.20/0.98  
% 3.20/0.98  --fof                                   false
% 3.20/0.98  --time_out_real                         305.
% 3.20/0.98  --time_out_virtual                      -1.
% 3.20/0.98  --symbol_type_check                     false
% 3.20/0.98  --clausify_out                          false
% 3.20/0.98  --sig_cnt_out                           false
% 3.20/0.98  --trig_cnt_out                          false
% 3.20/0.98  --trig_cnt_out_tolerance                1.
% 3.20/0.98  --trig_cnt_out_sk_spl                   false
% 3.20/0.98  --abstr_cl_out                          false
% 3.20/0.98  
% 3.20/0.98  ------ Global Options
% 3.20/0.98  
% 3.20/0.98  --schedule                              default
% 3.20/0.98  --add_important_lit                     false
% 3.20/0.98  --prop_solver_per_cl                    1000
% 3.20/0.98  --min_unsat_core                        false
% 3.20/0.98  --soft_assumptions                      false
% 3.20/0.98  --soft_lemma_size                       3
% 3.20/0.98  --prop_impl_unit_size                   0
% 3.20/0.98  --prop_impl_unit                        []
% 3.20/0.98  --share_sel_clauses                     true
% 3.20/0.98  --reset_solvers                         false
% 3.20/0.98  --bc_imp_inh                            [conj_cone]
% 3.20/0.98  --conj_cone_tolerance                   3.
% 3.20/0.98  --extra_neg_conj                        none
% 3.20/0.98  --large_theory_mode                     true
% 3.20/0.98  --prolific_symb_bound                   200
% 3.20/0.98  --lt_threshold                          2000
% 3.20/0.98  --clause_weak_htbl                      true
% 3.20/0.98  --gc_record_bc_elim                     false
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing Options
% 3.20/0.98  
% 3.20/0.98  --preprocessing_flag                    true
% 3.20/0.98  --time_out_prep_mult                    0.1
% 3.20/0.98  --splitting_mode                        input
% 3.20/0.98  --splitting_grd                         true
% 3.20/0.98  --splitting_cvd                         false
% 3.20/0.98  --splitting_cvd_svl                     false
% 3.20/0.98  --splitting_nvd                         32
% 3.20/0.98  --sub_typing                            true
% 3.20/0.98  --prep_gs_sim                           true
% 3.20/0.98  --prep_unflatten                        true
% 3.20/0.98  --prep_res_sim                          true
% 3.20/0.98  --prep_upred                            true
% 3.20/0.98  --prep_sem_filter                       exhaustive
% 3.20/0.98  --prep_sem_filter_out                   false
% 3.20/0.98  --pred_elim                             true
% 3.20/0.98  --res_sim_input                         true
% 3.20/0.98  --eq_ax_congr_red                       true
% 3.20/0.98  --pure_diseq_elim                       true
% 3.20/0.98  --brand_transform                       false
% 3.20/0.98  --non_eq_to_eq                          false
% 3.20/0.98  --prep_def_merge                        true
% 3.20/0.98  --prep_def_merge_prop_impl              false
% 3.20/0.98  --prep_def_merge_mbd                    true
% 3.20/0.98  --prep_def_merge_tr_red                 false
% 3.20/0.98  --prep_def_merge_tr_cl                  false
% 3.20/0.98  --smt_preprocessing                     true
% 3.20/0.98  --smt_ac_axioms                         fast
% 3.20/0.98  --preprocessed_out                      false
% 3.20/0.98  --preprocessed_stats                    false
% 3.20/0.98  
% 3.20/0.98  ------ Abstraction refinement Options
% 3.20/0.98  
% 3.20/0.98  --abstr_ref                             []
% 3.20/0.98  --abstr_ref_prep                        false
% 3.20/0.98  --abstr_ref_until_sat                   false
% 3.20/0.98  --abstr_ref_sig_restrict                funpre
% 3.20/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.98  --abstr_ref_under                       []
% 3.20/0.98  
% 3.20/0.98  ------ SAT Options
% 3.20/0.98  
% 3.20/0.98  --sat_mode                              false
% 3.20/0.98  --sat_fm_restart_options                ""
% 3.20/0.98  --sat_gr_def                            false
% 3.20/0.98  --sat_epr_types                         true
% 3.20/0.98  --sat_non_cyclic_types                  false
% 3.20/0.98  --sat_finite_models                     false
% 3.20/0.98  --sat_fm_lemmas                         false
% 3.20/0.98  --sat_fm_prep                           false
% 3.20/0.98  --sat_fm_uc_incr                        true
% 3.20/0.98  --sat_out_model                         small
% 3.20/0.98  --sat_out_clauses                       false
% 3.20/0.98  
% 3.20/0.98  ------ QBF Options
% 3.20/0.98  
% 3.20/0.98  --qbf_mode                              false
% 3.20/0.98  --qbf_elim_univ                         false
% 3.20/0.98  --qbf_dom_inst                          none
% 3.20/0.98  --qbf_dom_pre_inst                      false
% 3.20/0.98  --qbf_sk_in                             false
% 3.20/0.98  --qbf_pred_elim                         true
% 3.20/0.98  --qbf_split                             512
% 3.20/0.98  
% 3.20/0.98  ------ BMC1 Options
% 3.20/0.98  
% 3.20/0.98  --bmc1_incremental                      false
% 3.20/0.98  --bmc1_axioms                           reachable_all
% 3.20/0.98  --bmc1_min_bound                        0
% 3.20/0.98  --bmc1_max_bound                        -1
% 3.20/0.98  --bmc1_max_bound_default                -1
% 3.20/0.98  --bmc1_symbol_reachability              true
% 3.20/0.98  --bmc1_property_lemmas                  false
% 3.20/0.98  --bmc1_k_induction                      false
% 3.20/0.98  --bmc1_non_equiv_states                 false
% 3.20/0.98  --bmc1_deadlock                         false
% 3.20/0.98  --bmc1_ucm                              false
% 3.20/0.98  --bmc1_add_unsat_core                   none
% 3.20/0.98  --bmc1_unsat_core_children              false
% 3.20/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.98  --bmc1_out_stat                         full
% 3.20/0.98  --bmc1_ground_init                      false
% 3.20/0.98  --bmc1_pre_inst_next_state              false
% 3.20/0.98  --bmc1_pre_inst_state                   false
% 3.20/0.98  --bmc1_pre_inst_reach_state             false
% 3.20/0.98  --bmc1_out_unsat_core                   false
% 3.20/0.98  --bmc1_aig_witness_out                  false
% 3.20/0.98  --bmc1_verbose                          false
% 3.20/0.98  --bmc1_dump_clauses_tptp                false
% 3.20/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.98  --bmc1_dump_file                        -
% 3.20/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.98  --bmc1_ucm_extend_mode                  1
% 3.20/0.98  --bmc1_ucm_init_mode                    2
% 3.20/0.98  --bmc1_ucm_cone_mode                    none
% 3.20/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.98  --bmc1_ucm_relax_model                  4
% 3.20/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.98  --bmc1_ucm_layered_model                none
% 3.20/0.98  --bmc1_ucm_max_lemma_size               10
% 3.20/0.98  
% 3.20/0.98  ------ AIG Options
% 3.20/0.98  
% 3.20/0.98  --aig_mode                              false
% 3.20/0.98  
% 3.20/0.98  ------ Instantiation Options
% 3.20/0.98  
% 3.20/0.98  --instantiation_flag                    true
% 3.20/0.98  --inst_sos_flag                         false
% 3.20/0.98  --inst_sos_phase                        true
% 3.20/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.98  --inst_lit_sel_side                     none
% 3.20/0.98  --inst_solver_per_active                1400
% 3.20/0.98  --inst_solver_calls_frac                1.
% 3.20/0.98  --inst_passive_queue_type               priority_queues
% 3.20/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.98  --inst_passive_queues_freq              [25;2]
% 3.20/0.98  --inst_dismatching                      true
% 3.20/0.98  --inst_eager_unprocessed_to_passive     true
% 3.20/0.98  --inst_prop_sim_given                   true
% 3.20/0.98  --inst_prop_sim_new                     false
% 3.20/0.98  --inst_subs_new                         false
% 3.20/0.98  --inst_eq_res_simp                      false
% 3.20/0.98  --inst_subs_given                       false
% 3.20/0.98  --inst_orphan_elimination               true
% 3.20/0.98  --inst_learning_loop_flag               true
% 3.20/0.98  --inst_learning_start                   3000
% 3.20/0.98  --inst_learning_factor                  2
% 3.20/0.98  --inst_start_prop_sim_after_learn       3
% 3.20/0.98  --inst_sel_renew                        solver
% 3.20/0.98  --inst_lit_activity_flag                true
% 3.20/0.98  --inst_restr_to_given                   false
% 3.20/0.98  --inst_activity_threshold               500
% 3.20/0.98  --inst_out_proof                        true
% 3.20/0.98  
% 3.20/0.98  ------ Resolution Options
% 3.20/0.98  
% 3.20/0.98  --resolution_flag                       false
% 3.20/0.98  --res_lit_sel                           adaptive
% 3.20/0.98  --res_lit_sel_side                      none
% 3.20/0.98  --res_ordering                          kbo
% 3.20/0.98  --res_to_prop_solver                    active
% 3.20/0.98  --res_prop_simpl_new                    false
% 3.20/0.98  --res_prop_simpl_given                  true
% 3.20/0.98  --res_passive_queue_type                priority_queues
% 3.20/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.98  --res_passive_queues_freq               [15;5]
% 3.20/0.98  --res_forward_subs                      full
% 3.20/0.98  --res_backward_subs                     full
% 3.20/0.98  --res_forward_subs_resolution           true
% 3.20/0.98  --res_backward_subs_resolution          true
% 3.20/0.98  --res_orphan_elimination                true
% 3.20/0.98  --res_time_limit                        2.
% 3.20/0.98  --res_out_proof                         true
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Options
% 3.20/0.98  
% 3.20/0.98  --superposition_flag                    true
% 3.20/0.98  --sup_passive_queue_type                priority_queues
% 3.20/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.98  --demod_completeness_check              fast
% 3.20/0.98  --demod_use_ground                      true
% 3.20/0.98  --sup_to_prop_solver                    passive
% 3.20/0.98  --sup_prop_simpl_new                    true
% 3.20/0.98  --sup_prop_simpl_given                  true
% 3.20/0.98  --sup_fun_splitting                     false
% 3.20/0.98  --sup_smt_interval                      50000
% 3.20/0.98  
% 3.20/0.98  ------ Superposition Simplification Setup
% 3.20/0.98  
% 3.20/0.98  --sup_indices_passive                   []
% 3.20/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_full_bw                           [BwDemod]
% 3.20/0.98  --sup_immed_triv                        [TrivRules]
% 3.20/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_immed_bw_main                     []
% 3.20/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/0.98  
% 3.20/0.98  ------ Combination Options
% 3.20/0.98  
% 3.20/0.98  --comb_res_mult                         3
% 3.20/0.98  --comb_sup_mult                         2
% 3.20/0.98  --comb_inst_mult                        10
% 3.20/0.98  
% 3.20/0.98  ------ Debug Options
% 3.20/0.98  
% 3.20/0.98  --dbg_backtrace                         false
% 3.20/0.98  --dbg_dump_prop_clauses                 false
% 3.20/0.98  --dbg_dump_prop_clauses_file            -
% 3.20/0.98  --dbg_out_stat                          false
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  ------ Proving...
% 3.20/0.98  
% 3.20/0.98  
% 3.20/0.98  % SZS status Theorem for theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  fof(f16,conjecture,(
% 3.20/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f17,negated_conjecture,(
% 3.20/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.20/0.98    inference(negated_conjecture,[],[f16])).
% 3.20/0.98  
% 3.20/0.98  fof(f41,plain,(
% 3.20/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.20/0.98    inference(ennf_transformation,[],[f17])).
% 3.20/0.98  
% 3.20/0.98  fof(f42,plain,(
% 3.20/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.20/0.98    inference(flattening,[],[f41])).
% 3.20/0.98  
% 3.20/0.98  fof(f45,plain,(
% 3.20/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.20/0.98    introduced(choice_axiom,[])).
% 3.20/0.98  
% 3.20/0.98  fof(f46,plain,(
% 3.20/0.98    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.20/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f45])).
% 3.20/0.98  
% 3.20/0.98  fof(f73,plain,(
% 3.20/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.20/0.98    inference(cnf_transformation,[],[f46])).
% 3.20/0.98  
% 3.20/0.98  fof(f13,axiom,(
% 3.20/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f37,plain,(
% 3.20/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.20/0.98    inference(ennf_transformation,[],[f13])).
% 3.20/0.98  
% 3.20/0.98  fof(f38,plain,(
% 3.20/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.20/0.98    inference(flattening,[],[f37])).
% 3.20/0.98  
% 3.20/0.98  fof(f67,plain,(
% 3.20/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f38])).
% 3.20/0.98  
% 3.20/0.98  fof(f70,plain,(
% 3.20/0.98    v1_funct_1(sK2)),
% 3.20/0.98    inference(cnf_transformation,[],[f46])).
% 3.20/0.98  
% 3.20/0.98  fof(f71,plain,(
% 3.20/0.98    v1_funct_2(sK2,sK1,sK1)),
% 3.20/0.98    inference(cnf_transformation,[],[f46])).
% 3.20/0.98  
% 3.20/0.98  fof(f72,plain,(
% 3.20/0.98    v3_funct_2(sK2,sK1,sK1)),
% 3.20/0.98    inference(cnf_transformation,[],[f46])).
% 3.20/0.98  
% 3.20/0.98  fof(f9,axiom,(
% 3.20/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f33,plain,(
% 3.20/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.20/0.98    inference(ennf_transformation,[],[f9])).
% 3.20/0.98  
% 3.20/0.98  fof(f34,plain,(
% 3.20/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.20/0.98    inference(flattening,[],[f33])).
% 3.20/0.98  
% 3.20/0.98  fof(f60,plain,(
% 3.20/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f34])).
% 3.20/0.98  
% 3.20/0.98  fof(f6,axiom,(
% 3.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f28,plain,(
% 3.20/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.98    inference(ennf_transformation,[],[f6])).
% 3.20/0.98  
% 3.20/0.98  fof(f53,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.98    inference(cnf_transformation,[],[f28])).
% 3.20/0.98  
% 3.20/0.98  fof(f15,axiom,(
% 3.20/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f39,plain,(
% 3.20/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.20/0.98    inference(ennf_transformation,[],[f15])).
% 3.20/0.98  
% 3.20/0.98  fof(f40,plain,(
% 3.20/0.98    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.20/0.98    inference(flattening,[],[f39])).
% 3.20/0.98  
% 3.20/0.98  fof(f69,plain,(
% 3.20/0.98    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f40])).
% 3.20/0.98  
% 3.20/0.98  fof(f57,plain,(
% 3.20/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f34])).
% 3.20/0.98  
% 3.20/0.98  fof(f58,plain,(
% 3.20/0.98    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f34])).
% 3.20/0.98  
% 3.20/0.98  fof(f8,axiom,(
% 3.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f21,plain,(
% 3.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.20/0.98    inference(pure_predicate_removal,[],[f8])).
% 3.20/0.98  
% 3.20/0.98  fof(f31,plain,(
% 3.20/0.98    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.98    inference(ennf_transformation,[],[f21])).
% 3.20/0.98  
% 3.20/0.98  fof(f32,plain,(
% 3.20/0.98    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.98    inference(flattening,[],[f31])).
% 3.20/0.98  
% 3.20/0.98  fof(f56,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.98    inference(cnf_transformation,[],[f32])).
% 3.20/0.98  
% 3.20/0.98  fof(f59,plain,(
% 3.20/0.98    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f34])).
% 3.20/0.98  
% 3.20/0.98  fof(f3,axiom,(
% 3.20/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f23,plain,(
% 3.20/0.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.20/0.98    inference(ennf_transformation,[],[f3])).
% 3.20/0.98  
% 3.20/0.98  fof(f24,plain,(
% 3.20/0.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.20/0.98    inference(flattening,[],[f23])).
% 3.20/0.98  
% 3.20/0.98  fof(f49,plain,(
% 3.20/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f24])).
% 3.20/0.98  
% 3.20/0.98  fof(f14,axiom,(
% 3.20/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f68,plain,(
% 3.20/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f14])).
% 3.20/0.98  
% 3.20/0.98  fof(f76,plain,(
% 3.20/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f49,f68])).
% 3.20/0.98  
% 3.20/0.98  fof(f4,axiom,(
% 3.20/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f25,plain,(
% 3.20/0.98    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.20/0.98    inference(ennf_transformation,[],[f4])).
% 3.20/0.98  
% 3.20/0.98  fof(f26,plain,(
% 3.20/0.98    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.20/0.98    inference(flattening,[],[f25])).
% 3.20/0.98  
% 3.20/0.98  fof(f51,plain,(
% 3.20/0.98    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f26])).
% 3.20/0.98  
% 3.20/0.98  fof(f5,axiom,(
% 3.20/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f27,plain,(
% 3.20/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.98    inference(ennf_transformation,[],[f5])).
% 3.20/0.98  
% 3.20/0.98  fof(f52,plain,(
% 3.20/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.98    inference(cnf_transformation,[],[f27])).
% 3.20/0.98  
% 3.20/0.98  fof(f50,plain,(
% 3.20/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.98    inference(cnf_transformation,[],[f24])).
% 3.20/0.98  
% 3.20/0.98  fof(f75,plain,(
% 3.20/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.98    inference(definition_unfolding,[],[f50,f68])).
% 3.20/0.98  
% 3.20/0.98  fof(f12,axiom,(
% 3.20/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.20/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.98  
% 3.20/0.98  fof(f35,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.20/0.98    inference(ennf_transformation,[],[f12])).
% 3.20/0.98  
% 3.20/0.98  fof(f36,plain,(
% 3.20/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.20/0.98    inference(flattening,[],[f35])).
% 3.20/0.98  
% 3.20/0.98  fof(f66,plain,(
% 3.20/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f36])).
% 3.20/0.99  
% 3.20/0.99  fof(f74,plain,(
% 3.20/0.99    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.20/0.99    inference(cnf_transformation,[],[f46])).
% 3.20/0.99  
% 3.20/0.99  fof(f10,axiom,(
% 3.20/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f20,plain,(
% 3.20/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.20/0.99    inference(pure_predicate_removal,[],[f10])).
% 3.20/0.99  
% 3.20/0.99  fof(f61,plain,(
% 3.20/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f20])).
% 3.20/0.99  
% 3.20/0.99  fof(f7,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f29,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.20/0.99    inference(ennf_transformation,[],[f7])).
% 3.20/0.99  
% 3.20/0.99  fof(f30,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(flattening,[],[f29])).
% 3.20/0.99  
% 3.20/0.99  fof(f54,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f30])).
% 3.20/0.99  
% 3.20/0.99  cnf(c_23,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1104,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_20,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1107,plain,
% 3.20/0.99      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.20/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.20/0.99      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.20/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.20/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2200,plain,
% 3.20/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.20/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1104,c_1107]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_26,negated_conjecture,
% 3.20/0.99      ( v1_funct_1(sK2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_25,negated_conjecture,
% 3.20/0.99      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_24,negated_conjecture,
% 3.20/0.99      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1484,plain,
% 3.20/0.99      ( ~ v1_funct_2(sK2,X0,X0)
% 3.20/0.99      | ~ v3_funct_2(sK2,X0,X0)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1486,plain,
% 3.20/0.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.20/0.99      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1484]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2840,plain,
% 3.20/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2200,c_26,c_25,c_24,c_23,c_1486]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1117,plain,
% 3.20/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.20/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.20/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.20/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3733,plain,
% 3.20/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2840,c_1117]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_27,plain,
% 3.20/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_28,plain,
% 3.20/0.99      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_29,plain,
% 3.20/0.99      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_30,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4623,plain,
% 3.20/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3733,c_27,c_28,c_29,c_30]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1120,plain,
% 3.20/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4633,plain,
% 3.20/0.99      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4623,c_1120]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_21,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1106,plain,
% 3.20/0.99      ( k1_relset_1(X0,X0,X1) = X0
% 3.20/0.99      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.20/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.20/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4639,plain,
% 3.20/0.99      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
% 3.20/0.99      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4623,c_1106]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4688,plain,
% 3.20/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.20/0.99      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_4633,c_4639]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_13,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1114,plain,
% 3.20/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.20/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(X0) != iProver_top
% 3.20/0.99      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3187,plain,
% 3.20/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1104,c_1114]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3192,plain,
% 3.20/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3187,c_2840]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_12,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.20/0.99      | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.20/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1115,plain,
% 3.20/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.20/0.99      | v1_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.20/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3228,plain,
% 3.20/0.99      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.20/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1104,c_1115]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3233,plain,
% 3.20/0.99      ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top
% 3.20/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3228,c_2840]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6557,plain,
% 3.20/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4688,c_27,c_28,c_29,c_3192,c_3233]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8,plain,
% 3.20/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | v2_funct_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1118,plain,
% 3.20/0.99      ( v3_funct_2(X0,X1,X2) != iProver_top
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.20/0.99      | v1_funct_1(X0) != iProver_top
% 3.20/0.99      | v2_funct_1(X0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4629,plain,
% 3.20/0.99      ( v3_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.20/0.99      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4623,c_1118]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_11,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 3.20/0.99      | ~ v3_funct_2(X0,X1,X1)
% 3.20/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.20/0.99      | ~ v1_funct_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1116,plain,
% 3.20/0.99      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.20/0.99      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.20/0.99      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.20/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3295,plain,
% 3.20/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v3_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.20/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1104,c_1116]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3300,plain,
% 3.20/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v3_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top
% 3.20/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3295,c_2840]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5676,plain,
% 3.20/0.99      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4629,c_27,c_28,c_29,c_3192,c_3300]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3668,plain,
% 3.20/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3192,c_27,c_28,c_29]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3,plain,
% 3.20/0.99      ( ~ v1_funct_1(X0)
% 3.20/0.99      | ~ v2_funct_1(X0)
% 3.20/0.99      | ~ v1_relat_1(X0)
% 3.20/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1123,plain,
% 3.20/0.99      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.20/0.99      | v1_funct_1(X0) != iProver_top
% 3.20/0.99      | v2_funct_1(X0) != iProver_top
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3674,plain,
% 3.20/0.99      ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_partfun1(k1_relat_1(k2_funct_1(sK2)))
% 3.20/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.20/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3668,c_1123]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1101,plain,
% 3.20/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4,plain,
% 3.20/0.99      ( ~ v1_funct_1(X0)
% 3.20/0.99      | ~ v2_funct_1(X0)
% 3.20/0.99      | ~ v1_relat_1(X0)
% 3.20/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1122,plain,
% 3.20/0.99      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.20/0.99      | v1_funct_1(X0) != iProver_top
% 3.20/0.99      | v2_funct_1(X0) != iProver_top
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2309,plain,
% 3.20/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.20/0.99      | v2_funct_1(sK2) != iProver_top
% 3.20/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1101,c_1122]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | v1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1335,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.20/0.99      | v1_relat_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1358,plain,
% 3.20/0.99      ( ~ v1_funct_1(sK2)
% 3.20/0.99      | ~ v2_funct_1(sK2)
% 3.20/0.99      | ~ v1_relat_1(sK2)
% 3.20/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1395,plain,
% 3.20/0.99      ( ~ v3_funct_2(sK2,X0,X1)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | v2_funct_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1397,plain,
% 3.20/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | v2_funct_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1395]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2737,plain,
% 3.20/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2309,c_26,c_24,c_23,c_1335,c_1358,c_1397]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2,plain,
% 3.20/0.99      ( ~ v1_funct_1(X0)
% 3.20/0.99      | ~ v2_funct_1(X0)
% 3.20/0.99      | ~ v1_relat_1(X0)
% 3.20/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1124,plain,
% 3.20/0.99      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.20/0.99      | v1_funct_1(X0) != iProver_top
% 3.20/0.99      | v2_funct_1(X0) != iProver_top
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2419,plain,
% 3.20/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.20/0.99      | v2_funct_1(sK2) != iProver_top
% 3.20/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1101,c_1124]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1366,plain,
% 3.20/0.99      ( ~ v1_funct_1(sK2)
% 3.20/0.99      | ~ v2_funct_1(sK2)
% 3.20/0.99      | ~ v1_relat_1(sK2)
% 3.20/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2836,plain,
% 3.20/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2419,c_26,c_24,c_23,c_1335,c_1366,c_1397]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3683,plain,
% 3.20/0.99      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2))
% 3.20/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.20/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_3674,c_2737,c_2836]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5681,plain,
% 3.20/0.99      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2))
% 3.20/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_5676,c_3683]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1121,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.20/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4630,plain,
% 3.20/0.99      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4623,c_1121]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5784,plain,
% 3.20/0.99      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_5681,c_27,c_28,c_29,c_3192,c_3300,c_3683,c_4629,
% 3.20/0.99                 c_4630]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6563,plain,
% 3.20/0.99      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_6557,c_5784]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_19,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | ~ v1_funct_1(X3)
% 3.20/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1108,plain,
% 3.20/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.20/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.20/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(X5) != iProver_top
% 3.20/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4637,plain,
% 3.20/0.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(X2) != iProver_top
% 3.20/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4623,c_1108]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5846,plain,
% 3.20/0.99      ( v1_funct_1(X2) != iProver_top
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4637,c_27,c_28,c_29,c_3192]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5847,plain,
% 3.20/0.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_5846]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5858,plain,
% 3.20/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1104,c_5847]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2332,plain,
% 3.20/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.20/0.99      | v2_funct_1(sK2) != iProver_top
% 3.20/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1101,c_1123]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2008,plain,
% 3.20/0.99      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1104,c_1120]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1581,plain,
% 3.20/0.99      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.20/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1104,c_1106]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1439,plain,
% 3.20/0.99      ( ~ v1_funct_2(sK2,X0,X0)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | k1_relset_1(X0,X0,sK2) = X0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1441,plain,
% 3.20/0.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.20/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | k1_relset_1(sK1,sK1,sK2) = sK1 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1439]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1959,plain,
% 3.20/0.99      ( k1_relset_1(sK1,sK1,sK2) = sK1 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1581,c_26,c_25,c_23,c_1441]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2010,plain,
% 3.20/0.99      ( k1_relat_1(sK2) = sK1 ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_2008,c_1959]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2336,plain,
% 3.20/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.20/0.99      | v2_funct_1(sK2) != iProver_top
% 3.20/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_2332,c_2010]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1336,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.20/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1335]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1396,plain,
% 3.20/0.99      ( v3_funct_2(sK2,X0,X1) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top
% 3.20/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1395]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1398,plain,
% 3.20/0.99      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.20/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top
% 3.20/0.99      | v2_funct_1(sK2) = iProver_top ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1396]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2907,plain,
% 3.20/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2336,c_27,c_29,c_30,c_1336,c_1398]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5866,plain,
% 3.20/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_5858,c_2907]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5991,plain,
% 3.20/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_5866,c_27]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3033,plain,
% 3.20/0.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(X2) != iProver_top
% 3.20/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1104,c_1108]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3462,plain,
% 3.20/0.99      ( v1_funct_1(X2) != iProver_top
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3033,c_27]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3463,plain,
% 3.20/0.99      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.20/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_3462]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4631,plain,
% 3.20/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.20/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4623,c_3463]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4702,plain,
% 3.20/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.20/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_4631,c_2836]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4728,plain,
% 3.20/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_4702,c_27,c_28,c_29,c_3192]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_22,negated_conjecture,
% 3.20/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.20/0.99      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1105,plain,
% 3.20/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.20/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2843,plain,
% 3.20/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.20/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_2840,c_1105]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4731,plain,
% 3.20/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
% 3.20/0.99      | r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_4728,c_2843]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5994,plain,
% 3.20/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top
% 3.20/0.99      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_5991,c_4731]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_14,plain,
% 3.20/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_53,plain,
% 3.20/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_55,plain,
% 3.20/0.99      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_53]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7,plain,
% 3.20/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 3.20/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.20/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1419,plain,
% 3.20/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.20/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.20/0.99      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1851,plain,
% 3.20/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.20/0.99      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1419]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1852,plain,
% 3.20/0.99      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 3.20/0.99      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1851]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1854,plain,
% 3.20/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 3.20/0.99      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1852]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6433,plain,
% 3.20/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(k2_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_5994,c_55,c_1854]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6576,plain,
% 3.20/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_6563,c_6433]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(contradiction,plain,
% 3.20/0.99      ( $false ),
% 3.20/0.99      inference(minisat,[status(thm)],[c_6576,c_1854,c_55]) ).
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  ------                               Statistics
% 3.20/0.99  
% 3.20/0.99  ------ General
% 3.20/0.99  
% 3.20/0.99  abstr_ref_over_cycles:                  0
% 3.20/0.99  abstr_ref_under_cycles:                 0
% 3.20/0.99  gc_basic_clause_elim:                   0
% 3.20/0.99  forced_gc_time:                         0
% 3.20/0.99  parsing_time:                           0.009
% 3.20/0.99  unif_index_cands_time:                  0.
% 3.20/0.99  unif_index_add_time:                    0.
% 3.20/0.99  orderings_time:                         0.
% 3.20/0.99  out_proof_time:                         0.014
% 3.20/0.99  total_time:                             0.248
% 3.20/0.99  num_of_symbols:                         51
% 3.20/0.99  num_of_terms:                           9409
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing
% 3.20/0.99  
% 3.20/0.99  num_of_splits:                          0
% 3.20/0.99  num_of_split_atoms:                     0
% 3.20/0.99  num_of_reused_defs:                     0
% 3.20/0.99  num_eq_ax_congr_red:                    24
% 3.20/0.99  num_of_sem_filtered_clauses:            1
% 3.20/0.99  num_of_subtypes:                        0
% 3.20/0.99  monotx_restored_types:                  0
% 3.20/0.99  sat_num_of_epr_types:                   0
% 3.20/0.99  sat_num_of_non_cyclic_types:            0
% 3.20/0.99  sat_guarded_non_collapsed_types:        0
% 3.20/0.99  num_pure_diseq_elim:                    0
% 3.20/0.99  simp_replaced_by:                       0
% 3.20/0.99  res_preprocessed:                       135
% 3.20/0.99  prep_upred:                             0
% 3.20/0.99  prep_unflattend:                        0
% 3.20/0.99  smt_new_axioms:                         0
% 3.20/0.99  pred_elim_cands:                        7
% 3.20/0.99  pred_elim:                              0
% 3.20/0.99  pred_elim_cl:                           0
% 3.20/0.99  pred_elim_cycles:                       2
% 3.20/0.99  merged_defs:                            0
% 3.20/0.99  merged_defs_ncl:                        0
% 3.20/0.99  bin_hyper_res:                          0
% 3.20/0.99  prep_cycles:                            4
% 3.20/0.99  pred_elim_time:                         0.005
% 3.20/0.99  splitting_time:                         0.
% 3.20/0.99  sem_filter_time:                        0.
% 3.20/0.99  monotx_time:                            0.001
% 3.20/0.99  subtype_inf_time:                       0.
% 3.20/0.99  
% 3.20/0.99  ------ Problem properties
% 3.20/0.99  
% 3.20/0.99  clauses:                                26
% 3.20/0.99  conjectures:                            5
% 3.20/0.99  epr:                                    3
% 3.20/0.99  horn:                                   26
% 3.20/0.99  ground:                                 5
% 3.20/0.99  unary:                                  10
% 3.20/0.99  binary:                                 3
% 3.20/0.99  lits:                                   72
% 3.20/0.99  lits_eq:                                7
% 3.20/0.99  fd_pure:                                0
% 3.20/0.99  fd_pseudo:                              0
% 3.20/0.99  fd_cond:                                0
% 3.20/0.99  fd_pseudo_cond:                         0
% 3.20/0.99  ac_symbols:                             0
% 3.20/0.99  
% 3.20/0.99  ------ Propositional Solver
% 3.20/0.99  
% 3.20/0.99  prop_solver_calls:                      29
% 3.20/0.99  prop_fast_solver_calls:                 1105
% 3.20/0.99  smt_solver_calls:                       0
% 3.20/0.99  smt_fast_solver_calls:                  0
% 3.20/0.99  prop_num_of_clauses:                    2698
% 3.20/0.99  prop_preprocess_simplified:             6611
% 3.20/0.99  prop_fo_subsumed:                       64
% 3.20/0.99  prop_solver_time:                       0.
% 3.20/0.99  smt_solver_time:                        0.
% 3.20/0.99  smt_fast_solver_time:                   0.
% 3.20/0.99  prop_fast_solver_time:                  0.
% 3.20/0.99  prop_unsat_core_time:                   0.
% 3.20/0.99  
% 3.20/0.99  ------ QBF
% 3.20/0.99  
% 3.20/0.99  qbf_q_res:                              0
% 3.20/0.99  qbf_num_tautologies:                    0
% 3.20/0.99  qbf_prep_cycles:                        0
% 3.20/0.99  
% 3.20/0.99  ------ BMC1
% 3.20/0.99  
% 3.20/0.99  bmc1_current_bound:                     -1
% 3.20/0.99  bmc1_last_solved_bound:                 -1
% 3.20/0.99  bmc1_unsat_core_size:                   -1
% 3.20/0.99  bmc1_unsat_core_parents_size:           -1
% 3.20/0.99  bmc1_merge_next_fun:                    0
% 3.20/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation
% 3.20/0.99  
% 3.20/0.99  inst_num_of_clauses:                    742
% 3.20/0.99  inst_num_in_passive:                    287
% 3.20/0.99  inst_num_in_active:                     400
% 3.20/0.99  inst_num_in_unprocessed:                55
% 3.20/0.99  inst_num_of_loops:                      410
% 3.20/0.99  inst_num_of_learning_restarts:          0
% 3.20/0.99  inst_num_moves_active_passive:          6
% 3.20/0.99  inst_lit_activity:                      0
% 3.20/0.99  inst_lit_activity_moves:                0
% 3.20/0.99  inst_num_tautologies:                   0
% 3.20/0.99  inst_num_prop_implied:                  0
% 3.20/0.99  inst_num_existing_simplified:           0
% 3.20/0.99  inst_num_eq_res_simplified:             0
% 3.20/0.99  inst_num_child_elim:                    0
% 3.20/0.99  inst_num_of_dismatching_blockings:      273
% 3.20/0.99  inst_num_of_non_proper_insts:           608
% 3.20/0.99  inst_num_of_duplicates:                 0
% 3.20/0.99  inst_inst_num_from_inst_to_res:         0
% 3.20/0.99  inst_dismatching_checking_time:         0.
% 3.20/0.99  
% 3.20/0.99  ------ Resolution
% 3.20/0.99  
% 3.20/0.99  res_num_of_clauses:                     0
% 3.20/0.99  res_num_in_passive:                     0
% 3.20/0.99  res_num_in_active:                      0
% 3.20/0.99  res_num_of_loops:                       139
% 3.20/0.99  res_forward_subset_subsumed:            27
% 3.20/0.99  res_backward_subset_subsumed:           2
% 3.20/0.99  res_forward_subsumed:                   0
% 3.20/0.99  res_backward_subsumed:                  0
% 3.20/0.99  res_forward_subsumption_resolution:     0
% 3.20/0.99  res_backward_subsumption_resolution:    0
% 3.20/0.99  res_clause_to_clause_subsumption:       220
% 3.20/0.99  res_orphan_elimination:                 0
% 3.20/0.99  res_tautology_del:                      45
% 3.20/0.99  res_num_eq_res_simplified:              0
% 3.20/0.99  res_num_sel_changes:                    0
% 3.20/0.99  res_moves_from_active_to_pass:          0
% 3.20/0.99  
% 3.20/0.99  ------ Superposition
% 3.20/0.99  
% 3.20/0.99  sup_time_total:                         0.
% 3.20/0.99  sup_time_generating:                    0.
% 3.20/0.99  sup_time_sim_full:                      0.
% 3.20/0.99  sup_time_sim_immed:                     0.
% 3.20/0.99  
% 3.20/0.99  sup_num_of_clauses:                     117
% 3.20/0.99  sup_num_in_active:                      67
% 3.20/0.99  sup_num_in_passive:                     50
% 3.20/0.99  sup_num_of_loops:                       81
% 3.20/0.99  sup_fw_superposition:                   60
% 3.20/0.99  sup_bw_superposition:                   76
% 3.20/0.99  sup_immediate_simplified:               46
% 3.20/0.99  sup_given_eliminated:                   0
% 3.20/0.99  comparisons_done:                       0
% 3.20/0.99  comparisons_avoided:                    0
% 3.20/0.99  
% 3.20/0.99  ------ Simplifications
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  sim_fw_subset_subsumed:                 9
% 3.20/0.99  sim_bw_subset_subsumed:                 4
% 3.20/0.99  sim_fw_subsumed:                        7
% 3.20/0.99  sim_bw_subsumed:                        0
% 3.20/0.99  sim_fw_subsumption_res:                 3
% 3.20/0.99  sim_bw_subsumption_res:                 0
% 3.20/0.99  sim_tautology_del:                      0
% 3.20/0.99  sim_eq_tautology_del:                   3
% 3.20/0.99  sim_eq_res_simp:                        0
% 3.20/0.99  sim_fw_demodulated:                     2
% 3.20/0.99  sim_bw_demodulated:                     12
% 3.20/0.99  sim_light_normalised:                   31
% 3.20/0.99  sim_joinable_taut:                      0
% 3.20/0.99  sim_joinable_simp:                      0
% 3.20/0.99  sim_ac_normalised:                      0
% 3.20/0.99  sim_smt_subsumption:                    0
% 3.20/0.99  
%------------------------------------------------------------------------------
