%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:24 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f69,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f72,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
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

fof(f74,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f68])).

cnf(c_784,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1538,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_partfun1(X0_51)
    | k6_partfun1(X0_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_3158,plain,
    ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
    | X0_50 = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
    inference(instantiation,[status(thm)],[c_1538])).

cnf(c_4691,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3158])).

cnf(c_4695,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_4691])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_760,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1267,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_762,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1265,plain,
    ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_2221,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1265])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1252,plain,
    ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_1646,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1267,c_1252])).

cnf(c_2241,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2221,c_1646])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_28,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2806,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2241,c_28,c_29])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1251,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_1632,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1251])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_777,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1250,plain,
    ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_1737,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1250])).

cnf(c_25,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_819,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_822,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_773,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_831,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1822,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1737,c_27,c_25,c_24,c_819,c_822,c_831])).

cnf(c_2809,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2806,c_1822])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_763,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1264,plain,
    ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_2365,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1264])).

cnf(c_853,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_2555,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2365,c_27,c_26,c_25,c_24,c_853])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_772,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1255,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_2886,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_1255])).

cnf(c_30,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_833,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_835,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_782,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_1501,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_1559,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_funct_2(X0_51,X2_50)
    | k2_funct_2(X0_51,X2_50) != X1_50 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1663,plain,
    ( X0_50 = k2_funct_2(X0_51,X1_50)
    | X0_50 != k2_funct_1(X1_50)
    | k2_funct_2(X0_51,X1_50) != k2_funct_1(X1_50) ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_1798,plain,
    ( k2_funct_2(X0_51,X0_50) != k2_funct_1(X0_50)
    | k2_funct_1(X0_50) = k2_funct_2(X0_51,X0_50)
    | k2_funct_1(X0_50) != k2_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_1800,plain,
    ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_funct_2(sK1,sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_780,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1799,plain,
    ( k2_funct_1(X0_50) = k2_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_1801,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_792,plain,
    ( ~ m1_subset_1(X0_50,X0_52)
    | m1_subset_1(X1_50,X1_52)
    | X1_52 != X0_52
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1486,plain,
    ( m1_subset_1(X0_50,X0_52)
    | ~ m1_subset_1(k2_funct_2(X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
    | X0_50 != k2_funct_2(X0_51,X1_50) ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_2138,plain,
    ( ~ m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_1(X0_50),X0_52)
    | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
    | k2_funct_1(X0_50) != k2_funct_2(X0_51,X0_50) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_2787,plain,
    ( ~ m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50) ),
    inference(instantiation,[status(thm)],[c_2138])).

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

cnf(c_3813,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2886,c_27,c_28,c_26,c_29,c_25,c_30,c_24,c_31,c_835,c_853,c_1501,c_1800,c_1801,c_2790])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1263,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_3230,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1263])).

cnf(c_3361,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3230,c_28])).

cnf(c_3362,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3361])).

cnf(c_3818,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3813,c_3362])).

cnf(c_834,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_769,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1258,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_2325,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1258])).

cnf(c_842,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_769])).

cnf(c_844,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_842])).

cnf(c_2549,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_28,c_29,c_30,c_31,c_844])).

cnf(c_2558,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2555,c_2549])).

cnf(c_2566,plain,
    ( v1_funct_1(k2_funct_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2558])).

cnf(c_2789,plain,
    ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
    | k2_funct_1(sK2) != k2_funct_2(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2787])).

cnf(c_3792,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_funct_1(X0_50))
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,k2_funct_1(X0_50)) = k5_relat_1(X0_50,k2_funct_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_3795,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3792])).

cnf(c_4020,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3818,c_27,c_26,c_25,c_24,c_834,c_853,c_1501,c_1800,c_1801,c_2566,c_2789,c_3795])).

cnf(c_23,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_761,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1266,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_2559,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2555,c_1266])).

cnf(c_4023,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4020,c_2559])).

cnf(c_4523,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2809,c_4023])).

cnf(c_793,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
    | X2_51 != X0_51
    | X3_51 != X1_51
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_2295,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
    | X2_51 != X0_51
    | X3_51 != X1_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
    | k6_partfun1(X8_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_793])).

cnf(c_3437,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
    | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
    | X3_51 != X0_51
    | X4_51 != X1_51
    | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
    | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
    inference(instantiation,[status(thm)],[c_2295])).

cnf(c_4325,plain,
    ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
    | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
    | X0_51 != X7_51
    | X1_51 != X8_51
    | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
    | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
    inference(instantiation,[status(thm)],[c_3437])).

cnf(c_4327,plain,
    ( X0_51 != X1_51
    | X2_51 != X3_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X8_51)
    | k6_partfun1(X9_51) != k6_partfun1(X8_51)
    | r2_relset_1(X0_51,X2_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50),k6_partfun1(X9_51)) = iProver_top
    | r2_relset_1(X1_51,X3_51,k6_partfun1(X8_51),k6_partfun1(X8_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4325])).

cnf(c_4329,plain,
    ( sK1 != sK1
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) = iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4327])).

cnf(c_3591,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_3594,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3591])).

cnf(c_785,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2165,plain,
    ( k2_relat_1(X0_50) != X0_51
    | sK1 != X0_51
    | sK1 = k2_relat_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_2166,plain,
    ( k2_relat_1(sK2) != sK1
    | sK1 = k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2165])).

cnf(c_15,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_768,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1259,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_5,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_774,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1253,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_2074,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_1253])).

cnf(c_2092,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_787,plain,
    ( X0_51 != X1_51
    | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
    theory(equality)).

cnf(c_1519,plain,
    ( sK1 != X0_51
    | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_1987,plain,
    ( sK1 != k2_relat_1(X0_50)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_1988,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_1517,plain,
    ( X0_50 != X1_50
    | k6_partfun1(sK1) != X1_50
    | k6_partfun1(sK1) = X0_50 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_1599,plain,
    ( X0_50 != k6_partfun1(X0_51)
    | k6_partfun1(sK1) = X0_50
    | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1517])).

cnf(c_1692,plain,
    ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_1693,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1692])).

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

cnf(c_312,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_313,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_2])).

cnf(c_318,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_3,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_333,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_318,c_3])).

cnf(c_756,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | k2_relat_1(X0_50) = X1_51 ),
    inference(subtyping,[status(esa)],[c_333])).

cnf(c_864,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_756])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_778,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_816,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_781,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_812,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_781])).

cnf(c_799,plain,
    ( sK1 != sK1
    | k6_partfun1(sK1) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4695,c_4523,c_4329,c_3594,c_2789,c_2566,c_2166,c_2092,c_1988,c_1801,c_1800,c_1693,c_1501,c_864,c_853,c_834,c_831,c_822,c_816,c_812,c_799,c_31,c_24,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.07/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/1.00  
% 3.07/1.00  ------  iProver source info
% 3.07/1.00  
% 3.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/1.00  git: non_committed_changes: false
% 3.07/1.00  git: last_make_outside_of_git: false
% 3.07/1.00  
% 3.07/1.00  ------ 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options
% 3.07/1.00  
% 3.07/1.00  --out_options                           all
% 3.07/1.00  --tptp_safe_out                         true
% 3.07/1.00  --problem_path                          ""
% 3.07/1.00  --include_path                          ""
% 3.07/1.00  --clausifier                            res/vclausify_rel
% 3.07/1.00  --clausifier_options                    --mode clausify
% 3.07/1.00  --stdin                                 false
% 3.07/1.00  --stats_out                             all
% 3.07/1.00  
% 3.07/1.00  ------ General Options
% 3.07/1.00  
% 3.07/1.00  --fof                                   false
% 3.07/1.00  --time_out_real                         305.
% 3.07/1.00  --time_out_virtual                      -1.
% 3.07/1.00  --symbol_type_check                     false
% 3.07/1.00  --clausify_out                          false
% 3.07/1.00  --sig_cnt_out                           false
% 3.07/1.00  --trig_cnt_out                          false
% 3.07/1.00  --trig_cnt_out_tolerance                1.
% 3.07/1.00  --trig_cnt_out_sk_spl                   false
% 3.07/1.00  --abstr_cl_out                          false
% 3.07/1.00  
% 3.07/1.00  ------ Global Options
% 3.07/1.00  
% 3.07/1.00  --schedule                              default
% 3.07/1.00  --add_important_lit                     false
% 3.07/1.00  --prop_solver_per_cl                    1000
% 3.07/1.00  --min_unsat_core                        false
% 3.07/1.00  --soft_assumptions                      false
% 3.07/1.00  --soft_lemma_size                       3
% 3.07/1.00  --prop_impl_unit_size                   0
% 3.07/1.00  --prop_impl_unit                        []
% 3.07/1.00  --share_sel_clauses                     true
% 3.07/1.00  --reset_solvers                         false
% 3.07/1.00  --bc_imp_inh                            [conj_cone]
% 3.07/1.00  --conj_cone_tolerance                   3.
% 3.07/1.00  --extra_neg_conj                        none
% 3.07/1.00  --large_theory_mode                     true
% 3.07/1.00  --prolific_symb_bound                   200
% 3.07/1.00  --lt_threshold                          2000
% 3.07/1.00  --clause_weak_htbl                      true
% 3.07/1.00  --gc_record_bc_elim                     false
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing Options
% 3.07/1.00  
% 3.07/1.00  --preprocessing_flag                    true
% 3.07/1.00  --time_out_prep_mult                    0.1
% 3.07/1.00  --splitting_mode                        input
% 3.07/1.00  --splitting_grd                         true
% 3.07/1.00  --splitting_cvd                         false
% 3.07/1.00  --splitting_cvd_svl                     false
% 3.07/1.00  --splitting_nvd                         32
% 3.07/1.00  --sub_typing                            true
% 3.07/1.00  --prep_gs_sim                           true
% 3.07/1.00  --prep_unflatten                        true
% 3.07/1.00  --prep_res_sim                          true
% 3.07/1.00  --prep_upred                            true
% 3.07/1.00  --prep_sem_filter                       exhaustive
% 3.07/1.00  --prep_sem_filter_out                   false
% 3.07/1.00  --pred_elim                             true
% 3.07/1.00  --res_sim_input                         true
% 3.07/1.00  --eq_ax_congr_red                       true
% 3.07/1.00  --pure_diseq_elim                       true
% 3.07/1.00  --brand_transform                       false
% 3.07/1.00  --non_eq_to_eq                          false
% 3.07/1.00  --prep_def_merge                        true
% 3.07/1.00  --prep_def_merge_prop_impl              false
% 3.07/1.00  --prep_def_merge_mbd                    true
% 3.07/1.00  --prep_def_merge_tr_red                 false
% 3.07/1.00  --prep_def_merge_tr_cl                  false
% 3.07/1.00  --smt_preprocessing                     true
% 3.07/1.00  --smt_ac_axioms                         fast
% 3.07/1.00  --preprocessed_out                      false
% 3.07/1.00  --preprocessed_stats                    false
% 3.07/1.00  
% 3.07/1.00  ------ Abstraction refinement Options
% 3.07/1.00  
% 3.07/1.00  --abstr_ref                             []
% 3.07/1.00  --abstr_ref_prep                        false
% 3.07/1.00  --abstr_ref_until_sat                   false
% 3.07/1.00  --abstr_ref_sig_restrict                funpre
% 3.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/1.00  --abstr_ref_under                       []
% 3.07/1.00  
% 3.07/1.00  ------ SAT Options
% 3.07/1.00  
% 3.07/1.00  --sat_mode                              false
% 3.07/1.00  --sat_fm_restart_options                ""
% 3.07/1.00  --sat_gr_def                            false
% 3.07/1.00  --sat_epr_types                         true
% 3.07/1.00  --sat_non_cyclic_types                  false
% 3.07/1.00  --sat_finite_models                     false
% 3.07/1.00  --sat_fm_lemmas                         false
% 3.07/1.00  --sat_fm_prep                           false
% 3.07/1.00  --sat_fm_uc_incr                        true
% 3.07/1.00  --sat_out_model                         small
% 3.07/1.00  --sat_out_clauses                       false
% 3.07/1.00  
% 3.07/1.00  ------ QBF Options
% 3.07/1.00  
% 3.07/1.00  --qbf_mode                              false
% 3.07/1.00  --qbf_elim_univ                         false
% 3.07/1.00  --qbf_dom_inst                          none
% 3.07/1.00  --qbf_dom_pre_inst                      false
% 3.07/1.00  --qbf_sk_in                             false
% 3.07/1.00  --qbf_pred_elim                         true
% 3.07/1.00  --qbf_split                             512
% 3.07/1.00  
% 3.07/1.00  ------ BMC1 Options
% 3.07/1.00  
% 3.07/1.00  --bmc1_incremental                      false
% 3.07/1.00  --bmc1_axioms                           reachable_all
% 3.07/1.00  --bmc1_min_bound                        0
% 3.07/1.00  --bmc1_max_bound                        -1
% 3.07/1.00  --bmc1_max_bound_default                -1
% 3.07/1.00  --bmc1_symbol_reachability              true
% 3.07/1.00  --bmc1_property_lemmas                  false
% 3.07/1.00  --bmc1_k_induction                      false
% 3.07/1.00  --bmc1_non_equiv_states                 false
% 3.07/1.00  --bmc1_deadlock                         false
% 3.07/1.00  --bmc1_ucm                              false
% 3.07/1.00  --bmc1_add_unsat_core                   none
% 3.07/1.00  --bmc1_unsat_core_children              false
% 3.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/1.00  --bmc1_out_stat                         full
% 3.07/1.00  --bmc1_ground_init                      false
% 3.07/1.00  --bmc1_pre_inst_next_state              false
% 3.07/1.00  --bmc1_pre_inst_state                   false
% 3.07/1.00  --bmc1_pre_inst_reach_state             false
% 3.07/1.00  --bmc1_out_unsat_core                   false
% 3.07/1.00  --bmc1_aig_witness_out                  false
% 3.07/1.00  --bmc1_verbose                          false
% 3.07/1.00  --bmc1_dump_clauses_tptp                false
% 3.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.07/1.00  --bmc1_dump_file                        -
% 3.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.07/1.00  --bmc1_ucm_extend_mode                  1
% 3.07/1.00  --bmc1_ucm_init_mode                    2
% 3.07/1.00  --bmc1_ucm_cone_mode                    none
% 3.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.07/1.00  --bmc1_ucm_relax_model                  4
% 3.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/1.00  --bmc1_ucm_layered_model                none
% 3.07/1.00  --bmc1_ucm_max_lemma_size               10
% 3.07/1.00  
% 3.07/1.00  ------ AIG Options
% 3.07/1.00  
% 3.07/1.00  --aig_mode                              false
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation Options
% 3.07/1.00  
% 3.07/1.00  --instantiation_flag                    true
% 3.07/1.00  --inst_sos_flag                         false
% 3.07/1.00  --inst_sos_phase                        true
% 3.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel_side                     num_symb
% 3.07/1.00  --inst_solver_per_active                1400
% 3.07/1.00  --inst_solver_calls_frac                1.
% 3.07/1.00  --inst_passive_queue_type               priority_queues
% 3.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/1.00  --inst_passive_queues_freq              [25;2]
% 3.07/1.00  --inst_dismatching                      true
% 3.07/1.00  --inst_eager_unprocessed_to_passive     true
% 3.07/1.00  --inst_prop_sim_given                   true
% 3.07/1.00  --inst_prop_sim_new                     false
% 3.07/1.00  --inst_subs_new                         false
% 3.07/1.00  --inst_eq_res_simp                      false
% 3.07/1.00  --inst_subs_given                       false
% 3.07/1.00  --inst_orphan_elimination               true
% 3.07/1.00  --inst_learning_loop_flag               true
% 3.07/1.00  --inst_learning_start                   3000
% 3.07/1.00  --inst_learning_factor                  2
% 3.07/1.00  --inst_start_prop_sim_after_learn       3
% 3.07/1.00  --inst_sel_renew                        solver
% 3.07/1.00  --inst_lit_activity_flag                true
% 3.07/1.00  --inst_restr_to_given                   false
% 3.07/1.00  --inst_activity_threshold               500
% 3.07/1.00  --inst_out_proof                        true
% 3.07/1.00  
% 3.07/1.00  ------ Resolution Options
% 3.07/1.00  
% 3.07/1.00  --resolution_flag                       true
% 3.07/1.00  --res_lit_sel                           adaptive
% 3.07/1.00  --res_lit_sel_side                      none
% 3.07/1.00  --res_ordering                          kbo
% 3.07/1.00  --res_to_prop_solver                    active
% 3.07/1.00  --res_prop_simpl_new                    false
% 3.07/1.00  --res_prop_simpl_given                  true
% 3.07/1.00  --res_passive_queue_type                priority_queues
% 3.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/1.00  --res_passive_queues_freq               [15;5]
% 3.07/1.00  --res_forward_subs                      full
% 3.07/1.00  --res_backward_subs                     full
% 3.07/1.00  --res_forward_subs_resolution           true
% 3.07/1.00  --res_backward_subs_resolution          true
% 3.07/1.00  --res_orphan_elimination                true
% 3.07/1.00  --res_time_limit                        2.
% 3.07/1.00  --res_out_proof                         true
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Options
% 3.07/1.00  
% 3.07/1.00  --superposition_flag                    true
% 3.07/1.00  --sup_passive_queue_type                priority_queues
% 3.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.07/1.00  --demod_completeness_check              fast
% 3.07/1.00  --demod_use_ground                      true
% 3.07/1.00  --sup_to_prop_solver                    passive
% 3.07/1.00  --sup_prop_simpl_new                    true
% 3.07/1.00  --sup_prop_simpl_given                  true
% 3.07/1.00  --sup_fun_splitting                     false
% 3.07/1.00  --sup_smt_interval                      50000
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Simplification Setup
% 3.07/1.00  
% 3.07/1.00  --sup_indices_passive                   []
% 3.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_full_bw                           [BwDemod]
% 3.07/1.00  --sup_immed_triv                        [TrivRules]
% 3.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_immed_bw_main                     []
% 3.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  
% 3.07/1.00  ------ Combination Options
% 3.07/1.00  
% 3.07/1.00  --comb_res_mult                         3
% 3.07/1.00  --comb_sup_mult                         2
% 3.07/1.00  --comb_inst_mult                        10
% 3.07/1.00  
% 3.07/1.00  ------ Debug Options
% 3.07/1.00  
% 3.07/1.00  --dbg_backtrace                         false
% 3.07/1.00  --dbg_dump_prop_clauses                 false
% 3.07/1.00  --dbg_dump_prop_clauses_file            -
% 3.07/1.00  --dbg_out_stat                          false
% 3.07/1.00  ------ Parsing...
% 3.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/1.00  ------ Proving...
% 3.07/1.00  ------ Problem Properties 
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  clauses                                 23
% 3.07/1.00  conjectures                             5
% 3.07/1.00  EPR                                     3
% 3.07/1.00  Horn                                    23
% 3.07/1.00  unary                                   8
% 3.07/1.00  binary                                  3
% 3.07/1.00  lits                                    67
% 3.07/1.00  lits eq                                 7
% 3.07/1.00  fd_pure                                 0
% 3.07/1.00  fd_pseudo                               0
% 3.07/1.00  fd_cond                                 0
% 3.07/1.00  fd_pseudo_cond                          1
% 3.07/1.00  AC symbols                              0
% 3.07/1.00  
% 3.07/1.00  ------ Schedule dynamic 5 is on 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  ------ 
% 3.07/1.00  Current options:
% 3.07/1.00  ------ 
% 3.07/1.00  
% 3.07/1.00  ------ Input Options
% 3.07/1.00  
% 3.07/1.00  --out_options                           all
% 3.07/1.00  --tptp_safe_out                         true
% 3.07/1.00  --problem_path                          ""
% 3.07/1.00  --include_path                          ""
% 3.07/1.00  --clausifier                            res/vclausify_rel
% 3.07/1.00  --clausifier_options                    --mode clausify
% 3.07/1.00  --stdin                                 false
% 3.07/1.00  --stats_out                             all
% 3.07/1.00  
% 3.07/1.00  ------ General Options
% 3.07/1.00  
% 3.07/1.00  --fof                                   false
% 3.07/1.00  --time_out_real                         305.
% 3.07/1.00  --time_out_virtual                      -1.
% 3.07/1.00  --symbol_type_check                     false
% 3.07/1.00  --clausify_out                          false
% 3.07/1.00  --sig_cnt_out                           false
% 3.07/1.00  --trig_cnt_out                          false
% 3.07/1.00  --trig_cnt_out_tolerance                1.
% 3.07/1.00  --trig_cnt_out_sk_spl                   false
% 3.07/1.00  --abstr_cl_out                          false
% 3.07/1.00  
% 3.07/1.00  ------ Global Options
% 3.07/1.00  
% 3.07/1.00  --schedule                              default
% 3.07/1.00  --add_important_lit                     false
% 3.07/1.00  --prop_solver_per_cl                    1000
% 3.07/1.00  --min_unsat_core                        false
% 3.07/1.00  --soft_assumptions                      false
% 3.07/1.00  --soft_lemma_size                       3
% 3.07/1.00  --prop_impl_unit_size                   0
% 3.07/1.00  --prop_impl_unit                        []
% 3.07/1.00  --share_sel_clauses                     true
% 3.07/1.00  --reset_solvers                         false
% 3.07/1.00  --bc_imp_inh                            [conj_cone]
% 3.07/1.00  --conj_cone_tolerance                   3.
% 3.07/1.00  --extra_neg_conj                        none
% 3.07/1.00  --large_theory_mode                     true
% 3.07/1.00  --prolific_symb_bound                   200
% 3.07/1.00  --lt_threshold                          2000
% 3.07/1.00  --clause_weak_htbl                      true
% 3.07/1.00  --gc_record_bc_elim                     false
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing Options
% 3.07/1.00  
% 3.07/1.00  --preprocessing_flag                    true
% 3.07/1.00  --time_out_prep_mult                    0.1
% 3.07/1.00  --splitting_mode                        input
% 3.07/1.00  --splitting_grd                         true
% 3.07/1.00  --splitting_cvd                         false
% 3.07/1.00  --splitting_cvd_svl                     false
% 3.07/1.00  --splitting_nvd                         32
% 3.07/1.00  --sub_typing                            true
% 3.07/1.00  --prep_gs_sim                           true
% 3.07/1.00  --prep_unflatten                        true
% 3.07/1.00  --prep_res_sim                          true
% 3.07/1.00  --prep_upred                            true
% 3.07/1.00  --prep_sem_filter                       exhaustive
% 3.07/1.00  --prep_sem_filter_out                   false
% 3.07/1.00  --pred_elim                             true
% 3.07/1.00  --res_sim_input                         true
% 3.07/1.00  --eq_ax_congr_red                       true
% 3.07/1.00  --pure_diseq_elim                       true
% 3.07/1.00  --brand_transform                       false
% 3.07/1.00  --non_eq_to_eq                          false
% 3.07/1.00  --prep_def_merge                        true
% 3.07/1.00  --prep_def_merge_prop_impl              false
% 3.07/1.00  --prep_def_merge_mbd                    true
% 3.07/1.00  --prep_def_merge_tr_red                 false
% 3.07/1.00  --prep_def_merge_tr_cl                  false
% 3.07/1.00  --smt_preprocessing                     true
% 3.07/1.00  --smt_ac_axioms                         fast
% 3.07/1.00  --preprocessed_out                      false
% 3.07/1.00  --preprocessed_stats                    false
% 3.07/1.00  
% 3.07/1.00  ------ Abstraction refinement Options
% 3.07/1.00  
% 3.07/1.00  --abstr_ref                             []
% 3.07/1.00  --abstr_ref_prep                        false
% 3.07/1.00  --abstr_ref_until_sat                   false
% 3.07/1.00  --abstr_ref_sig_restrict                funpre
% 3.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/1.00  --abstr_ref_under                       []
% 3.07/1.00  
% 3.07/1.00  ------ SAT Options
% 3.07/1.00  
% 3.07/1.00  --sat_mode                              false
% 3.07/1.00  --sat_fm_restart_options                ""
% 3.07/1.00  --sat_gr_def                            false
% 3.07/1.00  --sat_epr_types                         true
% 3.07/1.00  --sat_non_cyclic_types                  false
% 3.07/1.00  --sat_finite_models                     false
% 3.07/1.00  --sat_fm_lemmas                         false
% 3.07/1.00  --sat_fm_prep                           false
% 3.07/1.00  --sat_fm_uc_incr                        true
% 3.07/1.00  --sat_out_model                         small
% 3.07/1.00  --sat_out_clauses                       false
% 3.07/1.00  
% 3.07/1.00  ------ QBF Options
% 3.07/1.00  
% 3.07/1.00  --qbf_mode                              false
% 3.07/1.00  --qbf_elim_univ                         false
% 3.07/1.00  --qbf_dom_inst                          none
% 3.07/1.00  --qbf_dom_pre_inst                      false
% 3.07/1.00  --qbf_sk_in                             false
% 3.07/1.00  --qbf_pred_elim                         true
% 3.07/1.00  --qbf_split                             512
% 3.07/1.00  
% 3.07/1.00  ------ BMC1 Options
% 3.07/1.00  
% 3.07/1.00  --bmc1_incremental                      false
% 3.07/1.00  --bmc1_axioms                           reachable_all
% 3.07/1.00  --bmc1_min_bound                        0
% 3.07/1.00  --bmc1_max_bound                        -1
% 3.07/1.00  --bmc1_max_bound_default                -1
% 3.07/1.00  --bmc1_symbol_reachability              true
% 3.07/1.00  --bmc1_property_lemmas                  false
% 3.07/1.00  --bmc1_k_induction                      false
% 3.07/1.00  --bmc1_non_equiv_states                 false
% 3.07/1.00  --bmc1_deadlock                         false
% 3.07/1.00  --bmc1_ucm                              false
% 3.07/1.00  --bmc1_add_unsat_core                   none
% 3.07/1.00  --bmc1_unsat_core_children              false
% 3.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/1.00  --bmc1_out_stat                         full
% 3.07/1.00  --bmc1_ground_init                      false
% 3.07/1.00  --bmc1_pre_inst_next_state              false
% 3.07/1.00  --bmc1_pre_inst_state                   false
% 3.07/1.00  --bmc1_pre_inst_reach_state             false
% 3.07/1.00  --bmc1_out_unsat_core                   false
% 3.07/1.00  --bmc1_aig_witness_out                  false
% 3.07/1.00  --bmc1_verbose                          false
% 3.07/1.00  --bmc1_dump_clauses_tptp                false
% 3.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.07/1.00  --bmc1_dump_file                        -
% 3.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.07/1.00  --bmc1_ucm_extend_mode                  1
% 3.07/1.00  --bmc1_ucm_init_mode                    2
% 3.07/1.00  --bmc1_ucm_cone_mode                    none
% 3.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.07/1.00  --bmc1_ucm_relax_model                  4
% 3.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/1.00  --bmc1_ucm_layered_model                none
% 3.07/1.00  --bmc1_ucm_max_lemma_size               10
% 3.07/1.00  
% 3.07/1.00  ------ AIG Options
% 3.07/1.00  
% 3.07/1.00  --aig_mode                              false
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation Options
% 3.07/1.00  
% 3.07/1.00  --instantiation_flag                    true
% 3.07/1.00  --inst_sos_flag                         false
% 3.07/1.00  --inst_sos_phase                        true
% 3.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/1.00  --inst_lit_sel_side                     none
% 3.07/1.00  --inst_solver_per_active                1400
% 3.07/1.00  --inst_solver_calls_frac                1.
% 3.07/1.00  --inst_passive_queue_type               priority_queues
% 3.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/1.00  --inst_passive_queues_freq              [25;2]
% 3.07/1.00  --inst_dismatching                      true
% 3.07/1.00  --inst_eager_unprocessed_to_passive     true
% 3.07/1.00  --inst_prop_sim_given                   true
% 3.07/1.00  --inst_prop_sim_new                     false
% 3.07/1.00  --inst_subs_new                         false
% 3.07/1.00  --inst_eq_res_simp                      false
% 3.07/1.00  --inst_subs_given                       false
% 3.07/1.00  --inst_orphan_elimination               true
% 3.07/1.00  --inst_learning_loop_flag               true
% 3.07/1.00  --inst_learning_start                   3000
% 3.07/1.00  --inst_learning_factor                  2
% 3.07/1.00  --inst_start_prop_sim_after_learn       3
% 3.07/1.00  --inst_sel_renew                        solver
% 3.07/1.00  --inst_lit_activity_flag                true
% 3.07/1.00  --inst_restr_to_given                   false
% 3.07/1.00  --inst_activity_threshold               500
% 3.07/1.00  --inst_out_proof                        true
% 3.07/1.00  
% 3.07/1.00  ------ Resolution Options
% 3.07/1.00  
% 3.07/1.00  --resolution_flag                       false
% 3.07/1.00  --res_lit_sel                           adaptive
% 3.07/1.00  --res_lit_sel_side                      none
% 3.07/1.00  --res_ordering                          kbo
% 3.07/1.00  --res_to_prop_solver                    active
% 3.07/1.00  --res_prop_simpl_new                    false
% 3.07/1.00  --res_prop_simpl_given                  true
% 3.07/1.00  --res_passive_queue_type                priority_queues
% 3.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/1.00  --res_passive_queues_freq               [15;5]
% 3.07/1.00  --res_forward_subs                      full
% 3.07/1.00  --res_backward_subs                     full
% 3.07/1.00  --res_forward_subs_resolution           true
% 3.07/1.00  --res_backward_subs_resolution          true
% 3.07/1.00  --res_orphan_elimination                true
% 3.07/1.00  --res_time_limit                        2.
% 3.07/1.00  --res_out_proof                         true
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Options
% 3.07/1.00  
% 3.07/1.00  --superposition_flag                    true
% 3.07/1.00  --sup_passive_queue_type                priority_queues
% 3.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.07/1.00  --demod_completeness_check              fast
% 3.07/1.00  --demod_use_ground                      true
% 3.07/1.00  --sup_to_prop_solver                    passive
% 3.07/1.00  --sup_prop_simpl_new                    true
% 3.07/1.00  --sup_prop_simpl_given                  true
% 3.07/1.00  --sup_fun_splitting                     false
% 3.07/1.00  --sup_smt_interval                      50000
% 3.07/1.00  
% 3.07/1.00  ------ Superposition Simplification Setup
% 3.07/1.00  
% 3.07/1.00  --sup_indices_passive                   []
% 3.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_full_bw                           [BwDemod]
% 3.07/1.00  --sup_immed_triv                        [TrivRules]
% 3.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_immed_bw_main                     []
% 3.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/1.00  
% 3.07/1.00  ------ Combination Options
% 3.07/1.00  
% 3.07/1.00  --comb_res_mult                         3
% 3.07/1.00  --comb_sup_mult                         2
% 3.07/1.00  --comb_inst_mult                        10
% 3.07/1.00  
% 3.07/1.00  ------ Debug Options
% 3.07/1.00  
% 3.07/1.00  --dbg_backtrace                         false
% 3.07/1.00  --dbg_dump_prop_clauses                 false
% 3.07/1.00  --dbg_dump_prop_clauses_file            -
% 3.07/1.00  --dbg_out_stat                          false
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  ------ Proving...
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  % SZS status Theorem for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  fof(f15,conjecture,(
% 3.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f16,negated_conjecture,(
% 3.07/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.07/1.00    inference(negated_conjecture,[],[f15])).
% 3.07/1.00  
% 3.07/1.00  fof(f39,plain,(
% 3.07/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.07/1.00    inference(ennf_transformation,[],[f16])).
% 3.07/1.00  
% 3.07/1.00  fof(f40,plain,(
% 3.07/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.07/1.00    inference(flattening,[],[f39])).
% 3.07/1.00  
% 3.07/1.00  fof(f44,plain,(
% 3.07/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.07/1.00    introduced(choice_axiom,[])).
% 3.07/1.00  
% 3.07/1.00  fof(f45,plain,(
% 3.07/1.00    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f44])).
% 3.07/1.00  
% 3.07/1.00  fof(f73,plain,(
% 3.07/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.07/1.00    inference(cnf_transformation,[],[f45])).
% 3.07/1.00  
% 3.07/1.00  fof(f14,axiom,(
% 3.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f37,plain,(
% 3.07/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.07/1.00    inference(ennf_transformation,[],[f14])).
% 3.07/1.00  
% 3.07/1.00  fof(f38,plain,(
% 3.07/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.07/1.00    inference(flattening,[],[f37])).
% 3.07/1.00  
% 3.07/1.00  fof(f69,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f38])).
% 3.07/1.00  
% 3.07/1.00  fof(f4,axiom,(
% 3.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f24,plain,(
% 3.07/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/1.00    inference(ennf_transformation,[],[f4])).
% 3.07/1.00  
% 3.07/1.00  fof(f50,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f24])).
% 3.07/1.00  
% 3.07/1.00  fof(f70,plain,(
% 3.07/1.00    v1_funct_1(sK2)),
% 3.07/1.00    inference(cnf_transformation,[],[f45])).
% 3.07/1.00  
% 3.07/1.00  fof(f71,plain,(
% 3.07/1.00    v1_funct_2(sK2,sK1,sK1)),
% 3.07/1.00    inference(cnf_transformation,[],[f45])).
% 3.07/1.00  
% 3.07/1.00  fof(f2,axiom,(
% 3.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f22,plain,(
% 3.07/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/1.00    inference(ennf_transformation,[],[f2])).
% 3.07/1.00  
% 3.07/1.00  fof(f48,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f22])).
% 3.07/1.00  
% 3.07/1.00  fof(f1,axiom,(
% 3.07/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f20,plain,(
% 3.07/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.07/1.00    inference(ennf_transformation,[],[f1])).
% 3.07/1.00  
% 3.07/1.00  fof(f21,plain,(
% 3.07/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.07/1.00    inference(flattening,[],[f20])).
% 3.07/1.00  
% 3.07/1.00  fof(f46,plain,(
% 3.07/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f21])).
% 3.07/1.00  
% 3.07/1.00  fof(f13,axiom,(
% 3.07/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f68,plain,(
% 3.07/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f13])).
% 3.07/1.00  
% 3.07/1.00  fof(f76,plain,(
% 3.07/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(definition_unfolding,[],[f46,f68])).
% 3.07/1.00  
% 3.07/1.00  fof(f72,plain,(
% 3.07/1.00    v3_funct_2(sK2,sK1,sK1)),
% 3.07/1.00    inference(cnf_transformation,[],[f45])).
% 3.07/1.00  
% 3.07/1.00  fof(f6,axiom,(
% 3.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f27,plain,(
% 3.07/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/1.00    inference(ennf_transformation,[],[f6])).
% 3.07/1.00  
% 3.07/1.00  fof(f28,plain,(
% 3.07/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/1.00    inference(flattening,[],[f27])).
% 3.07/1.00  
% 3.07/1.00  fof(f53,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f28])).
% 3.07/1.00  
% 3.07/1.00  fof(f12,axiom,(
% 3.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f35,plain,(
% 3.07/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.07/1.00    inference(ennf_transformation,[],[f12])).
% 3.07/1.00  
% 3.07/1.00  fof(f36,plain,(
% 3.07/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.07/1.00    inference(flattening,[],[f35])).
% 3.07/1.00  
% 3.07/1.00  fof(f67,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f36])).
% 3.07/1.00  
% 3.07/1.00  fof(f8,axiom,(
% 3.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f31,plain,(
% 3.07/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.07/1.00    inference(ennf_transformation,[],[f8])).
% 3.07/1.00  
% 3.07/1.00  fof(f32,plain,(
% 3.07/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.07/1.00    inference(flattening,[],[f31])).
% 3.07/1.00  
% 3.07/1.00  fof(f60,plain,(
% 3.07/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f32])).
% 3.07/1.00  
% 3.07/1.00  fof(f11,axiom,(
% 3.07/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f33,plain,(
% 3.07/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.07/1.00    inference(ennf_transformation,[],[f11])).
% 3.07/1.00  
% 3.07/1.00  fof(f34,plain,(
% 3.07/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.07/1.00    inference(flattening,[],[f33])).
% 3.07/1.00  
% 3.07/1.00  fof(f66,plain,(
% 3.07/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f34])).
% 3.07/1.00  
% 3.07/1.00  fof(f57,plain,(
% 3.07/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f32])).
% 3.07/1.00  
% 3.07/1.00  fof(f74,plain,(
% 3.07/1.00    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.07/1.00    inference(cnf_transformation,[],[f45])).
% 3.07/1.00  
% 3.07/1.00  fof(f9,axiom,(
% 3.07/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f17,plain,(
% 3.07/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.07/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.07/1.00  
% 3.07/1.00  fof(f61,plain,(
% 3.07/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f17])).
% 3.07/1.00  
% 3.07/1.00  fof(f5,axiom,(
% 3.07/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f25,plain,(
% 3.07/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.07/1.00    inference(ennf_transformation,[],[f5])).
% 3.07/1.00  
% 3.07/1.00  fof(f26,plain,(
% 3.07/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/1.00    inference(flattening,[],[f25])).
% 3.07/1.00  
% 3.07/1.00  fof(f51,plain,(
% 3.07/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f26])).
% 3.07/1.00  
% 3.07/1.00  fof(f54,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f28])).
% 3.07/1.00  
% 3.07/1.00  fof(f7,axiom,(
% 3.07/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f29,plain,(
% 3.07/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.07/1.00    inference(ennf_transformation,[],[f7])).
% 3.07/1.00  
% 3.07/1.00  fof(f30,plain,(
% 3.07/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.07/1.00    inference(flattening,[],[f29])).
% 3.07/1.00  
% 3.07/1.00  fof(f41,plain,(
% 3.07/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.07/1.00    inference(nnf_transformation,[],[f30])).
% 3.07/1.00  
% 3.07/1.00  fof(f55,plain,(
% 3.07/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f41])).
% 3.07/1.00  
% 3.07/1.00  fof(f3,axiom,(
% 3.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/1.00  
% 3.07/1.00  fof(f19,plain,(
% 3.07/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.07/1.00    inference(pure_predicate_removal,[],[f3])).
% 3.07/1.00  
% 3.07/1.00  fof(f23,plain,(
% 3.07/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.07/1.00    inference(ennf_transformation,[],[f19])).
% 3.07/1.00  
% 3.07/1.00  fof(f49,plain,(
% 3.07/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.07/1.00    inference(cnf_transformation,[],[f23])).
% 3.07/1.00  
% 3.07/1.00  fof(f47,plain,(
% 3.07/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(cnf_transformation,[],[f21])).
% 3.07/1.00  
% 3.07/1.00  fof(f75,plain,(
% 3.07/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.07/1.00    inference(definition_unfolding,[],[f47,f68])).
% 3.07/1.00  
% 3.07/1.00  cnf(c_784,plain,
% 3.07/1.00      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 3.07/1.00      theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1538,plain,
% 3.07/1.00      ( X0_50 != X1_50
% 3.07/1.00      | X0_50 = k6_partfun1(X0_51)
% 3.07/1.00      | k6_partfun1(X0_51) != X1_50 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_784]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3158,plain,
% 3.07/1.00      ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
% 3.07/1.00      | X0_50 = k6_partfun1(sK1)
% 3.07/1.00      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1538]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4691,plain,
% 3.07/1.00      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 3.07/1.00      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.07/1.00      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_3158]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4695,plain,
% 3.07/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 3.07/1.00      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.07/1.00      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_4691]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_24,negated_conjecture,
% 3.07/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.07/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_760,negated_conjecture,
% 3.07/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1267,plain,
% 3.07/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_22,plain,
% 3.07/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.07/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_762,plain,
% 3.07/1.00      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 3.07/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1265,plain,
% 3.07/1.00      ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
% 3.07/1.00      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2221,plain,
% 3.07/1.00      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.07/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1267,c_1265]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_775,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.07/1.00      | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1252,plain,
% 3.07/1.00      ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1646,plain,
% 3.07/1.00      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1267,c_1252]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2241,plain,
% 3.07/1.00      ( k1_relat_1(sK2) = sK1
% 3.07/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2221,c_1646]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_27,negated_conjecture,
% 3.07/1.00      ( v1_funct_1(sK2) ),
% 3.07/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_28,plain,
% 3.07/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_26,negated_conjecture,
% 3.07/1.00      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.07/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_29,plain,
% 3.07/1.00      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2806,plain,
% 3.07/1.00      ( k1_relat_1(sK2) = sK1 ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_2241,c_28,c_29]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | v1_relat_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_776,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.07/1.00      | v1_relat_1(X0_50) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1251,plain,
% 3.07/1.00      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.07/1.00      | v1_relat_1(X0_50) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1632,plain,
% 3.07/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1267,c_1251]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1,plain,
% 3.07/1.00      ( ~ v1_relat_1(X0)
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | ~ v2_funct_1(X0)
% 3.07/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_777,plain,
% 3.07/1.00      ( ~ v1_relat_1(X0_50)
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | ~ v2_funct_1(X0_50)
% 3.07/1.00      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1250,plain,
% 3.07/1.00      ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
% 3.07/1.00      | v1_relat_1(X0_50) != iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.07/1.00      | v2_funct_1(X0_50) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1737,plain,
% 3.07/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top
% 3.07/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1632,c_1250]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_25,negated_conjecture,
% 3.07/1.00      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.07/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_819,plain,
% 3.07/1.00      ( ~ v1_relat_1(sK2)
% 3.07/1.00      | ~ v1_funct_1(sK2)
% 3.07/1.00      | ~ v2_funct_1(sK2)
% 3.07/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_777]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_822,plain,
% 3.07/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | v1_relat_1(sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_776]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_7,plain,
% 3.07/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | v2_funct_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_773,plain,
% 3.07/1.00      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 3.07/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | v2_funct_1(X0_50) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_831,plain,
% 3.07/1.00      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.07/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ v1_funct_1(sK2)
% 3.07/1.00      | v2_funct_1(sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_773]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1822,plain,
% 3.07/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_1737,c_27,c_25,c_24,c_819,c_822,c_831]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2809,plain,
% 3.07/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2806,c_1822]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_21,plain,
% 3.07/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.07/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_763,plain,
% 3.07/1.00      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 3.07/1.00      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 3.07/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1264,plain,
% 3.07/1.00      ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
% 3.07/1.00      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2365,plain,
% 3.07/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.07/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1267,c_1264]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_853,plain,
% 3.07/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.07/1.00      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.07/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ v1_funct_1(sK2)
% 3.07/1.00      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_763]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2555,plain,
% 3.07/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_2365,c_27,c_26,c_25,c_24,c_853]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_11,plain,
% 3.07/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.07/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.07/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.07/1.00      | ~ v1_funct_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_772,plain,
% 3.07/1.00      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 3.07/1.00      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 3.07/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.07/1.00      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1255,plain,
% 3.07/1.00      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.07/1.00      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2886,plain,
% 3.07/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.07/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2555,c_1255]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_30,plain,
% 3.07/1.00      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_31,plain,
% 3.07/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_833,plain,
% 3.07/1.00      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.07/1.00      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_835,plain,
% 3.07/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.07/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_833]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_782,plain,( X0_52 = X0_52 ),theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1501,plain,
% 3.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_782]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1559,plain,
% 3.07/1.00      ( X0_50 != X1_50
% 3.07/1.00      | X0_50 = k2_funct_2(X0_51,X2_50)
% 3.07/1.00      | k2_funct_2(X0_51,X2_50) != X1_50 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_784]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1663,plain,
% 3.07/1.00      ( X0_50 = k2_funct_2(X0_51,X1_50)
% 3.07/1.00      | X0_50 != k2_funct_1(X1_50)
% 3.07/1.00      | k2_funct_2(X0_51,X1_50) != k2_funct_1(X1_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1559]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1798,plain,
% 3.07/1.00      ( k2_funct_2(X0_51,X0_50) != k2_funct_1(X0_50)
% 3.07/1.00      | k2_funct_1(X0_50) = k2_funct_2(X0_51,X0_50)
% 3.07/1.00      | k2_funct_1(X0_50) != k2_funct_1(X0_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1663]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1800,plain,
% 3.07/1.00      ( k2_funct_2(sK1,sK2) != k2_funct_1(sK2)
% 3.07/1.00      | k2_funct_1(sK2) = k2_funct_2(sK1,sK2)
% 3.07/1.00      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1798]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_780,plain,( X0_50 = X0_50 ),theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1799,plain,
% 3.07/1.00      ( k2_funct_1(X0_50) = k2_funct_1(X0_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_780]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1801,plain,
% 3.07/1.00      ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1799]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_792,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0_50,X0_52)
% 3.07/1.00      | m1_subset_1(X1_50,X1_52)
% 3.07/1.00      | X1_52 != X0_52
% 3.07/1.00      | X1_50 != X0_50 ),
% 3.07/1.00      theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1486,plain,
% 3.07/1.00      ( m1_subset_1(X0_50,X0_52)
% 3.07/1.00      | ~ m1_subset_1(k2_funct_2(X0_51,X1_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.07/1.00      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
% 3.07/1.00      | X0_50 != k2_funct_2(X0_51,X1_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_792]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2138,plain,
% 3.07/1.00      ( ~ m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.07/1.00      | m1_subset_1(k2_funct_1(X0_50),X0_52)
% 3.07/1.00      | X0_52 != k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))
% 3.07/1.00      | k2_funct_1(X0_50) != k2_funct_2(X0_51,X0_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1486]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2787,plain,
% 3.07/1.00      ( ~ m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 3.07/1.00      | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_2138]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2788,plain,
% 3.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 3.07/1.00      | k2_funct_1(X0_50) != k2_funct_2(sK1,X0_50)
% 3.07/1.00      | m1_subset_1(k2_funct_2(sK1,X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.07/1.00      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2790,plain,
% 3.07/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 3.07/1.00      | k2_funct_1(sK2) != k2_funct_2(sK1,sK2)
% 3.07/1.00      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.07/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_2788]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3813,plain,
% 3.07/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_2886,c_27,c_28,c_26,c_29,c_25,c_30,c_24,c_31,c_835,
% 3.07/1.00                 c_853,c_1501,c_1800,c_1801,c_2790]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_20,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | ~ v1_funct_1(X3)
% 3.07/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_764,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.07/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | ~ v1_funct_1(X1_50)
% 3.07/1.00      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1263,plain,
% 3.07/1.00      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 3.07/1.00      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.07/1.00      | v1_funct_1(X1_50) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3230,plain,
% 3.07/1.00      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1267,c_1263]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3361,plain,
% 3.07/1.00      ( v1_funct_1(X0_50) != iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.07/1.00      | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_3230,c_28]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3362,plain,
% 3.07/1.00      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top ),
% 3.07/1.00      inference(renaming,[status(thm)],[c_3361]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3818,plain,
% 3.07/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.07/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_3813,c_3362]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_834,plain,
% 3.07/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.07/1.00      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.07/1.00      | m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ v1_funct_1(sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_772]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_14,plain,
% 3.07/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.07/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_769,plain,
% 3.07/1.00      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 3.07/1.00      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 3.07/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1258,plain,
% 3.07/1.00      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.07/1.00      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_769]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2325,plain,
% 3.07/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1267,c_1258]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_842,plain,
% 3.07/1.00      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.07/1.00      | v1_funct_1(X0_50) != iProver_top
% 3.07/1.00      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_769]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_844,plain,
% 3.07/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.07/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.07/1.00      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.07/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_842]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2549,plain,
% 3.07/1.00      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_2325,c_28,c_29,c_30,c_31,c_844]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2558,plain,
% 3.07/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2555,c_2549]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2566,plain,
% 3.07/1.00      ( v1_funct_1(k2_funct_1(sK2)) ),
% 3.07/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2558]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2789,plain,
% 3.07/1.00      ( ~ m1_subset_1(k2_funct_2(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))
% 3.07/1.00      | k2_funct_1(sK2) != k2_funct_2(sK1,sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_2787]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3792,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.07/1.00      | ~ m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | ~ v1_funct_1(k2_funct_1(X0_50))
% 3.07/1.00      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,k2_funct_1(X0_50)) = k5_relat_1(X0_50,k2_funct_1(X0_50)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_764]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3795,plain,
% 3.07/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.07/1.00      | ~ v1_funct_1(sK2)
% 3.07/1.00      | k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_3792]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4020,plain,
% 3.07/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_3818,c_27,c_26,c_25,c_24,c_834,c_853,c_1501,c_1800,
% 3.07/1.00                 c_1801,c_2566,c_2789,c_3795]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_23,negated_conjecture,
% 3.07/1.00      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.07/1.00      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_761,negated_conjecture,
% 3.07/1.00      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.07/1.00      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1266,plain,
% 3.07/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.07/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2559,plain,
% 3.07/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.07/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2555,c_1266]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4023,plain,
% 3.07/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.07/1.00      | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_4020,c_2559]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4523,plain,
% 3.07/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.07/1.00      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_2809,c_4023]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_793,plain,
% 3.07/1.00      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 3.07/1.00      | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
% 3.07/1.00      | X2_51 != X0_51
% 3.07/1.00      | X3_51 != X1_51
% 3.07/1.00      | X2_50 != X0_50
% 3.07/1.00      | X3_50 != X1_50 ),
% 3.07/1.00      theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2295,plain,
% 3.07/1.00      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 3.07/1.00      | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
% 3.07/1.00      | X2_51 != X0_51
% 3.07/1.00      | X3_51 != X1_51
% 3.07/1.00      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
% 3.07/1.00      | k6_partfun1(X8_51) != X1_50 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_793]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3437,plain,
% 3.07/1.00      ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
% 3.07/1.00      | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
% 3.07/1.00      | X3_51 != X0_51
% 3.07/1.00      | X4_51 != X1_51
% 3.07/1.00      | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
% 3.07/1.00      | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_2295]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4325,plain,
% 3.07/1.00      ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
% 3.07/1.00      | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
% 3.07/1.00      | X0_51 != X7_51
% 3.07/1.00      | X1_51 != X8_51
% 3.07/1.00      | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
% 3.07/1.00      | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_3437]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4327,plain,
% 3.07/1.00      ( X0_51 != X1_51
% 3.07/1.00      | X2_51 != X3_51
% 3.07/1.00      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X8_51)
% 3.07/1.00      | k6_partfun1(X9_51) != k6_partfun1(X8_51)
% 3.07/1.00      | r2_relset_1(X0_51,X2_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50),k6_partfun1(X9_51)) = iProver_top
% 3.07/1.00      | r2_relset_1(X1_51,X3_51,k6_partfun1(X8_51),k6_partfun1(X8_51)) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_4325]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4329,plain,
% 3.07/1.00      ( sK1 != sK1
% 3.07/1.00      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 3.07/1.00      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 3.07/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) = iProver_top
% 3.07/1.00      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_4327]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3591,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.07/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.07/1.00      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_764]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3594,plain,
% 3.07/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.07/1.00      | ~ v1_funct_1(sK2)
% 3.07/1.00      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_3591]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_785,plain,
% 3.07/1.00      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 3.07/1.00      theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2165,plain,
% 3.07/1.00      ( k2_relat_1(X0_50) != X0_51
% 3.07/1.00      | sK1 != X0_51
% 3.07/1.00      | sK1 = k2_relat_1(X0_50) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_785]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2166,plain,
% 3.07/1.00      ( k2_relat_1(sK2) != sK1 | sK1 = k2_relat_1(sK2) | sK1 != sK1 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_2165]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_15,plain,
% 3.07/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.07/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_768,plain,
% 3.07/1.00      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1259,plain,
% 3.07/1.00      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_5,plain,
% 3.07/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.07/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.07/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.07/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_774,plain,
% 3.07/1.00      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
% 3.07/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.07/1.00      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1253,plain,
% 3.07/1.00      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.07/1.00      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2074,plain,
% 3.07/1.00      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
% 3.07/1.00      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_1259,c_1253]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2092,plain,
% 3.07/1.00      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 3.07/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_2074]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_787,plain,
% 3.07/1.00      ( X0_51 != X1_51 | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
% 3.07/1.00      theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1519,plain,
% 3.07/1.00      ( sK1 != X0_51 | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1987,plain,
% 3.07/1.00      ( sK1 != k2_relat_1(X0_50)
% 3.07/1.00      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1519]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1988,plain,
% 3.07/1.00      ( sK1 != k2_relat_1(sK2)
% 3.07/1.00      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1987]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1517,plain,
% 3.07/1.00      ( X0_50 != X1_50
% 3.07/1.00      | k6_partfun1(sK1) != X1_50
% 3.07/1.00      | k6_partfun1(sK1) = X0_50 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_784]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1599,plain,
% 3.07/1.00      ( X0_50 != k6_partfun1(X0_51)
% 3.07/1.00      | k6_partfun1(sK1) = X0_50
% 3.07/1.00      | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1517]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1692,plain,
% 3.07/1.00      ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
% 3.07/1.00      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
% 3.07/1.00      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1599]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_1693,plain,
% 3.07/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
% 3.07/1.00      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.07/1.00      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1692]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6,plain,
% 3.07/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.07/1.00      | v2_funct_2(X0,X2)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ v1_funct_1(X0) ),
% 3.07/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_10,plain,
% 3.07/1.00      ( ~ v2_funct_2(X0,X1)
% 3.07/1.00      | ~ v5_relat_1(X0,X1)
% 3.07/1.00      | ~ v1_relat_1(X0)
% 3.07/1.00      | k2_relat_1(X0) = X1 ),
% 3.07/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_312,plain,
% 3.07/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.07/1.00      | ~ v5_relat_1(X3,X4)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ v1_relat_1(X3)
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | X3 != X0
% 3.07/1.00      | X4 != X2
% 3.07/1.00      | k2_relat_1(X3) = X4 ),
% 3.07/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_313,plain,
% 3.07/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.07/1.00      | ~ v5_relat_1(X0,X2)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ v1_relat_1(X0)
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | k2_relat_1(X0) = X2 ),
% 3.07/1.00      inference(unflattening,[status(thm)],[c_312]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_317,plain,
% 3.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ v5_relat_1(X0,X2)
% 3.07/1.00      | ~ v3_funct_2(X0,X1,X2)
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | k2_relat_1(X0) = X2 ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_313,c_2]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_318,plain,
% 3.07/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.07/1.00      | ~ v5_relat_1(X0,X2)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | k2_relat_1(X0) = X2 ),
% 3.07/1.00      inference(renaming,[status(thm)],[c_317]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_3,plain,
% 3.07/1.00      ( v5_relat_1(X0,X1)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.07/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_333,plain,
% 3.07/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | k2_relat_1(X0) = X2 ),
% 3.07/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_318,c_3]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_756,plain,
% 3.07/1.00      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 3.07/1.00      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | k2_relat_1(X0_50) = X1_51 ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_333]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_864,plain,
% 3.07/1.00      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.07/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.07/1.00      | ~ v1_funct_1(sK2)
% 3.07/1.00      | k2_relat_1(sK2) = sK1 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_756]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_0,plain,
% 3.07/1.00      ( ~ v1_relat_1(X0)
% 3.07/1.00      | ~ v1_funct_1(X0)
% 3.07/1.00      | ~ v2_funct_1(X0)
% 3.07/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_778,plain,
% 3.07/1.00      ( ~ v1_relat_1(X0_50)
% 3.07/1.00      | ~ v1_funct_1(X0_50)
% 3.07/1.00      | ~ v2_funct_1(X0_50)
% 3.07/1.00      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
% 3.07/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_816,plain,
% 3.07/1.00      ( ~ v1_relat_1(sK2)
% 3.07/1.00      | ~ v1_funct_1(sK2)
% 3.07/1.00      | ~ v2_funct_1(sK2)
% 3.07/1.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_778]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_781,plain,( X0_51 = X0_51 ),theory(equality) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_812,plain,
% 3.07/1.00      ( sK1 = sK1 ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_781]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_799,plain,
% 3.07/1.00      ( sK1 != sK1 | k6_partfun1(sK1) = k6_partfun1(sK1) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_787]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(contradiction,plain,
% 3.07/1.00      ( $false ),
% 3.07/1.00      inference(minisat,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_4695,c_4523,c_4329,c_3594,c_2789,c_2566,c_2166,c_2092,
% 3.07/1.00                 c_1988,c_1801,c_1800,c_1693,c_1501,c_864,c_853,c_834,
% 3.07/1.00                 c_831,c_822,c_816,c_812,c_799,c_31,c_24,c_25,c_26,c_27]) ).
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  ------                               Statistics
% 3.07/1.00  
% 3.07/1.00  ------ General
% 3.07/1.00  
% 3.07/1.00  abstr_ref_over_cycles:                  0
% 3.07/1.00  abstr_ref_under_cycles:                 0
% 3.07/1.00  gc_basic_clause_elim:                   0
% 3.07/1.00  forced_gc_time:                         0
% 3.07/1.00  parsing_time:                           0.009
% 3.07/1.00  unif_index_cands_time:                  0.
% 3.07/1.00  unif_index_add_time:                    0.
% 3.07/1.00  orderings_time:                         0.
% 3.07/1.00  out_proof_time:                         0.014
% 3.07/1.00  total_time:                             0.196
% 3.07/1.00  num_of_symbols:                         57
% 3.07/1.00  num_of_terms:                           4231
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing
% 3.07/1.00  
% 3.07/1.00  num_of_splits:                          0
% 3.07/1.00  num_of_split_atoms:                     0
% 3.07/1.00  num_of_reused_defs:                     0
% 3.07/1.00  num_eq_ax_congr_red:                    28
% 3.07/1.00  num_of_sem_filtered_clauses:            1
% 3.07/1.00  num_of_subtypes:                        4
% 3.07/1.00  monotx_restored_types:                  1
% 3.07/1.00  sat_num_of_epr_types:                   0
% 3.07/1.00  sat_num_of_non_cyclic_types:            0
% 3.07/1.00  sat_guarded_non_collapsed_types:        0
% 3.07/1.00  num_pure_diseq_elim:                    0
% 3.07/1.00  simp_replaced_by:                       0
% 3.07/1.00  res_preprocessed:                       133
% 3.07/1.00  prep_upred:                             0
% 3.07/1.00  prep_unflattend:                        8
% 3.07/1.00  smt_new_axioms:                         0
% 3.07/1.00  pred_elim_cands:                        7
% 3.07/1.00  pred_elim:                              2
% 3.07/1.00  pred_elim_cl:                           4
% 3.07/1.00  pred_elim_cycles:                       6
% 3.07/1.00  merged_defs:                            0
% 3.07/1.00  merged_defs_ncl:                        0
% 3.07/1.00  bin_hyper_res:                          0
% 3.07/1.00  prep_cycles:                            4
% 3.07/1.00  pred_elim_time:                         0.007
% 3.07/1.00  splitting_time:                         0.004
% 3.07/1.00  sem_filter_time:                        0.
% 3.07/1.00  monotx_time:                            0.001
% 3.07/1.00  subtype_inf_time:                       0.001
% 3.07/1.00  
% 3.07/1.00  ------ Problem properties
% 3.07/1.00  
% 3.07/1.00  clauses:                                23
% 3.07/1.00  conjectures:                            5
% 3.07/1.00  epr:                                    3
% 3.07/1.00  horn:                                   23
% 3.07/1.00  ground:                                 5
% 3.07/1.00  unary:                                  8
% 3.07/1.00  binary:                                 3
% 3.07/1.00  lits:                                   67
% 3.07/1.00  lits_eq:                                7
% 3.07/1.00  fd_pure:                                0
% 3.07/1.00  fd_pseudo:                              0
% 3.07/1.00  fd_cond:                                0
% 3.07/1.00  fd_pseudo_cond:                         1
% 3.07/1.00  ac_symbols:                             0
% 3.07/1.00  
% 3.07/1.00  ------ Propositional Solver
% 3.07/1.00  
% 3.07/1.00  prop_solver_calls:                      29
% 3.07/1.00  prop_fast_solver_calls:                 1035
% 3.07/1.00  smt_solver_calls:                       0
% 3.07/1.00  smt_fast_solver_calls:                  0
% 3.07/1.00  prop_num_of_clauses:                    1338
% 3.07/1.00  prop_preprocess_simplified:             5296
% 3.07/1.00  prop_fo_subsumed:                       42
% 3.07/1.00  prop_solver_time:                       0.
% 3.07/1.00  smt_solver_time:                        0.
% 3.07/1.00  smt_fast_solver_time:                   0.
% 3.07/1.00  prop_fast_solver_time:                  0.
% 3.07/1.00  prop_unsat_core_time:                   0.
% 3.07/1.00  
% 3.07/1.00  ------ QBF
% 3.07/1.00  
% 3.07/1.00  qbf_q_res:                              0
% 3.07/1.00  qbf_num_tautologies:                    0
% 3.07/1.00  qbf_prep_cycles:                        0
% 3.07/1.00  
% 3.07/1.00  ------ BMC1
% 3.07/1.00  
% 3.07/1.00  bmc1_current_bound:                     -1
% 3.07/1.00  bmc1_last_solved_bound:                 -1
% 3.07/1.00  bmc1_unsat_core_size:                   -1
% 3.07/1.00  bmc1_unsat_core_parents_size:           -1
% 3.07/1.00  bmc1_merge_next_fun:                    0
% 3.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation
% 3.07/1.00  
% 3.07/1.00  inst_num_of_clauses:                    426
% 3.07/1.00  inst_num_in_passive:                    69
% 3.07/1.00  inst_num_in_active:                     271
% 3.07/1.00  inst_num_in_unprocessed:                85
% 3.07/1.00  inst_num_of_loops:                      296
% 3.07/1.00  inst_num_of_learning_restarts:          0
% 3.07/1.00  inst_num_moves_active_passive:          20
% 3.07/1.00  inst_lit_activity:                      0
% 3.07/1.00  inst_lit_activity_moves:                0
% 3.07/1.00  inst_num_tautologies:                   0
% 3.07/1.00  inst_num_prop_implied:                  0
% 3.07/1.00  inst_num_existing_simplified:           0
% 3.07/1.00  inst_num_eq_res_simplified:             0
% 3.07/1.00  inst_num_child_elim:                    0
% 3.07/1.00  inst_num_of_dismatching_blockings:      420
% 3.07/1.00  inst_num_of_non_proper_insts:           632
% 3.07/1.00  inst_num_of_duplicates:                 0
% 3.07/1.00  inst_inst_num_from_inst_to_res:         0
% 3.07/1.00  inst_dismatching_checking_time:         0.
% 3.07/1.00  
% 3.07/1.00  ------ Resolution
% 3.07/1.00  
% 3.07/1.00  res_num_of_clauses:                     0
% 3.07/1.00  res_num_in_passive:                     0
% 3.07/1.00  res_num_in_active:                      0
% 3.07/1.00  res_num_of_loops:                       137
% 3.07/1.00  res_forward_subset_subsumed:            94
% 3.07/1.00  res_backward_subset_subsumed:           4
% 3.07/1.00  res_forward_subsumed:                   0
% 3.07/1.00  res_backward_subsumed:                  0
% 3.07/1.00  res_forward_subsumption_resolution:     1
% 3.07/1.00  res_backward_subsumption_resolution:    0
% 3.07/1.00  res_clause_to_clause_subsumption:       178
% 3.07/1.00  res_orphan_elimination:                 0
% 3.07/1.00  res_tautology_del:                      82
% 3.07/1.00  res_num_eq_res_simplified:              0
% 3.07/1.00  res_num_sel_changes:                    0
% 3.07/1.00  res_moves_from_active_to_pass:          0
% 3.07/1.00  
% 3.07/1.00  ------ Superposition
% 3.07/1.00  
% 3.07/1.00  sup_time_total:                         0.
% 3.07/1.00  sup_time_generating:                    0.
% 3.07/1.00  sup_time_sim_full:                      0.
% 3.07/1.00  sup_time_sim_immed:                     0.
% 3.07/1.00  
% 3.07/1.00  sup_num_of_clauses:                     95
% 3.07/1.00  sup_num_in_active:                      49
% 3.07/1.00  sup_num_in_passive:                     46
% 3.07/1.00  sup_num_of_loops:                       58
% 3.07/1.00  sup_fw_superposition:                   54
% 3.07/1.00  sup_bw_superposition:                   24
% 3.07/1.00  sup_immediate_simplified:               12
% 3.07/1.00  sup_given_eliminated:                   0
% 3.07/1.00  comparisons_done:                       0
% 3.07/1.00  comparisons_avoided:                    0
% 3.07/1.00  
% 3.07/1.00  ------ Simplifications
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  sim_fw_subset_subsumed:                 0
% 3.07/1.00  sim_bw_subset_subsumed:                 2
% 3.07/1.00  sim_fw_subsumed:                        2
% 3.07/1.00  sim_bw_subsumed:                        0
% 3.07/1.00  sim_fw_subsumption_res:                 2
% 3.07/1.00  sim_bw_subsumption_res:                 0
% 3.07/1.00  sim_tautology_del:                      0
% 3.07/1.00  sim_eq_tautology_del:                   1
% 3.07/1.00  sim_eq_res_simp:                        0
% 3.07/1.00  sim_fw_demodulated:                     3
% 3.07/1.00  sim_bw_demodulated:                     9
% 3.07/1.00  sim_light_normalised:                   3
% 3.07/1.00  sim_joinable_taut:                      0
% 3.07/1.00  sim_joinable_simp:                      0
% 3.07/1.00  sim_ac_normalised:                      0
% 3.07/1.00  sim_smt_subsumption:                    0
% 3.07/1.00  
%------------------------------------------------------------------------------
