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
% DateTime   : Thu Dec  3 12:07:24 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 827 expanded)
%              Number of clauses        :  116 ( 274 expanded)
%              Number of leaves         :   20 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          :  609 (3904 expanded)
%              Number of equality atoms :  247 ( 440 expanded)
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

fof(f70,plain,(
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

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f69,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
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

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f61,plain,(
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

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f48,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f65])).

cnf(c_699,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1430,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_partfun1(X0_51)
    | k6_partfun1(X0_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_2987,plain,
    ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
    | X0_50 = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_4562,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_2987])).

cnf(c_4566,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_4562])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_677,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_677])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_679,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1137,plain,
    ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_2215,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1137])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_689,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1127,plain,
    ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_1466,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1139,c_1127])).

cnf(c_2248,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2215,c_1466])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2778,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2248,c_25,c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_690,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1126,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_1377,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1126])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_691,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1125,plain,
    ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_1675,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1125])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_735,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_738,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_687,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_747,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_1819,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1675,c_24,c_22,c_21,c_735,c_738,c_747])).

cnf(c_2781,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2778,c_1819])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_680,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1136,plain,
    ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
    | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_2382,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1136])).

cnf(c_766,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_2562,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2382,c_24,c_23,c_22,c_21,c_766])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_686,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1130,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_2575,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2562,c_1130])).

cnf(c_27,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2849,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2575,c_25,c_26,c_27,c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1135,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_3069,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1135])).

cnf(c_3360,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3069,c_25])).

cnf(c_3361,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3360])).

cnf(c_3371,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_3361])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_683,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1133,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_2268,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1133])).

cnf(c_758,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_760,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_758])).

cnf(c_2556,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2268,c_25,c_26,c_27,c_28,c_760])).

cnf(c_2565,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2562,c_2556])).

cnf(c_3629,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3371,c_2565])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_678,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1138,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_2566,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2562,c_1138])).

cnf(c_3632,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3629,c_2566])).

cnf(c_4506,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2781,c_3632])).

cnf(c_707,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
    | X2_51 != X0_51
    | X3_51 != X1_51
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_2202,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
    | X2_51 != X0_51
    | X3_51 != X1_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
    | k6_partfun1(X8_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_3251,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
    | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
    | X3_51 != X0_51
    | X4_51 != X1_51
    | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
    | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_4334,plain,
    ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
    | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
    | X0_51 != X7_51
    | X1_51 != X8_51
    | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
    | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
    inference(instantiation,[status(thm)],[c_3251])).

cnf(c_4336,plain,
    ( X0_51 != X1_51
    | X2_51 != X3_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X8_51)
    | k6_partfun1(X9_51) != k6_partfun1(X8_51)
    | r2_relset_1(X0_51,X2_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50),k6_partfun1(X9_51)) = iProver_top
    | r2_relset_1(X1_51,X3_51,k6_partfun1(X8_51),k6_partfun1(X8_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4334])).

cnf(c_4338,plain,
    ( sK1 != sK1
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) = iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4336])).

cnf(c_3073,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_1135])).

cnf(c_3133,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3073])).

cnf(c_700,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2141,plain,
    ( k2_relat_1(X0_50) != X0_51
    | sK1 != X0_51
    | sK1 = k2_relat_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_2142,plain,
    ( k2_relat_1(sK2) != sK1
    | sK1 = k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2141])).

cnf(c_704,plain,
    ( X0_51 != X1_51
    | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
    theory(equality)).

cnf(c_1401,plain,
    ( sK1 != X0_51
    | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_1922,plain,
    ( sK1 != k2_relat_1(X0_50)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1923,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_1399,plain,
    ( X0_50 != X1_50
    | k6_partfun1(sK1) != X1_50
    | k6_partfun1(sK1) = X0_50 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_1489,plain,
    ( X0_50 != k6_partfun1(X0_51)
    | k6_partfun1(sK1) = X0_50
    | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_1582,plain,
    ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_1583,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1582])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_682,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1134,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_688,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1128,plain,
    ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_1552,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1134,c_1128])).

cnf(c_1568,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_7,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_11,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_278,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_11])).

cnf(c_290,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_278,c_3])).

cnf(c_363,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_290])).

cnf(c_364,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_673,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | k2_relat_1(X0_50) = X1_51 ),
    inference(subtyping,[status(esa)],[c_364])).

cnf(c_777,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_692,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | ~ v2_funct_1(X0_50)
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_732,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_692])).

cnf(c_696,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_725,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_715,plain,
    ( sK1 != sK1
    | k6_partfun1(sK1) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4566,c_4506,c_4338,c_3133,c_2565,c_2142,c_1923,c_1583,c_1568,c_777,c_747,c_738,c_732,c_725,c_715,c_28,c_21,c_22,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.16/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.16/1.01  
% 3.16/1.01  ------  iProver source info
% 3.16/1.01  
% 3.16/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.16/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.16/1.01  git: non_committed_changes: false
% 3.16/1.01  git: last_make_outside_of_git: false
% 3.16/1.01  
% 3.16/1.01  ------ 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options
% 3.16/1.01  
% 3.16/1.01  --out_options                           all
% 3.16/1.01  --tptp_safe_out                         true
% 3.16/1.01  --problem_path                          ""
% 3.16/1.01  --include_path                          ""
% 3.16/1.01  --clausifier                            res/vclausify_rel
% 3.16/1.01  --clausifier_options                    --mode clausify
% 3.16/1.01  --stdin                                 false
% 3.16/1.01  --stats_out                             all
% 3.16/1.01  
% 3.16/1.01  ------ General Options
% 3.16/1.01  
% 3.16/1.01  --fof                                   false
% 3.16/1.01  --time_out_real                         305.
% 3.16/1.01  --time_out_virtual                      -1.
% 3.16/1.01  --symbol_type_check                     false
% 3.16/1.01  --clausify_out                          false
% 3.16/1.01  --sig_cnt_out                           false
% 3.16/1.01  --trig_cnt_out                          false
% 3.16/1.01  --trig_cnt_out_tolerance                1.
% 3.16/1.01  --trig_cnt_out_sk_spl                   false
% 3.16/1.01  --abstr_cl_out                          false
% 3.16/1.01  
% 3.16/1.01  ------ Global Options
% 3.16/1.01  
% 3.16/1.01  --schedule                              default
% 3.16/1.01  --add_important_lit                     false
% 3.16/1.01  --prop_solver_per_cl                    1000
% 3.16/1.01  --min_unsat_core                        false
% 3.16/1.01  --soft_assumptions                      false
% 3.16/1.01  --soft_lemma_size                       3
% 3.16/1.01  --prop_impl_unit_size                   0
% 3.16/1.01  --prop_impl_unit                        []
% 3.16/1.01  --share_sel_clauses                     true
% 3.16/1.01  --reset_solvers                         false
% 3.16/1.01  --bc_imp_inh                            [conj_cone]
% 3.16/1.01  --conj_cone_tolerance                   3.
% 3.16/1.01  --extra_neg_conj                        none
% 3.16/1.01  --large_theory_mode                     true
% 3.16/1.01  --prolific_symb_bound                   200
% 3.16/1.01  --lt_threshold                          2000
% 3.16/1.01  --clause_weak_htbl                      true
% 3.16/1.01  --gc_record_bc_elim                     false
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing Options
% 3.16/1.01  
% 3.16/1.01  --preprocessing_flag                    true
% 3.16/1.01  --time_out_prep_mult                    0.1
% 3.16/1.01  --splitting_mode                        input
% 3.16/1.01  --splitting_grd                         true
% 3.16/1.01  --splitting_cvd                         false
% 3.16/1.01  --splitting_cvd_svl                     false
% 3.16/1.01  --splitting_nvd                         32
% 3.16/1.01  --sub_typing                            true
% 3.16/1.01  --prep_gs_sim                           true
% 3.16/1.01  --prep_unflatten                        true
% 3.16/1.01  --prep_res_sim                          true
% 3.16/1.01  --prep_upred                            true
% 3.16/1.01  --prep_sem_filter                       exhaustive
% 3.16/1.01  --prep_sem_filter_out                   false
% 3.16/1.01  --pred_elim                             true
% 3.16/1.01  --res_sim_input                         true
% 3.16/1.01  --eq_ax_congr_red                       true
% 3.16/1.01  --pure_diseq_elim                       true
% 3.16/1.01  --brand_transform                       false
% 3.16/1.01  --non_eq_to_eq                          false
% 3.16/1.01  --prep_def_merge                        true
% 3.16/1.01  --prep_def_merge_prop_impl              false
% 3.16/1.01  --prep_def_merge_mbd                    true
% 3.16/1.01  --prep_def_merge_tr_red                 false
% 3.16/1.01  --prep_def_merge_tr_cl                  false
% 3.16/1.01  --smt_preprocessing                     true
% 3.16/1.01  --smt_ac_axioms                         fast
% 3.16/1.01  --preprocessed_out                      false
% 3.16/1.01  --preprocessed_stats                    false
% 3.16/1.01  
% 3.16/1.01  ------ Abstraction refinement Options
% 3.16/1.01  
% 3.16/1.01  --abstr_ref                             []
% 3.16/1.01  --abstr_ref_prep                        false
% 3.16/1.01  --abstr_ref_until_sat                   false
% 3.16/1.01  --abstr_ref_sig_restrict                funpre
% 3.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.01  --abstr_ref_under                       []
% 3.16/1.01  
% 3.16/1.01  ------ SAT Options
% 3.16/1.01  
% 3.16/1.01  --sat_mode                              false
% 3.16/1.01  --sat_fm_restart_options                ""
% 3.16/1.01  --sat_gr_def                            false
% 3.16/1.01  --sat_epr_types                         true
% 3.16/1.01  --sat_non_cyclic_types                  false
% 3.16/1.01  --sat_finite_models                     false
% 3.16/1.01  --sat_fm_lemmas                         false
% 3.16/1.01  --sat_fm_prep                           false
% 3.16/1.01  --sat_fm_uc_incr                        true
% 3.16/1.01  --sat_out_model                         small
% 3.16/1.01  --sat_out_clauses                       false
% 3.16/1.01  
% 3.16/1.01  ------ QBF Options
% 3.16/1.01  
% 3.16/1.01  --qbf_mode                              false
% 3.16/1.01  --qbf_elim_univ                         false
% 3.16/1.01  --qbf_dom_inst                          none
% 3.16/1.01  --qbf_dom_pre_inst                      false
% 3.16/1.01  --qbf_sk_in                             false
% 3.16/1.01  --qbf_pred_elim                         true
% 3.16/1.01  --qbf_split                             512
% 3.16/1.01  
% 3.16/1.01  ------ BMC1 Options
% 3.16/1.01  
% 3.16/1.01  --bmc1_incremental                      false
% 3.16/1.01  --bmc1_axioms                           reachable_all
% 3.16/1.01  --bmc1_min_bound                        0
% 3.16/1.01  --bmc1_max_bound                        -1
% 3.16/1.01  --bmc1_max_bound_default                -1
% 3.16/1.01  --bmc1_symbol_reachability              true
% 3.16/1.01  --bmc1_property_lemmas                  false
% 3.16/1.01  --bmc1_k_induction                      false
% 3.16/1.01  --bmc1_non_equiv_states                 false
% 3.16/1.01  --bmc1_deadlock                         false
% 3.16/1.01  --bmc1_ucm                              false
% 3.16/1.01  --bmc1_add_unsat_core                   none
% 3.16/1.01  --bmc1_unsat_core_children              false
% 3.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.01  --bmc1_out_stat                         full
% 3.16/1.01  --bmc1_ground_init                      false
% 3.16/1.01  --bmc1_pre_inst_next_state              false
% 3.16/1.01  --bmc1_pre_inst_state                   false
% 3.16/1.01  --bmc1_pre_inst_reach_state             false
% 3.16/1.01  --bmc1_out_unsat_core                   false
% 3.16/1.01  --bmc1_aig_witness_out                  false
% 3.16/1.01  --bmc1_verbose                          false
% 3.16/1.01  --bmc1_dump_clauses_tptp                false
% 3.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.01  --bmc1_dump_file                        -
% 3.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.01  --bmc1_ucm_extend_mode                  1
% 3.16/1.01  --bmc1_ucm_init_mode                    2
% 3.16/1.01  --bmc1_ucm_cone_mode                    none
% 3.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.01  --bmc1_ucm_relax_model                  4
% 3.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.01  --bmc1_ucm_layered_model                none
% 3.16/1.01  --bmc1_ucm_max_lemma_size               10
% 3.16/1.01  
% 3.16/1.01  ------ AIG Options
% 3.16/1.01  
% 3.16/1.01  --aig_mode                              false
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation Options
% 3.16/1.01  
% 3.16/1.01  --instantiation_flag                    true
% 3.16/1.01  --inst_sos_flag                         false
% 3.16/1.01  --inst_sos_phase                        true
% 3.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel_side                     num_symb
% 3.16/1.01  --inst_solver_per_active                1400
% 3.16/1.01  --inst_solver_calls_frac                1.
% 3.16/1.01  --inst_passive_queue_type               priority_queues
% 3.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.01  --inst_passive_queues_freq              [25;2]
% 3.16/1.01  --inst_dismatching                      true
% 3.16/1.01  --inst_eager_unprocessed_to_passive     true
% 3.16/1.01  --inst_prop_sim_given                   true
% 3.16/1.01  --inst_prop_sim_new                     false
% 3.16/1.01  --inst_subs_new                         false
% 3.16/1.01  --inst_eq_res_simp                      false
% 3.16/1.01  --inst_subs_given                       false
% 3.16/1.01  --inst_orphan_elimination               true
% 3.16/1.01  --inst_learning_loop_flag               true
% 3.16/1.01  --inst_learning_start                   3000
% 3.16/1.01  --inst_learning_factor                  2
% 3.16/1.01  --inst_start_prop_sim_after_learn       3
% 3.16/1.01  --inst_sel_renew                        solver
% 3.16/1.01  --inst_lit_activity_flag                true
% 3.16/1.01  --inst_restr_to_given                   false
% 3.16/1.01  --inst_activity_threshold               500
% 3.16/1.01  --inst_out_proof                        true
% 3.16/1.01  
% 3.16/1.01  ------ Resolution Options
% 3.16/1.01  
% 3.16/1.01  --resolution_flag                       true
% 3.16/1.01  --res_lit_sel                           adaptive
% 3.16/1.01  --res_lit_sel_side                      none
% 3.16/1.01  --res_ordering                          kbo
% 3.16/1.01  --res_to_prop_solver                    active
% 3.16/1.01  --res_prop_simpl_new                    false
% 3.16/1.01  --res_prop_simpl_given                  true
% 3.16/1.01  --res_passive_queue_type                priority_queues
% 3.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.01  --res_passive_queues_freq               [15;5]
% 3.16/1.01  --res_forward_subs                      full
% 3.16/1.01  --res_backward_subs                     full
% 3.16/1.01  --res_forward_subs_resolution           true
% 3.16/1.01  --res_backward_subs_resolution          true
% 3.16/1.01  --res_orphan_elimination                true
% 3.16/1.01  --res_time_limit                        2.
% 3.16/1.01  --res_out_proof                         true
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Options
% 3.16/1.01  
% 3.16/1.01  --superposition_flag                    true
% 3.16/1.01  --sup_passive_queue_type                priority_queues
% 3.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.01  --demod_completeness_check              fast
% 3.16/1.01  --demod_use_ground                      true
% 3.16/1.01  --sup_to_prop_solver                    passive
% 3.16/1.01  --sup_prop_simpl_new                    true
% 3.16/1.01  --sup_prop_simpl_given                  true
% 3.16/1.01  --sup_fun_splitting                     false
% 3.16/1.01  --sup_smt_interval                      50000
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Simplification Setup
% 3.16/1.01  
% 3.16/1.01  --sup_indices_passive                   []
% 3.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_full_bw                           [BwDemod]
% 3.16/1.01  --sup_immed_triv                        [TrivRules]
% 3.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_immed_bw_main                     []
% 3.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  
% 3.16/1.01  ------ Combination Options
% 3.16/1.01  
% 3.16/1.01  --comb_res_mult                         3
% 3.16/1.01  --comb_sup_mult                         2
% 3.16/1.01  --comb_inst_mult                        10
% 3.16/1.01  
% 3.16/1.01  ------ Debug Options
% 3.16/1.01  
% 3.16/1.01  --dbg_backtrace                         false
% 3.16/1.01  --dbg_dump_prop_clauses                 false
% 3.16/1.01  --dbg_dump_prop_clauses_file            -
% 3.16/1.01  --dbg_out_stat                          false
% 3.16/1.01  ------ Parsing...
% 3.16/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.16/1.01  ------ Proving...
% 3.16/1.01  ------ Problem Properties 
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  clauses                                 21
% 3.16/1.01  conjectures                             5
% 3.16/1.01  EPR                                     3
% 3.16/1.01  Horn                                    21
% 3.16/1.01  unary                                   6
% 3.16/1.01  binary                                  3
% 3.16/1.01  lits                                    66
% 3.16/1.01  lits eq                                 7
% 3.16/1.01  fd_pure                                 0
% 3.16/1.01  fd_pseudo                               0
% 3.16/1.01  fd_cond                                 0
% 3.16/1.01  fd_pseudo_cond                          1
% 3.16/1.01  AC symbols                              0
% 3.16/1.01  
% 3.16/1.01  ------ Schedule dynamic 5 is on 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  ------ 
% 3.16/1.01  Current options:
% 3.16/1.01  ------ 
% 3.16/1.01  
% 3.16/1.01  ------ Input Options
% 3.16/1.01  
% 3.16/1.01  --out_options                           all
% 3.16/1.01  --tptp_safe_out                         true
% 3.16/1.01  --problem_path                          ""
% 3.16/1.01  --include_path                          ""
% 3.16/1.01  --clausifier                            res/vclausify_rel
% 3.16/1.01  --clausifier_options                    --mode clausify
% 3.16/1.01  --stdin                                 false
% 3.16/1.01  --stats_out                             all
% 3.16/1.01  
% 3.16/1.01  ------ General Options
% 3.16/1.01  
% 3.16/1.01  --fof                                   false
% 3.16/1.01  --time_out_real                         305.
% 3.16/1.01  --time_out_virtual                      -1.
% 3.16/1.01  --symbol_type_check                     false
% 3.16/1.01  --clausify_out                          false
% 3.16/1.01  --sig_cnt_out                           false
% 3.16/1.01  --trig_cnt_out                          false
% 3.16/1.01  --trig_cnt_out_tolerance                1.
% 3.16/1.01  --trig_cnt_out_sk_spl                   false
% 3.16/1.01  --abstr_cl_out                          false
% 3.16/1.01  
% 3.16/1.01  ------ Global Options
% 3.16/1.01  
% 3.16/1.01  --schedule                              default
% 3.16/1.01  --add_important_lit                     false
% 3.16/1.01  --prop_solver_per_cl                    1000
% 3.16/1.01  --min_unsat_core                        false
% 3.16/1.01  --soft_assumptions                      false
% 3.16/1.01  --soft_lemma_size                       3
% 3.16/1.01  --prop_impl_unit_size                   0
% 3.16/1.01  --prop_impl_unit                        []
% 3.16/1.01  --share_sel_clauses                     true
% 3.16/1.01  --reset_solvers                         false
% 3.16/1.01  --bc_imp_inh                            [conj_cone]
% 3.16/1.01  --conj_cone_tolerance                   3.
% 3.16/1.01  --extra_neg_conj                        none
% 3.16/1.01  --large_theory_mode                     true
% 3.16/1.01  --prolific_symb_bound                   200
% 3.16/1.01  --lt_threshold                          2000
% 3.16/1.01  --clause_weak_htbl                      true
% 3.16/1.01  --gc_record_bc_elim                     false
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing Options
% 3.16/1.01  
% 3.16/1.01  --preprocessing_flag                    true
% 3.16/1.01  --time_out_prep_mult                    0.1
% 3.16/1.01  --splitting_mode                        input
% 3.16/1.01  --splitting_grd                         true
% 3.16/1.01  --splitting_cvd                         false
% 3.16/1.01  --splitting_cvd_svl                     false
% 3.16/1.01  --splitting_nvd                         32
% 3.16/1.01  --sub_typing                            true
% 3.16/1.01  --prep_gs_sim                           true
% 3.16/1.01  --prep_unflatten                        true
% 3.16/1.01  --prep_res_sim                          true
% 3.16/1.01  --prep_upred                            true
% 3.16/1.01  --prep_sem_filter                       exhaustive
% 3.16/1.01  --prep_sem_filter_out                   false
% 3.16/1.01  --pred_elim                             true
% 3.16/1.01  --res_sim_input                         true
% 3.16/1.01  --eq_ax_congr_red                       true
% 3.16/1.01  --pure_diseq_elim                       true
% 3.16/1.01  --brand_transform                       false
% 3.16/1.01  --non_eq_to_eq                          false
% 3.16/1.01  --prep_def_merge                        true
% 3.16/1.01  --prep_def_merge_prop_impl              false
% 3.16/1.01  --prep_def_merge_mbd                    true
% 3.16/1.01  --prep_def_merge_tr_red                 false
% 3.16/1.01  --prep_def_merge_tr_cl                  false
% 3.16/1.01  --smt_preprocessing                     true
% 3.16/1.01  --smt_ac_axioms                         fast
% 3.16/1.01  --preprocessed_out                      false
% 3.16/1.01  --preprocessed_stats                    false
% 3.16/1.01  
% 3.16/1.01  ------ Abstraction refinement Options
% 3.16/1.01  
% 3.16/1.01  --abstr_ref                             []
% 3.16/1.01  --abstr_ref_prep                        false
% 3.16/1.01  --abstr_ref_until_sat                   false
% 3.16/1.01  --abstr_ref_sig_restrict                funpre
% 3.16/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.16/1.01  --abstr_ref_under                       []
% 3.16/1.01  
% 3.16/1.01  ------ SAT Options
% 3.16/1.01  
% 3.16/1.01  --sat_mode                              false
% 3.16/1.01  --sat_fm_restart_options                ""
% 3.16/1.01  --sat_gr_def                            false
% 3.16/1.01  --sat_epr_types                         true
% 3.16/1.01  --sat_non_cyclic_types                  false
% 3.16/1.01  --sat_finite_models                     false
% 3.16/1.01  --sat_fm_lemmas                         false
% 3.16/1.01  --sat_fm_prep                           false
% 3.16/1.01  --sat_fm_uc_incr                        true
% 3.16/1.01  --sat_out_model                         small
% 3.16/1.01  --sat_out_clauses                       false
% 3.16/1.01  
% 3.16/1.01  ------ QBF Options
% 3.16/1.01  
% 3.16/1.01  --qbf_mode                              false
% 3.16/1.01  --qbf_elim_univ                         false
% 3.16/1.01  --qbf_dom_inst                          none
% 3.16/1.01  --qbf_dom_pre_inst                      false
% 3.16/1.01  --qbf_sk_in                             false
% 3.16/1.01  --qbf_pred_elim                         true
% 3.16/1.01  --qbf_split                             512
% 3.16/1.01  
% 3.16/1.01  ------ BMC1 Options
% 3.16/1.01  
% 3.16/1.01  --bmc1_incremental                      false
% 3.16/1.01  --bmc1_axioms                           reachable_all
% 3.16/1.01  --bmc1_min_bound                        0
% 3.16/1.01  --bmc1_max_bound                        -1
% 3.16/1.01  --bmc1_max_bound_default                -1
% 3.16/1.01  --bmc1_symbol_reachability              true
% 3.16/1.01  --bmc1_property_lemmas                  false
% 3.16/1.01  --bmc1_k_induction                      false
% 3.16/1.01  --bmc1_non_equiv_states                 false
% 3.16/1.01  --bmc1_deadlock                         false
% 3.16/1.01  --bmc1_ucm                              false
% 3.16/1.01  --bmc1_add_unsat_core                   none
% 3.16/1.01  --bmc1_unsat_core_children              false
% 3.16/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.16/1.01  --bmc1_out_stat                         full
% 3.16/1.01  --bmc1_ground_init                      false
% 3.16/1.01  --bmc1_pre_inst_next_state              false
% 3.16/1.01  --bmc1_pre_inst_state                   false
% 3.16/1.01  --bmc1_pre_inst_reach_state             false
% 3.16/1.01  --bmc1_out_unsat_core                   false
% 3.16/1.01  --bmc1_aig_witness_out                  false
% 3.16/1.01  --bmc1_verbose                          false
% 3.16/1.01  --bmc1_dump_clauses_tptp                false
% 3.16/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.16/1.01  --bmc1_dump_file                        -
% 3.16/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.16/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.16/1.01  --bmc1_ucm_extend_mode                  1
% 3.16/1.01  --bmc1_ucm_init_mode                    2
% 3.16/1.01  --bmc1_ucm_cone_mode                    none
% 3.16/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.16/1.01  --bmc1_ucm_relax_model                  4
% 3.16/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.16/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.16/1.01  --bmc1_ucm_layered_model                none
% 3.16/1.01  --bmc1_ucm_max_lemma_size               10
% 3.16/1.01  
% 3.16/1.01  ------ AIG Options
% 3.16/1.01  
% 3.16/1.01  --aig_mode                              false
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation Options
% 3.16/1.01  
% 3.16/1.01  --instantiation_flag                    true
% 3.16/1.01  --inst_sos_flag                         false
% 3.16/1.01  --inst_sos_phase                        true
% 3.16/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.16/1.01  --inst_lit_sel_side                     none
% 3.16/1.01  --inst_solver_per_active                1400
% 3.16/1.01  --inst_solver_calls_frac                1.
% 3.16/1.01  --inst_passive_queue_type               priority_queues
% 3.16/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.16/1.01  --inst_passive_queues_freq              [25;2]
% 3.16/1.01  --inst_dismatching                      true
% 3.16/1.01  --inst_eager_unprocessed_to_passive     true
% 3.16/1.01  --inst_prop_sim_given                   true
% 3.16/1.01  --inst_prop_sim_new                     false
% 3.16/1.01  --inst_subs_new                         false
% 3.16/1.01  --inst_eq_res_simp                      false
% 3.16/1.01  --inst_subs_given                       false
% 3.16/1.01  --inst_orphan_elimination               true
% 3.16/1.01  --inst_learning_loop_flag               true
% 3.16/1.01  --inst_learning_start                   3000
% 3.16/1.01  --inst_learning_factor                  2
% 3.16/1.01  --inst_start_prop_sim_after_learn       3
% 3.16/1.01  --inst_sel_renew                        solver
% 3.16/1.01  --inst_lit_activity_flag                true
% 3.16/1.01  --inst_restr_to_given                   false
% 3.16/1.01  --inst_activity_threshold               500
% 3.16/1.01  --inst_out_proof                        true
% 3.16/1.01  
% 3.16/1.01  ------ Resolution Options
% 3.16/1.01  
% 3.16/1.01  --resolution_flag                       false
% 3.16/1.01  --res_lit_sel                           adaptive
% 3.16/1.01  --res_lit_sel_side                      none
% 3.16/1.01  --res_ordering                          kbo
% 3.16/1.01  --res_to_prop_solver                    active
% 3.16/1.01  --res_prop_simpl_new                    false
% 3.16/1.01  --res_prop_simpl_given                  true
% 3.16/1.01  --res_passive_queue_type                priority_queues
% 3.16/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.16/1.01  --res_passive_queues_freq               [15;5]
% 3.16/1.01  --res_forward_subs                      full
% 3.16/1.01  --res_backward_subs                     full
% 3.16/1.01  --res_forward_subs_resolution           true
% 3.16/1.01  --res_backward_subs_resolution          true
% 3.16/1.01  --res_orphan_elimination                true
% 3.16/1.01  --res_time_limit                        2.
% 3.16/1.01  --res_out_proof                         true
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Options
% 3.16/1.01  
% 3.16/1.01  --superposition_flag                    true
% 3.16/1.01  --sup_passive_queue_type                priority_queues
% 3.16/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.16/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.16/1.01  --demod_completeness_check              fast
% 3.16/1.01  --demod_use_ground                      true
% 3.16/1.01  --sup_to_prop_solver                    passive
% 3.16/1.01  --sup_prop_simpl_new                    true
% 3.16/1.01  --sup_prop_simpl_given                  true
% 3.16/1.01  --sup_fun_splitting                     false
% 3.16/1.01  --sup_smt_interval                      50000
% 3.16/1.01  
% 3.16/1.01  ------ Superposition Simplification Setup
% 3.16/1.01  
% 3.16/1.01  --sup_indices_passive                   []
% 3.16/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.16/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.16/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_full_bw                           [BwDemod]
% 3.16/1.01  --sup_immed_triv                        [TrivRules]
% 3.16/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.16/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_immed_bw_main                     []
% 3.16/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.16/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.16/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.16/1.01  
% 3.16/1.01  ------ Combination Options
% 3.16/1.01  
% 3.16/1.01  --comb_res_mult                         3
% 3.16/1.01  --comb_sup_mult                         2
% 3.16/1.01  --comb_inst_mult                        10
% 3.16/1.01  
% 3.16/1.01  ------ Debug Options
% 3.16/1.01  
% 3.16/1.01  --dbg_backtrace                         false
% 3.16/1.01  --dbg_dump_prop_clauses                 false
% 3.16/1.01  --dbg_dump_prop_clauses_file            -
% 3.16/1.01  --dbg_out_stat                          false
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  ------ Proving...
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  % SZS status Theorem for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  fof(f15,conjecture,(
% 3.16/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f16,negated_conjecture,(
% 3.16/1.01    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.16/1.01    inference(negated_conjecture,[],[f15])).
% 3.16/1.01  
% 3.16/1.01  fof(f39,plain,(
% 3.16/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.16/1.01    inference(ennf_transformation,[],[f16])).
% 3.16/1.01  
% 3.16/1.01  fof(f40,plain,(
% 3.16/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.16/1.01    inference(flattening,[],[f39])).
% 3.16/1.01  
% 3.16/1.01  fof(f44,plain,(
% 3.16/1.01    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.16/1.01    introduced(choice_axiom,[])).
% 3.16/1.01  
% 3.16/1.01  fof(f45,plain,(
% 3.16/1.01    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.16/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f44])).
% 3.16/1.01  
% 3.16/1.01  fof(f70,plain,(
% 3.16/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.16/1.01    inference(cnf_transformation,[],[f45])).
% 3.16/1.01  
% 3.16/1.01  fof(f14,axiom,(
% 3.16/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f37,plain,(
% 3.16/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.16/1.01    inference(ennf_transformation,[],[f14])).
% 3.16/1.01  
% 3.16/1.01  fof(f38,plain,(
% 3.16/1.01    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.16/1.01    inference(flattening,[],[f37])).
% 3.16/1.01  
% 3.16/1.01  fof(f66,plain,(
% 3.16/1.01    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f38])).
% 3.16/1.01  
% 3.16/1.01  fof(f5,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f24,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f5])).
% 3.16/1.01  
% 3.16/1.01  fof(f51,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f24])).
% 3.16/1.01  
% 3.16/1.01  fof(f67,plain,(
% 3.16/1.01    v1_funct_1(sK2)),
% 3.16/1.01    inference(cnf_transformation,[],[f45])).
% 3.16/1.01  
% 3.16/1.01  fof(f68,plain,(
% 3.16/1.01    v1_funct_2(sK2,sK1,sK1)),
% 3.16/1.01    inference(cnf_transformation,[],[f45])).
% 3.16/1.01  
% 3.16/1.01  fof(f3,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f22,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f3])).
% 3.16/1.01  
% 3.16/1.01  fof(f49,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f22])).
% 3.16/1.01  
% 3.16/1.01  fof(f2,axiom,(
% 3.16/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f20,plain,(
% 3.16/1.01    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.16/1.01    inference(ennf_transformation,[],[f2])).
% 3.16/1.01  
% 3.16/1.01  fof(f21,plain,(
% 3.16/1.01    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.16/1.01    inference(flattening,[],[f20])).
% 3.16/1.01  
% 3.16/1.01  fof(f47,plain,(
% 3.16/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f21])).
% 3.16/1.01  
% 3.16/1.01  fof(f13,axiom,(
% 3.16/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f65,plain,(
% 3.16/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f13])).
% 3.16/1.01  
% 3.16/1.01  fof(f73,plain,(
% 3.16/1.01    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/1.01    inference(definition_unfolding,[],[f47,f65])).
% 3.16/1.01  
% 3.16/1.01  fof(f69,plain,(
% 3.16/1.01    v3_funct_2(sK2,sK1,sK1)),
% 3.16/1.01    inference(cnf_transformation,[],[f45])).
% 3.16/1.01  
% 3.16/1.01  fof(f7,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f27,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f7])).
% 3.16/1.01  
% 3.16/1.01  fof(f28,plain,(
% 3.16/1.01    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(flattening,[],[f27])).
% 3.16/1.01  
% 3.16/1.01  fof(f54,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f28])).
% 3.16/1.01  
% 3.16/1.01  fof(f12,axiom,(
% 3.16/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f35,plain,(
% 3.16/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.16/1.01    inference(ennf_transformation,[],[f12])).
% 3.16/1.01  
% 3.16/1.01  fof(f36,plain,(
% 3.16/1.01    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.16/1.01    inference(flattening,[],[f35])).
% 3.16/1.01  
% 3.16/1.01  fof(f64,plain,(
% 3.16/1.01    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f36])).
% 3.16/1.01  
% 3.16/1.01  fof(f9,axiom,(
% 3.16/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f31,plain,(
% 3.16/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.16/1.01    inference(ennf_transformation,[],[f9])).
% 3.16/1.01  
% 3.16/1.01  fof(f32,plain,(
% 3.16/1.01    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.16/1.01    inference(flattening,[],[f31])).
% 3.16/1.01  
% 3.16/1.01  fof(f61,plain,(
% 3.16/1.01    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f32])).
% 3.16/1.01  
% 3.16/1.01  fof(f11,axiom,(
% 3.16/1.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f33,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.16/1.01    inference(ennf_transformation,[],[f11])).
% 3.16/1.01  
% 3.16/1.01  fof(f34,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.16/1.01    inference(flattening,[],[f33])).
% 3.16/1.01  
% 3.16/1.01  fof(f63,plain,(
% 3.16/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f34])).
% 3.16/1.01  
% 3.16/1.01  fof(f58,plain,(
% 3.16/1.01    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f32])).
% 3.16/1.01  
% 3.16/1.01  fof(f71,plain,(
% 3.16/1.01    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.16/1.01    inference(cnf_transformation,[],[f45])).
% 3.16/1.01  
% 3.16/1.01  fof(f10,axiom,(
% 3.16/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f17,plain,(
% 3.16/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.16/1.01    inference(pure_predicate_removal,[],[f10])).
% 3.16/1.01  
% 3.16/1.01  fof(f62,plain,(
% 3.16/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f17])).
% 3.16/1.01  
% 3.16/1.01  fof(f6,axiom,(
% 3.16/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f25,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.16/1.01    inference(ennf_transformation,[],[f6])).
% 3.16/1.01  
% 3.16/1.01  fof(f26,plain,(
% 3.16/1.01    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(flattening,[],[f25])).
% 3.16/1.01  
% 3.16/1.01  fof(f52,plain,(
% 3.16/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f26])).
% 3.16/1.01  
% 3.16/1.01  fof(f55,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f28])).
% 3.16/1.01  
% 3.16/1.01  fof(f4,axiom,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f18,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.16/1.01    inference(pure_predicate_removal,[],[f4])).
% 3.16/1.01  
% 3.16/1.01  fof(f23,plain,(
% 3.16/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.16/1.01    inference(ennf_transformation,[],[f18])).
% 3.16/1.01  
% 3.16/1.01  fof(f50,plain,(
% 3.16/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.16/1.01    inference(cnf_transformation,[],[f23])).
% 3.16/1.01  
% 3.16/1.01  fof(f8,axiom,(
% 3.16/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.16/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.16/1.01  
% 3.16/1.01  fof(f29,plain,(
% 3.16/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.16/1.01    inference(ennf_transformation,[],[f8])).
% 3.16/1.01  
% 3.16/1.01  fof(f30,plain,(
% 3.16/1.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.01    inference(flattening,[],[f29])).
% 3.16/1.01  
% 3.16/1.01  fof(f43,plain,(
% 3.16/1.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.16/1.01    inference(nnf_transformation,[],[f30])).
% 3.16/1.01  
% 3.16/1.01  fof(f56,plain,(
% 3.16/1.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f43])).
% 3.16/1.01  
% 3.16/1.01  fof(f48,plain,(
% 3.16/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/1.01    inference(cnf_transformation,[],[f21])).
% 3.16/1.01  
% 3.16/1.01  fof(f72,plain,(
% 3.16/1.01    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.16/1.01    inference(definition_unfolding,[],[f48,f65])).
% 3.16/1.01  
% 3.16/1.01  cnf(c_699,plain,
% 3.16/1.01      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 3.16/1.01      theory(equality) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1430,plain,
% 3.16/1.01      ( X0_50 != X1_50
% 3.16/1.01      | X0_50 = k6_partfun1(X0_51)
% 3.16/1.01      | k6_partfun1(X0_51) != X1_50 ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_699]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2987,plain,
% 3.16/1.01      ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
% 3.16/1.01      | X0_50 = k6_partfun1(sK1)
% 3.16/1.01      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1430]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4562,plain,
% 3.16/1.01      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 3.16/1.01      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.16/1.01      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_2987]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4566,plain,
% 3.16/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 3.16/1.01      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.16/1.01      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_4562]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_21,negated_conjecture,
% 3.16/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_677,negated_conjecture,
% 3.16/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1139,plain,
% 3.16/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_19,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.16/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_679,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 3.16/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.16/1.01      | ~ v1_funct_1(X0_50)
% 3.16/1.01      | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_19]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1137,plain,
% 3.16/1.01      ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
% 3.16/1.01      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2215,plain,
% 3.16/1.01      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.16/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1139,c_1137]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_5,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_689,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.16/1.01      | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1127,plain,
% 3.16/1.01      ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1466,plain,
% 3.16/1.01      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1139,c_1127]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2248,plain,
% 3.16/1.01      ( k1_relat_1(sK2) = sK1
% 3.16/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_2215,c_1466]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_24,negated_conjecture,
% 3.16/1.01      ( v1_funct_1(sK2) ),
% 3.16/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_25,plain,
% 3.16/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_23,negated_conjecture,
% 3.16/1.01      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_26,plain,
% 3.16/1.01      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2778,plain,
% 3.16/1.01      ( k1_relat_1(sK2) = sK1 ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2248,c_25,c_26]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | v1_relat_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_690,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.16/1.01      | v1_relat_1(X0_50) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1126,plain,
% 3.16/1.01      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.16/1.01      | v1_relat_1(X0_50) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1377,plain,
% 3.16/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1139,c_1126]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2,plain,
% 3.16/1.01      ( ~ v1_relat_1(X0)
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v2_funct_1(X0)
% 3.16/1.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_691,plain,
% 3.16/1.01      ( ~ v1_relat_1(X0_50)
% 3.16/1.01      | ~ v1_funct_1(X0_50)
% 3.16/1.01      | ~ v2_funct_1(X0_50)
% 3.16/1.01      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1125,plain,
% 3.16/1.01      ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
% 3.16/1.01      | v1_relat_1(X0_50) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.16/1.01      | v2_funct_1(X0_50) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1675,plain,
% 3.16/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top
% 3.16/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1377,c_1125]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_22,negated_conjecture,
% 3.16/1.01      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.16/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_735,plain,
% 3.16/1.01      ( ~ v1_relat_1(sK2)
% 3.16/1.01      | ~ v1_funct_1(sK2)
% 3.16/1.01      | ~ v2_funct_1(sK2)
% 3.16/1.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_691]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_738,plain,
% 3.16/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/1.01      | v1_relat_1(sK2) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_690]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_8,plain,
% 3.16/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | v2_funct_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_687,plain,
% 3.16/1.01      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 3.16/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.16/1.01      | ~ v1_funct_1(X0_50)
% 3.16/1.01      | v2_funct_1(X0_50) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_747,plain,
% 3.16/1.01      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.16/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/1.01      | ~ v1_funct_1(sK2)
% 3.16/1.01      | v2_funct_1(sK2) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_687]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1819,plain,
% 3.16/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_1675,c_24,c_22,c_21,c_735,c_738,c_747]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2781,plain,
% 3.16/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_2778,c_1819]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_18,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.16/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_680,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 3.16/1.01      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 3.16/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.16/1.01      | ~ v1_funct_1(X0_50)
% 3.16/1.01      | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1136,plain,
% 3.16/1.01      ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
% 3.16/1.01      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2382,plain,
% 3.16/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.16/1.01      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1139,c_1136]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_766,plain,
% 3.16/1.01      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.16/1.01      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.16/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/1.01      | ~ v1_funct_1(sK2)
% 3.16/1.01      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_680]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2562,plain,
% 3.16/1.01      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2382,c_24,c_23,c_22,c_21,c_766]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_12,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.16/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.01      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.01      | ~ v1_funct_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_686,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 3.16/1.01      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 3.16/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.16/1.01      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.16/1.01      | ~ v1_funct_1(X0_50) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1130,plain,
% 3.16/1.01      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.16/1.01      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2575,plain,
% 3.16/1.01      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.16/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_2562,c_1130]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_27,plain,
% 3.16/1.01      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_28,plain,
% 3.16/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2849,plain,
% 3.16/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2575,c_25,c_26,c_27,c_28]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_17,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v1_funct_1(X3)
% 3.16/1.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_681,plain,
% 3.16/1.01      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.16/1.01      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 3.16/1.01      | ~ v1_funct_1(X0_50)
% 3.16/1.01      | ~ v1_funct_1(X1_50)
% 3.16/1.01      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1135,plain,
% 3.16/1.01      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 3.16/1.01      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.16/1.01      | v1_funct_1(X1_50) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3069,plain,
% 3.16/1.01      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1139,c_1135]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3360,plain,
% 3.16/1.01      ( v1_funct_1(X0_50) != iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.16/1.01      | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_3069,c_25]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3361,plain,
% 3.16/1.01      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top ),
% 3.16/1.01      inference(renaming,[status(thm)],[c_3360]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3371,plain,
% 3.16/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.16/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_2849,c_3361]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_15,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0,X1,X1)
% 3.16/1.01      | ~ v3_funct_2(X0,X1,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_683,plain,
% 3.16/1.01      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 3.16/1.01      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 3.16/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 3.16/1.01      | ~ v1_funct_1(X0_50)
% 3.16/1.01      | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_15]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1133,plain,
% 3.16/1.01      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.16/1.01      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2268,plain,
% 3.16/1.01      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1139,c_1133]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_758,plain,
% 3.16/1.01      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.16/1.01      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_760,plain,
% 3.16/1.01      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.16/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.16/1.01      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_758]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2556,plain,
% 3.16/1.01      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_2268,c_25,c_26,c_27,c_28,c_760]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2565,plain,
% 3.16/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_2562,c_2556]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3629,plain,
% 3.16/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 3.16/1.01      inference(global_propositional_subsumption,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_3371,c_2565]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_20,negated_conjecture,
% 3.16/1.01      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.16/1.01      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_678,negated_conjecture,
% 3.16/1.01      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.16/1.01      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_20]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1138,plain,
% 3.16/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.16/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2566,plain,
% 3.16/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.16/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_2562,c_1138]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3632,plain,
% 3.16/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.16/1.01      | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_3629,c_2566]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4506,plain,
% 3.16/1.01      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.16/1.01      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.16/1.01      inference(demodulation,[status(thm)],[c_2781,c_3632]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_707,plain,
% 3.16/1.01      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 3.16/1.01      | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
% 3.16/1.01      | X2_51 != X0_51
% 3.16/1.01      | X3_51 != X1_51
% 3.16/1.01      | X2_50 != X0_50
% 3.16/1.01      | X3_50 != X1_50 ),
% 3.16/1.01      theory(equality) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2202,plain,
% 3.16/1.01      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 3.16/1.01      | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
% 3.16/1.01      | X2_51 != X0_51
% 3.16/1.01      | X3_51 != X1_51
% 3.16/1.01      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
% 3.16/1.01      | k6_partfun1(X8_51) != X1_50 ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_707]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3251,plain,
% 3.16/1.01      ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
% 3.16/1.01      | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
% 3.16/1.01      | X3_51 != X0_51
% 3.16/1.01      | X4_51 != X1_51
% 3.16/1.01      | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
% 3.16/1.01      | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_2202]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4334,plain,
% 3.16/1.01      ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
% 3.16/1.01      | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
% 3.16/1.01      | X0_51 != X7_51
% 3.16/1.01      | X1_51 != X8_51
% 3.16/1.01      | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
% 3.16/1.01      | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_3251]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4336,plain,
% 3.16/1.01      ( X0_51 != X1_51
% 3.16/1.01      | X2_51 != X3_51
% 3.16/1.01      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X8_51)
% 3.16/1.01      | k6_partfun1(X9_51) != k6_partfun1(X8_51)
% 3.16/1.01      | r2_relset_1(X0_51,X2_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X0_50),k6_partfun1(X9_51)) = iProver_top
% 3.16/1.01      | r2_relset_1(X1_51,X3_51,k6_partfun1(X8_51),k6_partfun1(X8_51)) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_4334]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4338,plain,
% 3.16/1.01      ( sK1 != sK1
% 3.16/1.01      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 3.16/1.01      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 3.16/1.01      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) = iProver_top
% 3.16/1.01      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_4336]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3073,plain,
% 3.16/1.01      ( k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50)
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.16/1.01      | v1_funct_1(X0_50) != iProver_top
% 3.16/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_2849,c_1135]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_3133,plain,
% 3.16/1.01      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.16/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.16/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.16/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_3073]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_700,plain,
% 3.16/1.01      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 3.16/1.01      theory(equality) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2141,plain,
% 3.16/1.01      ( k2_relat_1(X0_50) != X0_51
% 3.16/1.01      | sK1 != X0_51
% 3.16/1.01      | sK1 = k2_relat_1(X0_50) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_700]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_2142,plain,
% 3.16/1.01      ( k2_relat_1(sK2) != sK1 | sK1 = k2_relat_1(sK2) | sK1 != sK1 ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_2141]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_704,plain,
% 3.16/1.01      ( X0_51 != X1_51 | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
% 3.16/1.01      theory(equality) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1401,plain,
% 3.16/1.01      ( sK1 != X0_51 | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_704]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1922,plain,
% 3.16/1.01      ( sK1 != k2_relat_1(X0_50)
% 3.16/1.01      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1923,plain,
% 3.16/1.01      ( sK1 != k2_relat_1(sK2)
% 3.16/1.01      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1922]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1399,plain,
% 3.16/1.01      ( X0_50 != X1_50
% 3.16/1.01      | k6_partfun1(sK1) != X1_50
% 3.16/1.01      | k6_partfun1(sK1) = X0_50 ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_699]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1489,plain,
% 3.16/1.01      ( X0_50 != k6_partfun1(X0_51)
% 3.16/1.01      | k6_partfun1(sK1) = X0_50
% 3.16/1.01      | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1399]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1582,plain,
% 3.16/1.01      ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
% 3.16/1.01      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
% 3.16/1.01      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1489]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1583,plain,
% 3.16/1.01      ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
% 3.16/1.01      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.16/1.01      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1582]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_16,plain,
% 3.16/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_682,plain,
% 3.16/1.01      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1134,plain,
% 3.16/1.01      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_6,plain,
% 3.16/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 3.16/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_688,plain,
% 3.16/1.01      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
% 3.16/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.16/1.01      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1128,plain,
% 3.16/1.01      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.16/1.01      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.16/1.01      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1552,plain,
% 3.16/1.01      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
% 3.16/1.01      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
% 3.16/1.01      inference(superposition,[status(thm)],[c_1134,c_1128]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1568,plain,
% 3.16/1.01      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top
% 3.16/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_1552]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_7,plain,
% 3.16/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.01      | v2_funct_2(X0,X2)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ v1_funct_1(X0) ),
% 3.16/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_4,plain,
% 3.16/1.01      ( v5_relat_1(X0,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.16/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_11,plain,
% 3.16/1.01      ( ~ v2_funct_2(X0,X1)
% 3.16/1.01      | ~ v5_relat_1(X0,X1)
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | k2_relat_1(X0) = X1 ),
% 3.16/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_278,plain,
% 3.16/1.01      ( ~ v2_funct_2(X0,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.16/1.01      | ~ v1_relat_1(X0)
% 3.16/1.01      | k2_relat_1(X0) = X1 ),
% 3.16/1.01      inference(resolution,[status(thm)],[c_4,c_11]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_290,plain,
% 3.16/1.01      ( ~ v2_funct_2(X0,X1)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.16/1.01      | k2_relat_1(X0) = X1 ),
% 3.16/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_278,c_3]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_363,plain,
% 3.16/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | X3 != X0
% 3.16/1.01      | X5 != X2
% 3.16/1.01      | k2_relat_1(X3) = X5 ),
% 3.16/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_290]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_364,plain,
% 3.16/1.01      ( ~ v3_funct_2(X0,X1,X2)
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.16/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | k2_relat_1(X0) = X2 ),
% 3.16/1.01      inference(unflattening,[status(thm)],[c_363]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_673,plain,
% 3.16/1.01      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 3.16/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.16/1.01      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 3.16/1.01      | ~ v1_funct_1(X0_50)
% 3.16/1.01      | k2_relat_1(X0_50) = X1_51 ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_364]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_777,plain,
% 3.16/1.01      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.16/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.16/1.01      | ~ v1_funct_1(sK2)
% 3.16/1.01      | k2_relat_1(sK2) = sK1 ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_673]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_1,plain,
% 3.16/1.01      ( ~ v1_relat_1(X0)
% 3.16/1.01      | ~ v1_funct_1(X0)
% 3.16/1.01      | ~ v2_funct_1(X0)
% 3.16/1.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.16/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_692,plain,
% 3.16/1.01      ( ~ v1_relat_1(X0_50)
% 3.16/1.01      | ~ v1_funct_1(X0_50)
% 3.16/1.01      | ~ v2_funct_1(X0_50)
% 3.16/1.01      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
% 3.16/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_732,plain,
% 3.16/1.01      ( ~ v1_relat_1(sK2)
% 3.16/1.01      | ~ v1_funct_1(sK2)
% 3.16/1.01      | ~ v2_funct_1(sK2)
% 3.16/1.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_692]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_696,plain,( X0_51 = X0_51 ),theory(equality) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_725,plain,
% 3.16/1.01      ( sK1 = sK1 ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_696]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(c_715,plain,
% 3.16/1.01      ( sK1 != sK1 | k6_partfun1(sK1) = k6_partfun1(sK1) ),
% 3.16/1.01      inference(instantiation,[status(thm)],[c_704]) ).
% 3.16/1.01  
% 3.16/1.01  cnf(contradiction,plain,
% 3.16/1.01      ( $false ),
% 3.16/1.01      inference(minisat,
% 3.16/1.01                [status(thm)],
% 3.16/1.01                [c_4566,c_4506,c_4338,c_3133,c_2565,c_2142,c_1923,c_1583,
% 3.16/1.01                 c_1568,c_777,c_747,c_738,c_732,c_725,c_715,c_28,c_21,
% 3.16/1.01                 c_22,c_25,c_24]) ).
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.16/1.01  
% 3.16/1.01  ------                               Statistics
% 3.16/1.01  
% 3.16/1.01  ------ General
% 3.16/1.01  
% 3.16/1.01  abstr_ref_over_cycles:                  0
% 3.16/1.01  abstr_ref_under_cycles:                 0
% 3.16/1.01  gc_basic_clause_elim:                   0
% 3.16/1.01  forced_gc_time:                         0
% 3.16/1.01  parsing_time:                           0.011
% 3.16/1.01  unif_index_cands_time:                  0.
% 3.16/1.01  unif_index_add_time:                    0.
% 3.16/1.01  orderings_time:                         0.
% 3.16/1.01  out_proof_time:                         0.04
% 3.16/1.01  total_time:                             0.229
% 3.16/1.01  num_of_symbols:                         57
% 3.16/1.01  num_of_terms:                           4199
% 3.16/1.01  
% 3.16/1.01  ------ Preprocessing
% 3.16/1.01  
% 3.16/1.01  num_of_splits:                          0
% 3.16/1.01  num_of_split_atoms:                     0
% 3.16/1.01  num_of_reused_defs:                     0
% 3.16/1.01  num_eq_ax_congr_red:                    29
% 3.16/1.01  num_of_sem_filtered_clauses:            1
% 3.16/1.01  num_of_subtypes:                        4
% 3.16/1.01  monotx_restored_types:                  1
% 3.16/1.01  sat_num_of_epr_types:                   0
% 3.16/1.01  sat_num_of_non_cyclic_types:            0
% 3.16/1.01  sat_guarded_non_collapsed_types:        0
% 3.16/1.01  num_pure_diseq_elim:                    0
% 3.16/1.01  simp_replaced_by:                       0
% 3.16/1.01  res_preprocessed:                       122
% 3.16/1.01  prep_upred:                             0
% 3.16/1.01  prep_unflattend:                        6
% 3.16/1.01  smt_new_axioms:                         0
% 3.16/1.01  pred_elim_cands:                        7
% 3.16/1.01  pred_elim:                              2
% 3.16/1.01  pred_elim_cl:                           3
% 3.16/1.01  pred_elim_cycles:                       6
% 3.16/1.01  merged_defs:                            0
% 3.16/1.01  merged_defs_ncl:                        0
% 3.16/1.01  bin_hyper_res:                          0
% 3.16/1.01  prep_cycles:                            4
% 3.16/1.01  pred_elim_time:                         0.006
% 3.16/1.01  splitting_time:                         0.
% 3.16/1.01  sem_filter_time:                        0.
% 3.16/1.01  monotx_time:                            0.001
% 3.16/1.01  subtype_inf_time:                       0.001
% 3.16/1.01  
% 3.16/1.01  ------ Problem properties
% 3.16/1.01  
% 3.16/1.01  clauses:                                21
% 3.16/1.01  conjectures:                            5
% 3.16/1.01  epr:                                    3
% 3.16/1.01  horn:                                   21
% 3.16/1.01  ground:                                 5
% 3.16/1.01  unary:                                  6
% 3.16/1.01  binary:                                 3
% 3.16/1.01  lits:                                   66
% 3.16/1.01  lits_eq:                                7
% 3.16/1.01  fd_pure:                                0
% 3.16/1.01  fd_pseudo:                              0
% 3.16/1.01  fd_cond:                                0
% 3.16/1.01  fd_pseudo_cond:                         1
% 3.16/1.01  ac_symbols:                             0
% 3.16/1.01  
% 3.16/1.01  ------ Propositional Solver
% 3.16/1.01  
% 3.16/1.01  prop_solver_calls:                      28
% 3.16/1.01  prop_fast_solver_calls:                 990
% 3.16/1.01  smt_solver_calls:                       0
% 3.16/1.01  smt_fast_solver_calls:                  0
% 3.16/1.01  prop_num_of_clauses:                    1331
% 3.16/1.01  prop_preprocess_simplified:             5040
% 3.16/1.01  prop_fo_subsumed:                       37
% 3.16/1.01  prop_solver_time:                       0.
% 3.16/1.01  smt_solver_time:                        0.
% 3.16/1.01  smt_fast_solver_time:                   0.
% 3.16/1.01  prop_fast_solver_time:                  0.
% 3.16/1.01  prop_unsat_core_time:                   0.
% 3.16/1.01  
% 3.16/1.01  ------ QBF
% 3.16/1.01  
% 3.16/1.01  qbf_q_res:                              0
% 3.16/1.01  qbf_num_tautologies:                    0
% 3.16/1.01  qbf_prep_cycles:                        0
% 3.16/1.01  
% 3.16/1.01  ------ BMC1
% 3.16/1.01  
% 3.16/1.01  bmc1_current_bound:                     -1
% 3.16/1.01  bmc1_last_solved_bound:                 -1
% 3.16/1.01  bmc1_unsat_core_size:                   -1
% 3.16/1.01  bmc1_unsat_core_parents_size:           -1
% 3.16/1.01  bmc1_merge_next_fun:                    0
% 3.16/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.16/1.01  
% 3.16/1.01  ------ Instantiation
% 3.16/1.01  
% 3.16/1.01  inst_num_of_clauses:                    450
% 3.16/1.01  inst_num_in_passive:                    51
% 3.16/1.01  inst_num_in_active:                     264
% 3.16/1.01  inst_num_in_unprocessed:                134
% 3.16/1.01  inst_num_of_loops:                      285
% 3.16/1.01  inst_num_of_learning_restarts:          0
% 3.16/1.01  inst_num_moves_active_passive:          16
% 3.16/1.01  inst_lit_activity:                      0
% 3.16/1.01  inst_lit_activity_moves:                0
% 3.16/1.01  inst_num_tautologies:                   0
% 3.16/1.01  inst_num_prop_implied:                  0
% 3.16/1.01  inst_num_existing_simplified:           0
% 3.16/1.01  inst_num_eq_res_simplified:             0
% 3.16/1.01  inst_num_child_elim:                    0
% 3.16/1.01  inst_num_of_dismatching_blockings:      416
% 3.16/1.01  inst_num_of_non_proper_insts:           597
% 3.16/1.01  inst_num_of_duplicates:                 0
% 3.16/1.01  inst_inst_num_from_inst_to_res:         0
% 3.16/1.01  inst_dismatching_checking_time:         0.
% 3.16/1.01  
% 3.16/1.01  ------ Resolution
% 3.16/1.01  
% 3.16/1.01  res_num_of_clauses:                     0
% 3.16/1.01  res_num_in_passive:                     0
% 3.16/1.01  res_num_in_active:                      0
% 3.16/1.01  res_num_of_loops:                       126
% 3.16/1.01  res_forward_subset_subsumed:            102
% 3.16/1.01  res_backward_subset_subsumed:           4
% 3.16/1.01  res_forward_subsumed:                   0
% 3.16/1.01  res_backward_subsumed:                  0
% 3.16/1.01  res_forward_subsumption_resolution:     2
% 3.16/1.01  res_backward_subsumption_resolution:    0
% 3.16/1.01  res_clause_to_clause_subsumption:       199
% 3.16/1.01  res_orphan_elimination:                 0
% 3.16/1.01  res_tautology_del:                      78
% 3.16/1.01  res_num_eq_res_simplified:              0
% 3.16/1.01  res_num_sel_changes:                    0
% 3.16/1.01  res_moves_from_active_to_pass:          0
% 3.16/1.01  
% 3.16/1.01  ------ Superposition
% 3.16/1.01  
% 3.16/1.01  sup_time_total:                         0.
% 3.16/1.01  sup_time_generating:                    0.
% 3.16/1.01  sup_time_sim_full:                      0.
% 3.16/1.01  sup_time_sim_immed:                     0.
% 3.16/1.01  
% 3.16/1.01  sup_num_of_clauses:                     94
% 3.16/1.01  sup_num_in_active:                      47
% 3.16/1.01  sup_num_in_passive:                     47
% 3.16/1.01  sup_num_of_loops:                       56
% 3.16/1.01  sup_fw_superposition:                   58
% 3.16/1.01  sup_bw_superposition:                   21
% 3.16/1.01  sup_immediate_simplified:               10
% 3.16/1.01  sup_given_eliminated:                   0
% 3.16/1.01  comparisons_done:                       0
% 3.16/1.01  comparisons_avoided:                    0
% 3.16/1.01  
% 3.16/1.01  ------ Simplifications
% 3.16/1.01  
% 3.16/1.01  
% 3.16/1.01  sim_fw_subset_subsumed:                 1
% 3.16/1.01  sim_bw_subset_subsumed:                 2
% 3.16/1.01  sim_fw_subsumed:                        0
% 3.16/1.01  sim_bw_subsumed:                        1
% 3.16/1.01  sim_fw_subsumption_res:                 3
% 3.16/1.01  sim_bw_subsumption_res:                 0
% 3.16/1.01  sim_tautology_del:                      0
% 3.16/1.01  sim_eq_tautology_del:                   1
% 3.16/1.01  sim_eq_res_simp:                        0
% 3.16/1.01  sim_fw_demodulated:                     1
% 3.16/1.01  sim_bw_demodulated:                     9
% 3.16/1.01  sim_light_normalised:                   3
% 3.16/1.01  sim_joinable_taut:                      0
% 3.16/1.01  sim_joinable_simp:                      0
% 3.16/1.01  sim_ac_normalised:                      0
% 3.16/1.01  sim_smt_subsumption:                    0
% 3.16/1.01  
%------------------------------------------------------------------------------
