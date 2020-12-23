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
% DateTime   : Thu Dec  3 12:07:25 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 830 expanded)
%              Number of clauses        :  117 ( 275 expanded)
%              Number of leaves         :   20 ( 163 expanded)
%              Depth                    :   18
%              Number of atoms          :  606 (3903 expanded)
%              Number of equality atoms :  237 ( 432 expanded)
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

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f42,plain,
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

fof(f43,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f42])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f67,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f63])).

cnf(c_699,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_1427,plain,
    ( X0_50 != X1_50
    | X0_50 = k6_partfun1(X0_51)
    | k6_partfun1(X0_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_3157,plain,
    ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
    | X0_50 = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_4798,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_4802,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_4798])).

cnf(c_707,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
    | X2_51 != X0_51
    | X3_51 != X1_51
    | X2_50 != X0_50
    | X3_50 != X1_50 ),
    theory(equality)).

cnf(c_2213,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
    | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
    | X2_51 != X0_51
    | X3_51 != X1_51
    | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
    | k6_partfun1(X8_51) != X1_50 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_3377,plain,
    ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
    | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
    | X3_51 != X0_51
    | X4_51 != X1_51
    | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
    | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_4632,plain,
    ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
    | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
    | X0_51 != X7_51
    | X1_51 != X8_51
    | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
    | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
    inference(instantiation,[status(thm)],[c_3377])).

cnf(c_4635,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | sK1 != sK1
    | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | k6_partfun1(sK1) != k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_4632])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f68])).

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
    inference(cnf_transformation,[],[f64])).

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

cnf(c_2225,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1137])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_689,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1127,plain,
    ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_1461,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1139,c_1127])).

cnf(c_2258,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2225,c_1461])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_26,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2773,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2258,c_25,c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(cnf_transformation,[],[f71])).

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

cnf(c_1676,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1125])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f67])).

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

cnf(c_9,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_686,plain,
    ( ~ v3_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v2_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_748,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_1834,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1676,c_24,c_22,c_21,c_735,c_738,c_748])).

cnf(c_2776,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2773,c_1834])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

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

cnf(c_2413,plain,
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

cnf(c_2599,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2413,c_24,c_23,c_22,c_21,c_766])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_685,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1131,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_2612,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2599,c_1131])).

cnf(c_27,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2851,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2612,c_25,c_26,c_27,c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f61])).

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

cnf(c_3075,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1135])).

cnf(c_3322,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3075,c_25])).

cnf(c_3323,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_3322])).

cnf(c_3333,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2851,c_3323])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_682,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X0_51)
    | ~ v3_funct_2(X0_50,X0_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1134,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_2278,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1134])).

cnf(c_759,plain,
    ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_761,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_2593,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2278,c_25,c_26,c_27,c_28,c_761])).

cnf(c_2602,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2599,c_2593])).

cnf(c_3574,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3333,c_2602])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_678,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1138,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_2603,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2599,c_1138])).

cnf(c_3577,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3574,c_2603])).

cnf(c_4483,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2776,c_3577])).

cnf(c_4491,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4483])).

cnf(c_3079,plain,
    ( k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2851,c_1135])).

cnf(c_3139,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3079])).

cnf(c_700,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2037,plain,
    ( k2_relat_1(X0_50) != X0_51
    | sK1 != X0_51
    | sK1 = k2_relat_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_700])).

cnf(c_2038,plain,
    ( k2_relat_1(sK2) != sK1
    | sK1 = k2_relat_1(sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2037])).

cnf(c_703,plain,
    ( X0_51 != X1_51
    | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
    theory(equality)).

cnf(c_1401,plain,
    ( sK1 != X0_51
    | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_1937,plain,
    ( sK1 != k2_relat_1(X0_50)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1938,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_1399,plain,
    ( X0_50 != X1_50
    | k6_partfun1(sK1) != X1_50
    | k6_partfun1(sK1) = X0_50 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_1484,plain,
    ( X0_50 != k6_partfun1(X0_51)
    | k6_partfun1(sK1) = X0_50
    | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_1576,plain,
    ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_1577,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
    | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_7,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_687,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1129,plain,
    ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_6,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f50])).

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

cnf(c_1546,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1129,c_1128])).

cnf(c_1561,plain,
    ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1546])).

cnf(c_1563,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_8,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_278,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_12])).

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
    inference(resolution_lifted,[status(thm)],[c_8,c_290])).

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
    inference(cnf_transformation,[],[f70])).

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

cnf(c_714,plain,
    ( sK1 != sK1
    | k6_partfun1(sK1) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4802,c_4635,c_4491,c_3139,c_2602,c_2038,c_1938,c_1577,c_1563,c_777,c_748,c_738,c_732,c_725,c_714,c_28,c_21,c_22,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:59:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.76/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/0.98  
% 2.76/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/0.98  
% 2.76/0.98  ------  iProver source info
% 2.76/0.98  
% 2.76/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.76/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/0.98  git: non_committed_changes: false
% 2.76/0.98  git: last_make_outside_of_git: false
% 2.76/0.98  
% 2.76/0.98  ------ 
% 2.76/0.98  
% 2.76/0.98  ------ Input Options
% 2.76/0.98  
% 2.76/0.98  --out_options                           all
% 2.76/0.98  --tptp_safe_out                         true
% 2.76/0.98  --problem_path                          ""
% 2.76/0.98  --include_path                          ""
% 2.76/0.98  --clausifier                            res/vclausify_rel
% 2.76/0.98  --clausifier_options                    --mode clausify
% 2.76/0.98  --stdin                                 false
% 2.76/0.98  --stats_out                             all
% 2.76/0.98  
% 2.76/0.98  ------ General Options
% 2.76/0.98  
% 2.76/0.98  --fof                                   false
% 2.76/0.98  --time_out_real                         305.
% 2.76/0.98  --time_out_virtual                      -1.
% 2.76/0.98  --symbol_type_check                     false
% 2.76/0.98  --clausify_out                          false
% 2.76/0.98  --sig_cnt_out                           false
% 2.76/0.98  --trig_cnt_out                          false
% 2.76/0.98  --trig_cnt_out_tolerance                1.
% 2.76/0.98  --trig_cnt_out_sk_spl                   false
% 2.76/0.98  --abstr_cl_out                          false
% 2.76/0.98  
% 2.76/0.98  ------ Global Options
% 2.76/0.98  
% 2.76/0.98  --schedule                              default
% 2.76/0.98  --add_important_lit                     false
% 2.76/0.98  --prop_solver_per_cl                    1000
% 2.76/0.98  --min_unsat_core                        false
% 2.76/0.98  --soft_assumptions                      false
% 2.76/0.98  --soft_lemma_size                       3
% 2.76/0.98  --prop_impl_unit_size                   0
% 2.76/0.98  --prop_impl_unit                        []
% 2.76/0.98  --share_sel_clauses                     true
% 2.76/0.98  --reset_solvers                         false
% 2.76/0.98  --bc_imp_inh                            [conj_cone]
% 2.76/0.98  --conj_cone_tolerance                   3.
% 2.76/0.98  --extra_neg_conj                        none
% 2.76/0.98  --large_theory_mode                     true
% 2.76/0.98  --prolific_symb_bound                   200
% 2.76/0.98  --lt_threshold                          2000
% 2.76/0.98  --clause_weak_htbl                      true
% 2.76/0.98  --gc_record_bc_elim                     false
% 2.76/0.98  
% 2.76/0.98  ------ Preprocessing Options
% 2.76/0.98  
% 2.76/0.98  --preprocessing_flag                    true
% 2.76/0.98  --time_out_prep_mult                    0.1
% 2.76/0.98  --splitting_mode                        input
% 2.76/0.98  --splitting_grd                         true
% 2.76/0.98  --splitting_cvd                         false
% 2.76/0.98  --splitting_cvd_svl                     false
% 2.76/0.98  --splitting_nvd                         32
% 2.76/0.98  --sub_typing                            true
% 2.76/0.98  --prep_gs_sim                           true
% 2.76/0.98  --prep_unflatten                        true
% 2.76/0.98  --prep_res_sim                          true
% 2.76/0.98  --prep_upred                            true
% 2.76/0.98  --prep_sem_filter                       exhaustive
% 2.76/0.98  --prep_sem_filter_out                   false
% 2.76/0.98  --pred_elim                             true
% 2.76/0.98  --res_sim_input                         true
% 2.76/0.98  --eq_ax_congr_red                       true
% 2.76/0.98  --pure_diseq_elim                       true
% 2.76/0.98  --brand_transform                       false
% 2.76/0.98  --non_eq_to_eq                          false
% 2.76/0.98  --prep_def_merge                        true
% 2.76/0.98  --prep_def_merge_prop_impl              false
% 2.76/0.99  --prep_def_merge_mbd                    true
% 2.76/0.99  --prep_def_merge_tr_red                 false
% 2.76/0.99  --prep_def_merge_tr_cl                  false
% 2.76/0.99  --smt_preprocessing                     true
% 2.76/0.99  --smt_ac_axioms                         fast
% 2.76/0.99  --preprocessed_out                      false
% 2.76/0.99  --preprocessed_stats                    false
% 2.76/0.99  
% 2.76/0.99  ------ Abstraction refinement Options
% 2.76/0.99  
% 2.76/0.99  --abstr_ref                             []
% 2.76/0.99  --abstr_ref_prep                        false
% 2.76/0.99  --abstr_ref_until_sat                   false
% 2.76/0.99  --abstr_ref_sig_restrict                funpre
% 2.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.99  --abstr_ref_under                       []
% 2.76/0.99  
% 2.76/0.99  ------ SAT Options
% 2.76/0.99  
% 2.76/0.99  --sat_mode                              false
% 2.76/0.99  --sat_fm_restart_options                ""
% 2.76/0.99  --sat_gr_def                            false
% 2.76/0.99  --sat_epr_types                         true
% 2.76/0.99  --sat_non_cyclic_types                  false
% 2.76/0.99  --sat_finite_models                     false
% 2.76/0.99  --sat_fm_lemmas                         false
% 2.76/0.99  --sat_fm_prep                           false
% 2.76/0.99  --sat_fm_uc_incr                        true
% 2.76/0.99  --sat_out_model                         small
% 2.76/0.99  --sat_out_clauses                       false
% 2.76/0.99  
% 2.76/0.99  ------ QBF Options
% 2.76/0.99  
% 2.76/0.99  --qbf_mode                              false
% 2.76/0.99  --qbf_elim_univ                         false
% 2.76/0.99  --qbf_dom_inst                          none
% 2.76/0.99  --qbf_dom_pre_inst                      false
% 2.76/0.99  --qbf_sk_in                             false
% 2.76/0.99  --qbf_pred_elim                         true
% 2.76/0.99  --qbf_split                             512
% 2.76/0.99  
% 2.76/0.99  ------ BMC1 Options
% 2.76/0.99  
% 2.76/0.99  --bmc1_incremental                      false
% 2.76/0.99  --bmc1_axioms                           reachable_all
% 2.76/0.99  --bmc1_min_bound                        0
% 2.76/0.99  --bmc1_max_bound                        -1
% 2.76/0.99  --bmc1_max_bound_default                -1
% 2.76/0.99  --bmc1_symbol_reachability              true
% 2.76/0.99  --bmc1_property_lemmas                  false
% 2.76/0.99  --bmc1_k_induction                      false
% 2.76/0.99  --bmc1_non_equiv_states                 false
% 2.76/0.99  --bmc1_deadlock                         false
% 2.76/0.99  --bmc1_ucm                              false
% 2.76/0.99  --bmc1_add_unsat_core                   none
% 2.76/0.99  --bmc1_unsat_core_children              false
% 2.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.99  --bmc1_out_stat                         full
% 2.76/0.99  --bmc1_ground_init                      false
% 2.76/0.99  --bmc1_pre_inst_next_state              false
% 2.76/0.99  --bmc1_pre_inst_state                   false
% 2.76/0.99  --bmc1_pre_inst_reach_state             false
% 2.76/0.99  --bmc1_out_unsat_core                   false
% 2.76/0.99  --bmc1_aig_witness_out                  false
% 2.76/0.99  --bmc1_verbose                          false
% 2.76/0.99  --bmc1_dump_clauses_tptp                false
% 2.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.99  --bmc1_dump_file                        -
% 2.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.99  --bmc1_ucm_extend_mode                  1
% 2.76/0.99  --bmc1_ucm_init_mode                    2
% 2.76/0.99  --bmc1_ucm_cone_mode                    none
% 2.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.99  --bmc1_ucm_relax_model                  4
% 2.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.99  --bmc1_ucm_layered_model                none
% 2.76/0.99  --bmc1_ucm_max_lemma_size               10
% 2.76/0.99  
% 2.76/0.99  ------ AIG Options
% 2.76/0.99  
% 2.76/0.99  --aig_mode                              false
% 2.76/0.99  
% 2.76/0.99  ------ Instantiation Options
% 2.76/0.99  
% 2.76/0.99  --instantiation_flag                    true
% 2.76/0.99  --inst_sos_flag                         false
% 2.76/0.99  --inst_sos_phase                        true
% 2.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.99  --inst_lit_sel_side                     num_symb
% 2.76/0.99  --inst_solver_per_active                1400
% 2.76/0.99  --inst_solver_calls_frac                1.
% 2.76/0.99  --inst_passive_queue_type               priority_queues
% 2.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.99  --inst_passive_queues_freq              [25;2]
% 2.76/0.99  --inst_dismatching                      true
% 2.76/0.99  --inst_eager_unprocessed_to_passive     true
% 2.76/0.99  --inst_prop_sim_given                   true
% 2.76/0.99  --inst_prop_sim_new                     false
% 2.76/0.99  --inst_subs_new                         false
% 2.76/0.99  --inst_eq_res_simp                      false
% 2.76/0.99  --inst_subs_given                       false
% 2.76/0.99  --inst_orphan_elimination               true
% 2.76/0.99  --inst_learning_loop_flag               true
% 2.76/0.99  --inst_learning_start                   3000
% 2.76/0.99  --inst_learning_factor                  2
% 2.76/0.99  --inst_start_prop_sim_after_learn       3
% 2.76/0.99  --inst_sel_renew                        solver
% 2.76/0.99  --inst_lit_activity_flag                true
% 2.76/0.99  --inst_restr_to_given                   false
% 2.76/0.99  --inst_activity_threshold               500
% 2.76/0.99  --inst_out_proof                        true
% 2.76/0.99  
% 2.76/0.99  ------ Resolution Options
% 2.76/0.99  
% 2.76/0.99  --resolution_flag                       true
% 2.76/0.99  --res_lit_sel                           adaptive
% 2.76/0.99  --res_lit_sel_side                      none
% 2.76/0.99  --res_ordering                          kbo
% 2.76/0.99  --res_to_prop_solver                    active
% 2.76/0.99  --res_prop_simpl_new                    false
% 2.76/0.99  --res_prop_simpl_given                  true
% 2.76/0.99  --res_passive_queue_type                priority_queues
% 2.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.99  --res_passive_queues_freq               [15;5]
% 2.76/0.99  --res_forward_subs                      full
% 2.76/0.99  --res_backward_subs                     full
% 2.76/0.99  --res_forward_subs_resolution           true
% 2.76/0.99  --res_backward_subs_resolution          true
% 2.76/0.99  --res_orphan_elimination                true
% 2.76/0.99  --res_time_limit                        2.
% 2.76/0.99  --res_out_proof                         true
% 2.76/0.99  
% 2.76/0.99  ------ Superposition Options
% 2.76/0.99  
% 2.76/0.99  --superposition_flag                    true
% 2.76/0.99  --sup_passive_queue_type                priority_queues
% 2.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.99  --demod_completeness_check              fast
% 2.76/0.99  --demod_use_ground                      true
% 2.76/0.99  --sup_to_prop_solver                    passive
% 2.76/0.99  --sup_prop_simpl_new                    true
% 2.76/0.99  --sup_prop_simpl_given                  true
% 2.76/0.99  --sup_fun_splitting                     false
% 2.76/0.99  --sup_smt_interval                      50000
% 2.76/0.99  
% 2.76/0.99  ------ Superposition Simplification Setup
% 2.76/0.99  
% 2.76/0.99  --sup_indices_passive                   []
% 2.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.99  --sup_full_bw                           [BwDemod]
% 2.76/0.99  --sup_immed_triv                        [TrivRules]
% 2.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.99  --sup_immed_bw_main                     []
% 2.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.99  
% 2.76/0.99  ------ Combination Options
% 2.76/0.99  
% 2.76/0.99  --comb_res_mult                         3
% 2.76/0.99  --comb_sup_mult                         2
% 2.76/0.99  --comb_inst_mult                        10
% 2.76/0.99  
% 2.76/0.99  ------ Debug Options
% 2.76/0.99  
% 2.76/0.99  --dbg_backtrace                         false
% 2.76/0.99  --dbg_dump_prop_clauses                 false
% 2.76/0.99  --dbg_dump_prop_clauses_file            -
% 2.76/0.99  --dbg_out_stat                          false
% 2.76/0.99  ------ Parsing...
% 2.76/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/0.99  
% 2.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.76/0.99  
% 2.76/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/0.99  
% 2.76/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/0.99  ------ Proving...
% 2.76/0.99  ------ Problem Properties 
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  clauses                                 21
% 2.76/0.99  conjectures                             5
% 2.76/0.99  EPR                                     3
% 2.76/0.99  Horn                                    21
% 2.76/0.99  unary                                   6
% 2.76/0.99  binary                                  3
% 2.76/0.99  lits                                    66
% 2.76/0.99  lits eq                                 7
% 2.76/0.99  fd_pure                                 0
% 2.76/0.99  fd_pseudo                               0
% 2.76/0.99  fd_cond                                 0
% 2.76/0.99  fd_pseudo_cond                          1
% 2.76/0.99  AC symbols                              0
% 2.76/0.99  
% 2.76/0.99  ------ Schedule dynamic 5 is on 
% 2.76/0.99  
% 2.76/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  ------ 
% 2.76/0.99  Current options:
% 2.76/0.99  ------ 
% 2.76/0.99  
% 2.76/0.99  ------ Input Options
% 2.76/0.99  
% 2.76/0.99  --out_options                           all
% 2.76/0.99  --tptp_safe_out                         true
% 2.76/0.99  --problem_path                          ""
% 2.76/0.99  --include_path                          ""
% 2.76/0.99  --clausifier                            res/vclausify_rel
% 2.76/0.99  --clausifier_options                    --mode clausify
% 2.76/0.99  --stdin                                 false
% 2.76/0.99  --stats_out                             all
% 2.76/0.99  
% 2.76/0.99  ------ General Options
% 2.76/0.99  
% 2.76/0.99  --fof                                   false
% 2.76/0.99  --time_out_real                         305.
% 2.76/0.99  --time_out_virtual                      -1.
% 2.76/0.99  --symbol_type_check                     false
% 2.76/0.99  --clausify_out                          false
% 2.76/0.99  --sig_cnt_out                           false
% 2.76/0.99  --trig_cnt_out                          false
% 2.76/0.99  --trig_cnt_out_tolerance                1.
% 2.76/0.99  --trig_cnt_out_sk_spl                   false
% 2.76/0.99  --abstr_cl_out                          false
% 2.76/0.99  
% 2.76/0.99  ------ Global Options
% 2.76/0.99  
% 2.76/0.99  --schedule                              default
% 2.76/0.99  --add_important_lit                     false
% 2.76/0.99  --prop_solver_per_cl                    1000
% 2.76/0.99  --min_unsat_core                        false
% 2.76/0.99  --soft_assumptions                      false
% 2.76/0.99  --soft_lemma_size                       3
% 2.76/0.99  --prop_impl_unit_size                   0
% 2.76/0.99  --prop_impl_unit                        []
% 2.76/0.99  --share_sel_clauses                     true
% 2.76/0.99  --reset_solvers                         false
% 2.76/0.99  --bc_imp_inh                            [conj_cone]
% 2.76/0.99  --conj_cone_tolerance                   3.
% 2.76/0.99  --extra_neg_conj                        none
% 2.76/0.99  --large_theory_mode                     true
% 2.76/0.99  --prolific_symb_bound                   200
% 2.76/0.99  --lt_threshold                          2000
% 2.76/0.99  --clause_weak_htbl                      true
% 2.76/0.99  --gc_record_bc_elim                     false
% 2.76/0.99  
% 2.76/0.99  ------ Preprocessing Options
% 2.76/0.99  
% 2.76/0.99  --preprocessing_flag                    true
% 2.76/0.99  --time_out_prep_mult                    0.1
% 2.76/0.99  --splitting_mode                        input
% 2.76/0.99  --splitting_grd                         true
% 2.76/0.99  --splitting_cvd                         false
% 2.76/0.99  --splitting_cvd_svl                     false
% 2.76/0.99  --splitting_nvd                         32
% 2.76/0.99  --sub_typing                            true
% 2.76/0.99  --prep_gs_sim                           true
% 2.76/0.99  --prep_unflatten                        true
% 2.76/0.99  --prep_res_sim                          true
% 2.76/0.99  --prep_upred                            true
% 2.76/0.99  --prep_sem_filter                       exhaustive
% 2.76/0.99  --prep_sem_filter_out                   false
% 2.76/0.99  --pred_elim                             true
% 2.76/0.99  --res_sim_input                         true
% 2.76/0.99  --eq_ax_congr_red                       true
% 2.76/0.99  --pure_diseq_elim                       true
% 2.76/0.99  --brand_transform                       false
% 2.76/0.99  --non_eq_to_eq                          false
% 2.76/0.99  --prep_def_merge                        true
% 2.76/0.99  --prep_def_merge_prop_impl              false
% 2.76/0.99  --prep_def_merge_mbd                    true
% 2.76/0.99  --prep_def_merge_tr_red                 false
% 2.76/0.99  --prep_def_merge_tr_cl                  false
% 2.76/0.99  --smt_preprocessing                     true
% 2.76/0.99  --smt_ac_axioms                         fast
% 2.76/0.99  --preprocessed_out                      false
% 2.76/0.99  --preprocessed_stats                    false
% 2.76/0.99  
% 2.76/0.99  ------ Abstraction refinement Options
% 2.76/0.99  
% 2.76/0.99  --abstr_ref                             []
% 2.76/0.99  --abstr_ref_prep                        false
% 2.76/0.99  --abstr_ref_until_sat                   false
% 2.76/0.99  --abstr_ref_sig_restrict                funpre
% 2.76/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.99  --abstr_ref_under                       []
% 2.76/0.99  
% 2.76/0.99  ------ SAT Options
% 2.76/0.99  
% 2.76/0.99  --sat_mode                              false
% 2.76/0.99  --sat_fm_restart_options                ""
% 2.76/0.99  --sat_gr_def                            false
% 2.76/0.99  --sat_epr_types                         true
% 2.76/0.99  --sat_non_cyclic_types                  false
% 2.76/0.99  --sat_finite_models                     false
% 2.76/0.99  --sat_fm_lemmas                         false
% 2.76/0.99  --sat_fm_prep                           false
% 2.76/0.99  --sat_fm_uc_incr                        true
% 2.76/0.99  --sat_out_model                         small
% 2.76/0.99  --sat_out_clauses                       false
% 2.76/0.99  
% 2.76/0.99  ------ QBF Options
% 2.76/0.99  
% 2.76/0.99  --qbf_mode                              false
% 2.76/0.99  --qbf_elim_univ                         false
% 2.76/0.99  --qbf_dom_inst                          none
% 2.76/0.99  --qbf_dom_pre_inst                      false
% 2.76/0.99  --qbf_sk_in                             false
% 2.76/0.99  --qbf_pred_elim                         true
% 2.76/0.99  --qbf_split                             512
% 2.76/0.99  
% 2.76/0.99  ------ BMC1 Options
% 2.76/0.99  
% 2.76/0.99  --bmc1_incremental                      false
% 2.76/0.99  --bmc1_axioms                           reachable_all
% 2.76/0.99  --bmc1_min_bound                        0
% 2.76/0.99  --bmc1_max_bound                        -1
% 2.76/0.99  --bmc1_max_bound_default                -1
% 2.76/0.99  --bmc1_symbol_reachability              true
% 2.76/0.99  --bmc1_property_lemmas                  false
% 2.76/0.99  --bmc1_k_induction                      false
% 2.76/0.99  --bmc1_non_equiv_states                 false
% 2.76/0.99  --bmc1_deadlock                         false
% 2.76/0.99  --bmc1_ucm                              false
% 2.76/0.99  --bmc1_add_unsat_core                   none
% 2.76/0.99  --bmc1_unsat_core_children              false
% 2.76/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.99  --bmc1_out_stat                         full
% 2.76/0.99  --bmc1_ground_init                      false
% 2.76/0.99  --bmc1_pre_inst_next_state              false
% 2.76/0.99  --bmc1_pre_inst_state                   false
% 2.76/0.99  --bmc1_pre_inst_reach_state             false
% 2.76/0.99  --bmc1_out_unsat_core                   false
% 2.76/0.99  --bmc1_aig_witness_out                  false
% 2.76/0.99  --bmc1_verbose                          false
% 2.76/0.99  --bmc1_dump_clauses_tptp                false
% 2.76/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.99  --bmc1_dump_file                        -
% 2.76/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.99  --bmc1_ucm_extend_mode                  1
% 2.76/0.99  --bmc1_ucm_init_mode                    2
% 2.76/0.99  --bmc1_ucm_cone_mode                    none
% 2.76/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.99  --bmc1_ucm_relax_model                  4
% 2.76/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.99  --bmc1_ucm_layered_model                none
% 2.76/0.99  --bmc1_ucm_max_lemma_size               10
% 2.76/0.99  
% 2.76/0.99  ------ AIG Options
% 2.76/0.99  
% 2.76/0.99  --aig_mode                              false
% 2.76/0.99  
% 2.76/0.99  ------ Instantiation Options
% 2.76/0.99  
% 2.76/0.99  --instantiation_flag                    true
% 2.76/0.99  --inst_sos_flag                         false
% 2.76/0.99  --inst_sos_phase                        true
% 2.76/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.99  --inst_lit_sel_side                     none
% 2.76/0.99  --inst_solver_per_active                1400
% 2.76/0.99  --inst_solver_calls_frac                1.
% 2.76/0.99  --inst_passive_queue_type               priority_queues
% 2.76/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.99  --inst_passive_queues_freq              [25;2]
% 2.76/0.99  --inst_dismatching                      true
% 2.76/0.99  --inst_eager_unprocessed_to_passive     true
% 2.76/0.99  --inst_prop_sim_given                   true
% 2.76/0.99  --inst_prop_sim_new                     false
% 2.76/0.99  --inst_subs_new                         false
% 2.76/0.99  --inst_eq_res_simp                      false
% 2.76/0.99  --inst_subs_given                       false
% 2.76/0.99  --inst_orphan_elimination               true
% 2.76/0.99  --inst_learning_loop_flag               true
% 2.76/0.99  --inst_learning_start                   3000
% 2.76/0.99  --inst_learning_factor                  2
% 2.76/0.99  --inst_start_prop_sim_after_learn       3
% 2.76/0.99  --inst_sel_renew                        solver
% 2.76/0.99  --inst_lit_activity_flag                true
% 2.76/0.99  --inst_restr_to_given                   false
% 2.76/0.99  --inst_activity_threshold               500
% 2.76/0.99  --inst_out_proof                        true
% 2.76/0.99  
% 2.76/0.99  ------ Resolution Options
% 2.76/0.99  
% 2.76/0.99  --resolution_flag                       false
% 2.76/0.99  --res_lit_sel                           adaptive
% 2.76/0.99  --res_lit_sel_side                      none
% 2.76/0.99  --res_ordering                          kbo
% 2.76/0.99  --res_to_prop_solver                    active
% 2.76/0.99  --res_prop_simpl_new                    false
% 2.76/0.99  --res_prop_simpl_given                  true
% 2.76/0.99  --res_passive_queue_type                priority_queues
% 2.76/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.99  --res_passive_queues_freq               [15;5]
% 2.76/0.99  --res_forward_subs                      full
% 2.76/0.99  --res_backward_subs                     full
% 2.76/0.99  --res_forward_subs_resolution           true
% 2.76/0.99  --res_backward_subs_resolution          true
% 2.76/0.99  --res_orphan_elimination                true
% 2.76/0.99  --res_time_limit                        2.
% 2.76/0.99  --res_out_proof                         true
% 2.76/0.99  
% 2.76/0.99  ------ Superposition Options
% 2.76/0.99  
% 2.76/0.99  --superposition_flag                    true
% 2.76/0.99  --sup_passive_queue_type                priority_queues
% 2.76/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.99  --demod_completeness_check              fast
% 2.76/0.99  --demod_use_ground                      true
% 2.76/0.99  --sup_to_prop_solver                    passive
% 2.76/0.99  --sup_prop_simpl_new                    true
% 2.76/0.99  --sup_prop_simpl_given                  true
% 2.76/0.99  --sup_fun_splitting                     false
% 2.76/0.99  --sup_smt_interval                      50000
% 2.76/0.99  
% 2.76/0.99  ------ Superposition Simplification Setup
% 2.76/0.99  
% 2.76/0.99  --sup_indices_passive                   []
% 2.76/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.99  --sup_full_bw                           [BwDemod]
% 2.76/0.99  --sup_immed_triv                        [TrivRules]
% 2.76/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.99  --sup_immed_bw_main                     []
% 2.76/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.99  
% 2.76/0.99  ------ Combination Options
% 2.76/0.99  
% 2.76/0.99  --comb_res_mult                         3
% 2.76/0.99  --comb_sup_mult                         2
% 2.76/0.99  --comb_inst_mult                        10
% 2.76/0.99  
% 2.76/0.99  ------ Debug Options
% 2.76/0.99  
% 2.76/0.99  --dbg_backtrace                         false
% 2.76/0.99  --dbg_dump_prop_clauses                 false
% 2.76/0.99  --dbg_dump_prop_clauses_file            -
% 2.76/0.99  --dbg_out_stat                          false
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  ------ Proving...
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  % SZS status Theorem for theBenchmark.p
% 2.76/0.99  
% 2.76/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/0.99  
% 2.76/0.99  fof(f15,conjecture,(
% 2.76/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f16,negated_conjecture,(
% 2.76/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.76/0.99    inference(negated_conjecture,[],[f15])).
% 2.76/0.99  
% 2.76/0.99  fof(f37,plain,(
% 2.76/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.76/0.99    inference(ennf_transformation,[],[f16])).
% 2.76/0.99  
% 2.76/0.99  fof(f38,plain,(
% 2.76/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.76/0.99    inference(flattening,[],[f37])).
% 2.76/0.99  
% 2.76/0.99  fof(f42,plain,(
% 2.76/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 2.76/0.99    introduced(choice_axiom,[])).
% 2.76/0.99  
% 2.76/0.99  fof(f43,plain,(
% 2.76/0.99    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 2.76/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f42])).
% 2.76/0.99  
% 2.76/0.99  fof(f68,plain,(
% 2.76/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 2.76/0.99    inference(cnf_transformation,[],[f43])).
% 2.76/0.99  
% 2.76/0.99  fof(f14,axiom,(
% 2.76/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f35,plain,(
% 2.76/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.76/0.99    inference(ennf_transformation,[],[f14])).
% 2.76/0.99  
% 2.76/0.99  fof(f36,plain,(
% 2.76/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.76/0.99    inference(flattening,[],[f35])).
% 2.76/0.99  
% 2.76/0.99  fof(f64,plain,(
% 2.76/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f36])).
% 2.76/0.99  
% 2.76/0.99  fof(f5,axiom,(
% 2.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f22,plain,(
% 2.76/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.99    inference(ennf_transformation,[],[f5])).
% 2.76/0.99  
% 2.76/0.99  fof(f49,plain,(
% 2.76/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.99    inference(cnf_transformation,[],[f22])).
% 2.76/0.99  
% 2.76/0.99  fof(f65,plain,(
% 2.76/0.99    v1_funct_1(sK2)),
% 2.76/0.99    inference(cnf_transformation,[],[f43])).
% 2.76/0.99  
% 2.76/0.99  fof(f66,plain,(
% 2.76/0.99    v1_funct_2(sK2,sK1,sK1)),
% 2.76/0.99    inference(cnf_transformation,[],[f43])).
% 2.76/0.99  
% 2.76/0.99  fof(f3,axiom,(
% 2.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f20,plain,(
% 2.76/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.99    inference(ennf_transformation,[],[f3])).
% 2.76/0.99  
% 2.76/0.99  fof(f47,plain,(
% 2.76/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.99    inference(cnf_transformation,[],[f20])).
% 2.76/0.99  
% 2.76/0.99  fof(f2,axiom,(
% 2.76/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f18,plain,(
% 2.76/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.76/0.99    inference(ennf_transformation,[],[f2])).
% 2.76/0.99  
% 2.76/0.99  fof(f19,plain,(
% 2.76/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.76/0.99    inference(flattening,[],[f18])).
% 2.76/0.99  
% 2.76/0.99  fof(f45,plain,(
% 2.76/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f19])).
% 2.76/0.99  
% 2.76/0.99  fof(f13,axiom,(
% 2.76/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f63,plain,(
% 2.76/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f13])).
% 2.76/0.99  
% 2.76/0.99  fof(f71,plain,(
% 2.76/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.99    inference(definition_unfolding,[],[f45,f63])).
% 2.76/0.99  
% 2.76/0.99  fof(f67,plain,(
% 2.76/0.99    v3_funct_2(sK2,sK1,sK1)),
% 2.76/0.99    inference(cnf_transformation,[],[f43])).
% 2.76/0.99  
% 2.76/0.99  fof(f8,axiom,(
% 2.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f25,plain,(
% 2.76/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.99    inference(ennf_transformation,[],[f8])).
% 2.76/0.99  
% 2.76/0.99  fof(f26,plain,(
% 2.76/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.99    inference(flattening,[],[f25])).
% 2.76/0.99  
% 2.76/0.99  fof(f53,plain,(
% 2.76/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.99    inference(cnf_transformation,[],[f26])).
% 2.76/0.99  
% 2.76/0.99  fof(f12,axiom,(
% 2.76/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f33,plain,(
% 2.76/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.76/0.99    inference(ennf_transformation,[],[f12])).
% 2.76/0.99  
% 2.76/0.99  fof(f34,plain,(
% 2.76/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.76/0.99    inference(flattening,[],[f33])).
% 2.76/0.99  
% 2.76/0.99  fof(f62,plain,(
% 2.76/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f34])).
% 2.76/0.99  
% 2.76/0.99  fof(f10,axiom,(
% 2.76/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f29,plain,(
% 2.76/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.76/0.99    inference(ennf_transformation,[],[f10])).
% 2.76/0.99  
% 2.76/0.99  fof(f30,plain,(
% 2.76/0.99    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.76/0.99    inference(flattening,[],[f29])).
% 2.76/0.99  
% 2.76/0.99  fof(f60,plain,(
% 2.76/0.99    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f30])).
% 2.76/0.99  
% 2.76/0.99  fof(f11,axiom,(
% 2.76/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f31,plain,(
% 2.76/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.76/0.99    inference(ennf_transformation,[],[f11])).
% 2.76/0.99  
% 2.76/0.99  fof(f32,plain,(
% 2.76/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.76/0.99    inference(flattening,[],[f31])).
% 2.76/0.99  
% 2.76/0.99  fof(f61,plain,(
% 2.76/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f32])).
% 2.76/0.99  
% 2.76/0.99  fof(f57,plain,(
% 2.76/0.99    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f30])).
% 2.76/0.99  
% 2.76/0.99  fof(f69,plain,(
% 2.76/0.99    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 2.76/0.99    inference(cnf_transformation,[],[f43])).
% 2.76/0.99  
% 2.76/0.99  fof(f7,axiom,(
% 2.76/0.99    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f51,plain,(
% 2.76/0.99    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.76/0.99    inference(cnf_transformation,[],[f7])).
% 2.76/0.99  
% 2.76/0.99  fof(f72,plain,(
% 2.76/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.76/0.99    inference(definition_unfolding,[],[f51,f63])).
% 2.76/0.99  
% 2.76/0.99  fof(f6,axiom,(
% 2.76/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f23,plain,(
% 2.76/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.76/0.99    inference(ennf_transformation,[],[f6])).
% 2.76/0.99  
% 2.76/0.99  fof(f24,plain,(
% 2.76/0.99    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.99    inference(flattening,[],[f23])).
% 2.76/0.99  
% 2.76/0.99  fof(f50,plain,(
% 2.76/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.99    inference(cnf_transformation,[],[f24])).
% 2.76/0.99  
% 2.76/0.99  fof(f54,plain,(
% 2.76/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.99    inference(cnf_transformation,[],[f26])).
% 2.76/0.99  
% 2.76/0.99  fof(f4,axiom,(
% 2.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f17,plain,(
% 2.76/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.76/0.99    inference(pure_predicate_removal,[],[f4])).
% 2.76/0.99  
% 2.76/0.99  fof(f21,plain,(
% 2.76/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.76/0.99    inference(ennf_transformation,[],[f17])).
% 2.76/0.99  
% 2.76/0.99  fof(f48,plain,(
% 2.76/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.76/0.99    inference(cnf_transformation,[],[f21])).
% 2.76/0.99  
% 2.76/0.99  fof(f9,axiom,(
% 2.76/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.76/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.76/0.99  
% 2.76/0.99  fof(f27,plain,(
% 2.76/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.76/0.99    inference(ennf_transformation,[],[f9])).
% 2.76/0.99  
% 2.76/0.99  fof(f28,plain,(
% 2.76/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/0.99    inference(flattening,[],[f27])).
% 2.76/0.99  
% 2.76/0.99  fof(f41,plain,(
% 2.76/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.76/0.99    inference(nnf_transformation,[],[f28])).
% 2.76/0.99  
% 2.76/0.99  fof(f55,plain,(
% 2.76/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f41])).
% 2.76/0.99  
% 2.76/0.99  fof(f46,plain,(
% 2.76/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.99    inference(cnf_transformation,[],[f19])).
% 2.76/0.99  
% 2.76/0.99  fof(f70,plain,(
% 2.76/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.76/0.99    inference(definition_unfolding,[],[f46,f63])).
% 2.76/0.99  
% 2.76/0.99  cnf(c_699,plain,
% 2.76/0.99      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 2.76/0.99      theory(equality) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1427,plain,
% 2.76/0.99      ( X0_50 != X1_50
% 2.76/0.99      | X0_50 = k6_partfun1(X0_51)
% 2.76/0.99      | k6_partfun1(X0_51) != X1_50 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_699]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3157,plain,
% 2.76/0.99      ( X0_50 != k5_relat_1(k2_funct_1(X1_50),X1_50)
% 2.76/0.99      | X0_50 = k6_partfun1(sK1)
% 2.76/0.99      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(X1_50),X1_50) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1427]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_4798,plain,
% 2.76/0.99      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 2.76/0.99      | k1_partfun1(X0_51,X1_51,X2_51,X3_51,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.76/0.99      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_3157]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_4802,plain,
% 2.76/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k5_relat_1(k2_funct_1(sK2),sK2)
% 2.76/0.99      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 2.76/0.99      | k6_partfun1(sK1) != k5_relat_1(k2_funct_1(sK2),sK2) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_4798]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_707,plain,
% 2.76/0.99      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 2.76/0.99      | r2_relset_1(X2_51,X3_51,X2_50,X3_50)
% 2.76/0.99      | X2_51 != X0_51
% 2.76/0.99      | X3_51 != X1_51
% 2.76/0.99      | X2_50 != X0_50
% 2.76/0.99      | X3_50 != X1_50 ),
% 2.76/0.99      theory(equality) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2213,plain,
% 2.76/0.99      ( ~ r2_relset_1(X0_51,X1_51,X0_50,X1_50)
% 2.76/0.99      | r2_relset_1(X2_51,X3_51,k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50),k6_partfun1(X8_51))
% 2.76/0.99      | X2_51 != X0_51
% 2.76/0.99      | X3_51 != X1_51
% 2.76/0.99      | k1_partfun1(X4_51,X5_51,X6_51,X7_51,k2_funct_1(sK2),X2_50) != X0_50
% 2.76/0.99      | k6_partfun1(X8_51) != X1_50 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_707]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3377,plain,
% 2.76/0.99      ( ~ r2_relset_1(X0_51,X1_51,X0_50,k6_partfun1(X2_51))
% 2.76/0.99      | r2_relset_1(X3_51,X4_51,k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50),k6_partfun1(X9_51))
% 2.76/0.99      | X3_51 != X0_51
% 2.76/0.99      | X4_51 != X1_51
% 2.76/0.99      | k1_partfun1(X5_51,X6_51,X7_51,X8_51,k2_funct_1(sK2),X1_50) != X0_50
% 2.76/0.99      | k6_partfun1(X9_51) != k6_partfun1(X2_51) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2213]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_4632,plain,
% 2.76/0.99      ( r2_relset_1(X0_51,X1_51,k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50),k6_partfun1(X6_51))
% 2.76/0.99      | ~ r2_relset_1(X7_51,X8_51,k6_partfun1(X9_51),k6_partfun1(X9_51))
% 2.76/0.99      | X0_51 != X7_51
% 2.76/0.99      | X1_51 != X8_51
% 2.76/0.99      | k1_partfun1(X2_51,X3_51,X4_51,X5_51,k2_funct_1(sK2),X0_50) != k6_partfun1(X9_51)
% 2.76/0.99      | k6_partfun1(X6_51) != k6_partfun1(X9_51) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_3377]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_4635,plain,
% 2.76/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1))
% 2.76/0.99      | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 2.76/0.99      | sK1 != sK1
% 2.76/0.99      | k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 2.76/0.99      | k6_partfun1(sK1) != k6_partfun1(sK1) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_4632]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_21,negated_conjecture,
% 2.76/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.76/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_677,negated_conjecture,
% 2.76/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1139,plain,
% 2.76/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_677]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_19,plain,
% 2.76/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.76/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_679,plain,
% 2.76/0.99      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.76/0.99      | ~ v1_funct_1(X0_50)
% 2.76/0.99      | k1_relset_1(X0_51,X0_51,X0_50) = X0_51 ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1137,plain,
% 2.76/0.99      ( k1_relset_1(X0_51,X0_51,X0_50) = X0_51
% 2.76/0.99      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2225,plain,
% 2.76/0.99      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 2.76/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1139,c_1137]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_5,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_689,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.76/0.99      | k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1127,plain,
% 2.76/0.99      ( k1_relset_1(X0_51,X1_51,X0_50) = k1_relat_1(X0_50)
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1461,plain,
% 2.76/0.99      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1139,c_1127]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2258,plain,
% 2.76/0.99      ( k1_relat_1(sK2) = sK1
% 2.76/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(demodulation,[status(thm)],[c_2225,c_1461]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_24,negated_conjecture,
% 2.76/0.99      ( v1_funct_1(sK2) ),
% 2.76/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_25,plain,
% 2.76/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_23,negated_conjecture,
% 2.76/0.99      ( v1_funct_2(sK2,sK1,sK1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_26,plain,
% 2.76/0.99      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2773,plain,
% 2.76/0.99      ( k1_relat_1(sK2) = sK1 ),
% 2.76/0.99      inference(global_propositional_subsumption,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_2258,c_25,c_26]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.99      | v1_relat_1(X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_690,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.76/0.99      | v1_relat_1(X0_50) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1126,plain,
% 2.76/0.99      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.76/0.99      | v1_relat_1(X0_50) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1377,plain,
% 2.76/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1139,c_1126]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2,plain,
% 2.76/0.99      ( ~ v1_relat_1(X0)
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | ~ v2_funct_1(X0)
% 2.76/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.76/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_691,plain,
% 2.76/0.99      ( ~ v1_relat_1(X0_50)
% 2.76/0.99      | ~ v1_funct_1(X0_50)
% 2.76/0.99      | ~ v2_funct_1(X0_50)
% 2.76/0.99      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1125,plain,
% 2.76/0.99      ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
% 2.76/0.99      | v1_relat_1(X0_50) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.76/0.99      | v2_funct_1(X0_50) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1676,plain,
% 2.76/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top
% 2.76/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1377,c_1125]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_22,negated_conjecture,
% 2.76/0.99      ( v3_funct_2(sK2,sK1,sK1) ),
% 2.76/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_735,plain,
% 2.76/0.99      ( ~ v1_relat_1(sK2)
% 2.76/0.99      | ~ v1_funct_1(sK2)
% 2.76/0.99      | ~ v2_funct_1(sK2)
% 2.76/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_691]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_738,plain,
% 2.76/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.76/0.99      | v1_relat_1(sK2) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_690]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_9,plain,
% 2.76/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | v2_funct_1(X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_686,plain,
% 2.76/0.99      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.76/0.99      | ~ v1_funct_1(X0_50)
% 2.76/0.99      | v2_funct_1(X0_50) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_748,plain,
% 2.76/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.76/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.76/0.99      | ~ v1_funct_1(sK2)
% 2.76/0.99      | v2_funct_1(sK2) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_686]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1834,plain,
% 2.76/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 2.76/0.99      inference(global_propositional_subsumption,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_1676,c_24,c_22,c_21,c_735,c_738,c_748]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2776,plain,
% 2.76/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 2.76/0.99      inference(demodulation,[status(thm)],[c_2773,c_1834]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_18,plain,
% 2.76/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.76/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_680,plain,
% 2.76/0.99      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.76/0.99      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.76/0.99      | ~ v1_funct_1(X0_50)
% 2.76/0.99      | k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1136,plain,
% 2.76/0.99      ( k2_funct_2(X0_51,X0_50) = k2_funct_1(X0_50)
% 2.76/0.99      | v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2413,plain,
% 2.76/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 2.76/0.99      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1139,c_1136]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_766,plain,
% 2.76/0.99      ( ~ v1_funct_2(sK2,sK1,sK1)
% 2.76/0.99      | ~ v3_funct_2(sK2,sK1,sK1)
% 2.76/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.76/0.99      | ~ v1_funct_1(sK2)
% 2.76/0.99      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_680]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2599,plain,
% 2.76/0.99      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 2.76/0.99      inference(global_propositional_subsumption,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_2413,c_24,c_23,c_22,c_21,c_766]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_13,plain,
% 2.76/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.76/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.76/0.99      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.76/0.99      | ~ v1_funct_1(X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_685,plain,
% 2.76/0.99      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.76/0.99      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.76/0.99      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.76/0.99      | ~ v1_funct_1(X0_50) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1131,plain,
% 2.76/0.99      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.76/0.99      | m1_subset_1(k2_funct_2(X0_51,X0_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2612,plain,
% 2.76/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 2.76/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_2599,c_1131]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_27,plain,
% 2.76/0.99      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_28,plain,
% 2.76/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2851,plain,
% 2.76/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 2.76/0.99      inference(global_propositional_subsumption,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_2612,c_25,c_26,c_27,c_28]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_17,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | ~ v1_funct_1(X3)
% 2.76/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_681,plain,
% 2.76/0.99      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.76/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 2.76/0.99      | ~ v1_funct_1(X0_50)
% 2.76/0.99      | ~ v1_funct_1(X1_50)
% 2.76/0.99      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1135,plain,
% 2.76/0.99      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 2.76/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.76/0.99      | v1_funct_1(X1_50) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3075,plain,
% 2.76/0.99      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1139,c_1135]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3322,plain,
% 2.76/0.99      ( v1_funct_1(X0_50) != iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.76/0.99      | k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50) ),
% 2.76/0.99      inference(global_propositional_subsumption,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_3075,c_25]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3323,plain,
% 2.76/0.99      ( k1_partfun1(sK1,sK1,X0_51,X1_51,sK2,X0_50) = k5_relat_1(sK2,X0_50)
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top ),
% 2.76/0.99      inference(renaming,[status(thm)],[c_3322]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3333,plain,
% 2.76/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 2.76/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_2851,c_3323]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_16,plain,
% 2.76/0.99      ( ~ v1_funct_2(X0,X1,X1)
% 2.76/0.99      | ~ v3_funct_2(X0,X1,X1)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 2.76/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_682,plain,
% 2.76/0.99      ( ~ v1_funct_2(X0_50,X0_51,X0_51)
% 2.76/0.99      | ~ v3_funct_2(X0_50,X0_51,X0_51)
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51)))
% 2.76/0.99      | ~ v1_funct_1(X0_50)
% 2.76/0.99      | v1_funct_1(k2_funct_2(X0_51,X0_50)) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1134,plain,
% 2.76/0.99      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.76/0.99      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2278,plain,
% 2.76/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1139,c_1134]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_759,plain,
% 2.76/0.99      ( v1_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | v3_funct_2(X0_50,X0_51,X0_51) != iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.76/0.99      | v1_funct_1(k2_funct_2(X0_51,X0_50)) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_761,plain,
% 2.76/0.99      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 2.76/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.76/0.99      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_759]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2593,plain,
% 2.76/0.99      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 2.76/0.99      inference(global_propositional_subsumption,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_2278,c_25,c_26,c_27,c_28,c_761]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2602,plain,
% 2.76/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.76/0.99      inference(demodulation,[status(thm)],[c_2599,c_2593]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3574,plain,
% 2.76/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 2.76/0.99      inference(global_propositional_subsumption,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_3333,c_2602]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_20,negated_conjecture,
% 2.76/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.76/0.99      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.76/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_678,negated_conjecture,
% 2.76/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 2.76/0.99      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_20]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1138,plain,
% 2.76/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.76/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2603,plain,
% 2.76/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.76/0.99      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.76/0.99      inference(demodulation,[status(thm)],[c_2599,c_1138]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3577,plain,
% 2.76/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.76/0.99      | r2_relset_1(sK1,sK1,k5_relat_1(sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 2.76/0.99      inference(demodulation,[status(thm)],[c_3574,c_2603]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_4483,plain,
% 2.76/0.99      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 2.76/0.99      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 2.76/0.99      inference(demodulation,[status(thm)],[c_2776,c_3577]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_4491,plain,
% 2.76/0.99      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1))
% 2.76/0.99      | ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) ),
% 2.76/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4483]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3079,plain,
% 2.76/0.99      ( k1_partfun1(sK1,sK1,X0_51,X1_51,k2_funct_1(sK2),X0_50) = k5_relat_1(k2_funct_1(sK2),X0_50)
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.76/0.99      | v1_funct_1(X0_50) != iProver_top
% 2.76/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_2851,c_1135]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_3139,plain,
% 2.76/0.99      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.76/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 2.76/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.76/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_3079]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_700,plain,
% 2.76/0.99      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 2.76/0.99      theory(equality) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2037,plain,
% 2.76/0.99      ( k2_relat_1(X0_50) != X0_51
% 2.76/0.99      | sK1 != X0_51
% 2.76/0.99      | sK1 = k2_relat_1(X0_50) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_700]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_2038,plain,
% 2.76/0.99      ( k2_relat_1(sK2) != sK1 | sK1 = k2_relat_1(sK2) | sK1 != sK1 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_2037]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_703,plain,
% 2.76/0.99      ( X0_51 != X1_51 | k6_partfun1(X0_51) = k6_partfun1(X1_51) ),
% 2.76/0.99      theory(equality) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1401,plain,
% 2.76/0.99      ( sK1 != X0_51 | k6_partfun1(sK1) = k6_partfun1(X0_51) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_703]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1937,plain,
% 2.76/0.99      ( sK1 != k2_relat_1(X0_50)
% 2.76/0.99      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1401]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1938,plain,
% 2.76/0.99      ( sK1 != k2_relat_1(sK2)
% 2.76/0.99      | k6_partfun1(sK1) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1937]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1399,plain,
% 2.76/0.99      ( X0_50 != X1_50
% 2.76/0.99      | k6_partfun1(sK1) != X1_50
% 2.76/0.99      | k6_partfun1(sK1) = X0_50 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_699]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1484,plain,
% 2.76/0.99      ( X0_50 != k6_partfun1(X0_51)
% 2.76/0.99      | k6_partfun1(sK1) = X0_50
% 2.76/0.99      | k6_partfun1(sK1) != k6_partfun1(X0_51) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1399]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1576,plain,
% 2.76/0.99      ( k5_relat_1(k2_funct_1(X0_50),X0_50) != k6_partfun1(k2_relat_1(X0_50))
% 2.76/0.99      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(X0_50),X0_50)
% 2.76/0.99      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(X0_50)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1484]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1577,plain,
% 2.76/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(k2_relat_1(sK2))
% 2.76/0.99      | k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)
% 2.76/0.99      | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1576]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_7,plain,
% 2.76/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.76/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_687,plain,
% 2.76/0.99      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1129,plain,
% 2.76/0.99      ( m1_subset_1(k6_partfun1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) = iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_6,plain,
% 2.76/0.99      ( r2_relset_1(X0,X1,X2,X2)
% 2.76/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.76/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.76/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_688,plain,
% 2.76/0.99      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50)
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.76/0.99      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1128,plain,
% 2.76/0.99      ( r2_relset_1(X0_51,X1_51,X0_50,X0_50) = iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 2.76/0.99      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 2.76/0.99      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1546,plain,
% 2.76/0.99      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51)) = iProver_top
% 2.76/0.99      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) != iProver_top ),
% 2.76/0.99      inference(superposition,[status(thm)],[c_1129,c_1128]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1561,plain,
% 2.76/0.99      ( r2_relset_1(X0_51,X0_51,k6_partfun1(X0_51),k6_partfun1(X0_51))
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X0_51))) ),
% 2.76/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1546]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1563,plain,
% 2.76/0.99      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 2.76/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_1561]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_8,plain,
% 2.76/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.76/0.99      | v2_funct_2(X0,X2)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.99      | ~ v1_funct_1(X0) ),
% 2.76/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_4,plain,
% 2.76/0.99      ( v5_relat_1(X0,X1)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.76/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_12,plain,
% 2.76/0.99      ( ~ v2_funct_2(X0,X1)
% 2.76/0.99      | ~ v5_relat_1(X0,X1)
% 2.76/0.99      | ~ v1_relat_1(X0)
% 2.76/0.99      | k2_relat_1(X0) = X1 ),
% 2.76/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_278,plain,
% 2.76/0.99      ( ~ v2_funct_2(X0,X1)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.76/0.99      | ~ v1_relat_1(X0)
% 2.76/0.99      | k2_relat_1(X0) = X1 ),
% 2.76/0.99      inference(resolution,[status(thm)],[c_4,c_12]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_290,plain,
% 2.76/0.99      ( ~ v2_funct_2(X0,X1)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.76/0.99      | k2_relat_1(X0) = X1 ),
% 2.76/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_278,c_3]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_363,plain,
% 2.76/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | X3 != X0
% 2.76/0.99      | X5 != X2
% 2.76/0.99      | k2_relat_1(X3) = X5 ),
% 2.76/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_290]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_364,plain,
% 2.76/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | k2_relat_1(X0) = X2 ),
% 2.76/0.99      inference(unflattening,[status(thm)],[c_363]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_673,plain,
% 2.76/0.99      ( ~ v3_funct_2(X0_50,X0_51,X1_51)
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 2.76/0.99      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 2.76/0.99      | ~ v1_funct_1(X0_50)
% 2.76/0.99      | k2_relat_1(X0_50) = X1_51 ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_364]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_777,plain,
% 2.76/0.99      ( ~ v3_funct_2(sK2,sK1,sK1)
% 2.76/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 2.76/0.99      | ~ v1_funct_1(sK2)
% 2.76/0.99      | k2_relat_1(sK2) = sK1 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_673]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_1,plain,
% 2.76/0.99      ( ~ v1_relat_1(X0)
% 2.76/0.99      | ~ v1_funct_1(X0)
% 2.76/0.99      | ~ v2_funct_1(X0)
% 2.76/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.76/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_692,plain,
% 2.76/0.99      ( ~ v1_relat_1(X0_50)
% 2.76/0.99      | ~ v1_funct_1(X0_50)
% 2.76/0.99      | ~ v2_funct_1(X0_50)
% 2.76/0.99      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(k2_relat_1(X0_50)) ),
% 2.76/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_732,plain,
% 2.76/0.99      ( ~ v1_relat_1(sK2)
% 2.76/0.99      | ~ v1_funct_1(sK2)
% 2.76/0.99      | ~ v2_funct_1(sK2)
% 2.76/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_692]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_696,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_725,plain,
% 2.76/0.99      ( sK1 = sK1 ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_696]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(c_714,plain,
% 2.76/0.99      ( sK1 != sK1 | k6_partfun1(sK1) = k6_partfun1(sK1) ),
% 2.76/0.99      inference(instantiation,[status(thm)],[c_703]) ).
% 2.76/0.99  
% 2.76/0.99  cnf(contradiction,plain,
% 2.76/0.99      ( $false ),
% 2.76/0.99      inference(minisat,
% 2.76/0.99                [status(thm)],
% 2.76/0.99                [c_4802,c_4635,c_4491,c_3139,c_2602,c_2038,c_1938,c_1577,
% 2.76/0.99                 c_1563,c_777,c_748,c_738,c_732,c_725,c_714,c_28,c_21,
% 2.76/0.99                 c_22,c_25,c_24]) ).
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/0.99  
% 2.76/0.99  ------                               Statistics
% 2.76/0.99  
% 2.76/0.99  ------ General
% 2.76/0.99  
% 2.76/0.99  abstr_ref_over_cycles:                  0
% 2.76/0.99  abstr_ref_under_cycles:                 0
% 2.76/0.99  gc_basic_clause_elim:                   0
% 2.76/0.99  forced_gc_time:                         0
% 2.76/0.99  parsing_time:                           0.01
% 2.76/0.99  unif_index_cands_time:                  0.
% 2.76/0.99  unif_index_add_time:                    0.
% 2.76/0.99  orderings_time:                         0.
% 2.76/0.99  out_proof_time:                         0.011
% 2.76/0.99  total_time:                             0.195
% 2.76/0.99  num_of_symbols:                         57
% 2.76/0.99  num_of_terms:                           4343
% 2.76/0.99  
% 2.76/0.99  ------ Preprocessing
% 2.76/0.99  
% 2.76/0.99  num_of_splits:                          0
% 2.76/0.99  num_of_split_atoms:                     0
% 2.76/0.99  num_of_reused_defs:                     0
% 2.76/0.99  num_eq_ax_congr_red:                    29
% 2.76/0.99  num_of_sem_filtered_clauses:            1
% 2.76/0.99  num_of_subtypes:                        4
% 2.76/0.99  monotx_restored_types:                  1
% 2.76/0.99  sat_num_of_epr_types:                   0
% 2.76/0.99  sat_num_of_non_cyclic_types:            0
% 2.76/0.99  sat_guarded_non_collapsed_types:        0
% 2.76/0.99  num_pure_diseq_elim:                    0
% 2.76/0.99  simp_replaced_by:                       0
% 2.76/0.99  res_preprocessed:                       122
% 2.76/0.99  prep_upred:                             0
% 2.76/0.99  prep_unflattend:                        6
% 2.76/0.99  smt_new_axioms:                         0
% 2.76/0.99  pred_elim_cands:                        7
% 2.76/0.99  pred_elim:                              2
% 2.76/0.99  pred_elim_cl:                           3
% 2.76/0.99  pred_elim_cycles:                       6
% 2.76/0.99  merged_defs:                            0
% 2.76/0.99  merged_defs_ncl:                        0
% 2.76/0.99  bin_hyper_res:                          0
% 2.76/0.99  prep_cycles:                            4
% 2.76/0.99  pred_elim_time:                         0.005
% 2.76/0.99  splitting_time:                         0.
% 2.76/0.99  sem_filter_time:                        0.
% 2.76/0.99  monotx_time:                            0.001
% 2.76/0.99  subtype_inf_time:                       0.002
% 2.76/0.99  
% 2.76/0.99  ------ Problem properties
% 2.76/0.99  
% 2.76/0.99  clauses:                                21
% 2.76/0.99  conjectures:                            5
% 2.76/0.99  epr:                                    3
% 2.76/0.99  horn:                                   21
% 2.76/0.99  ground:                                 5
% 2.76/0.99  unary:                                  6
% 2.76/0.99  binary:                                 3
% 2.76/0.99  lits:                                   66
% 2.76/0.99  lits_eq:                                7
% 2.76/0.99  fd_pure:                                0
% 2.76/0.99  fd_pseudo:                              0
% 2.76/0.99  fd_cond:                                0
% 2.76/0.99  fd_pseudo_cond:                         1
% 2.76/0.99  ac_symbols:                             0
% 2.76/0.99  
% 2.76/0.99  ------ Propositional Solver
% 2.76/0.99  
% 2.76/0.99  prop_solver_calls:                      28
% 2.76/0.99  prop_fast_solver_calls:                 1007
% 2.76/0.99  smt_solver_calls:                       0
% 2.76/0.99  smt_fast_solver_calls:                  0
% 2.76/0.99  prop_num_of_clauses:                    1393
% 2.76/0.99  prop_preprocess_simplified:             5188
% 2.76/0.99  prop_fo_subsumed:                       46
% 2.76/0.99  prop_solver_time:                       0.
% 2.76/0.99  smt_solver_time:                        0.
% 2.76/0.99  smt_fast_solver_time:                   0.
% 2.76/0.99  prop_fast_solver_time:                  0.
% 2.76/0.99  prop_unsat_core_time:                   0.
% 2.76/0.99  
% 2.76/0.99  ------ QBF
% 2.76/0.99  
% 2.76/0.99  qbf_q_res:                              0
% 2.76/0.99  qbf_num_tautologies:                    0
% 2.76/0.99  qbf_prep_cycles:                        0
% 2.76/0.99  
% 2.76/0.99  ------ BMC1
% 2.76/0.99  
% 2.76/0.99  bmc1_current_bound:                     -1
% 2.76/0.99  bmc1_last_solved_bound:                 -1
% 2.76/0.99  bmc1_unsat_core_size:                   -1
% 2.76/0.99  bmc1_unsat_core_parents_size:           -1
% 2.76/0.99  bmc1_merge_next_fun:                    0
% 2.76/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.76/0.99  
% 2.76/0.99  ------ Instantiation
% 2.76/0.99  
% 2.76/0.99  inst_num_of_clauses:                    460
% 2.76/0.99  inst_num_in_passive:                    30
% 2.76/0.99  inst_num_in_active:                     290
% 2.76/0.99  inst_num_in_unprocessed:                139
% 2.76/0.99  inst_num_of_loops:                      309
% 2.76/0.99  inst_num_of_learning_restarts:          0
% 2.76/0.99  inst_num_moves_active_passive:          14
% 2.76/0.99  inst_lit_activity:                      0
% 2.76/0.99  inst_lit_activity_moves:                0
% 2.76/0.99  inst_num_tautologies:                   0
% 2.76/0.99  inst_num_prop_implied:                  0
% 2.76/0.99  inst_num_existing_simplified:           0
% 2.76/0.99  inst_num_eq_res_simplified:             0
% 2.76/0.99  inst_num_child_elim:                    0
% 2.76/0.99  inst_num_of_dismatching_blockings:      447
% 2.76/0.99  inst_num_of_non_proper_insts:           633
% 2.76/0.99  inst_num_of_duplicates:                 0
% 2.76/0.99  inst_inst_num_from_inst_to_res:         0
% 2.76/0.99  inst_dismatching_checking_time:         0.
% 2.76/0.99  
% 2.76/0.99  ------ Resolution
% 2.76/0.99  
% 2.76/0.99  res_num_of_clauses:                     0
% 2.76/0.99  res_num_in_passive:                     0
% 2.76/0.99  res_num_in_active:                      0
% 2.76/0.99  res_num_of_loops:                       126
% 2.76/0.99  res_forward_subset_subsumed:            111
% 2.76/0.99  res_backward_subset_subsumed:           4
% 2.76/0.99  res_forward_subsumed:                   0
% 2.76/0.99  res_backward_subsumed:                  0
% 2.76/0.99  res_forward_subsumption_resolution:     2
% 2.76/0.99  res_backward_subsumption_resolution:    0
% 2.76/0.99  res_clause_to_clause_subsumption:       199
% 2.76/0.99  res_orphan_elimination:                 0
% 2.76/0.99  res_tautology_del:                      88
% 2.76/0.99  res_num_eq_res_simplified:              0
% 2.76/0.99  res_num_sel_changes:                    0
% 2.76/0.99  res_moves_from_active_to_pass:          0
% 2.76/0.99  
% 2.76/0.99  ------ Superposition
% 2.76/0.99  
% 2.76/0.99  sup_time_total:                         0.
% 2.76/0.99  sup_time_generating:                    0.
% 2.76/0.99  sup_time_sim_full:                      0.
% 2.76/0.99  sup_time_sim_immed:                     0.
% 2.76/0.99  
% 2.76/0.99  sup_num_of_clauses:                     94
% 2.76/0.99  sup_num_in_active:                      51
% 2.76/0.99  sup_num_in_passive:                     43
% 2.76/0.99  sup_num_of_loops:                       60
% 2.76/0.99  sup_fw_superposition:                   58
% 2.76/0.99  sup_bw_superposition:                   21
% 2.76/0.99  sup_immediate_simplified:               10
% 2.76/0.99  sup_given_eliminated:                   0
% 2.76/0.99  comparisons_done:                       0
% 2.76/0.99  comparisons_avoided:                    0
% 2.76/0.99  
% 2.76/0.99  ------ Simplifications
% 2.76/0.99  
% 2.76/0.99  
% 2.76/0.99  sim_fw_subset_subsumed:                 1
% 2.76/0.99  sim_bw_subset_subsumed:                 2
% 2.76/0.99  sim_fw_subsumed:                        0
% 2.76/0.99  sim_bw_subsumed:                        1
% 2.76/0.99  sim_fw_subsumption_res:                 3
% 2.76/0.99  sim_bw_subsumption_res:                 0
% 2.76/0.99  sim_tautology_del:                      0
% 2.76/0.99  sim_eq_tautology_del:                   1
% 2.76/0.99  sim_eq_res_simp:                        0
% 2.76/0.99  sim_fw_demodulated:                     1
% 2.76/0.99  sim_bw_demodulated:                     9
% 2.76/0.99  sim_light_normalised:                   3
% 2.76/0.99  sim_joinable_taut:                      0
% 2.76/0.99  sim_joinable_simp:                      0
% 2.76/0.99  sim_ac_normalised:                      0
% 2.76/0.99  sim_smt_subsumption:                    0
% 2.76/0.99  
%------------------------------------------------------------------------------
