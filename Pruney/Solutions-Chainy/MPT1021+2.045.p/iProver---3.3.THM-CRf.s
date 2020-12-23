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
% DateTime   : Thu Dec  3 12:07:27 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  201 (1570 expanded)
%              Number of clauses        :  129 ( 505 expanded)
%              Number of leaves         :   18 ( 300 expanded)
%              Depth                    :   21
%              Number of atoms          :  637 (7331 expanded)
%              Number of equality atoms :  281 ( 774 expanded)
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

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k4_relat_1(X2) = k3_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_relat_1(X2) = k3_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f48,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f66])).

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

fof(f72,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] :
                ( r2_hidden(X3,X0)
               => k11_relat_1(X1,X3) = k11_relat_1(X2,X3) )
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ! [X3] : k11_relat_1(X1,X3) = k11_relat_1(X2,X3)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] : k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | ? [X3] : k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X2,X1] :
      ( ? [X3] : k11_relat_1(X1,X3) != k11_relat_1(X2,X3)
     => k11_relat_1(X1,sK0(X1,X2)) != k11_relat_1(X2,sK0(X1,X2)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X0,X1,X2)
          | k11_relat_1(X1,sK0(X1,X2)) != k11_relat_1(X2,sK0(X1,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f43])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X0,X1,X2)
      | k11_relat_1(X1,sK0(X1,X2)) != k11_relat_1(X2,sK0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_723,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1260,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_726,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | ~ v3_funct_2(X0_52,X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | k2_funct_2(X0_53,X0_52) = k2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1257,plain,
    ( k2_funct_2(X0_53,X0_52) = k2_funct_1(X0_52)
    | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_2822,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1257])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_22,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_839,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_3030,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2822,c_24,c_23,c_22,c_21,c_839])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_731,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | ~ v3_funct_2(X0_52,X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1252,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_3321,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3030,c_1252])).

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

cnf(c_4154,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3321,c_25,c_26,c_27,c_28])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_727,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52) = k5_relat_1(X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1256,plain,
    ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X0_52,X1_52) = k5_relat_1(X0_52,X1_52)
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_4166,plain,
    ( k1_partfun1(sK1,sK1,X0_53,X1_53,k2_funct_1(sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4154,c_1256])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_728,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | ~ v3_funct_2(X0_52,X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_funct_2(X0_53,X0_52)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1255,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_2(X0_53,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_2685,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1255])).

cnf(c_832,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_2(X0_53,X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_834,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_2984,plain,
    ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2685,c_25,c_26,c_27,c_28,c_834])).

cnf(c_3033,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3030,c_2984])).

cnf(c_6027,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_53,X1_53,k2_funct_1(sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4166,c_3033])).

cnf(c_6028,plain,
    ( k1_partfun1(sK1,sK1,X0_53,X1_53,k2_funct_1(sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_6027])).

cnf(c_6036,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_6028])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_725,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | k1_relset_1(X0_53,X0_53,X0_52) = X0_53 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1258,plain,
    ( k1_relset_1(X0_53,X0_53,X0_52) = X0_53
    | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_4164,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4154,c_1258])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_735,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k1_relset_1(X1_53,X0_53,k3_relset_1(X0_53,X1_53,X0_52)) = k2_relset_1(X0_53,X1_53,X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1248,plain,
    ( k1_relset_1(X0_53,X1_53,k3_relset_1(X1_53,X0_53,X0_52)) = k2_relset_1(X1_53,X0_53,X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_2026,plain,
    ( k1_relset_1(sK1,sK1,k3_relset_1(sK1,sK1,sK2)) = k2_relset_1(sK1,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1260,c_1248])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1245,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_1599,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1260,c_1245])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_740,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1243,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_1496,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1243])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k4_relat_1(X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_743,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k4_relat_1(X0_52) = k2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1240,plain,
    ( k4_relat_1(X0_52) = k2_funct_1(X0_52)
    | v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_1548,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1240])).

cnf(c_790,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_799,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_732,plain,
    ( ~ v3_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | v2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_821,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_1816,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1548,c_24,c_22,c_21,c_790,c_799,c_821])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k3_relset_1(X0_53,X1_53,X0_52) = k4_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1246,plain,
    ( k3_relset_1(X0_53,X1_53,X0_52) = k4_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_1609,plain,
    ( k3_relset_1(sK1,sK1,sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1260,c_1246])).

cnf(c_1820,plain,
    ( k3_relset_1(sK1,sK1,sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1816,c_1609])).

cnf(c_2031,plain,
    ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2026,c_1599,c_1820])).

cnf(c_4218,plain,
    ( k2_relat_1(sK2) = sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4164,c_2031])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_729,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X0_53)
    | v1_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53)
    | ~ v3_funct_2(X0_52,X0_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1254,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v1_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53) = iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_2961,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1254])).

cnf(c_829,plain,
    ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v1_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53) = iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_831,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_3160,plain,
    ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2961,c_25,c_26,c_27,c_28,c_831])).

cnf(c_3164,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3160,c_3030])).

cnf(c_5048,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4218,c_3033,c_3164])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_742,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k5_relat_1(k2_funct_1(X0_52),X0_52) = k6_partfun1(k2_relat_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1241,plain,
    ( k5_relat_1(k2_funct_1(X0_52),X0_52) = k6_partfun1(k2_relat_1(X0_52))
    | v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_1961,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1241])).

cnf(c_793,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_742])).

cnf(c_2455,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1961,c_24,c_22,c_21,c_793,c_799,c_821])).

cnf(c_5052,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_5048,c_2455])).

cnf(c_6062,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6036,c_5052])).

cnf(c_6125,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6062,c_25])).

cnf(c_3633,plain,
    ( k1_partfun1(sK1,sK1,X0_53,X1_53,sK2,X0_52) = k5_relat_1(sK2,X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1256])).

cnf(c_3941,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k1_partfun1(sK1,sK1,X0_53,X1_53,sK2,X0_52) = k5_relat_1(sK2,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3633,c_25])).

cnf(c_3942,plain,
    ( k1_partfun1(sK1,sK1,X0_53,X1_53,sK2,X0_52) = k5_relat_1(sK2,X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3941])).

cnf(c_3949,plain,
    ( k1_partfun1(sK1,sK1,X0_53,X0_53,sK2,k2_funct_2(X0_53,X0_52)) = k5_relat_1(sK2,k2_funct_2(X0_53,X0_52))
    | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_2(X0_53,X0_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1252,c_3942])).

cnf(c_4269,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | k1_partfun1(sK1,sK1,X0_53,X0_53,sK2,k2_funct_2(X0_53,X0_52)) = k5_relat_1(sK2,k2_funct_2(X0_53,X0_52)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3949,c_832])).

cnf(c_4270,plain,
    ( k1_partfun1(sK1,sK1,X0_53,X0_53,sK2,k2_funct_2(X0_53,X0_52)) = k5_relat_1(sK2,k2_funct_2(X0_53,X0_52))
    | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4269])).

cnf(c_4280,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_4270])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_741,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k5_relat_1(X0_52,k2_funct_1(X0_52)) = k6_partfun1(k1_relat_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1242,plain,
    ( k5_relat_1(X0_52,k2_funct_1(X0_52)) = k6_partfun1(k1_relat_1(X0_52))
    | v1_relat_1(X0_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_2039,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1242])).

cnf(c_796,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_2459,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2039,c_24,c_22,c_21,c_796,c_799,c_821])).

cnf(c_2183,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1258])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_739,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1244,plain,
    ( k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_1553,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1260,c_1244])).

cnf(c_2194,plain,
    ( k1_relat_1(sK2) = sK1
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2183,c_1553])).

cnf(c_2385,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_25,c_26])).

cnf(c_2461,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_2459,c_2385])).

cnf(c_4320,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4280,c_2461,c_3030])).

cnf(c_4165,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4154,c_3942])).

cnf(c_4212,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4165,c_2461])).

cnf(c_4459,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4320,c_3033,c_4212])).

cnf(c_20,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_724,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1259,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_3034,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3030,c_1259])).

cnf(c_4462,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4459,c_3034])).

cnf(c_9,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_734,plain,
    ( m1_subset_1(k6_partfun1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1249,plain,
    ( m1_subset_1(k6_partfun1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | k11_relat_1(X2,sK0(X1,X2)) != k11_relat_1(X1,sK0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_733,plain,
    ( r2_relset_1(X0_53,X0_53,X0_52,X1_52)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
    | k11_relat_1(X1_52,sK0(X0_52,X1_52)) != k11_relat_1(X0_52,sK0(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1250,plain,
    ( k11_relat_1(X0_52,sK0(X1_52,X0_52)) != k11_relat_1(X1_52,sK0(X1_52,X0_52))
    | r2_relset_1(X0_53,X0_53,X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_2675,plain,
    ( r2_relset_1(X0_53,X0_53,X0_52,X0_52) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1250])).

cnf(c_3776,plain,
    ( r2_relset_1(X0_53,X0_53,k6_partfun1(X0_53),k6_partfun1(X0_53)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_2675])).

cnf(c_3796,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3776])).

cnf(c_4465,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4462,c_3796])).

cnf(c_6128,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6125,c_4465])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6128,c_3796])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.34/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/1.00  
% 3.34/1.00  ------  iProver source info
% 3.34/1.00  
% 3.34/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.34/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/1.00  git: non_committed_changes: false
% 3.34/1.00  git: last_make_outside_of_git: false
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    --mode clausify
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         false
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     num_symb
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       true
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     false
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   []
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_full_bw                           [BwDemod]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  ------ Parsing...
% 3.34/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.00  ------ Proving...
% 3.34/1.00  ------ Problem Properties 
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  clauses                                 24
% 3.34/1.00  conjectures                             5
% 3.34/1.00  EPR                                     3
% 3.34/1.00  Horn                                    24
% 3.34/1.00  unary                                   5
% 3.34/1.00  binary                                  7
% 3.34/1.00  lits                                    73
% 3.34/1.00  lits eq                                 12
% 3.34/1.00  fd_pure                                 0
% 3.34/1.00  fd_pseudo                               0
% 3.34/1.00  fd_cond                                 0
% 3.34/1.00  fd_pseudo_cond                          0
% 3.34/1.00  AC symbols                              0
% 3.34/1.00  
% 3.34/1.00  ------ Schedule dynamic 5 is on 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  Current options:
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    --mode clausify
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         false
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     none
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       false
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     false
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   []
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_full_bw                           [BwDemod]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ Proving...
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS status Theorem for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  fof(f16,conjecture,(
% 3.34/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f17,negated_conjecture,(
% 3.34/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.34/1.00    inference(negated_conjecture,[],[f16])).
% 3.34/1.00  
% 3.34/1.00  fof(f41,plain,(
% 3.34/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.34/1.00    inference(ennf_transformation,[],[f17])).
% 3.34/1.00  
% 3.34/1.00  fof(f42,plain,(
% 3.34/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.34/1.00    inference(flattening,[],[f41])).
% 3.34/1.00  
% 3.34/1.00  fof(f45,plain,(
% 3.34/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f46,plain,(
% 3.34/1.00    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f45])).
% 3.34/1.00  
% 3.34/1.00  fof(f71,plain,(
% 3.34/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.34/1.00    inference(cnf_transformation,[],[f46])).
% 3.34/1.00  
% 3.34/1.00  fof(f13,axiom,(
% 3.34/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f37,plain,(
% 3.34/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.34/1.00    inference(ennf_transformation,[],[f13])).
% 3.34/1.00  
% 3.34/1.00  fof(f38,plain,(
% 3.34/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.34/1.00    inference(flattening,[],[f37])).
% 3.34/1.00  
% 3.34/1.00  fof(f65,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f38])).
% 3.34/1.00  
% 3.34/1.00  fof(f68,plain,(
% 3.34/1.00    v1_funct_1(sK2)),
% 3.34/1.00    inference(cnf_transformation,[],[f46])).
% 3.34/1.00  
% 3.34/1.00  fof(f69,plain,(
% 3.34/1.00    v1_funct_2(sK2,sK1,sK1)),
% 3.34/1.00    inference(cnf_transformation,[],[f46])).
% 3.34/1.00  
% 3.34/1.00  fof(f70,plain,(
% 3.34/1.00    v3_funct_2(sK2,sK1,sK1)),
% 3.34/1.00    inference(cnf_transformation,[],[f46])).
% 3.34/1.00  
% 3.34/1.00  fof(f11,axiom,(
% 3.34/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f33,plain,(
% 3.34/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.34/1.00    inference(ennf_transformation,[],[f11])).
% 3.34/1.00  
% 3.34/1.00  fof(f34,plain,(
% 3.34/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.34/1.00    inference(flattening,[],[f33])).
% 3.34/1.00  
% 3.34/1.00  fof(f63,plain,(
% 3.34/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f34])).
% 3.34/1.00  
% 3.34/1.00  fof(f12,axiom,(
% 3.34/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f35,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.34/1.00    inference(ennf_transformation,[],[f12])).
% 3.34/1.00  
% 3.34/1.00  fof(f36,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.34/1.00    inference(flattening,[],[f35])).
% 3.34/1.00  
% 3.34/1.00  fof(f64,plain,(
% 3.34/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f36])).
% 3.34/1.00  
% 3.34/1.00  fof(f60,plain,(
% 3.34/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f34])).
% 3.34/1.00  
% 3.34/1.00  fof(f15,axiom,(
% 3.34/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f39,plain,(
% 3.34/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.34/1.00    inference(ennf_transformation,[],[f15])).
% 3.34/1.00  
% 3.34/1.00  fof(f40,plain,(
% 3.34/1.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.34/1.00    inference(flattening,[],[f39])).
% 3.34/1.00  
% 3.34/1.00  fof(f67,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f40])).
% 3.34/1.00  
% 3.34/1.00  fof(f7,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f28,plain,(
% 3.34/1.00    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.00    inference(ennf_transformation,[],[f7])).
% 3.34/1.00  
% 3.34/1.00  fof(f54,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f28])).
% 3.34/1.00  
% 3.34/1.00  fof(f5,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f26,plain,(
% 3.34/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.00    inference(ennf_transformation,[],[f5])).
% 3.34/1.00  
% 3.34/1.00  fof(f52,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f26])).
% 3.34/1.00  
% 3.34/1.00  fof(f3,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f24,plain,(
% 3.34/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.00    inference(ennf_transformation,[],[f3])).
% 3.34/1.00  
% 3.34/1.00  fof(f50,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f24])).
% 3.34/1.00  
% 3.34/1.00  fof(f1,axiom,(
% 3.34/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f20,plain,(
% 3.34/1.00    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f1])).
% 3.34/1.00  
% 3.34/1.00  fof(f21,plain,(
% 3.34/1.00    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.34/1.00    inference(flattening,[],[f20])).
% 3.34/1.00  
% 3.34/1.00  fof(f47,plain,(
% 3.34/1.00    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f21])).
% 3.34/1.00  
% 3.34/1.00  fof(f10,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f18,plain,(
% 3.34/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.34/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.34/1.00  
% 3.34/1.00  fof(f31,plain,(
% 3.34/1.00    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.00    inference(ennf_transformation,[],[f18])).
% 3.34/1.00  
% 3.34/1.00  fof(f32,plain,(
% 3.34/1.00    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.00    inference(flattening,[],[f31])).
% 3.34/1.00  
% 3.34/1.00  fof(f59,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f32])).
% 3.34/1.00  
% 3.34/1.00  fof(f6,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k4_relat_1(X2) = k3_relset_1(X0,X1,X2))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f27,plain,(
% 3.34/1.00    ! [X0,X1,X2] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.00    inference(ennf_transformation,[],[f6])).
% 3.34/1.00  
% 3.34/1.00  fof(f53,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k4_relat_1(X2) = k3_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f27])).
% 3.34/1.00  
% 3.34/1.00  fof(f61,plain,(
% 3.34/1.00    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f34])).
% 3.34/1.00  
% 3.34/1.00  fof(f2,axiom,(
% 3.34/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f22,plain,(
% 3.34/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.34/1.00    inference(ennf_transformation,[],[f2])).
% 3.34/1.00  
% 3.34/1.00  fof(f23,plain,(
% 3.34/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.34/1.00    inference(flattening,[],[f22])).
% 3.34/1.00  
% 3.34/1.00  fof(f49,plain,(
% 3.34/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f23])).
% 3.34/1.00  
% 3.34/1.00  fof(f14,axiom,(
% 3.34/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f66,plain,(
% 3.34/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f14])).
% 3.34/1.00  
% 3.34/1.00  fof(f73,plain,(
% 3.34/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/1.00    inference(definition_unfolding,[],[f49,f66])).
% 3.34/1.00  
% 3.34/1.00  fof(f48,plain,(
% 3.34/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f23])).
% 3.34/1.00  
% 3.34/1.00  fof(f74,plain,(
% 3.34/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/1.00    inference(definition_unfolding,[],[f48,f66])).
% 3.34/1.00  
% 3.34/1.00  fof(f4,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f25,plain,(
% 3.34/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/1.00    inference(ennf_transformation,[],[f4])).
% 3.34/1.00  
% 3.34/1.00  fof(f51,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f25])).
% 3.34/1.00  
% 3.34/1.00  fof(f72,plain,(
% 3.34/1.00    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.34/1.00    inference(cnf_transformation,[],[f46])).
% 3.34/1.00  
% 3.34/1.00  fof(f8,axiom,(
% 3.34/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f56,plain,(
% 3.34/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f8])).
% 3.34/1.00  
% 3.34/1.00  fof(f75,plain,(
% 3.34/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.34/1.00    inference(definition_unfolding,[],[f56,f66])).
% 3.34/1.00  
% 3.34/1.00  fof(f9,axiom,(
% 3.34/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : (r2_hidden(X3,X0) => k11_relat_1(X1,X3) = k11_relat_1(X2,X3)) => r2_relset_1(X0,X0,X1,X2))))),
% 3.34/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f19,plain,(
% 3.34/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => (! [X3] : k11_relat_1(X1,X3) = k11_relat_1(X2,X3) => r2_relset_1(X0,X0,X1,X2))))),
% 3.34/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.34/1.00  
% 3.34/1.00  fof(f29,plain,(
% 3.34/1.00    ! [X0,X1] : (! [X2] : ((r2_relset_1(X0,X0,X1,X2) | ? [X3] : k11_relat_1(X1,X3) != k11_relat_1(X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.34/1.00    inference(ennf_transformation,[],[f19])).
% 3.34/1.00  
% 3.34/1.00  fof(f30,plain,(
% 3.34/1.00    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | ? [X3] : k11_relat_1(X1,X3) != k11_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.34/1.00    inference(flattening,[],[f29])).
% 3.34/1.00  
% 3.34/1.00  fof(f43,plain,(
% 3.34/1.00    ! [X2,X1] : (? [X3] : k11_relat_1(X1,X3) != k11_relat_1(X2,X3) => k11_relat_1(X1,sK0(X1,X2)) != k11_relat_1(X2,sK0(X1,X2)))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f44,plain,(
% 3.34/1.00    ! [X0,X1] : (! [X2] : (r2_relset_1(X0,X0,X1,X2) | k11_relat_1(X1,sK0(X1,X2)) != k11_relat_1(X2,sK0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f43])).
% 3.34/1.00  
% 3.34/1.00  fof(f57,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (r2_relset_1(X0,X0,X1,X2) | k11_relat_1(X1,sK0(X1,X2)) != k11_relat_1(X2,sK0(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.34/1.00    inference(cnf_transformation,[],[f44])).
% 3.34/1.00  
% 3.34/1.00  cnf(c_21,negated_conjecture,
% 3.34/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.34/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_723,negated_conjecture,
% 3.34/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1260,plain,
% 3.34/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_18,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/1.00      | ~ v1_funct_1(X0)
% 3.34/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_726,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | ~ v3_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 3.34/1.00      | ~ v1_funct_1(X0_52)
% 3.34/1.00      | k2_funct_2(X0_53,X0_52) = k2_funct_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1257,plain,
% 3.34/1.00      ( k2_funct_2(X0_53,X0_52) = k2_funct_1(X0_52)
% 3.34/1.00      | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2822,plain,
% 3.34/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.34/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1257]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_24,negated_conjecture,
% 3.34/1.00      ( v1_funct_1(sK2) ),
% 3.34/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_23,negated_conjecture,
% 3.34/1.00      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_22,negated_conjecture,
% 3.34/1.00      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.34/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_839,plain,
% 3.34/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.34/1.00      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.34/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.34/1.00      | ~ v1_funct_1(sK2)
% 3.34/1.00      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_726]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3030,plain,
% 3.34/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_2822,c_24,c_23,c_22,c_21,c_839]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_13,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/1.00      | ~ v1_funct_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_731,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | ~ v3_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 3.34/1.00      | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 3.34/1.00      | ~ v1_funct_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1252,plain,
% 3.34/1.00      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | m1_subset_1(k2_funct_2(X0_53,X0_52),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3321,plain,
% 3.34/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.34/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_3030,c_1252]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_25,plain,
% 3.34/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_26,plain,
% 3.34/1.00      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_27,plain,
% 3.34/1.00      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_28,plain,
% 3.34/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4154,plain,
% 3.34/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_3321,c_25,c_26,c_27,c_28]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_17,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.34/1.00      | ~ v1_funct_1(X0)
% 3.34/1.00      | ~ v1_funct_1(X3)
% 3.34/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_727,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.34/1.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
% 3.34/1.00      | ~ v1_funct_1(X0_52)
% 3.34/1.00      | ~ v1_funct_1(X1_52)
% 3.34/1.00      | k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52) = k5_relat_1(X1_52,X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1256,plain,
% 3.34/1.00      ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X0_52,X1_52) = k5_relat_1(X0_52,X1_52)
% 3.34/1.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(X1_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4166,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,X0_53,X1_53,k2_funct_1(sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),X0_52)
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_4154,c_1256]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_16,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/1.00      | ~ v1_funct_1(X0)
% 3.34/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_728,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | ~ v3_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 3.34/1.00      | ~ v1_funct_1(X0_52)
% 3.34/1.00      | v1_funct_1(k2_funct_2(X0_53,X0_52)) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1255,plain,
% 3.34/1.00      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(k2_funct_2(X0_53,X0_52)) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2685,plain,
% 3.34/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1255]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_832,plain,
% 3.34/1.00      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(k2_funct_2(X0_53,X0_52)) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_834,plain,
% 3.34/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.34/1.00      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_832]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2984,plain,
% 3.34/1.00      ( v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_2685,c_25,c_26,c_27,c_28,c_834]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3033,plain,
% 3.34/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_3030,c_2984]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_6027,plain,
% 3.34/1.00      ( v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.34/1.00      | k1_partfun1(sK1,sK1,X0_53,X1_53,k2_funct_1(sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),X0_52) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_4166,c_3033]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_6028,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,X0_53,X1_53,k2_funct_1(sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),X0_52)
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(renaming,[status(thm)],[c_6027]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_6036,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_6028]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_19,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/1.00      | ~ v1_funct_1(X0)
% 3.34/1.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 3.34/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_725,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 3.34/1.00      | ~ v1_funct_1(X0_52)
% 3.34/1.00      | k1_relset_1(X0_53,X0_53,X0_52) = X0_53 ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1258,plain,
% 3.34/1.00      ( k1_relset_1(X0_53,X0_53,X0_52) = X0_53
% 3.34/1.00      | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4164,plain,
% 3.34/1.00      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = sK1
% 3.34/1.00      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_4154,c_1258]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_8,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.00      | k1_relset_1(X2,X1,k3_relset_1(X1,X2,X0)) = k2_relset_1(X1,X2,X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_735,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.34/1.00      | k1_relset_1(X1_53,X0_53,k3_relset_1(X0_53,X1_53,X0_52)) = k2_relset_1(X0_53,X1_53,X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1248,plain,
% 3.34/1.00      ( k1_relset_1(X0_53,X1_53,k3_relset_1(X1_53,X0_53,X0_52)) = k2_relset_1(X1_53,X0_53,X0_52)
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2026,plain,
% 3.34/1.00      ( k1_relset_1(sK1,sK1,k3_relset_1(sK1,sK1,sK2)) = k2_relset_1(sK1,sK1,sK2) ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1248]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_5,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_738,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.34/1.00      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1245,plain,
% 3.34/1.00      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1599,plain,
% 3.34/1.00      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1245]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.00      | v1_relat_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_740,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.34/1.00      | v1_relat_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1243,plain,
% 3.34/1.00      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.34/1.00      | v1_relat_1(X0_52) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1496,plain,
% 3.34/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1243]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_0,plain,
% 3.34/1.00      ( ~ v1_relat_1(X0)
% 3.34/1.00      | ~ v1_funct_1(X0)
% 3.34/1.00      | ~ v2_funct_1(X0)
% 3.34/1.00      | k4_relat_1(X0) = k2_funct_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_743,plain,
% 3.34/1.00      ( ~ v1_relat_1(X0_52)
% 3.34/1.00      | ~ v1_funct_1(X0_52)
% 3.34/1.00      | ~ v2_funct_1(X0_52)
% 3.34/1.00      | k4_relat_1(X0_52) = k2_funct_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1240,plain,
% 3.34/1.00      ( k4_relat_1(X0_52) = k2_funct_1(X0_52)
% 3.34/1.00      | v1_relat_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1548,plain,
% 3.34/1.00      ( k4_relat_1(sK2) = k2_funct_1(sK2)
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top
% 3.34/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1496,c_1240]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_790,plain,
% 3.34/1.00      ( ~ v1_relat_1(sK2)
% 3.34/1.00      | ~ v1_funct_1(sK2)
% 3.34/1.00      | ~ v2_funct_1(sK2)
% 3.34/1.00      | k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_743]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_799,plain,
% 3.34/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.34/1.00      | v1_relat_1(sK2) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_740]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_11,plain,
% 3.34/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.00      | ~ v1_funct_1(X0)
% 3.34/1.00      | v2_funct_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_732,plain,
% 3.34/1.00      ( ~ v3_funct_2(X0_52,X0_53,X1_53)
% 3.34/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.34/1.00      | ~ v1_funct_1(X0_52)
% 3.34/1.00      | v2_funct_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_821,plain,
% 3.34/1.00      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.34/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.34/1.00      | ~ v1_funct_1(sK2)
% 3.34/1.00      | v2_funct_1(sK2) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_732]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1816,plain,
% 3.34/1.00      ( k4_relat_1(sK2) = k2_funct_1(sK2) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_1548,c_24,c_22,c_21,c_790,c_799,c_821]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_6,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.00      | k3_relset_1(X1,X2,X0) = k4_relat_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_737,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.34/1.00      | k3_relset_1(X0_53,X1_53,X0_52) = k4_relat_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1246,plain,
% 3.34/1.00      ( k3_relset_1(X0_53,X1_53,X0_52) = k4_relat_1(X0_52)
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1609,plain,
% 3.34/1.00      ( k3_relset_1(sK1,sK1,sK2) = k4_relat_1(sK2) ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1246]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1820,plain,
% 3.34/1.00      ( k3_relset_1(sK1,sK1,sK2) = k2_funct_1(sK2) ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_1816,c_1609]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2031,plain,
% 3.34/1.00      ( k1_relset_1(sK1,sK1,k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_2026,c_1599,c_1820]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4218,plain,
% 3.34/1.00      ( k2_relat_1(sK2) = sK1
% 3.34/1.00      | v1_funct_2(k2_funct_1(sK2),sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_4164,c_2031]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_15,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/1.00      | v1_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.34/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.34/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/1.00      | ~ v1_funct_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_729,plain,
% 3.34/1.00      ( ~ v1_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | v1_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53)
% 3.34/1.00      | ~ v3_funct_2(X0_52,X0_53,X0_53)
% 3.34/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 3.34/1.00      | ~ v1_funct_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1254,plain,
% 3.34/1.00      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v1_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53) = iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2961,plain,
% 3.34/1.00      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.34/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1254]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_829,plain,
% 3.34/1.00      ( v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v1_funct_2(k2_funct_2(X0_53,X0_52),X0_53,X0_53) = iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_831,plain,
% 3.34/1.00      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top
% 3.34/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_829]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3160,plain,
% 3.34/1.00      ( v1_funct_2(k2_funct_2(sK1,sK2),sK1,sK1) = iProver_top ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_2961,c_25,c_26,c_27,c_28,c_831]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3164,plain,
% 3.34/1.00      ( v1_funct_2(k2_funct_1(sK2),sK1,sK1) = iProver_top ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_3160,c_3030]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_5048,plain,
% 3.34/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_4218,c_3033,c_3164]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1,plain,
% 3.34/1.00      ( ~ v1_relat_1(X0)
% 3.34/1.00      | ~ v1_funct_1(X0)
% 3.34/1.00      | ~ v2_funct_1(X0)
% 3.34/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_742,plain,
% 3.34/1.00      ( ~ v1_relat_1(X0_52)
% 3.34/1.00      | ~ v1_funct_1(X0_52)
% 3.34/1.00      | ~ v2_funct_1(X0_52)
% 3.34/1.00      | k5_relat_1(k2_funct_1(X0_52),X0_52) = k6_partfun1(k2_relat_1(X0_52)) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1241,plain,
% 3.34/1.00      ( k5_relat_1(k2_funct_1(X0_52),X0_52) = k6_partfun1(k2_relat_1(X0_52))
% 3.34/1.00      | v1_relat_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1961,plain,
% 3.34/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top
% 3.34/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1496,c_1241]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_793,plain,
% 3.34/1.00      ( ~ v1_relat_1(sK2)
% 3.34/1.00      | ~ v1_funct_1(sK2)
% 3.34/1.00      | ~ v2_funct_1(sK2)
% 3.34/1.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_742]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2455,plain,
% 3.34/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_1961,c_24,c_22,c_21,c_793,c_799,c_821]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_5052,plain,
% 3.34/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_5048,c_2455]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_6062,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_6036,c_5052]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_6125,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_6062,c_25]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3633,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,X0_53,X1_53,sK2,X0_52) = k5_relat_1(sK2,X0_52)
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1256]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3941,plain,
% 3.34/1.00      ( v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.34/1.00      | k1_partfun1(sK1,sK1,X0_53,X1_53,sK2,X0_52) = k5_relat_1(sK2,X0_52) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_3633,c_25]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3942,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,X0_53,X1_53,sK2,X0_52) = k5_relat_1(sK2,X0_52)
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(renaming,[status(thm)],[c_3941]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3949,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,X0_53,X0_53,sK2,k2_funct_2(X0_53,X0_52)) = k5_relat_1(sK2,k2_funct_2(X0_53,X0_52))
% 3.34/1.00      | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(k2_funct_2(X0_53,X0_52)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1252,c_3942]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4269,plain,
% 3.34/1.00      ( v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | k1_partfun1(sK1,sK1,X0_53,X0_53,sK2,k2_funct_2(X0_53,X0_52)) = k5_relat_1(sK2,k2_funct_2(X0_53,X0_52)) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_3949,c_832]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4270,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,X0_53,X0_53,sK2,k2_funct_2(X0_53,X0_52)) = k5_relat_1(sK2,k2_funct_2(X0_53,X0_52))
% 3.34/1.00      | v1_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | v3_funct_2(X0_52,X0_53,X0_53) != iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(renaming,[status(thm)],[c_4269]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4280,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)) = k5_relat_1(sK2,k2_funct_2(sK1,sK2))
% 3.34/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_4270]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2,plain,
% 3.34/1.00      ( ~ v1_relat_1(X0)
% 3.34/1.00      | ~ v1_funct_1(X0)
% 3.34/1.00      | ~ v2_funct_1(X0)
% 3.34/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_741,plain,
% 3.34/1.00      ( ~ v1_relat_1(X0_52)
% 3.34/1.00      | ~ v1_funct_1(X0_52)
% 3.34/1.00      | ~ v2_funct_1(X0_52)
% 3.34/1.00      | k5_relat_1(X0_52,k2_funct_1(X0_52)) = k6_partfun1(k1_relat_1(X0_52)) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1242,plain,
% 3.34/1.00      ( k5_relat_1(X0_52,k2_funct_1(X0_52)) = k6_partfun1(k1_relat_1(X0_52))
% 3.34/1.00      | v1_relat_1(X0_52) != iProver_top
% 3.34/1.00      | v1_funct_1(X0_52) != iProver_top
% 3.34/1.00      | v2_funct_1(X0_52) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2039,plain,
% 3.34/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top
% 3.34/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1496,c_1242]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_796,plain,
% 3.34/1.00      ( ~ v1_relat_1(sK2)
% 3.34/1.00      | ~ v1_funct_1(sK2)
% 3.34/1.00      | ~ v2_funct_1(sK2)
% 3.34/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_741]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2459,plain,
% 3.34/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_2039,c_24,c_22,c_21,c_796,c_799,c_821]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2183,plain,
% 3.34/1.00      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.34/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1258]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_739,plain,
% 3.34/1.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.34/1.00      | k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1244,plain,
% 3.34/1.00      ( k1_relset_1(X0_53,X1_53,X0_52) = k1_relat_1(X0_52)
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1553,plain,
% 3.34/1.00      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1260,c_1244]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2194,plain,
% 3.34/1.00      ( k1_relat_1(sK2) = sK1
% 3.34/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_2183,c_1553]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2385,plain,
% 3.34/1.00      ( k1_relat_1(sK2) = sK1 ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_2194,c_25,c_26]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2461,plain,
% 3.34/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_2459,c_2385]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4320,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.34/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.34/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_4280,c_2461,c_3030]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4165,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.34/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_4154,c_3942]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4212,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1)
% 3.34/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.34/1.00      inference(light_normalisation,[status(thm)],[c_4165,c_2461]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4459,plain,
% 3.34/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(sK1) ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_4320,c_3033,c_4212]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_20,negated_conjecture,
% 3.34/1.00      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.34/1.00      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_724,negated_conjecture,
% 3.34/1.00      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.34/1.00      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1259,plain,
% 3.34/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.34/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3034,plain,
% 3.34/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.34/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_3030,c_1259]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4462,plain,
% 3.34/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.34/1.00      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_4459,c_3034]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_9,plain,
% 3.34/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.34/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_734,plain,
% 3.34/1.00      ( m1_subset_1(k6_partfun1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1249,plain,
% 3.34/1.00      ( m1_subset_1(k6_partfun1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) = iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_10,plain,
% 3.34/1.00      ( r2_relset_1(X0,X0,X1,X2)
% 3.34/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.34/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.34/1.00      | k11_relat_1(X2,sK0(X1,X2)) != k11_relat_1(X1,sK0(X1,X2)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_733,plain,
% 3.34/1.00      ( r2_relset_1(X0_53,X0_53,X0_52,X1_52)
% 3.34/1.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 3.34/1.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53)))
% 3.34/1.00      | k11_relat_1(X1_52,sK0(X0_52,X1_52)) != k11_relat_1(X0_52,sK0(X0_52,X1_52)) ),
% 3.34/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1250,plain,
% 3.34/1.00      ( k11_relat_1(X0_52,sK0(X1_52,X0_52)) != k11_relat_1(X1_52,sK0(X1_52,X0_52))
% 3.34/1.00      | r2_relset_1(X0_53,X0_53,X1_52,X0_52) = iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top
% 3.34/1.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top ),
% 3.34/1.00      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2675,plain,
% 3.34/1.00      ( r2_relset_1(X0_53,X0_53,X0_52,X0_52) = iProver_top
% 3.34/1.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X0_53))) != iProver_top ),
% 3.34/1.00      inference(equality_resolution,[status(thm)],[c_1250]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3776,plain,
% 3.34/1.00      ( r2_relset_1(X0_53,X0_53,k6_partfun1(X0_53),k6_partfun1(X0_53)) = iProver_top ),
% 3.34/1.00      inference(superposition,[status(thm)],[c_1249,c_2675]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_3796,plain,
% 3.34/1.00      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) = iProver_top ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_3776]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4465,plain,
% 3.34/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top ),
% 3.34/1.00      inference(global_propositional_subsumption,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_4462,c_3796]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_6128,plain,
% 3.34/1.00      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.34/1.00      inference(demodulation,[status(thm)],[c_6125,c_4465]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(contradiction,plain,
% 3.34/1.00      ( $false ),
% 3.34/1.00      inference(minisat,[status(thm)],[c_6128,c_3796]) ).
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  ------                               Statistics
% 3.34/1.00  
% 3.34/1.00  ------ General
% 3.34/1.00  
% 3.34/1.00  abstr_ref_over_cycles:                  0
% 3.34/1.00  abstr_ref_under_cycles:                 0
% 3.34/1.00  gc_basic_clause_elim:                   0
% 3.34/1.00  forced_gc_time:                         0
% 3.34/1.00  parsing_time:                           0.012
% 3.34/1.00  unif_index_cands_time:                  0.
% 3.34/1.00  unif_index_add_time:                    0.
% 3.34/1.00  orderings_time:                         0.
% 3.34/1.00  out_proof_time:                         0.013
% 3.34/1.00  total_time:                             0.248
% 3.34/1.00  num_of_symbols:                         61
% 3.34/1.00  num_of_terms:                           5836
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing
% 3.34/1.00  
% 3.34/1.00  num_of_splits:                          0
% 3.34/1.00  num_of_split_atoms:                     0
% 3.34/1.00  num_of_reused_defs:                     0
% 3.34/1.00  num_eq_ax_congr_red:                    48
% 3.34/1.00  num_of_sem_filtered_clauses:            1
% 3.34/1.00  num_of_subtypes:                        6
% 3.34/1.00  monotx_restored_types:                  1
% 3.34/1.00  sat_num_of_epr_types:                   0
% 3.34/1.00  sat_num_of_non_cyclic_types:            0
% 3.34/1.00  sat_guarded_non_collapsed_types:        0
% 3.34/1.00  num_pure_diseq_elim:                    0
% 3.34/1.00  simp_replaced_by:                       0
% 3.34/1.00  res_preprocessed:                       143
% 3.34/1.00  prep_upred:                             0
% 3.34/1.00  prep_unflattend:                        0
% 3.34/1.00  smt_new_axioms:                         0
% 3.34/1.00  pred_elim_cands:                        7
% 3.34/1.00  pred_elim:                              0
% 3.34/1.00  pred_elim_cl:                           0
% 3.34/1.00  pred_elim_cycles:                       4
% 3.34/1.00  merged_defs:                            0
% 3.34/1.00  merged_defs_ncl:                        0
% 3.34/1.00  bin_hyper_res:                          0
% 3.34/1.00  prep_cycles:                            4
% 3.34/1.00  pred_elim_time:                         0.005
% 3.34/1.00  splitting_time:                         0.
% 3.34/1.00  sem_filter_time:                        0.
% 3.34/1.00  monotx_time:                            0.001
% 3.34/1.00  subtype_inf_time:                       0.002
% 3.34/1.00  
% 3.34/1.00  ------ Problem properties
% 3.34/1.00  
% 3.34/1.00  clauses:                                24
% 3.34/1.00  conjectures:                            5
% 3.34/1.00  epr:                                    3
% 3.34/1.00  horn:                                   24
% 3.34/1.00  ground:                                 5
% 3.34/1.00  unary:                                  5
% 3.34/1.00  binary:                                 7
% 3.34/1.00  lits:                                   73
% 3.34/1.00  lits_eq:                                12
% 3.34/1.00  fd_pure:                                0
% 3.34/1.00  fd_pseudo:                              0
% 3.34/1.00  fd_cond:                                0
% 3.34/1.00  fd_pseudo_cond:                         0
% 3.34/1.00  ac_symbols:                             0
% 3.34/1.00  
% 3.34/1.00  ------ Propositional Solver
% 3.34/1.00  
% 3.34/1.00  prop_solver_calls:                      30
% 3.34/1.00  prop_fast_solver_calls:                 1172
% 3.34/1.00  smt_solver_calls:                       0
% 3.34/1.00  smt_fast_solver_calls:                  0
% 3.34/1.00  prop_num_of_clauses:                    1931
% 3.34/1.00  prop_preprocess_simplified:             6865
% 3.34/1.00  prop_fo_subsumed:                       61
% 3.34/1.00  prop_solver_time:                       0.
% 3.34/1.00  smt_solver_time:                        0.
% 3.34/1.00  smt_fast_solver_time:                   0.
% 3.34/1.00  prop_fast_solver_time:                  0.
% 3.34/1.00  prop_unsat_core_time:                   0.
% 3.34/1.00  
% 3.34/1.00  ------ QBF
% 3.34/1.00  
% 3.34/1.00  qbf_q_res:                              0
% 3.34/1.00  qbf_num_tautologies:                    0
% 3.34/1.00  qbf_prep_cycles:                        0
% 3.34/1.00  
% 3.34/1.00  ------ BMC1
% 3.34/1.00  
% 3.34/1.00  bmc1_current_bound:                     -1
% 3.34/1.00  bmc1_last_solved_bound:                 -1
% 3.34/1.00  bmc1_unsat_core_size:                   -1
% 3.34/1.00  bmc1_unsat_core_parents_size:           -1
% 3.34/1.00  bmc1_merge_next_fun:                    0
% 3.34/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation
% 3.34/1.00  
% 3.34/1.00  inst_num_of_clauses:                    781
% 3.34/1.00  inst_num_in_passive:                    383
% 3.34/1.00  inst_num_in_active:                     389
% 3.34/1.00  inst_num_in_unprocessed:                9
% 3.34/1.00  inst_num_of_loops:                      420
% 3.34/1.00  inst_num_of_learning_restarts:          0
% 3.34/1.00  inst_num_moves_active_passive:          25
% 3.34/1.00  inst_lit_activity:                      0
% 3.34/1.00  inst_lit_activity_moves:                0
% 3.34/1.00  inst_num_tautologies:                   0
% 3.34/1.00  inst_num_prop_implied:                  0
% 3.34/1.00  inst_num_existing_simplified:           0
% 3.34/1.00  inst_num_eq_res_simplified:             0
% 3.34/1.00  inst_num_child_elim:                    0
% 3.34/1.00  inst_num_of_dismatching_blockings:      584
% 3.34/1.00  inst_num_of_non_proper_insts:           1029
% 3.34/1.00  inst_num_of_duplicates:                 0
% 3.34/1.00  inst_inst_num_from_inst_to_res:         0
% 3.34/1.00  inst_dismatching_checking_time:         0.
% 3.34/1.00  
% 3.34/1.00  ------ Resolution
% 3.34/1.00  
% 3.34/1.00  res_num_of_clauses:                     0
% 3.34/1.00  res_num_in_passive:                     0
% 3.34/1.00  res_num_in_active:                      0
% 3.34/1.00  res_num_of_loops:                       147
% 3.34/1.00  res_forward_subset_subsumed:            107
% 3.34/1.00  res_backward_subset_subsumed:           4
% 3.34/1.00  res_forward_subsumed:                   0
% 3.34/1.00  res_backward_subsumed:                  0
% 3.34/1.00  res_forward_subsumption_resolution:     0
% 3.34/1.00  res_backward_subsumption_resolution:    0
% 3.34/1.00  res_clause_to_clause_subsumption:       188
% 3.34/1.00  res_orphan_elimination:                 0
% 3.34/1.00  res_tautology_del:                      140
% 3.34/1.00  res_num_eq_res_simplified:              0
% 3.34/1.00  res_num_sel_changes:                    0
% 3.34/1.00  res_moves_from_active_to_pass:          0
% 3.34/1.00  
% 3.34/1.00  ------ Superposition
% 3.34/1.00  
% 3.34/1.00  sup_time_total:                         0.
% 3.34/1.00  sup_time_generating:                    0.
% 3.34/1.00  sup_time_sim_full:                      0.
% 3.34/1.00  sup_time_sim_immed:                     0.
% 3.34/1.00  
% 3.34/1.00  sup_num_of_clauses:                     103
% 3.34/1.00  sup_num_in_active:                      68
% 3.34/1.00  sup_num_in_passive:                     35
% 3.34/1.00  sup_num_of_loops:                       82
% 3.34/1.00  sup_fw_superposition:                   47
% 3.34/1.00  sup_bw_superposition:                   32
% 3.34/1.00  sup_immediate_simplified:               12
% 3.34/1.00  sup_given_eliminated:                   0
% 3.34/1.00  comparisons_done:                       0
% 3.34/1.00  comparisons_avoided:                    0
% 3.34/1.00  
% 3.34/1.00  ------ Simplifications
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  sim_fw_subset_subsumed:                 0
% 3.34/1.00  sim_bw_subset_subsumed:                 1
% 3.34/1.00  sim_fw_subsumed:                        0
% 3.34/1.00  sim_bw_subsumed:                        0
% 3.34/1.00  sim_fw_subsumption_res:                 0
% 3.34/1.00  sim_bw_subsumption_res:                 0
% 3.34/1.00  sim_tautology_del:                      0
% 3.34/1.00  sim_eq_tautology_del:                   0
% 3.34/1.00  sim_eq_res_simp:                        0
% 3.34/1.00  sim_fw_demodulated:                     3
% 3.34/1.00  sim_bw_demodulated:                     16
% 3.34/1.00  sim_light_normalised:                   16
% 3.34/1.00  sim_joinable_taut:                      0
% 3.34/1.00  sim_joinable_simp:                      0
% 3.34/1.00  sim_ac_normalised:                      0
% 3.34/1.00  sim_smt_subsumption:                    0
% 3.34/1.00  
%------------------------------------------------------------------------------
