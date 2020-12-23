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
% DateTime   : Thu Dec  3 12:07:23 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :  196 (1294 expanded)
%              Number of clauses        :  121 ( 423 expanded)
%              Number of leaves         :   17 ( 242 expanded)
%              Depth                    :   27
%              Number of atoms          :  599 (5701 expanded)
%              Number of equality atoms :  207 ( 554 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f47])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
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

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f54,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f77,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_624,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_947,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_2,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | sK1 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_391,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v2_funct_1(sK1)
    | ~ v1_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_393,plain,
    ( v2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_27,c_24])).

cnf(c_469,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_393])).

cnf(c_470,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_469])).

cnf(c_472,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_470,c_27])).

cnf(c_616,plain,
    ( ~ v1_relat_1(sK1)
    | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_472])).

cnf(c_952,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_682,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1425,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_952,c_24,c_682,c_616])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | k1_relset_1(X0_50,X1_50,X0_49) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_940,plain,
    ( k1_relset_1(X0_50,X1_50,X0_49) = k1_relat_1(X0_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1328,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_947,c_940])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_419,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_421,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_27,c_24])).

cnf(c_620,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_1333,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1328,c_620])).

cnf(c_1427,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1425,c_1333])).

cnf(c_19,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_626,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),k2_relat_1(X0_49))))
    | ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_945,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),k2_relat_1(X0_49)))) = iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_1796,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0))) = iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1427,c_945])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_455,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_393])).

cnf(c_456,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_458,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_27])).

cnf(c_617,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_458])).

cnf(c_951,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_308,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_15])).

cnf(c_320,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_308,c_6])).

cnf(c_351,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_320])).

cnf(c_352,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2
    | sK1 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_25])).

cnf(c_381,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_385,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_27,c_24,c_383])).

cnf(c_622,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(subtyping,[status(esa)],[c_385])).

cnf(c_965,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_951,c_622])).

cnf(c_31,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_681,plain,
    ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_relat_1(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_683,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_1096,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_965,c_31,c_683])).

cnf(c_1826,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1796,c_1096])).

cnf(c_28,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_634,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_675,plain,
    ( v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_1(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_677,plain,
    ( v1_relat_1(sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_633,plain,
    ( ~ v1_relat_1(X0_49)
    | v1_relat_1(k2_funct_1(X0_49))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_678,plain,
    ( v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(k2_funct_1(X0_49)) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_680,plain,
    ( v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_2292,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1826,c_28,c_31,c_677,c_680,c_683])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_627,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_944,plain,
    ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_2302,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1))
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_944])).

cnf(c_3124,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2302,c_28,c_31,c_677,c_683])).

cnf(c_3125,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1))
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_3124])).

cnf(c_3133,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_3125])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_427,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_393])).

cnf(c_428,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_430,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_27])).

cnf(c_619,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_430])).

cnf(c_949,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_1520,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_949,c_24,c_682,c_619])).

cnf(c_1522,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1520,c_1333])).

cnf(c_3153,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3133,c_1522])).

cnf(c_3165,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3153,c_28])).

cnf(c_1856,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_947,c_944])).

cnf(c_2019,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1856,c_28])).

cnf(c_2020,plain,
    ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1)
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_2019])).

cnf(c_2297,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2292,c_2020])).

cnf(c_4,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_441,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_393])).

cnf(c_442,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_444,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_27])).

cnf(c_618,plain,
    ( ~ v1_relat_1(sK1)
    | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_444])).

cnf(c_950,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_982,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_950,c_622])).

cnf(c_1100,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_982,c_31,c_683])).

cnf(c_2331,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2297,c_1100])).

cnf(c_2866,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2331,c_28,c_31,c_677,c_683])).

cnf(c_23,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_625,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_946,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_401,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_402,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_404,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_27,c_26,c_24])).

cnf(c_621,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(subtyping,[status(esa)],[c_404])).

cnf(c_1021,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_946,c_621])).

cnf(c_2869,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2866,c_1021])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_49,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_51,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_630,plain,
    ( r2_relset_1(X0_50,X1_50,X0_49,X0_49)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1433,plain,
    ( r2_relset_1(X0_50,X1_50,k6_partfun1(X2_50),k6_partfun1(X2_50))
    | ~ m1_subset_1(k6_partfun1(X2_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_1436,plain,
    ( r2_relset_1(X0_50,X1_50,k6_partfun1(X2_50),k6_partfun1(X2_50)) = iProver_top
    | m1_subset_1(k6_partfun1(X2_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1433])).

cnf(c_1438,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_3003,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2869,c_51,c_1438])).

cnf(c_3168,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3165,c_3003])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3168,c_1438,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:58:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.87/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/0.99  
% 2.87/0.99  ------  iProver source info
% 2.87/0.99  
% 2.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/0.99  git: non_committed_changes: false
% 2.87/0.99  git: last_make_outside_of_git: false
% 2.87/0.99  
% 2.87/0.99  ------ 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options
% 2.87/0.99  
% 2.87/0.99  --out_options                           all
% 2.87/0.99  --tptp_safe_out                         true
% 2.87/0.99  --problem_path                          ""
% 2.87/0.99  --include_path                          ""
% 2.87/0.99  --clausifier                            res/vclausify_rel
% 2.87/0.99  --clausifier_options                    --mode clausify
% 2.87/0.99  --stdin                                 false
% 2.87/0.99  --stats_out                             all
% 2.87/0.99  
% 2.87/0.99  ------ General Options
% 2.87/0.99  
% 2.87/0.99  --fof                                   false
% 2.87/0.99  --time_out_real                         305.
% 2.87/0.99  --time_out_virtual                      -1.
% 2.87/0.99  --symbol_type_check                     false
% 2.87/0.99  --clausify_out                          false
% 2.87/0.99  --sig_cnt_out                           false
% 2.87/0.99  --trig_cnt_out                          false
% 2.87/0.99  --trig_cnt_out_tolerance                1.
% 2.87/0.99  --trig_cnt_out_sk_spl                   false
% 2.87/0.99  --abstr_cl_out                          false
% 2.87/0.99  
% 2.87/0.99  ------ Global Options
% 2.87/0.99  
% 2.87/0.99  --schedule                              default
% 2.87/0.99  --add_important_lit                     false
% 2.87/0.99  --prop_solver_per_cl                    1000
% 2.87/0.99  --min_unsat_core                        false
% 2.87/0.99  --soft_assumptions                      false
% 2.87/0.99  --soft_lemma_size                       3
% 2.87/0.99  --prop_impl_unit_size                   0
% 2.87/0.99  --prop_impl_unit                        []
% 2.87/0.99  --share_sel_clauses                     true
% 2.87/0.99  --reset_solvers                         false
% 2.87/0.99  --bc_imp_inh                            [conj_cone]
% 2.87/0.99  --conj_cone_tolerance                   3.
% 2.87/0.99  --extra_neg_conj                        none
% 2.87/0.99  --large_theory_mode                     true
% 2.87/0.99  --prolific_symb_bound                   200
% 2.87/0.99  --lt_threshold                          2000
% 2.87/0.99  --clause_weak_htbl                      true
% 2.87/0.99  --gc_record_bc_elim                     false
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing Options
% 2.87/0.99  
% 2.87/0.99  --preprocessing_flag                    true
% 2.87/0.99  --time_out_prep_mult                    0.1
% 2.87/0.99  --splitting_mode                        input
% 2.87/0.99  --splitting_grd                         true
% 2.87/0.99  --splitting_cvd                         false
% 2.87/0.99  --splitting_cvd_svl                     false
% 2.87/0.99  --splitting_nvd                         32
% 2.87/0.99  --sub_typing                            true
% 2.87/0.99  --prep_gs_sim                           true
% 2.87/0.99  --prep_unflatten                        true
% 2.87/0.99  --prep_res_sim                          true
% 2.87/0.99  --prep_upred                            true
% 2.87/0.99  --prep_sem_filter                       exhaustive
% 2.87/0.99  --prep_sem_filter_out                   false
% 2.87/0.99  --pred_elim                             true
% 2.87/0.99  --res_sim_input                         true
% 2.87/0.99  --eq_ax_congr_red                       true
% 2.87/0.99  --pure_diseq_elim                       true
% 2.87/0.99  --brand_transform                       false
% 2.87/0.99  --non_eq_to_eq                          false
% 2.87/0.99  --prep_def_merge                        true
% 2.87/0.99  --prep_def_merge_prop_impl              false
% 2.87/0.99  --prep_def_merge_mbd                    true
% 2.87/0.99  --prep_def_merge_tr_red                 false
% 2.87/0.99  --prep_def_merge_tr_cl                  false
% 2.87/0.99  --smt_preprocessing                     true
% 2.87/0.99  --smt_ac_axioms                         fast
% 2.87/0.99  --preprocessed_out                      false
% 2.87/0.99  --preprocessed_stats                    false
% 2.87/0.99  
% 2.87/0.99  ------ Abstraction refinement Options
% 2.87/0.99  
% 2.87/0.99  --abstr_ref                             []
% 2.87/0.99  --abstr_ref_prep                        false
% 2.87/0.99  --abstr_ref_until_sat                   false
% 2.87/0.99  --abstr_ref_sig_restrict                funpre
% 2.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.99  --abstr_ref_under                       []
% 2.87/0.99  
% 2.87/0.99  ------ SAT Options
% 2.87/0.99  
% 2.87/0.99  --sat_mode                              false
% 2.87/0.99  --sat_fm_restart_options                ""
% 2.87/0.99  --sat_gr_def                            false
% 2.87/0.99  --sat_epr_types                         true
% 2.87/0.99  --sat_non_cyclic_types                  false
% 2.87/0.99  --sat_finite_models                     false
% 2.87/0.99  --sat_fm_lemmas                         false
% 2.87/0.99  --sat_fm_prep                           false
% 2.87/0.99  --sat_fm_uc_incr                        true
% 2.87/0.99  --sat_out_model                         small
% 2.87/0.99  --sat_out_clauses                       false
% 2.87/0.99  
% 2.87/0.99  ------ QBF Options
% 2.87/0.99  
% 2.87/0.99  --qbf_mode                              false
% 2.87/0.99  --qbf_elim_univ                         false
% 2.87/0.99  --qbf_dom_inst                          none
% 2.87/0.99  --qbf_dom_pre_inst                      false
% 2.87/0.99  --qbf_sk_in                             false
% 2.87/0.99  --qbf_pred_elim                         true
% 2.87/0.99  --qbf_split                             512
% 2.87/0.99  
% 2.87/0.99  ------ BMC1 Options
% 2.87/0.99  
% 2.87/0.99  --bmc1_incremental                      false
% 2.87/0.99  --bmc1_axioms                           reachable_all
% 2.87/0.99  --bmc1_min_bound                        0
% 2.87/0.99  --bmc1_max_bound                        -1
% 2.87/0.99  --bmc1_max_bound_default                -1
% 2.87/0.99  --bmc1_symbol_reachability              true
% 2.87/0.99  --bmc1_property_lemmas                  false
% 2.87/0.99  --bmc1_k_induction                      false
% 2.87/0.99  --bmc1_non_equiv_states                 false
% 2.87/0.99  --bmc1_deadlock                         false
% 2.87/0.99  --bmc1_ucm                              false
% 2.87/0.99  --bmc1_add_unsat_core                   none
% 2.87/0.99  --bmc1_unsat_core_children              false
% 2.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.99  --bmc1_out_stat                         full
% 2.87/0.99  --bmc1_ground_init                      false
% 2.87/0.99  --bmc1_pre_inst_next_state              false
% 2.87/0.99  --bmc1_pre_inst_state                   false
% 2.87/0.99  --bmc1_pre_inst_reach_state             false
% 2.87/0.99  --bmc1_out_unsat_core                   false
% 2.87/0.99  --bmc1_aig_witness_out                  false
% 2.87/0.99  --bmc1_verbose                          false
% 2.87/0.99  --bmc1_dump_clauses_tptp                false
% 2.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.99  --bmc1_dump_file                        -
% 2.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.99  --bmc1_ucm_extend_mode                  1
% 2.87/0.99  --bmc1_ucm_init_mode                    2
% 2.87/0.99  --bmc1_ucm_cone_mode                    none
% 2.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.99  --bmc1_ucm_relax_model                  4
% 2.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.99  --bmc1_ucm_layered_model                none
% 2.87/0.99  --bmc1_ucm_max_lemma_size               10
% 2.87/0.99  
% 2.87/0.99  ------ AIG Options
% 2.87/0.99  
% 2.87/0.99  --aig_mode                              false
% 2.87/0.99  
% 2.87/0.99  ------ Instantiation Options
% 2.87/0.99  
% 2.87/0.99  --instantiation_flag                    true
% 2.87/0.99  --inst_sos_flag                         false
% 2.87/0.99  --inst_sos_phase                        true
% 2.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel_side                     num_symb
% 2.87/0.99  --inst_solver_per_active                1400
% 2.87/0.99  --inst_solver_calls_frac                1.
% 2.87/0.99  --inst_passive_queue_type               priority_queues
% 2.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.99  --inst_passive_queues_freq              [25;2]
% 2.87/0.99  --inst_dismatching                      true
% 2.87/0.99  --inst_eager_unprocessed_to_passive     true
% 2.87/0.99  --inst_prop_sim_given                   true
% 2.87/0.99  --inst_prop_sim_new                     false
% 2.87/0.99  --inst_subs_new                         false
% 2.87/0.99  --inst_eq_res_simp                      false
% 2.87/0.99  --inst_subs_given                       false
% 2.87/0.99  --inst_orphan_elimination               true
% 2.87/0.99  --inst_learning_loop_flag               true
% 2.87/0.99  --inst_learning_start                   3000
% 2.87/0.99  --inst_learning_factor                  2
% 2.87/0.99  --inst_start_prop_sim_after_learn       3
% 2.87/0.99  --inst_sel_renew                        solver
% 2.87/0.99  --inst_lit_activity_flag                true
% 2.87/0.99  --inst_restr_to_given                   false
% 2.87/0.99  --inst_activity_threshold               500
% 2.87/0.99  --inst_out_proof                        true
% 2.87/0.99  
% 2.87/0.99  ------ Resolution Options
% 2.87/0.99  
% 2.87/0.99  --resolution_flag                       true
% 2.87/0.99  --res_lit_sel                           adaptive
% 2.87/0.99  --res_lit_sel_side                      none
% 2.87/0.99  --res_ordering                          kbo
% 2.87/0.99  --res_to_prop_solver                    active
% 2.87/0.99  --res_prop_simpl_new                    false
% 2.87/0.99  --res_prop_simpl_given                  true
% 2.87/0.99  --res_passive_queue_type                priority_queues
% 2.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.99  --res_passive_queues_freq               [15;5]
% 2.87/0.99  --res_forward_subs                      full
% 2.87/0.99  --res_backward_subs                     full
% 2.87/0.99  --res_forward_subs_resolution           true
% 2.87/0.99  --res_backward_subs_resolution          true
% 2.87/0.99  --res_orphan_elimination                true
% 2.87/0.99  --res_time_limit                        2.
% 2.87/0.99  --res_out_proof                         true
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Options
% 2.87/0.99  
% 2.87/0.99  --superposition_flag                    true
% 2.87/0.99  --sup_passive_queue_type                priority_queues
% 2.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.99  --demod_completeness_check              fast
% 2.87/0.99  --demod_use_ground                      true
% 2.87/0.99  --sup_to_prop_solver                    passive
% 2.87/0.99  --sup_prop_simpl_new                    true
% 2.87/0.99  --sup_prop_simpl_given                  true
% 2.87/0.99  --sup_fun_splitting                     false
% 2.87/0.99  --sup_smt_interval                      50000
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Simplification Setup
% 2.87/0.99  
% 2.87/0.99  --sup_indices_passive                   []
% 2.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_full_bw                           [BwDemod]
% 2.87/0.99  --sup_immed_triv                        [TrivRules]
% 2.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_immed_bw_main                     []
% 2.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  
% 2.87/0.99  ------ Combination Options
% 2.87/0.99  
% 2.87/0.99  --comb_res_mult                         3
% 2.87/0.99  --comb_sup_mult                         2
% 2.87/0.99  --comb_inst_mult                        10
% 2.87/0.99  
% 2.87/0.99  ------ Debug Options
% 2.87/0.99  
% 2.87/0.99  --dbg_backtrace                         false
% 2.87/0.99  --dbg_dump_prop_clauses                 false
% 2.87/0.99  --dbg_dump_prop_clauses_file            -
% 2.87/0.99  --dbg_out_stat                          false
% 2.87/0.99  ------ Parsing...
% 2.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/0.99  ------ Proving...
% 2.87/0.99  ------ Problem Properties 
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  clauses                                 19
% 2.87/0.99  conjectures                             3
% 2.87/0.99  EPR                                     1
% 2.87/0.99  Horn                                    19
% 2.87/0.99  unary                                   6
% 2.87/0.99  binary                                  8
% 2.87/0.99  lits                                    40
% 2.87/0.99  lits eq                                 10
% 2.87/0.99  fd_pure                                 0
% 2.87/0.99  fd_pseudo                               0
% 2.87/0.99  fd_cond                                 0
% 2.87/0.99  fd_pseudo_cond                          1
% 2.87/0.99  AC symbols                              0
% 2.87/0.99  
% 2.87/0.99  ------ Schedule dynamic 5 is on 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  ------ 
% 2.87/0.99  Current options:
% 2.87/0.99  ------ 
% 2.87/0.99  
% 2.87/0.99  ------ Input Options
% 2.87/0.99  
% 2.87/0.99  --out_options                           all
% 2.87/0.99  --tptp_safe_out                         true
% 2.87/0.99  --problem_path                          ""
% 2.87/0.99  --include_path                          ""
% 2.87/0.99  --clausifier                            res/vclausify_rel
% 2.87/0.99  --clausifier_options                    --mode clausify
% 2.87/0.99  --stdin                                 false
% 2.87/0.99  --stats_out                             all
% 2.87/0.99  
% 2.87/0.99  ------ General Options
% 2.87/0.99  
% 2.87/0.99  --fof                                   false
% 2.87/0.99  --time_out_real                         305.
% 2.87/0.99  --time_out_virtual                      -1.
% 2.87/0.99  --symbol_type_check                     false
% 2.87/0.99  --clausify_out                          false
% 2.87/0.99  --sig_cnt_out                           false
% 2.87/0.99  --trig_cnt_out                          false
% 2.87/0.99  --trig_cnt_out_tolerance                1.
% 2.87/0.99  --trig_cnt_out_sk_spl                   false
% 2.87/0.99  --abstr_cl_out                          false
% 2.87/0.99  
% 2.87/0.99  ------ Global Options
% 2.87/0.99  
% 2.87/0.99  --schedule                              default
% 2.87/0.99  --add_important_lit                     false
% 2.87/0.99  --prop_solver_per_cl                    1000
% 2.87/0.99  --min_unsat_core                        false
% 2.87/0.99  --soft_assumptions                      false
% 2.87/0.99  --soft_lemma_size                       3
% 2.87/0.99  --prop_impl_unit_size                   0
% 2.87/0.99  --prop_impl_unit                        []
% 2.87/0.99  --share_sel_clauses                     true
% 2.87/0.99  --reset_solvers                         false
% 2.87/0.99  --bc_imp_inh                            [conj_cone]
% 2.87/0.99  --conj_cone_tolerance                   3.
% 2.87/0.99  --extra_neg_conj                        none
% 2.87/0.99  --large_theory_mode                     true
% 2.87/0.99  --prolific_symb_bound                   200
% 2.87/0.99  --lt_threshold                          2000
% 2.87/0.99  --clause_weak_htbl                      true
% 2.87/0.99  --gc_record_bc_elim                     false
% 2.87/0.99  
% 2.87/0.99  ------ Preprocessing Options
% 2.87/0.99  
% 2.87/0.99  --preprocessing_flag                    true
% 2.87/0.99  --time_out_prep_mult                    0.1
% 2.87/0.99  --splitting_mode                        input
% 2.87/0.99  --splitting_grd                         true
% 2.87/0.99  --splitting_cvd                         false
% 2.87/0.99  --splitting_cvd_svl                     false
% 2.87/0.99  --splitting_nvd                         32
% 2.87/0.99  --sub_typing                            true
% 2.87/0.99  --prep_gs_sim                           true
% 2.87/0.99  --prep_unflatten                        true
% 2.87/0.99  --prep_res_sim                          true
% 2.87/0.99  --prep_upred                            true
% 2.87/0.99  --prep_sem_filter                       exhaustive
% 2.87/0.99  --prep_sem_filter_out                   false
% 2.87/0.99  --pred_elim                             true
% 2.87/0.99  --res_sim_input                         true
% 2.87/0.99  --eq_ax_congr_red                       true
% 2.87/0.99  --pure_diseq_elim                       true
% 2.87/0.99  --brand_transform                       false
% 2.87/0.99  --non_eq_to_eq                          false
% 2.87/0.99  --prep_def_merge                        true
% 2.87/0.99  --prep_def_merge_prop_impl              false
% 2.87/0.99  --prep_def_merge_mbd                    true
% 2.87/0.99  --prep_def_merge_tr_red                 false
% 2.87/0.99  --prep_def_merge_tr_cl                  false
% 2.87/0.99  --smt_preprocessing                     true
% 2.87/0.99  --smt_ac_axioms                         fast
% 2.87/0.99  --preprocessed_out                      false
% 2.87/0.99  --preprocessed_stats                    false
% 2.87/0.99  
% 2.87/0.99  ------ Abstraction refinement Options
% 2.87/0.99  
% 2.87/0.99  --abstr_ref                             []
% 2.87/0.99  --abstr_ref_prep                        false
% 2.87/0.99  --abstr_ref_until_sat                   false
% 2.87/0.99  --abstr_ref_sig_restrict                funpre
% 2.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.99  --abstr_ref_under                       []
% 2.87/0.99  
% 2.87/0.99  ------ SAT Options
% 2.87/0.99  
% 2.87/0.99  --sat_mode                              false
% 2.87/0.99  --sat_fm_restart_options                ""
% 2.87/0.99  --sat_gr_def                            false
% 2.87/0.99  --sat_epr_types                         true
% 2.87/0.99  --sat_non_cyclic_types                  false
% 2.87/0.99  --sat_finite_models                     false
% 2.87/0.99  --sat_fm_lemmas                         false
% 2.87/0.99  --sat_fm_prep                           false
% 2.87/0.99  --sat_fm_uc_incr                        true
% 2.87/0.99  --sat_out_model                         small
% 2.87/0.99  --sat_out_clauses                       false
% 2.87/0.99  
% 2.87/0.99  ------ QBF Options
% 2.87/0.99  
% 2.87/0.99  --qbf_mode                              false
% 2.87/0.99  --qbf_elim_univ                         false
% 2.87/0.99  --qbf_dom_inst                          none
% 2.87/0.99  --qbf_dom_pre_inst                      false
% 2.87/0.99  --qbf_sk_in                             false
% 2.87/0.99  --qbf_pred_elim                         true
% 2.87/0.99  --qbf_split                             512
% 2.87/0.99  
% 2.87/0.99  ------ BMC1 Options
% 2.87/0.99  
% 2.87/0.99  --bmc1_incremental                      false
% 2.87/0.99  --bmc1_axioms                           reachable_all
% 2.87/0.99  --bmc1_min_bound                        0
% 2.87/0.99  --bmc1_max_bound                        -1
% 2.87/0.99  --bmc1_max_bound_default                -1
% 2.87/0.99  --bmc1_symbol_reachability              true
% 2.87/0.99  --bmc1_property_lemmas                  false
% 2.87/0.99  --bmc1_k_induction                      false
% 2.87/0.99  --bmc1_non_equiv_states                 false
% 2.87/0.99  --bmc1_deadlock                         false
% 2.87/0.99  --bmc1_ucm                              false
% 2.87/0.99  --bmc1_add_unsat_core                   none
% 2.87/0.99  --bmc1_unsat_core_children              false
% 2.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.99  --bmc1_out_stat                         full
% 2.87/0.99  --bmc1_ground_init                      false
% 2.87/0.99  --bmc1_pre_inst_next_state              false
% 2.87/0.99  --bmc1_pre_inst_state                   false
% 2.87/0.99  --bmc1_pre_inst_reach_state             false
% 2.87/0.99  --bmc1_out_unsat_core                   false
% 2.87/0.99  --bmc1_aig_witness_out                  false
% 2.87/0.99  --bmc1_verbose                          false
% 2.87/0.99  --bmc1_dump_clauses_tptp                false
% 2.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.99  --bmc1_dump_file                        -
% 2.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.99  --bmc1_ucm_extend_mode                  1
% 2.87/0.99  --bmc1_ucm_init_mode                    2
% 2.87/0.99  --bmc1_ucm_cone_mode                    none
% 2.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.99  --bmc1_ucm_relax_model                  4
% 2.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.99  --bmc1_ucm_layered_model                none
% 2.87/0.99  --bmc1_ucm_max_lemma_size               10
% 2.87/0.99  
% 2.87/0.99  ------ AIG Options
% 2.87/0.99  
% 2.87/0.99  --aig_mode                              false
% 2.87/0.99  
% 2.87/0.99  ------ Instantiation Options
% 2.87/0.99  
% 2.87/0.99  --instantiation_flag                    true
% 2.87/0.99  --inst_sos_flag                         false
% 2.87/0.99  --inst_sos_phase                        true
% 2.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.99  --inst_lit_sel_side                     none
% 2.87/0.99  --inst_solver_per_active                1400
% 2.87/0.99  --inst_solver_calls_frac                1.
% 2.87/0.99  --inst_passive_queue_type               priority_queues
% 2.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.99  --inst_passive_queues_freq              [25;2]
% 2.87/0.99  --inst_dismatching                      true
% 2.87/0.99  --inst_eager_unprocessed_to_passive     true
% 2.87/0.99  --inst_prop_sim_given                   true
% 2.87/0.99  --inst_prop_sim_new                     false
% 2.87/0.99  --inst_subs_new                         false
% 2.87/0.99  --inst_eq_res_simp                      false
% 2.87/0.99  --inst_subs_given                       false
% 2.87/0.99  --inst_orphan_elimination               true
% 2.87/0.99  --inst_learning_loop_flag               true
% 2.87/0.99  --inst_learning_start                   3000
% 2.87/0.99  --inst_learning_factor                  2
% 2.87/0.99  --inst_start_prop_sim_after_learn       3
% 2.87/0.99  --inst_sel_renew                        solver
% 2.87/0.99  --inst_lit_activity_flag                true
% 2.87/0.99  --inst_restr_to_given                   false
% 2.87/0.99  --inst_activity_threshold               500
% 2.87/0.99  --inst_out_proof                        true
% 2.87/0.99  
% 2.87/0.99  ------ Resolution Options
% 2.87/0.99  
% 2.87/0.99  --resolution_flag                       false
% 2.87/0.99  --res_lit_sel                           adaptive
% 2.87/0.99  --res_lit_sel_side                      none
% 2.87/0.99  --res_ordering                          kbo
% 2.87/0.99  --res_to_prop_solver                    active
% 2.87/0.99  --res_prop_simpl_new                    false
% 2.87/0.99  --res_prop_simpl_given                  true
% 2.87/0.99  --res_passive_queue_type                priority_queues
% 2.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.99  --res_passive_queues_freq               [15;5]
% 2.87/0.99  --res_forward_subs                      full
% 2.87/0.99  --res_backward_subs                     full
% 2.87/0.99  --res_forward_subs_resolution           true
% 2.87/0.99  --res_backward_subs_resolution          true
% 2.87/0.99  --res_orphan_elimination                true
% 2.87/0.99  --res_time_limit                        2.
% 2.87/0.99  --res_out_proof                         true
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Options
% 2.87/0.99  
% 2.87/0.99  --superposition_flag                    true
% 2.87/0.99  --sup_passive_queue_type                priority_queues
% 2.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.99  --demod_completeness_check              fast
% 2.87/0.99  --demod_use_ground                      true
% 2.87/0.99  --sup_to_prop_solver                    passive
% 2.87/0.99  --sup_prop_simpl_new                    true
% 2.87/0.99  --sup_prop_simpl_given                  true
% 2.87/0.99  --sup_fun_splitting                     false
% 2.87/0.99  --sup_smt_interval                      50000
% 2.87/0.99  
% 2.87/0.99  ------ Superposition Simplification Setup
% 2.87/0.99  
% 2.87/0.99  --sup_indices_passive                   []
% 2.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_full_bw                           [BwDemod]
% 2.87/0.99  --sup_immed_triv                        [TrivRules]
% 2.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_immed_bw_main                     []
% 2.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.99  
% 2.87/0.99  ------ Combination Options
% 2.87/0.99  
% 2.87/0.99  --comb_res_mult                         3
% 2.87/0.99  --comb_sup_mult                         2
% 2.87/0.99  --comb_inst_mult                        10
% 2.87/0.99  
% 2.87/0.99  ------ Debug Options
% 2.87/0.99  
% 2.87/0.99  --dbg_backtrace                         false
% 2.87/0.99  --dbg_dump_prop_clauses                 false
% 2.87/0.99  --dbg_dump_prop_clauses_file            -
% 2.87/0.99  --dbg_out_stat                          false
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  ------ Proving...
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  % SZS status Theorem for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/0.99  
% 2.87/0.99  fof(f16,conjecture,(
% 2.87/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f17,negated_conjecture,(
% 2.87/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 2.87/0.99    inference(negated_conjecture,[],[f16])).
% 2.87/0.99  
% 2.87/0.99  fof(f43,plain,(
% 2.87/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 2.87/0.99    inference(ennf_transformation,[],[f17])).
% 2.87/0.99  
% 2.87/0.99  fof(f44,plain,(
% 2.87/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 2.87/0.99    inference(flattening,[],[f43])).
% 2.87/0.99  
% 2.87/0.99  fof(f47,plain,(
% 2.87/0.99    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 2.87/0.99    introduced(choice_axiom,[])).
% 2.87/0.99  
% 2.87/0.99  fof(f48,plain,(
% 2.87/0.99    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 2.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f47])).
% 2.87/0.99  
% 2.87/0.99  fof(f76,plain,(
% 2.87/0.99    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.87/0.99    inference(cnf_transformation,[],[f48])).
% 2.87/0.99  
% 2.87/0.99  fof(f2,axiom,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f22,plain,(
% 2.87/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/0.99    inference(ennf_transformation,[],[f2])).
% 2.87/0.99  
% 2.87/0.99  fof(f23,plain,(
% 2.87/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(flattening,[],[f22])).
% 2.87/0.99  
% 2.87/0.99  fof(f52,plain,(
% 2.87/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f23])).
% 2.87/0.99  
% 2.87/0.99  fof(f8,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f31,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f8])).
% 2.87/0.99  
% 2.87/0.99  fof(f32,plain,(
% 2.87/0.99    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(flattening,[],[f31])).
% 2.87/0.99  
% 2.87/0.99  fof(f61,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f32])).
% 2.87/0.99  
% 2.87/0.99  fof(f75,plain,(
% 2.87/0.99    v3_funct_2(sK1,sK0,sK0)),
% 2.87/0.99    inference(cnf_transformation,[],[f48])).
% 2.87/0.99  
% 2.87/0.99  fof(f73,plain,(
% 2.87/0.99    v1_funct_1(sK1)),
% 2.87/0.99    inference(cnf_transformation,[],[f48])).
% 2.87/0.99  
% 2.87/0.99  fof(f4,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f26,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f4])).
% 2.87/0.99  
% 2.87/0.99  fof(f55,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f26])).
% 2.87/0.99  
% 2.87/0.99  fof(f6,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f28,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f6])).
% 2.87/0.99  
% 2.87/0.99  fof(f57,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f28])).
% 2.87/0.99  
% 2.87/0.99  fof(f15,axiom,(
% 2.87/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f41,plain,(
% 2.87/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.87/0.99    inference(ennf_transformation,[],[f15])).
% 2.87/0.99  
% 2.87/0.99  fof(f42,plain,(
% 2.87/0.99    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.87/0.99    inference(flattening,[],[f41])).
% 2.87/0.99  
% 2.87/0.99  fof(f72,plain,(
% 2.87/0.99    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f42])).
% 2.87/0.99  
% 2.87/0.99  fof(f74,plain,(
% 2.87/0.99    v1_funct_2(sK1,sK0,sK0)),
% 2.87/0.99    inference(cnf_transformation,[],[f48])).
% 2.87/0.99  
% 2.87/0.99  fof(f14,axiom,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f39,plain,(
% 2.87/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/0.99    inference(ennf_transformation,[],[f14])).
% 2.87/0.99  
% 2.87/0.99  fof(f40,plain,(
% 2.87/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(flattening,[],[f39])).
% 2.87/0.99  
% 2.87/0.99  fof(f71,plain,(
% 2.87/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f40])).
% 2.87/0.99  
% 2.87/0.99  fof(f51,plain,(
% 2.87/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f23])).
% 2.87/0.99  
% 2.87/0.99  fof(f62,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f32])).
% 2.87/0.99  
% 2.87/0.99  fof(f5,axiom,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f19,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.87/0.99    inference(pure_predicate_removal,[],[f5])).
% 2.87/0.99  
% 2.87/0.99  fof(f27,plain,(
% 2.87/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(ennf_transformation,[],[f19])).
% 2.87/0.99  
% 2.87/0.99  fof(f56,plain,(
% 2.87/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f27])).
% 2.87/0.99  
% 2.87/0.99  fof(f9,axiom,(
% 2.87/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f33,plain,(
% 2.87/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.87/0.99    inference(ennf_transformation,[],[f9])).
% 2.87/0.99  
% 2.87/0.99  fof(f34,plain,(
% 2.87/0.99    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.87/0.99    inference(flattening,[],[f33])).
% 2.87/0.99  
% 2.87/0.99  fof(f46,plain,(
% 2.87/0.99    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.87/0.99    inference(nnf_transformation,[],[f34])).
% 2.87/0.99  
% 2.87/0.99  fof(f63,plain,(
% 2.87/0.99    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f46])).
% 2.87/0.99  
% 2.87/0.99  fof(f1,axiom,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f20,plain,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/0.99    inference(ennf_transformation,[],[f1])).
% 2.87/0.99  
% 2.87/0.99  fof(f21,plain,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(flattening,[],[f20])).
% 2.87/0.99  
% 2.87/0.99  fof(f50,plain,(
% 2.87/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f21])).
% 2.87/0.99  
% 2.87/0.99  fof(f49,plain,(
% 2.87/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f21])).
% 2.87/0.99  
% 2.87/0.99  fof(f11,axiom,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f35,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.87/0.99    inference(ennf_transformation,[],[f11])).
% 2.87/0.99  
% 2.87/0.99  fof(f36,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.87/0.99    inference(flattening,[],[f35])).
% 2.87/0.99  
% 2.87/0.99  fof(f66,plain,(
% 2.87/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f36])).
% 2.87/0.99  
% 2.87/0.99  fof(f3,axiom,(
% 2.87/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f24,plain,(
% 2.87/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.87/0.99    inference(ennf_transformation,[],[f3])).
% 2.87/0.99  
% 2.87/0.99  fof(f25,plain,(
% 2.87/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.87/0.99    inference(flattening,[],[f24])).
% 2.87/0.99  
% 2.87/0.99  fof(f53,plain,(
% 2.87/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f13,axiom,(
% 2.87/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f68,plain,(
% 2.87/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f13])).
% 2.87/0.99  
% 2.87/0.99  fof(f79,plain,(
% 2.87/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(definition_unfolding,[],[f53,f68])).
% 2.87/0.99  
% 2.87/0.99  fof(f54,plain,(
% 2.87/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f25])).
% 2.87/0.99  
% 2.87/0.99  fof(f78,plain,(
% 2.87/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.87/0.99    inference(definition_unfolding,[],[f54,f68])).
% 2.87/0.99  
% 2.87/0.99  fof(f77,plain,(
% 2.87/0.99    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 2.87/0.99    inference(cnf_transformation,[],[f48])).
% 2.87/0.99  
% 2.87/0.99  fof(f12,axiom,(
% 2.87/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f37,plain,(
% 2.87/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 2.87/0.99    inference(ennf_transformation,[],[f12])).
% 2.87/0.99  
% 2.87/0.99  fof(f38,plain,(
% 2.87/0.99    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 2.87/0.99    inference(flattening,[],[f37])).
% 2.87/0.99  
% 2.87/0.99  fof(f67,plain,(
% 2.87/0.99    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 2.87/0.99    inference(cnf_transformation,[],[f38])).
% 2.87/0.99  
% 2.87/0.99  fof(f10,axiom,(
% 2.87/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f18,plain,(
% 2.87/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.87/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.87/0.99  
% 2.87/0.99  fof(f65,plain,(
% 2.87/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f18])).
% 2.87/0.99  
% 2.87/0.99  fof(f7,axiom,(
% 2.87/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.99  
% 2.87/0.99  fof(f29,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.87/0.99    inference(ennf_transformation,[],[f7])).
% 2.87/0.99  
% 2.87/0.99  fof(f30,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(flattening,[],[f29])).
% 2.87/0.99  
% 2.87/0.99  fof(f45,plain,(
% 2.87/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.87/0.99    inference(nnf_transformation,[],[f30])).
% 2.87/0.99  
% 2.87/0.99  fof(f59,plain,(
% 2.87/0.99    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(cnf_transformation,[],[f45])).
% 2.87/0.99  
% 2.87/0.99  fof(f80,plain,(
% 2.87/0.99    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.87/0.99    inference(equality_resolution,[],[f59])).
% 2.87/0.99  
% 2.87/0.99  cnf(c_24,negated_conjecture,
% 2.87/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.87/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_624,negated_conjecture,
% 2.87/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_947,plain,
% 2.87/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.87/0.99      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_2,plain,
% 2.87/0.99      ( ~ v2_funct_1(X0)
% 2.87/0.99      | ~ v1_relat_1(X0)
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_12,plain,
% 2.87/0.99      ( ~ v3_funct_2(X0,X1,X2)
% 2.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | v2_funct_1(X0)
% 2.87/0.99      | ~ v1_funct_1(X0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_25,negated_conjecture,
% 2.87/0.99      ( v3_funct_2(sK1,sK0,sK0) ),
% 2.87/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_390,plain,
% 2.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/0.99      | v2_funct_1(X0)
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | sK1 != X0
% 2.87/0.99      | sK0 != X2
% 2.87/0.99      | sK0 != X1 ),
% 2.87/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_391,plain,
% 2.87/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.87/0.99      | v2_funct_1(sK1)
% 2.87/0.99      | ~ v1_funct_1(sK1) ),
% 2.87/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_27,negated_conjecture,
% 2.87/0.99      ( v1_funct_1(sK1) ),
% 2.87/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_393,plain,
% 2.87/0.99      ( v2_funct_1(sK1) ),
% 2.87/0.99      inference(global_propositional_subsumption,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_391,c_27,c_24]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_469,plain,
% 2.87/0.99      ( ~ v1_relat_1(X0)
% 2.87/0.99      | ~ v1_funct_1(X0)
% 2.87/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.87/0.99      | sK1 != X0 ),
% 2.87/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_393]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_470,plain,
% 2.87/0.99      ( ~ v1_relat_1(sK1)
% 2.87/0.99      | ~ v1_funct_1(sK1)
% 2.87/0.99      | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 2.87/0.99      inference(unflattening,[status(thm)],[c_469]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_472,plain,
% 2.87/0.99      ( ~ v1_relat_1(sK1)
% 2.87/0.99      | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 2.87/0.99      inference(global_propositional_subsumption,
% 2.87/0.99                [status(thm)],
% 2.87/0.99                [c_470,c_27]) ).
% 2.87/0.99  
% 2.87/0.99  cnf(c_616,plain,
% 2.87/0.99      ( ~ v1_relat_1(sK1)
% 2.87/0.99      | k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 2.87/0.99      inference(subtyping,[status(esa)],[c_472]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_952,plain,
% 2.87/1.00      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
% 2.87/1.00      | v1_relat_1(sK1) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_6,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | v1_relat_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_632,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.87/1.00      | v1_relat_1(X0_49) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_682,plain,
% 2.87/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.87/1.00      | v1_relat_1(sK1) ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_632]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1425,plain,
% 2.87/1.00      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_952,c_24,c_682,c_616]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_8,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_631,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.87/1.00      | k1_relset_1(X0_50,X1_50,X0_49) = k1_relat_1(X0_49) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_940,plain,
% 2.87/1.00      ( k1_relset_1(X0_50,X1_50,X0_49) = k1_relat_1(X0_49)
% 2.87/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1328,plain,
% 2.87/1.00      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_947,c_940]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_22,plain,
% 2.87/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_26,negated_conjecture,
% 2.87/1.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_418,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k1_relset_1(X1,X1,X0) = X1
% 2.87/1.00      | sK1 != X0
% 2.87/1.00      | sK0 != X1 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_419,plain,
% 2.87/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.87/1.00      | ~ v1_funct_1(sK1)
% 2.87/1.00      | k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_418]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_421,plain,
% 2.87/1.00      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_419,c_27,c_24]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_620,plain,
% 2.87/1.00      ( k1_relset_1(sK0,sK0,sK1) = sK0 ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_421]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1333,plain,
% 2.87/1.00      ( k1_relat_1(sK1) = sK0 ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_1328,c_620]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1427,plain,
% 2.87/1.00      ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_1425,c_1333]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_19,plain,
% 2.87/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_626,plain,
% 2.87/1.00      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),k2_relat_1(X0_49))))
% 2.87/1.00      | ~ v1_relat_1(X0_49)
% 2.87/1.00      | ~ v1_funct_1(X0_49) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_19]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_945,plain,
% 2.87/1.00      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_49),k2_relat_1(X0_49)))) = iProver_top
% 2.87/1.00      | v1_relat_1(X0_49) != iProver_top
% 2.87/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1796,plain,
% 2.87/1.00      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0))) = iProver_top
% 2.87/1.00      | v1_relat_1(k2_funct_1(sK1)) != iProver_top
% 2.87/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_1427,c_945]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3,plain,
% 2.87/1.00      ( ~ v2_funct_1(X0)
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_455,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.87/1.00      | sK1 != X0 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_393]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_456,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | ~ v1_funct_1(sK1)
% 2.87/1.00      | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_455]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_458,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_456,c_27]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_617,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_458]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_951,plain,
% 2.87/1.00      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
% 2.87/1.00      | v1_relat_1(sK1) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_11,plain,
% 2.87/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.87/1.00      | v2_funct_2(X0,X2)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | ~ v1_funct_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_7,plain,
% 2.87/1.00      ( v5_relat_1(X0,X1)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.87/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_15,plain,
% 2.87/1.00      ( ~ v2_funct_2(X0,X1)
% 2.87/1.00      | ~ v5_relat_1(X0,X1)
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | k2_relat_1(X0) = X1 ),
% 2.87/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_308,plain,
% 2.87/1.00      ( ~ v2_funct_2(X0,X1)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | k2_relat_1(X0) = X1 ),
% 2.87/1.00      inference(resolution,[status(thm)],[c_7,c_15]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_320,plain,
% 2.87/1.00      ( ~ v2_funct_2(X0,X1)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.87/1.00      | k2_relat_1(X0) = X1 ),
% 2.87/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_308,c_6]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_351,plain,
% 2.87/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | X3 != X0
% 2.87/1.00      | X5 != X2
% 2.87/1.00      | k2_relat_1(X3) = X5 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_320]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_352,plain,
% 2.87/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k2_relat_1(X0) = X2 ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_351]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_380,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k2_relat_1(X0) = X2
% 2.87/1.00      | sK1 != X0
% 2.87/1.00      | sK0 != X2
% 2.87/1.00      | sK0 != X1 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_352,c_25]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_381,plain,
% 2.87/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 2.87/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.87/1.00      | ~ v1_funct_1(sK1)
% 2.87/1.00      | k2_relat_1(sK1) = sK0 ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_380]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_383,plain,
% 2.87/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.87/1.00      | ~ v1_funct_1(sK1)
% 2.87/1.00      | k2_relat_1(sK1) = sK0 ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_381]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_385,plain,
% 2.87/1.00      ( k2_relat_1(sK1) = sK0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_381,c_27,c_24,c_383]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_622,plain,
% 2.87/1.00      ( k2_relat_1(sK1) = sK0 ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_385]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_965,plain,
% 2.87/1.00      ( k1_relat_1(k2_funct_1(sK1)) = sK0
% 2.87/1.00      | v1_relat_1(sK1) != iProver_top ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_951,c_622]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_31,plain,
% 2.87/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_681,plain,
% 2.87/1.00      ( m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.87/1.00      | v1_relat_1(X0_49) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_683,plain,
% 2.87/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 2.87/1.00      | v1_relat_1(sK1) = iProver_top ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_681]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1096,plain,
% 2.87/1.00      ( k1_relat_1(k2_funct_1(sK1)) = sK0 ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_965,c_31,c_683]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1826,plain,
% 2.87/1.00      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 2.87/1.00      | v1_relat_1(k2_funct_1(sK1)) != iProver_top
% 2.87/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_1796,c_1096]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_28,plain,
% 2.87/1.00      ( v1_funct_1(sK1) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_0,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | v1_funct_1(k2_funct_1(X0)) ),
% 2.87/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_634,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0_49)
% 2.87/1.00      | ~ v1_funct_1(X0_49)
% 2.87/1.00      | v1_funct_1(k2_funct_1(X0_49)) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_675,plain,
% 2.87/1.00      ( v1_relat_1(X0_49) != iProver_top
% 2.87/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.87/1.00      | v1_funct_1(k2_funct_1(X0_49)) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_677,plain,
% 2.87/1.00      ( v1_relat_1(sK1) != iProver_top
% 2.87/1.00      | v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 2.87/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_675]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0)
% 2.87/1.00      | v1_relat_1(k2_funct_1(X0))
% 2.87/1.00      | ~ v1_funct_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_633,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0_49)
% 2.87/1.00      | v1_relat_1(k2_funct_1(X0_49))
% 2.87/1.00      | ~ v1_funct_1(X0_49) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_678,plain,
% 2.87/1.00      ( v1_relat_1(X0_49) != iProver_top
% 2.87/1.00      | v1_relat_1(k2_funct_1(X0_49)) = iProver_top
% 2.87/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_680,plain,
% 2.87/1.00      ( v1_relat_1(k2_funct_1(sK1)) = iProver_top
% 2.87/1.00      | v1_relat_1(sK1) != iProver_top
% 2.87/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_678]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2292,plain,
% 2.87/1.00      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_1826,c_28,c_31,c_677,c_680,c_683]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_17,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.87/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X3)
% 2.87/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_627,plain,
% 2.87/1.00      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 2.87/1.00      | ~ m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50)))
% 2.87/1.00      | ~ v1_funct_1(X0_49)
% 2.87/1.00      | ~ v1_funct_1(X1_49)
% 2.87/1.00      | k1_partfun1(X2_50,X3_50,X0_50,X1_50,X1_49,X0_49) = k5_relat_1(X1_49,X0_49) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_944,plain,
% 2.87/1.00      ( k1_partfun1(X0_50,X1_50,X2_50,X3_50,X0_49,X1_49) = k5_relat_1(X0_49,X1_49)
% 2.87/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.87/1.00      | m1_subset_1(X1_49,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 2.87/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.87/1.00      | v1_funct_1(X1_49) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2302,plain,
% 2.87/1.00      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1))
% 2.87/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.87/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.87/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2292,c_944]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3124,plain,
% 2.87/1.00      ( v1_funct_1(X0_49) != iProver_top
% 2.87/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.87/1.00      | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1)) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_2302,c_28,c_31,c_677,c_683]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3125,plain,
% 2.87/1.00      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,k2_funct_1(sK1)) = k5_relat_1(X0_49,k2_funct_1(sK1))
% 2.87/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.87/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 2.87/1.00      inference(renaming,[status(thm)],[c_3124]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3133,plain,
% 2.87/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 2.87/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_947,c_3125]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_5,plain,
% 2.87/1.00      ( ~ v2_funct_1(X0)
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.87/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_427,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 2.87/1.00      | sK1 != X0 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_393]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_428,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | ~ v1_funct_1(sK1)
% 2.87/1.00      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_427]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_430,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_428,c_27]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_619,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_430]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_949,plain,
% 2.87/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 2.87/1.00      | v1_relat_1(sK1) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1520,plain,
% 2.87/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_949,c_24,c_682,c_619]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1522,plain,
% 2.87/1.00      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_1520,c_1333]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3153,plain,
% 2.87/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0)
% 2.87/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_3133,c_1522]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3165,plain,
% 2.87/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(sK0) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_3153,c_28]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1856,plain,
% 2.87/1.00      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1)
% 2.87/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.87/1.00      | v1_funct_1(X0_49) != iProver_top
% 2.87/1.00      | v1_funct_1(sK1) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_947,c_944]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2019,plain,
% 2.87/1.00      ( v1_funct_1(X0_49) != iProver_top
% 2.87/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.87/1.00      | k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_1856,c_28]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2020,plain,
% 2.87/1.00      ( k1_partfun1(X0_50,X1_50,sK0,sK0,X0_49,sK1) = k5_relat_1(X0_49,sK1)
% 2.87/1.00      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 2.87/1.00      | v1_funct_1(X0_49) != iProver_top ),
% 2.87/1.00      inference(renaming,[status(thm)],[c_2019]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2297,plain,
% 2.87/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 2.87/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 2.87/1.00      inference(superposition,[status(thm)],[c_2292,c_2020]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_4,plain,
% 2.87/1.00      ( ~ v2_funct_1(X0)
% 2.87/1.00      | ~ v1_relat_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 2.87/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_441,plain,
% 2.87/1.00      ( ~ v1_relat_1(X0)
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 2.87/1.00      | sK1 != X0 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_393]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_442,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | ~ v1_funct_1(sK1)
% 2.87/1.00      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_444,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_442,c_27]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_618,plain,
% 2.87/1.00      ( ~ v1_relat_1(sK1)
% 2.87/1.00      | k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_444]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_950,plain,
% 2.87/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 2.87/1.00      | v1_relat_1(sK1) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_982,plain,
% 2.87/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 2.87/1.00      | v1_relat_1(sK1) != iProver_top ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_950,c_622]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1100,plain,
% 2.87/1.00      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_982,c_31,c_683]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2331,plain,
% 2.87/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 2.87/1.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_2297,c_1100]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2866,plain,
% 2.87/1.00      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_2331,c_28,c_31,c_677,c_683]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_23,negated_conjecture,
% 2.87/1.00      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 2.87/1.00      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 2.87/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_625,negated_conjecture,
% 2.87/1.00      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 2.87/1.00      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_946,plain,
% 2.87/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 2.87/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_18,plain,
% 2.87/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.87/1.00      | ~ v3_funct_2(X0,X1,X1)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 2.87/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_401,plain,
% 2.87/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 2.87/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 2.87/1.00      | ~ v1_funct_1(X0)
% 2.87/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0)
% 2.87/1.00      | sK1 != X0
% 2.87/1.00      | sK0 != X1 ),
% 2.87/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_402,plain,
% 2.87/1.00      ( ~ v1_funct_2(sK1,sK0,sK0)
% 2.87/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 2.87/1.00      | ~ v1_funct_1(sK1)
% 2.87/1.00      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.87/1.00      inference(unflattening,[status(thm)],[c_401]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_404,plain,
% 2.87/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_402,c_27,c_26,c_24]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_621,plain,
% 2.87/1.00      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_404]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1021,plain,
% 2.87/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 2.87/1.00      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 2.87/1.00      inference(light_normalisation,[status(thm)],[c_946,c_621]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_2869,plain,
% 2.87/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 2.87/1.00      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_2866,c_1021]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_16,plain,
% 2.87/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 2.87/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_49,plain,
% 2.87/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_51,plain,
% 2.87/1.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_49]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_9,plain,
% 2.87/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 2.87/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.87/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_630,plain,
% 2.87/1.00      ( r2_relset_1(X0_50,X1_50,X0_49,X0_49)
% 2.87/1.00      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 2.87/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1433,plain,
% 2.87/1.00      ( r2_relset_1(X0_50,X1_50,k6_partfun1(X2_50),k6_partfun1(X2_50))
% 2.87/1.00      | ~ m1_subset_1(k6_partfun1(X2_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_630]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1436,plain,
% 2.87/1.00      ( r2_relset_1(X0_50,X1_50,k6_partfun1(X2_50),k6_partfun1(X2_50)) = iProver_top
% 2.87/1.00      | m1_subset_1(k6_partfun1(X2_50),k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top ),
% 2.87/1.00      inference(predicate_to_equality,[status(thm)],[c_1433]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_1438,plain,
% 2.87/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 2.87/1.00      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 2.87/1.00      inference(instantiation,[status(thm)],[c_1436]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3003,plain,
% 2.87/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 2.87/1.00      inference(global_propositional_subsumption,
% 2.87/1.00                [status(thm)],
% 2.87/1.00                [c_2869,c_51,c_1438]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(c_3168,plain,
% 2.87/1.00      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 2.87/1.00      inference(demodulation,[status(thm)],[c_3165,c_3003]) ).
% 2.87/1.00  
% 2.87/1.00  cnf(contradiction,plain,
% 2.87/1.00      ( $false ),
% 2.87/1.00      inference(minisat,[status(thm)],[c_3168,c_1438,c_51]) ).
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/1.00  
% 2.87/1.00  ------                               Statistics
% 2.87/1.00  
% 2.87/1.00  ------ General
% 2.87/1.00  
% 2.87/1.00  abstr_ref_over_cycles:                  0
% 2.87/1.00  abstr_ref_under_cycles:                 0
% 2.87/1.00  gc_basic_clause_elim:                   0
% 2.87/1.00  forced_gc_time:                         0
% 2.87/1.00  parsing_time:                           0.006
% 2.87/1.00  unif_index_cands_time:                  0.
% 2.87/1.00  unif_index_add_time:                    0.
% 2.87/1.00  orderings_time:                         0.
% 2.87/1.00  out_proof_time:                         0.013
% 2.87/1.00  total_time:                             0.148
% 2.87/1.00  num_of_symbols:                         56
% 2.87/1.00  num_of_terms:                           3269
% 2.87/1.00  
% 2.87/1.00  ------ Preprocessing
% 2.87/1.00  
% 2.87/1.00  num_of_splits:                          0
% 2.87/1.00  num_of_split_atoms:                     0
% 2.87/1.00  num_of_reused_defs:                     0
% 2.87/1.00  num_eq_ax_congr_red:                    7
% 2.87/1.00  num_of_sem_filtered_clauses:            1
% 2.87/1.00  num_of_subtypes:                        4
% 2.87/1.00  monotx_restored_types:                  1
% 2.87/1.00  sat_num_of_epr_types:                   0
% 2.87/1.00  sat_num_of_non_cyclic_types:            0
% 2.87/1.00  sat_guarded_non_collapsed_types:        0
% 2.87/1.00  num_pure_diseq_elim:                    0
% 2.87/1.00  simp_replaced_by:                       0
% 2.87/1.00  res_preprocessed:                       124
% 2.87/1.00  prep_upred:                             0
% 2.87/1.00  prep_unflattend:                        22
% 2.87/1.00  smt_new_axioms:                         0
% 2.87/1.00  pred_elim_cands:                        4
% 2.87/1.00  pred_elim:                              5
% 2.87/1.00  pred_elim_cl:                           7
% 2.87/1.00  pred_elim_cycles:                       7
% 2.87/1.00  merged_defs:                            0
% 2.87/1.00  merged_defs_ncl:                        0
% 2.87/1.00  bin_hyper_res:                          0
% 2.87/1.00  prep_cycles:                            4
% 2.87/1.00  pred_elim_time:                         0.004
% 2.87/1.00  splitting_time:                         0.
% 2.87/1.00  sem_filter_time:                        0.
% 2.87/1.00  monotx_time:                            0.
% 2.87/1.00  subtype_inf_time:                       0.001
% 2.87/1.00  
% 2.87/1.00  ------ Problem properties
% 2.87/1.00  
% 2.87/1.00  clauses:                                19
% 2.87/1.00  conjectures:                            3
% 2.87/1.00  epr:                                    1
% 2.87/1.00  horn:                                   19
% 2.87/1.00  ground:                                 10
% 2.87/1.00  unary:                                  6
% 2.87/1.00  binary:                                 8
% 2.87/1.00  lits:                                   40
% 2.87/1.00  lits_eq:                                10
% 2.87/1.00  fd_pure:                                0
% 2.87/1.00  fd_pseudo:                              0
% 2.87/1.00  fd_cond:                                0
% 2.87/1.00  fd_pseudo_cond:                         1
% 2.87/1.00  ac_symbols:                             0
% 2.87/1.00  
% 2.87/1.00  ------ Propositional Solver
% 2.87/1.00  
% 2.87/1.00  prop_solver_calls:                      29
% 2.87/1.00  prop_fast_solver_calls:                 778
% 2.87/1.00  smt_solver_calls:                       0
% 2.87/1.00  smt_fast_solver_calls:                  0
% 2.87/1.00  prop_num_of_clauses:                    1067
% 2.87/1.00  prop_preprocess_simplified:             4338
% 2.87/1.00  prop_fo_subsumed:                       30
% 2.87/1.00  prop_solver_time:                       0.
% 2.87/1.00  smt_solver_time:                        0.
% 2.87/1.00  smt_fast_solver_time:                   0.
% 2.87/1.00  prop_fast_solver_time:                  0.
% 2.87/1.00  prop_unsat_core_time:                   0.
% 2.87/1.00  
% 2.87/1.00  ------ QBF
% 2.87/1.00  
% 2.87/1.00  qbf_q_res:                              0
% 2.87/1.00  qbf_num_tautologies:                    0
% 2.87/1.00  qbf_prep_cycles:                        0
% 2.87/1.00  
% 2.87/1.00  ------ BMC1
% 2.87/1.00  
% 2.87/1.00  bmc1_current_bound:                     -1
% 2.87/1.00  bmc1_last_solved_bound:                 -1
% 2.87/1.00  bmc1_unsat_core_size:                   -1
% 2.87/1.00  bmc1_unsat_core_parents_size:           -1
% 2.87/1.00  bmc1_merge_next_fun:                    0
% 2.87/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.87/1.00  
% 2.87/1.00  ------ Instantiation
% 2.87/1.00  
% 2.87/1.00  inst_num_of_clauses:                    343
% 2.87/1.00  inst_num_in_passive:                    139
% 2.87/1.00  inst_num_in_active:                     200
% 2.87/1.00  inst_num_in_unprocessed:                4
% 2.87/1.00  inst_num_of_loops:                      230
% 2.87/1.00  inst_num_of_learning_restarts:          0
% 2.87/1.00  inst_num_moves_active_passive:          26
% 2.87/1.00  inst_lit_activity:                      0
% 2.87/1.00  inst_lit_activity_moves:                0
% 2.87/1.00  inst_num_tautologies:                   0
% 2.87/1.00  inst_num_prop_implied:                  0
% 2.87/1.00  inst_num_existing_simplified:           0
% 2.87/1.00  inst_num_eq_res_simplified:             0
% 2.87/1.00  inst_num_child_elim:                    0
% 2.87/1.00  inst_num_of_dismatching_blockings:      203
% 2.87/1.00  inst_num_of_non_proper_insts:           440
% 2.87/1.00  inst_num_of_duplicates:                 0
% 2.87/1.00  inst_inst_num_from_inst_to_res:         0
% 2.87/1.00  inst_dismatching_checking_time:         0.
% 2.87/1.00  
% 2.87/1.00  ------ Resolution
% 2.87/1.00  
% 2.87/1.00  res_num_of_clauses:                     0
% 2.87/1.00  res_num_in_passive:                     0
% 2.87/1.00  res_num_in_active:                      0
% 2.87/1.00  res_num_of_loops:                       128
% 2.87/1.00  res_forward_subset_subsumed:            66
% 2.87/1.00  res_backward_subset_subsumed:           0
% 2.87/1.00  res_forward_subsumed:                   1
% 2.87/1.00  res_backward_subsumed:                  0
% 2.87/1.00  res_forward_subsumption_resolution:     2
% 2.87/1.00  res_backward_subsumption_resolution:    0
% 2.87/1.00  res_clause_to_clause_subsumption:       97
% 2.87/1.00  res_orphan_elimination:                 0
% 2.87/1.00  res_tautology_del:                      34
% 2.87/1.00  res_num_eq_res_simplified:              0
% 2.87/1.00  res_num_sel_changes:                    0
% 2.87/1.00  res_moves_from_active_to_pass:          0
% 2.87/1.00  
% 2.87/1.00  ------ Superposition
% 2.87/1.00  
% 2.87/1.00  sup_time_total:                         0.
% 2.87/1.00  sup_time_generating:                    0.
% 2.87/1.00  sup_time_sim_full:                      0.
% 2.87/1.00  sup_time_sim_immed:                     0.
% 2.87/1.00  
% 2.87/1.00  sup_num_of_clauses:                     56
% 2.87/1.00  sup_num_in_active:                      43
% 2.87/1.00  sup_num_in_passive:                     13
% 2.87/1.00  sup_num_of_loops:                       45
% 2.87/1.00  sup_fw_superposition:                   40
% 2.87/1.00  sup_bw_superposition:                   11
% 2.87/1.00  sup_immediate_simplified:               16
% 2.87/1.00  sup_given_eliminated:                   0
% 2.87/1.00  comparisons_done:                       0
% 2.87/1.00  comparisons_avoided:                    0
% 2.87/1.00  
% 2.87/1.00  ------ Simplifications
% 2.87/1.00  
% 2.87/1.00  
% 2.87/1.00  sim_fw_subset_subsumed:                 0
% 2.87/1.00  sim_bw_subset_subsumed:                 1
% 2.87/1.00  sim_fw_subsumed:                        4
% 2.87/1.00  sim_bw_subsumed:                        0
% 2.87/1.00  sim_fw_subsumption_res:                 0
% 2.87/1.00  sim_bw_subsumption_res:                 0
% 2.87/1.00  sim_tautology_del:                      1
% 2.87/1.00  sim_eq_tautology_del:                   6
% 2.87/1.00  sim_eq_res_simp:                        0
% 2.87/1.00  sim_fw_demodulated:                     0
% 2.87/1.00  sim_bw_demodulated:                     2
% 2.87/1.00  sim_light_normalised:                   21
% 2.87/1.00  sim_joinable_taut:                      0
% 2.87/1.00  sim_joinable_simp:                      0
% 2.87/1.00  sim_ac_normalised:                      0
% 2.87/1.00  sim_smt_subsumption:                    0
% 2.87/1.00  
%------------------------------------------------------------------------------
