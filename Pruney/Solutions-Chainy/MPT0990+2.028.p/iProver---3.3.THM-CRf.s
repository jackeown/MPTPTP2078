%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:02 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  238 (2193 expanded)
%              Number of clauses        :  150 ( 706 expanded)
%              Number of leaves         :   21 ( 521 expanded)
%              Depth                    :   28
%              Number of atoms          :  882 (17483 expanded)
%              Number of equality atoms :  413 (6338 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f89])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f50,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f55,f54])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f97,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f70,f89])).

fof(f98,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f107,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f73,f89,f89])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f100,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f101,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_810,plain,
    ( v2_funct_1(k6_partfun1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1344,plain,
    ( v2_funct_1(k6_partfun1(X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_783,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_41])).

cnf(c_1366,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k2_relset_1(X1_49,X2_49,X0_49) = k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1358,plain,
    ( k2_relset_1(X0_49,X1_49,X2_49) = k2_relat_1(X2_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_2231,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1366,c_1358])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_786,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_2233,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2231,c_786])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_785,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_1364,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_796,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1357,plain,
    ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_2159,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1364,c_1357])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X2
    | sK1 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_39])).

cnf(c_535,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_537,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_38,c_34])).

cnf(c_776,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(subtyping,[status(esa)],[c_537])).

cnf(c_2163,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2159,c_776])).

cnf(c_7,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_807,plain,
    ( v2_funct_1(X0_49)
    | ~ v2_funct_1(k5_relat_1(X1_49,X0_49))
    | ~ v1_relat_1(X0_49)
    | ~ v1_relat_1(X1_49)
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k1_relat_1(X0_49) != k2_relat_1(X1_49) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1347,plain,
    ( k1_relat_1(X0_49) != k2_relat_1(X1_49)
    | v2_funct_1(X0_49) = iProver_top
    | v2_funct_1(k5_relat_1(X1_49,X0_49)) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_807])).

cnf(c_3093,plain,
    ( k2_relat_1(X0_49) != sK1
    | v2_funct_1(k5_relat_1(X0_49,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2163,c_1347])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1435,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_1455,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_1456,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_4921,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | k2_relat_1(X0_49) != sK1
    | v2_funct_1(k5_relat_1(X0_49,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3093,c_47,c_49,c_1456])).

cnf(c_4922,plain,
    ( k2_relat_1(X0_49) != sK1
    | v2_funct_1(k5_relat_1(X0_49,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_4921])).

cnf(c_4927,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_4922])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_791,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X3_49)
    | k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49) = k5_relat_1(X3_49,X0_49) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1362,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X4_49,X5_49) = k5_relat_1(X4_49,X5_49)
    | m1_subset_1(X5_49,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | m1_subset_1(X4_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X5_49) != iProver_top
    | v1_funct_1(X4_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_3267,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X2_49) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1362])).

cnf(c_3280,plain,
    ( v1_funct_1(X2_49) != iProver_top
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3267,c_47])).

cnf(c_3281,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3)
    | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X2_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_3280])).

cnf(c_3287,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_3281])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_36,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_443,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_30,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_451,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_443,c_30])).

cnf(c_781,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_451])).

cnf(c_1368,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49)))
    | m1_subset_1(k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X4_49,X2_49)))
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X3_49) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1427,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_2035,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1368,c_43,c_41,c_40,c_38,c_781,c_1427])).

cnf(c_3289,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3287,c_2035])).

cnf(c_44,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_3618,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3289,c_44])).

cnf(c_4929,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4927,c_3618])).

cnf(c_46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_1502,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_1503,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1502])).

cnf(c_4933,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4929,c_44,c_46,c_1503])).

cnf(c_4937,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_4933])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_800,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | k2_funct_1(k2_funct_1(X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1354,plain,
    ( k2_funct_1(k2_funct_1(X0_49)) = X0_49
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_5244,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4937,c_1354])).

cnf(c_1744,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_1745,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1744])).

cnf(c_6016,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5244,c_47,c_49,c_1456,c_1745,c_4937])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_801,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | ~ v1_relat_1(X1_49)
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k5_relat_1(X1_49,X0_49) != k6_partfun1(k2_relat_1(X0_49))
    | k1_relat_1(X0_49) != k2_relat_1(X1_49)
    | k2_funct_1(X0_49) = X1_49 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1353,plain,
    ( k5_relat_1(X0_49,X1_49) != k6_partfun1(k2_relat_1(X1_49))
    | k1_relat_1(X1_49) != k2_relat_1(X0_49)
    | k2_funct_1(X1_49) = X0_49
    | v2_funct_1(X1_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_3712,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_1353])).

cnf(c_3714,plain,
    ( k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | sK1 != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3712,c_2163,c_2233])).

cnf(c_3715,plain,
    ( k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3714])).

cnf(c_35,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_51,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_811,plain,
    ( ~ v1_relat_1(X0_49)
    | v1_relat_1(k2_funct_1(X0_49))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1720,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_1721,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1720])).

cnf(c_1723,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_1724,plain,
    ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1723])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_812,plain,
    ( ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_1(X0_49)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2694,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_2695,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2694])).

cnf(c_4189,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_4190,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4189])).

cnf(c_4,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_808,plain,
    ( ~ v2_funct_1(X0_49)
    | v2_funct_1(k2_funct_1(X0_49))
    | ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_4224,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_4225,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4224])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_805,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | k2_relat_1(k2_funct_1(X0_49)) = k1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1349,plain,
    ( k2_relat_1(k2_funct_1(X0_49)) = k1_relat_1(X0_49)
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_805])).

cnf(c_5243,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4937,c_1349])).

cnf(c_5246,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5243,c_2163])).

cnf(c_787,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1363,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_799,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v2_funct_1(X1_49)
    | ~ v1_relat_1(X0_49)
    | ~ v1_relat_1(X1_49)
    | ~ v1_funct_1(X0_49)
    | ~ v1_funct_1(X1_49)
    | k5_relat_1(k2_funct_1(X1_49),k2_funct_1(X0_49)) = k2_funct_1(k5_relat_1(X0_49,X1_49)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1355,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(X1_49)) = k2_funct_1(k5_relat_1(X1_49,X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v2_funct_1(X1_49) != iProver_top
    | v1_relat_1(X1_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X1_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_3811,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1355])).

cnf(c_4094,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | k5_relat_1(k2_funct_1(X0_49),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3811,c_44,c_46,c_1503])).

cnf(c_4095,plain,
    ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,X0_49))
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_4094])).

cnf(c_5239,plain,
    ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,sK3))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4937,c_4095])).

cnf(c_5248,plain,
    ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) = k2_funct_1(k6_partfun1(sK0))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5239,c_3618])).

cnf(c_16,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_798,plain,
    ( k2_funct_1(k6_partfun1(X0_49)) = k6_partfun1(X0_49) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_5249,plain,
    ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5248,c_798])).

cnf(c_5262,plain,
    ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5249,c_47,c_49,c_1456])).

cnf(c_5264,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK3))
    | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(sK0)
    | k2_funct_1(k2_funct_1(sK2)) = k2_funct_1(sK3)
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5262,c_1353])).

cnf(c_2593,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1354])).

cnf(c_2049,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_2732,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2593,c_43,c_41,c_35,c_1502,c_2049])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_804,plain,
    ( ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | ~ v1_funct_1(X0_49)
    | k1_relat_1(k2_funct_1(X0_49)) = k2_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1350,plain,
    ( k1_relat_1(k2_funct_1(X0_49)) = k2_relat_1(X0_49)
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_2675,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1350])).

cnf(c_2679,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2675,c_2233])).

cnf(c_2738,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2679,c_44,c_46,c_1503])).

cnf(c_2602,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1349])).

cnf(c_2160,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1366,c_1357])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_42])).

cnf(c_543,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_545,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_41,c_33])).

cnf(c_775,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(subtyping,[status(esa)],[c_545])).

cnf(c_2162,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2160,c_775])).

cnf(c_2606,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2602,c_2162])).

cnf(c_2850,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2606,c_44,c_46,c_1503])).

cnf(c_5265,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5264,c_2732,c_2738,c_2850])).

cnf(c_5266,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5265])).

cnf(c_5508,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3715,c_44,c_46,c_47,c_49,c_51,c_1456,c_1503,c_1721,c_1724,c_2695,c_4190,c_4225,c_5246,c_5266])).

cnf(c_6018,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_6016,c_5508])).

cnf(c_32,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_790,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6018,c_790])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:13:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.81/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/0.98  
% 3.81/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/0.98  
% 3.81/0.98  ------  iProver source info
% 3.81/0.98  
% 3.81/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.81/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/0.98  git: non_committed_changes: false
% 3.81/0.98  git: last_make_outside_of_git: false
% 3.81/0.98  
% 3.81/0.98  ------ 
% 3.81/0.98  
% 3.81/0.98  ------ Input Options
% 3.81/0.98  
% 3.81/0.98  --out_options                           all
% 3.81/0.98  --tptp_safe_out                         true
% 3.81/0.98  --problem_path                          ""
% 3.81/0.98  --include_path                          ""
% 3.81/0.98  --clausifier                            res/vclausify_rel
% 3.81/0.98  --clausifier_options                    ""
% 3.81/0.98  --stdin                                 false
% 3.81/0.98  --stats_out                             all
% 3.81/0.98  
% 3.81/0.98  ------ General Options
% 3.81/0.98  
% 3.81/0.98  --fof                                   false
% 3.81/0.98  --time_out_real                         305.
% 3.81/0.98  --time_out_virtual                      -1.
% 3.81/0.98  --symbol_type_check                     false
% 3.81/0.98  --clausify_out                          false
% 3.81/0.98  --sig_cnt_out                           false
% 3.81/0.98  --trig_cnt_out                          false
% 3.81/0.98  --trig_cnt_out_tolerance                1.
% 3.81/0.98  --trig_cnt_out_sk_spl                   false
% 3.81/0.98  --abstr_cl_out                          false
% 3.81/0.98  
% 3.81/0.98  ------ Global Options
% 3.81/0.98  
% 3.81/0.98  --schedule                              default
% 3.81/0.98  --add_important_lit                     false
% 3.81/0.98  --prop_solver_per_cl                    1000
% 3.81/0.98  --min_unsat_core                        false
% 3.81/0.98  --soft_assumptions                      false
% 3.81/0.98  --soft_lemma_size                       3
% 3.81/0.98  --prop_impl_unit_size                   0
% 3.81/0.98  --prop_impl_unit                        []
% 3.81/0.98  --share_sel_clauses                     true
% 3.81/0.98  --reset_solvers                         false
% 3.81/0.98  --bc_imp_inh                            [conj_cone]
% 3.81/0.98  --conj_cone_tolerance                   3.
% 3.81/0.98  --extra_neg_conj                        none
% 3.81/0.98  --large_theory_mode                     true
% 3.81/0.98  --prolific_symb_bound                   200
% 3.81/0.98  --lt_threshold                          2000
% 3.81/0.98  --clause_weak_htbl                      true
% 3.81/0.98  --gc_record_bc_elim                     false
% 3.81/0.98  
% 3.81/0.98  ------ Preprocessing Options
% 3.81/0.98  
% 3.81/0.98  --preprocessing_flag                    true
% 3.81/0.98  --time_out_prep_mult                    0.1
% 3.81/0.98  --splitting_mode                        input
% 3.81/0.98  --splitting_grd                         true
% 3.81/0.98  --splitting_cvd                         false
% 3.81/0.98  --splitting_cvd_svl                     false
% 3.81/0.98  --splitting_nvd                         32
% 3.81/0.98  --sub_typing                            true
% 3.81/0.98  --prep_gs_sim                           true
% 3.81/0.98  --prep_unflatten                        true
% 3.81/0.98  --prep_res_sim                          true
% 3.81/0.98  --prep_upred                            true
% 3.81/0.98  --prep_sem_filter                       exhaustive
% 3.81/0.98  --prep_sem_filter_out                   false
% 3.81/0.98  --pred_elim                             true
% 3.81/0.98  --res_sim_input                         true
% 3.81/0.98  --eq_ax_congr_red                       true
% 3.81/0.98  --pure_diseq_elim                       true
% 3.81/0.98  --brand_transform                       false
% 3.81/0.98  --non_eq_to_eq                          false
% 3.81/0.98  --prep_def_merge                        true
% 3.81/0.98  --prep_def_merge_prop_impl              false
% 3.81/0.98  --prep_def_merge_mbd                    true
% 3.81/0.98  --prep_def_merge_tr_red                 false
% 3.81/0.98  --prep_def_merge_tr_cl                  false
% 3.81/0.98  --smt_preprocessing                     true
% 3.81/0.98  --smt_ac_axioms                         fast
% 3.81/0.98  --preprocessed_out                      false
% 3.81/0.98  --preprocessed_stats                    false
% 3.81/0.98  
% 3.81/0.98  ------ Abstraction refinement Options
% 3.81/0.98  
% 3.81/0.98  --abstr_ref                             []
% 3.81/0.98  --abstr_ref_prep                        false
% 3.81/0.98  --abstr_ref_until_sat                   false
% 3.81/0.98  --abstr_ref_sig_restrict                funpre
% 3.81/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.98  --abstr_ref_under                       []
% 3.81/0.98  
% 3.81/0.98  ------ SAT Options
% 3.81/0.98  
% 3.81/0.98  --sat_mode                              false
% 3.81/0.98  --sat_fm_restart_options                ""
% 3.81/0.98  --sat_gr_def                            false
% 3.81/0.98  --sat_epr_types                         true
% 3.81/0.98  --sat_non_cyclic_types                  false
% 3.81/0.98  --sat_finite_models                     false
% 3.81/0.98  --sat_fm_lemmas                         false
% 3.81/0.98  --sat_fm_prep                           false
% 3.81/0.98  --sat_fm_uc_incr                        true
% 3.81/0.98  --sat_out_model                         small
% 3.81/0.98  --sat_out_clauses                       false
% 3.81/0.98  
% 3.81/0.98  ------ QBF Options
% 3.81/0.98  
% 3.81/0.98  --qbf_mode                              false
% 3.81/0.98  --qbf_elim_univ                         false
% 3.81/0.98  --qbf_dom_inst                          none
% 3.81/0.98  --qbf_dom_pre_inst                      false
% 3.81/0.98  --qbf_sk_in                             false
% 3.81/0.98  --qbf_pred_elim                         true
% 3.81/0.98  --qbf_split                             512
% 3.81/0.98  
% 3.81/0.98  ------ BMC1 Options
% 3.81/0.98  
% 3.81/0.98  --bmc1_incremental                      false
% 3.81/0.98  --bmc1_axioms                           reachable_all
% 3.81/0.98  --bmc1_min_bound                        0
% 3.81/0.98  --bmc1_max_bound                        -1
% 3.81/0.98  --bmc1_max_bound_default                -1
% 3.81/0.98  --bmc1_symbol_reachability              true
% 3.81/0.98  --bmc1_property_lemmas                  false
% 3.81/0.98  --bmc1_k_induction                      false
% 3.81/0.98  --bmc1_non_equiv_states                 false
% 3.81/0.98  --bmc1_deadlock                         false
% 3.81/0.98  --bmc1_ucm                              false
% 3.81/0.98  --bmc1_add_unsat_core                   none
% 3.81/0.98  --bmc1_unsat_core_children              false
% 3.81/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.98  --bmc1_out_stat                         full
% 3.81/0.98  --bmc1_ground_init                      false
% 3.81/0.98  --bmc1_pre_inst_next_state              false
% 3.81/0.98  --bmc1_pre_inst_state                   false
% 3.81/0.98  --bmc1_pre_inst_reach_state             false
% 3.81/0.98  --bmc1_out_unsat_core                   false
% 3.81/0.98  --bmc1_aig_witness_out                  false
% 3.81/0.98  --bmc1_verbose                          false
% 3.81/0.98  --bmc1_dump_clauses_tptp                false
% 3.81/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.98  --bmc1_dump_file                        -
% 3.81/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.98  --bmc1_ucm_extend_mode                  1
% 3.81/0.98  --bmc1_ucm_init_mode                    2
% 3.81/0.98  --bmc1_ucm_cone_mode                    none
% 3.81/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.98  --bmc1_ucm_relax_model                  4
% 3.81/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.98  --bmc1_ucm_layered_model                none
% 3.81/0.98  --bmc1_ucm_max_lemma_size               10
% 3.81/0.98  
% 3.81/0.98  ------ AIG Options
% 3.81/0.98  
% 3.81/0.98  --aig_mode                              false
% 3.81/0.98  
% 3.81/0.98  ------ Instantiation Options
% 3.81/0.98  
% 3.81/0.98  --instantiation_flag                    true
% 3.81/0.98  --inst_sos_flag                         true
% 3.81/0.98  --inst_sos_phase                        true
% 3.81/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.98  --inst_lit_sel_side                     num_symb
% 3.81/0.98  --inst_solver_per_active                1400
% 3.81/0.98  --inst_solver_calls_frac                1.
% 3.81/0.98  --inst_passive_queue_type               priority_queues
% 3.81/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.98  --inst_passive_queues_freq              [25;2]
% 3.81/0.98  --inst_dismatching                      true
% 3.81/0.98  --inst_eager_unprocessed_to_passive     true
% 3.81/0.98  --inst_prop_sim_given                   true
% 3.81/0.98  --inst_prop_sim_new                     false
% 3.81/0.98  --inst_subs_new                         false
% 3.81/0.98  --inst_eq_res_simp                      false
% 3.81/0.98  --inst_subs_given                       false
% 3.81/0.98  --inst_orphan_elimination               true
% 3.81/0.98  --inst_learning_loop_flag               true
% 3.81/0.98  --inst_learning_start                   3000
% 3.81/0.98  --inst_learning_factor                  2
% 3.81/0.98  --inst_start_prop_sim_after_learn       3
% 3.81/0.98  --inst_sel_renew                        solver
% 3.81/0.98  --inst_lit_activity_flag                true
% 3.81/0.98  --inst_restr_to_given                   false
% 3.81/0.98  --inst_activity_threshold               500
% 3.81/0.98  --inst_out_proof                        true
% 3.81/0.98  
% 3.81/0.98  ------ Resolution Options
% 3.81/0.98  
% 3.81/0.98  --resolution_flag                       true
% 3.81/0.98  --res_lit_sel                           adaptive
% 3.81/0.98  --res_lit_sel_side                      none
% 3.81/0.98  --res_ordering                          kbo
% 3.81/0.98  --res_to_prop_solver                    active
% 3.81/0.98  --res_prop_simpl_new                    false
% 3.81/0.98  --res_prop_simpl_given                  true
% 3.81/0.98  --res_passive_queue_type                priority_queues
% 3.81/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.98  --res_passive_queues_freq               [15;5]
% 3.81/0.98  --res_forward_subs                      full
% 3.81/0.98  --res_backward_subs                     full
% 3.81/0.98  --res_forward_subs_resolution           true
% 3.81/0.98  --res_backward_subs_resolution          true
% 3.81/0.98  --res_orphan_elimination                true
% 3.81/0.98  --res_time_limit                        2.
% 3.81/0.98  --res_out_proof                         true
% 3.81/0.98  
% 3.81/0.98  ------ Superposition Options
% 3.81/0.98  
% 3.81/0.98  --superposition_flag                    true
% 3.81/0.98  --sup_passive_queue_type                priority_queues
% 3.81/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.98  --demod_completeness_check              fast
% 3.81/0.98  --demod_use_ground                      true
% 3.81/0.98  --sup_to_prop_solver                    passive
% 3.81/0.98  --sup_prop_simpl_new                    true
% 3.81/0.98  --sup_prop_simpl_given                  true
% 3.81/0.98  --sup_fun_splitting                     true
% 3.81/0.98  --sup_smt_interval                      50000
% 3.81/0.99  
% 3.81/0.99  ------ Superposition Simplification Setup
% 3.81/0.99  
% 3.81/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.81/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.81/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.81/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.81/0.99  --sup_immed_triv                        [TrivRules]
% 3.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.99  --sup_immed_bw_main                     []
% 3.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.99  --sup_input_bw                          []
% 3.81/0.99  
% 3.81/0.99  ------ Combination Options
% 3.81/0.99  
% 3.81/0.99  --comb_res_mult                         3
% 3.81/0.99  --comb_sup_mult                         2
% 3.81/0.99  --comb_inst_mult                        10
% 3.81/0.99  
% 3.81/0.99  ------ Debug Options
% 3.81/0.99  
% 3.81/0.99  --dbg_backtrace                         false
% 3.81/0.99  --dbg_dump_prop_clauses                 false
% 3.81/0.99  --dbg_dump_prop_clauses_file            -
% 3.81/0.99  --dbg_out_stat                          false
% 3.81/0.99  ------ Parsing...
% 3.81/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/0.99  
% 3.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.81/0.99  
% 3.81/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/0.99  
% 3.81/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/0.99  ------ Proving...
% 3.81/0.99  ------ Problem Properties 
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  clauses                                 38
% 3.81/0.99  conjectures                             9
% 3.81/0.99  EPR                                     5
% 3.81/0.99  Horn                                    38
% 3.81/0.99  unary                                   15
% 3.81/0.99  binary                                  4
% 3.81/0.99  lits                                    109
% 3.81/0.99  lits eq                                 30
% 3.81/0.99  fd_pure                                 0
% 3.81/0.99  fd_pseudo                               0
% 3.81/0.99  fd_cond                                 0
% 3.81/0.99  fd_pseudo_cond                          1
% 3.81/0.99  AC symbols                              0
% 3.81/0.99  
% 3.81/0.99  ------ Schedule dynamic 5 is on 
% 3.81/0.99  
% 3.81/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  ------ 
% 3.81/0.99  Current options:
% 3.81/0.99  ------ 
% 3.81/0.99  
% 3.81/0.99  ------ Input Options
% 3.81/0.99  
% 3.81/0.99  --out_options                           all
% 3.81/0.99  --tptp_safe_out                         true
% 3.81/0.99  --problem_path                          ""
% 3.81/0.99  --include_path                          ""
% 3.81/0.99  --clausifier                            res/vclausify_rel
% 3.81/0.99  --clausifier_options                    ""
% 3.81/0.99  --stdin                                 false
% 3.81/0.99  --stats_out                             all
% 3.81/0.99  
% 3.81/0.99  ------ General Options
% 3.81/0.99  
% 3.81/0.99  --fof                                   false
% 3.81/0.99  --time_out_real                         305.
% 3.81/0.99  --time_out_virtual                      -1.
% 3.81/0.99  --symbol_type_check                     false
% 3.81/0.99  --clausify_out                          false
% 3.81/0.99  --sig_cnt_out                           false
% 3.81/0.99  --trig_cnt_out                          false
% 3.81/0.99  --trig_cnt_out_tolerance                1.
% 3.81/0.99  --trig_cnt_out_sk_spl                   false
% 3.81/0.99  --abstr_cl_out                          false
% 3.81/0.99  
% 3.81/0.99  ------ Global Options
% 3.81/0.99  
% 3.81/0.99  --schedule                              default
% 3.81/0.99  --add_important_lit                     false
% 3.81/0.99  --prop_solver_per_cl                    1000
% 3.81/0.99  --min_unsat_core                        false
% 3.81/0.99  --soft_assumptions                      false
% 3.81/0.99  --soft_lemma_size                       3
% 3.81/0.99  --prop_impl_unit_size                   0
% 3.81/0.99  --prop_impl_unit                        []
% 3.81/0.99  --share_sel_clauses                     true
% 3.81/0.99  --reset_solvers                         false
% 3.81/0.99  --bc_imp_inh                            [conj_cone]
% 3.81/0.99  --conj_cone_tolerance                   3.
% 3.81/0.99  --extra_neg_conj                        none
% 3.81/0.99  --large_theory_mode                     true
% 3.81/0.99  --prolific_symb_bound                   200
% 3.81/0.99  --lt_threshold                          2000
% 3.81/0.99  --clause_weak_htbl                      true
% 3.81/0.99  --gc_record_bc_elim                     false
% 3.81/0.99  
% 3.81/0.99  ------ Preprocessing Options
% 3.81/0.99  
% 3.81/0.99  --preprocessing_flag                    true
% 3.81/0.99  --time_out_prep_mult                    0.1
% 3.81/0.99  --splitting_mode                        input
% 3.81/0.99  --splitting_grd                         true
% 3.81/0.99  --splitting_cvd                         false
% 3.81/0.99  --splitting_cvd_svl                     false
% 3.81/0.99  --splitting_nvd                         32
% 3.81/0.99  --sub_typing                            true
% 3.81/0.99  --prep_gs_sim                           true
% 3.81/0.99  --prep_unflatten                        true
% 3.81/0.99  --prep_res_sim                          true
% 3.81/0.99  --prep_upred                            true
% 3.81/0.99  --prep_sem_filter                       exhaustive
% 3.81/0.99  --prep_sem_filter_out                   false
% 3.81/0.99  --pred_elim                             true
% 3.81/0.99  --res_sim_input                         true
% 3.81/0.99  --eq_ax_congr_red                       true
% 3.81/0.99  --pure_diseq_elim                       true
% 3.81/0.99  --brand_transform                       false
% 3.81/0.99  --non_eq_to_eq                          false
% 3.81/0.99  --prep_def_merge                        true
% 3.81/0.99  --prep_def_merge_prop_impl              false
% 3.81/0.99  --prep_def_merge_mbd                    true
% 3.81/0.99  --prep_def_merge_tr_red                 false
% 3.81/0.99  --prep_def_merge_tr_cl                  false
% 3.81/0.99  --smt_preprocessing                     true
% 3.81/0.99  --smt_ac_axioms                         fast
% 3.81/0.99  --preprocessed_out                      false
% 3.81/0.99  --preprocessed_stats                    false
% 3.81/0.99  
% 3.81/0.99  ------ Abstraction refinement Options
% 3.81/0.99  
% 3.81/0.99  --abstr_ref                             []
% 3.81/0.99  --abstr_ref_prep                        false
% 3.81/0.99  --abstr_ref_until_sat                   false
% 3.81/0.99  --abstr_ref_sig_restrict                funpre
% 3.81/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/0.99  --abstr_ref_under                       []
% 3.81/0.99  
% 3.81/0.99  ------ SAT Options
% 3.81/0.99  
% 3.81/0.99  --sat_mode                              false
% 3.81/0.99  --sat_fm_restart_options                ""
% 3.81/0.99  --sat_gr_def                            false
% 3.81/0.99  --sat_epr_types                         true
% 3.81/0.99  --sat_non_cyclic_types                  false
% 3.81/0.99  --sat_finite_models                     false
% 3.81/0.99  --sat_fm_lemmas                         false
% 3.81/0.99  --sat_fm_prep                           false
% 3.81/0.99  --sat_fm_uc_incr                        true
% 3.81/0.99  --sat_out_model                         small
% 3.81/0.99  --sat_out_clauses                       false
% 3.81/0.99  
% 3.81/0.99  ------ QBF Options
% 3.81/0.99  
% 3.81/0.99  --qbf_mode                              false
% 3.81/0.99  --qbf_elim_univ                         false
% 3.81/0.99  --qbf_dom_inst                          none
% 3.81/0.99  --qbf_dom_pre_inst                      false
% 3.81/0.99  --qbf_sk_in                             false
% 3.81/0.99  --qbf_pred_elim                         true
% 3.81/0.99  --qbf_split                             512
% 3.81/0.99  
% 3.81/0.99  ------ BMC1 Options
% 3.81/0.99  
% 3.81/0.99  --bmc1_incremental                      false
% 3.81/0.99  --bmc1_axioms                           reachable_all
% 3.81/0.99  --bmc1_min_bound                        0
% 3.81/0.99  --bmc1_max_bound                        -1
% 3.81/0.99  --bmc1_max_bound_default                -1
% 3.81/0.99  --bmc1_symbol_reachability              true
% 3.81/0.99  --bmc1_property_lemmas                  false
% 3.81/0.99  --bmc1_k_induction                      false
% 3.81/0.99  --bmc1_non_equiv_states                 false
% 3.81/0.99  --bmc1_deadlock                         false
% 3.81/0.99  --bmc1_ucm                              false
% 3.81/0.99  --bmc1_add_unsat_core                   none
% 3.81/0.99  --bmc1_unsat_core_children              false
% 3.81/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/0.99  --bmc1_out_stat                         full
% 3.81/0.99  --bmc1_ground_init                      false
% 3.81/0.99  --bmc1_pre_inst_next_state              false
% 3.81/0.99  --bmc1_pre_inst_state                   false
% 3.81/0.99  --bmc1_pre_inst_reach_state             false
% 3.81/0.99  --bmc1_out_unsat_core                   false
% 3.81/0.99  --bmc1_aig_witness_out                  false
% 3.81/0.99  --bmc1_verbose                          false
% 3.81/0.99  --bmc1_dump_clauses_tptp                false
% 3.81/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.81/0.99  --bmc1_dump_file                        -
% 3.81/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.81/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.81/0.99  --bmc1_ucm_extend_mode                  1
% 3.81/0.99  --bmc1_ucm_init_mode                    2
% 3.81/0.99  --bmc1_ucm_cone_mode                    none
% 3.81/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.81/0.99  --bmc1_ucm_relax_model                  4
% 3.81/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.81/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/0.99  --bmc1_ucm_layered_model                none
% 3.81/0.99  --bmc1_ucm_max_lemma_size               10
% 3.81/0.99  
% 3.81/0.99  ------ AIG Options
% 3.81/0.99  
% 3.81/0.99  --aig_mode                              false
% 3.81/0.99  
% 3.81/0.99  ------ Instantiation Options
% 3.81/0.99  
% 3.81/0.99  --instantiation_flag                    true
% 3.81/0.99  --inst_sos_flag                         true
% 3.81/0.99  --inst_sos_phase                        true
% 3.81/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/0.99  --inst_lit_sel_side                     none
% 3.81/0.99  --inst_solver_per_active                1400
% 3.81/0.99  --inst_solver_calls_frac                1.
% 3.81/0.99  --inst_passive_queue_type               priority_queues
% 3.81/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/0.99  --inst_passive_queues_freq              [25;2]
% 3.81/0.99  --inst_dismatching                      true
% 3.81/0.99  --inst_eager_unprocessed_to_passive     true
% 3.81/0.99  --inst_prop_sim_given                   true
% 3.81/0.99  --inst_prop_sim_new                     false
% 3.81/0.99  --inst_subs_new                         false
% 3.81/0.99  --inst_eq_res_simp                      false
% 3.81/0.99  --inst_subs_given                       false
% 3.81/0.99  --inst_orphan_elimination               true
% 3.81/0.99  --inst_learning_loop_flag               true
% 3.81/0.99  --inst_learning_start                   3000
% 3.81/0.99  --inst_learning_factor                  2
% 3.81/0.99  --inst_start_prop_sim_after_learn       3
% 3.81/0.99  --inst_sel_renew                        solver
% 3.81/0.99  --inst_lit_activity_flag                true
% 3.81/0.99  --inst_restr_to_given                   false
% 3.81/0.99  --inst_activity_threshold               500
% 3.81/0.99  --inst_out_proof                        true
% 3.81/0.99  
% 3.81/0.99  ------ Resolution Options
% 3.81/0.99  
% 3.81/0.99  --resolution_flag                       false
% 3.81/0.99  --res_lit_sel                           adaptive
% 3.81/0.99  --res_lit_sel_side                      none
% 3.81/0.99  --res_ordering                          kbo
% 3.81/0.99  --res_to_prop_solver                    active
% 3.81/0.99  --res_prop_simpl_new                    false
% 3.81/0.99  --res_prop_simpl_given                  true
% 3.81/0.99  --res_passive_queue_type                priority_queues
% 3.81/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/0.99  --res_passive_queues_freq               [15;5]
% 3.81/0.99  --res_forward_subs                      full
% 3.81/0.99  --res_backward_subs                     full
% 3.81/0.99  --res_forward_subs_resolution           true
% 3.81/0.99  --res_backward_subs_resolution          true
% 3.81/0.99  --res_orphan_elimination                true
% 3.81/0.99  --res_time_limit                        2.
% 3.81/0.99  --res_out_proof                         true
% 3.81/0.99  
% 3.81/0.99  ------ Superposition Options
% 3.81/0.99  
% 3.81/0.99  --superposition_flag                    true
% 3.81/0.99  --sup_passive_queue_type                priority_queues
% 3.81/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.81/0.99  --demod_completeness_check              fast
% 3.81/0.99  --demod_use_ground                      true
% 3.81/0.99  --sup_to_prop_solver                    passive
% 3.81/0.99  --sup_prop_simpl_new                    true
% 3.81/0.99  --sup_prop_simpl_given                  true
% 3.81/0.99  --sup_fun_splitting                     true
% 3.81/0.99  --sup_smt_interval                      50000
% 3.81/0.99  
% 3.81/0.99  ------ Superposition Simplification Setup
% 3.81/0.99  
% 3.81/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.81/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.81/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.81/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.81/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.81/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.81/0.99  --sup_immed_triv                        [TrivRules]
% 3.81/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.99  --sup_immed_bw_main                     []
% 3.81/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.81/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/0.99  --sup_input_bw                          []
% 3.81/0.99  
% 3.81/0.99  ------ Combination Options
% 3.81/0.99  
% 3.81/0.99  --comb_res_mult                         3
% 3.81/0.99  --comb_sup_mult                         2
% 3.81/0.99  --comb_inst_mult                        10
% 3.81/0.99  
% 3.81/0.99  ------ Debug Options
% 3.81/0.99  
% 3.81/0.99  --dbg_backtrace                         false
% 3.81/0.99  --dbg_dump_prop_clauses                 false
% 3.81/0.99  --dbg_dump_prop_clauses_file            -
% 3.81/0.99  --dbg_out_stat                          false
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  ------ Proving...
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  % SZS status Theorem for theBenchmark.p
% 3.81/0.99  
% 3.81/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/0.99  
% 3.81/0.99  fof(f2,axiom,(
% 3.81/0.99    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f60,plain,(
% 3.81/0.99    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.81/0.99    inference(cnf_transformation,[],[f2])).
% 3.81/0.99  
% 3.81/0.99  fof(f19,axiom,(
% 3.81/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f89,plain,(
% 3.81/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f19])).
% 3.81/0.99  
% 3.81/0.99  fof(f102,plain,(
% 3.81/0.99    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.81/0.99    inference(definition_unfolding,[],[f60,f89])).
% 3.81/0.99  
% 3.81/0.99  fof(f20,conjecture,(
% 3.81/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f21,negated_conjecture,(
% 3.81/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.81/0.99    inference(negated_conjecture,[],[f20])).
% 3.81/0.99  
% 3.81/0.99  fof(f50,plain,(
% 3.81/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.81/0.99    inference(ennf_transformation,[],[f21])).
% 3.81/0.99  
% 3.81/0.99  fof(f51,plain,(
% 3.81/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.81/0.99    inference(flattening,[],[f50])).
% 3.81/0.99  
% 3.81/0.99  fof(f55,plain,(
% 3.81/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.81/0.99    introduced(choice_axiom,[])).
% 3.81/0.99  
% 3.81/0.99  fof(f54,plain,(
% 3.81/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.81/0.99    introduced(choice_axiom,[])).
% 3.81/0.99  
% 3.81/0.99  fof(f56,plain,(
% 3.81/0.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.81/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f55,f54])).
% 3.81/0.99  
% 3.81/0.99  fof(f92,plain,(
% 3.81/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f13,axiom,(
% 3.81/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f41,plain,(
% 3.81/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/0.99    inference(ennf_transformation,[],[f13])).
% 3.81/0.99  
% 3.81/0.99  fof(f76,plain,(
% 3.81/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/0.99    inference(cnf_transformation,[],[f41])).
% 3.81/0.99  
% 3.81/0.99  fof(f96,plain,(
% 3.81/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f95,plain,(
% 3.81/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f12,axiom,(
% 3.81/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f40,plain,(
% 3.81/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/0.99    inference(ennf_transformation,[],[f12])).
% 3.81/0.99  
% 3.81/0.99  fof(f75,plain,(
% 3.81/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/0.99    inference(cnf_transformation,[],[f40])).
% 3.81/0.99  
% 3.81/0.99  fof(f15,axiom,(
% 3.81/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f44,plain,(
% 3.81/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/0.99    inference(ennf_transformation,[],[f15])).
% 3.81/0.99  
% 3.81/0.99  fof(f45,plain,(
% 3.81/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/0.99    inference(flattening,[],[f44])).
% 3.81/0.99  
% 3.81/0.99  fof(f53,plain,(
% 3.81/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/0.99    inference(nnf_transformation,[],[f45])).
% 3.81/0.99  
% 3.81/0.99  fof(f79,plain,(
% 3.81/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/0.99    inference(cnf_transformation,[],[f53])).
% 3.81/0.99  
% 3.81/0.99  fof(f94,plain,(
% 3.81/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f99,plain,(
% 3.81/0.99    k1_xboole_0 != sK0),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f4,axiom,(
% 3.81/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f27,plain,(
% 3.81/0.99    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.99    inference(ennf_transformation,[],[f4])).
% 3.81/0.99  
% 3.81/0.99  fof(f28,plain,(
% 3.81/0.99    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.99    inference(flattening,[],[f27])).
% 3.81/0.99  
% 3.81/0.99  fof(f65,plain,(
% 3.81/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f28])).
% 3.81/0.99  
% 3.81/0.99  fof(f93,plain,(
% 3.81/0.99    v1_funct_1(sK3)),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f11,axiom,(
% 3.81/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f39,plain,(
% 3.81/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/0.99    inference(ennf_transformation,[],[f11])).
% 3.81/0.99  
% 3.81/0.99  fof(f74,plain,(
% 3.81/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/0.99    inference(cnf_transformation,[],[f39])).
% 3.81/0.99  
% 3.81/0.99  fof(f18,axiom,(
% 3.81/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f48,plain,(
% 3.81/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.81/0.99    inference(ennf_transformation,[],[f18])).
% 3.81/0.99  
% 3.81/0.99  fof(f49,plain,(
% 3.81/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.81/0.99    inference(flattening,[],[f48])).
% 3.81/0.99  
% 3.81/0.99  fof(f88,plain,(
% 3.81/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f49])).
% 3.81/0.99  
% 3.81/0.99  fof(f14,axiom,(
% 3.81/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f42,plain,(
% 3.81/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.81/0.99    inference(ennf_transformation,[],[f14])).
% 3.81/0.99  
% 3.81/0.99  fof(f43,plain,(
% 3.81/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/0.99    inference(flattening,[],[f42])).
% 3.81/0.99  
% 3.81/0.99  fof(f52,plain,(
% 3.81/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.81/0.99    inference(nnf_transformation,[],[f43])).
% 3.81/0.99  
% 3.81/0.99  fof(f77,plain,(
% 3.81/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.81/0.99    inference(cnf_transformation,[],[f52])).
% 3.81/0.99  
% 3.81/0.99  fof(f97,plain,(
% 3.81/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f17,axiom,(
% 3.81/0.99    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f22,plain,(
% 3.81/0.99    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.81/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.81/0.99  
% 3.81/0.99  fof(f87,plain,(
% 3.81/0.99    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.81/0.99    inference(cnf_transformation,[],[f22])).
% 3.81/0.99  
% 3.81/0.99  fof(f90,plain,(
% 3.81/0.99    v1_funct_1(sK2)),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f16,axiom,(
% 3.81/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f46,plain,(
% 3.81/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.81/0.99    inference(ennf_transformation,[],[f16])).
% 3.81/0.99  
% 3.81/0.99  fof(f47,plain,(
% 3.81/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.81/0.99    inference(flattening,[],[f46])).
% 3.81/0.99  
% 3.81/0.99  fof(f86,plain,(
% 3.81/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f47])).
% 3.81/0.99  
% 3.81/0.99  fof(f8,axiom,(
% 3.81/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f35,plain,(
% 3.81/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.99    inference(ennf_transformation,[],[f8])).
% 3.81/0.99  
% 3.81/0.99  fof(f36,plain,(
% 3.81/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.99    inference(flattening,[],[f35])).
% 3.81/0.99  
% 3.81/0.99  fof(f71,plain,(
% 3.81/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f36])).
% 3.81/0.99  
% 3.81/0.99  fof(f7,axiom,(
% 3.81/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f33,plain,(
% 3.81/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.99    inference(ennf_transformation,[],[f7])).
% 3.81/0.99  
% 3.81/0.99  fof(f34,plain,(
% 3.81/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.99    inference(flattening,[],[f33])).
% 3.81/0.99  
% 3.81/0.99  fof(f70,plain,(
% 3.81/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f34])).
% 3.81/0.99  
% 3.81/0.99  fof(f106,plain,(
% 3.81/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(definition_unfolding,[],[f70,f89])).
% 3.81/0.99  
% 3.81/0.99  fof(f98,plain,(
% 3.81/0.99    v2_funct_1(sK2)),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f1,axiom,(
% 3.81/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f23,plain,(
% 3.81/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.99    inference(ennf_transformation,[],[f1])).
% 3.81/0.99  
% 3.81/0.99  fof(f24,plain,(
% 3.81/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.99    inference(flattening,[],[f23])).
% 3.81/0.99  
% 3.81/0.99  fof(f57,plain,(
% 3.81/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f24])).
% 3.81/0.99  
% 3.81/0.99  fof(f58,plain,(
% 3.81/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f24])).
% 3.81/0.99  
% 3.81/0.99  fof(f3,axiom,(
% 3.81/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f25,plain,(
% 3.81/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.99    inference(ennf_transformation,[],[f3])).
% 3.81/0.99  
% 3.81/0.99  fof(f26,plain,(
% 3.81/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.99    inference(flattening,[],[f25])).
% 3.81/0.99  
% 3.81/0.99  fof(f63,plain,(
% 3.81/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f26])).
% 3.81/0.99  
% 3.81/0.99  fof(f5,axiom,(
% 3.81/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f29,plain,(
% 3.81/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.99    inference(ennf_transformation,[],[f5])).
% 3.81/0.99  
% 3.81/0.99  fof(f30,plain,(
% 3.81/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.99    inference(flattening,[],[f29])).
% 3.81/0.99  
% 3.81/0.99  fof(f67,plain,(
% 3.81/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f30])).
% 3.81/0.99  
% 3.81/0.99  fof(f9,axiom,(
% 3.81/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f37,plain,(
% 3.81/0.99    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.81/0.99    inference(ennf_transformation,[],[f9])).
% 3.81/0.99  
% 3.81/0.99  fof(f38,plain,(
% 3.81/0.99    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.81/0.99    inference(flattening,[],[f37])).
% 3.81/0.99  
% 3.81/0.99  fof(f72,plain,(
% 3.81/0.99    ( ! [X0,X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f38])).
% 3.81/0.99  
% 3.81/0.99  fof(f10,axiom,(
% 3.81/0.99    ! [X0] : k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 3.81/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/0.99  
% 3.81/0.99  fof(f73,plain,(
% 3.81/0.99    ( ! [X0] : (k2_funct_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f10])).
% 3.81/0.99  
% 3.81/0.99  fof(f107,plain,(
% 3.81/0.99    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 3.81/0.99    inference(definition_unfolding,[],[f73,f89,f89])).
% 3.81/0.99  
% 3.81/0.99  fof(f66,plain,(
% 3.81/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.81/0.99    inference(cnf_transformation,[],[f30])).
% 3.81/0.99  
% 3.81/0.99  fof(f91,plain,(
% 3.81/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f100,plain,(
% 3.81/0.99    k1_xboole_0 != sK1),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  fof(f101,plain,(
% 3.81/0.99    k2_funct_1(sK2) != sK3),
% 3.81/0.99    inference(cnf_transformation,[],[f56])).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2,plain,
% 3.81/0.99      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.81/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_810,plain,
% 3.81/0.99      ( v2_funct_1(k6_partfun1(X0_49)) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1344,plain,
% 3.81/0.99      ( v2_funct_1(k6_partfun1(X0_49)) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_41,negated_conjecture,
% 3.81/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.81/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_783,negated_conjecture,
% 3.81/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_41]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1366,plain,
% 3.81/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_19,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_795,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.81/0.99      | k2_relset_1(X1_49,X2_49,X0_49) = k2_relat_1(X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1358,plain,
% 3.81/0.99      ( k2_relset_1(X0_49,X1_49,X2_49) = k2_relat_1(X2_49)
% 3.81/0.99      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2231,plain,
% 3.81/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1366,c_1358]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_37,negated_conjecture,
% 3.81/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.81/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_786,negated_conjecture,
% 3.81/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_37]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2233,plain,
% 3.81/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_2231,c_786]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_38,negated_conjecture,
% 3.81/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.81/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_785,negated_conjecture,
% 3.81/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_38]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1364,plain,
% 3.81/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_18,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_796,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.81/0.99      | k1_relset_1(X1_49,X2_49,X0_49) = k1_relat_1(X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1357,plain,
% 3.81/0.99      ( k1_relset_1(X0_49,X1_49,X2_49) = k1_relat_1(X2_49)
% 3.81/0.99      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2159,plain,
% 3.81/0.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1364,c_1357]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_27,plain,
% 3.81/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.81/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.81/0.99      | k1_xboole_0 = X2 ),
% 3.81/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_39,negated_conjecture,
% 3.81/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_534,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.81/0.99      | sK0 != X2
% 3.81/0.99      | sK1 != X1
% 3.81/0.99      | sK3 != X0
% 3.81/0.99      | k1_xboole_0 = X2 ),
% 3.81/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_39]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_535,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.81/0.99      | k1_relset_1(sK1,sK0,sK3) = sK1
% 3.81/0.99      | k1_xboole_0 = sK0 ),
% 3.81/0.99      inference(unflattening,[status(thm)],[c_534]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_34,negated_conjecture,
% 3.81/0.99      ( k1_xboole_0 != sK0 ),
% 3.81/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_537,plain,
% 3.81/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_535,c_38,c_34]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_776,plain,
% 3.81/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_537]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2163,plain,
% 3.81/0.99      ( k1_relat_1(sK3) = sK1 ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_2159,c_776]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_7,plain,
% 3.81/0.99      ( v2_funct_1(X0)
% 3.81/0.99      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 3.81/0.99      | ~ v1_relat_1(X0)
% 3.81/0.99      | ~ v1_relat_1(X1)
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X1)
% 3.81/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.81/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_807,plain,
% 3.81/0.99      ( v2_funct_1(X0_49)
% 3.81/0.99      | ~ v2_funct_1(k5_relat_1(X1_49,X0_49))
% 3.81/0.99      | ~ v1_relat_1(X0_49)
% 3.81/0.99      | ~ v1_relat_1(X1_49)
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X1_49)
% 3.81/0.99      | k1_relat_1(X0_49) != k2_relat_1(X1_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1347,plain,
% 3.81/0.99      ( k1_relat_1(X0_49) != k2_relat_1(X1_49)
% 3.81/0.99      | v2_funct_1(X0_49) = iProver_top
% 3.81/0.99      | v2_funct_1(k5_relat_1(X1_49,X0_49)) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X1_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X1_49) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_807]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3093,plain,
% 3.81/0.99      ( k2_relat_1(X0_49) != sK1
% 3.81/0.99      | v2_funct_1(k5_relat_1(X0_49,sK3)) != iProver_top
% 3.81/0.99      | v2_funct_1(sK3) = iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_2163,c_1347]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_40,negated_conjecture,
% 3.81/0.99      ( v1_funct_1(sK3) ),
% 3.81/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_47,plain,
% 3.81/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_49,plain,
% 3.81/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_17,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | v1_relat_1(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_797,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.81/0.99      | v1_relat_1(X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1435,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 3.81/0.99      | v1_relat_1(sK3) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_797]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1455,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.81/0.99      | v1_relat_1(sK3) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_1435]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1456,plain,
% 3.81/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.81/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4921,plain,
% 3.81/0.99      ( v1_funct_1(X0_49) != iProver_top
% 3.81/0.99      | k2_relat_1(X0_49) != sK1
% 3.81/0.99      | v2_funct_1(k5_relat_1(X0_49,sK3)) != iProver_top
% 3.81/0.99      | v2_funct_1(sK3) = iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_3093,c_47,c_49,c_1456]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4922,plain,
% 3.81/0.99      ( k2_relat_1(X0_49) != sK1
% 3.81/0.99      | v2_funct_1(k5_relat_1(X0_49,sK3)) != iProver_top
% 3.81/0.99      | v2_funct_1(sK3) = iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_4921]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4927,plain,
% 3.81/0.99      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 3.81/0.99      | v2_funct_1(sK3) = iProver_top
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_2233,c_4922]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_31,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X3)
% 3.81/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_791,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.81/0.99      | ~ m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49)))
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X3_49)
% 3.81/0.99      | k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49) = k5_relat_1(X3_49,X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_31]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1362,plain,
% 3.81/0.99      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X4_49,X5_49) = k5_relat_1(X4_49,X5_49)
% 3.81/0.99      | m1_subset_1(X5_49,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 3.81/0.99      | m1_subset_1(X4_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.81/0.99      | v1_funct_1(X5_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X4_49) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3267,plain,
% 3.81/0.99      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3)
% 3.81/0.99      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.81/0.99      | v1_funct_1(X2_49) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1364,c_1362]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3280,plain,
% 3.81/0.99      ( v1_funct_1(X2_49) != iProver_top
% 3.81/0.99      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.81/0.99      | k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3) ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_3267,c_47]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3281,plain,
% 3.81/0.99      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X2_49,sK3) = k5_relat_1(X2_49,sK3)
% 3.81/0.99      | m1_subset_1(X2_49,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 3.81/0.99      | v1_funct_1(X2_49) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_3280]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3287,plain,
% 3.81/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1366,c_3281]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_21,plain,
% 3.81/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.81/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.81/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.81/0.99      | X3 = X2 ),
% 3.81/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_36,negated_conjecture,
% 3.81/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.81/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_442,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | X3 = X0
% 3.81/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.81/0.99      | k6_partfun1(sK0) != X3
% 3.81/0.99      | sK0 != X2
% 3.81/0.99      | sK0 != X1 ),
% 3.81/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_443,plain,
% 3.81/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.81/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.81/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.81/0.99      inference(unflattening,[status(thm)],[c_442]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_30,plain,
% 3.81/0.99      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.81/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_451,plain,
% 3.81/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.81/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.81/0.99      inference(forward_subsumption_resolution,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_443,c_30]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_781,plain,
% 3.81/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.81/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_451]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1368,plain,
% 3.81/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.81/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_43,negated_conjecture,
% 3.81/0.99      ( v1_funct_1(sK2) ),
% 3.81/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_28,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.81/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X3) ),
% 3.81/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_794,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 3.81/0.99      | ~ m1_subset_1(X3_49,k1_zfmisc_1(k2_zfmisc_1(X4_49,X5_49)))
% 3.81/0.99      | m1_subset_1(k1_partfun1(X4_49,X5_49,X1_49,X2_49,X3_49,X0_49),k1_zfmisc_1(k2_zfmisc_1(X4_49,X2_49)))
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X3_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_28]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1427,plain,
% 3.81/0.99      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.81/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.81/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.81/0.99      | ~ v1_funct_1(sK3)
% 3.81/0.99      | ~ v1_funct_1(sK2) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_794]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2035,plain,
% 3.81/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_1368,c_43,c_41,c_40,c_38,c_781,c_1427]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3289,plain,
% 3.81/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_3287,c_2035]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_44,plain,
% 3.81/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3618,plain,
% 3.81/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_3289,c_44]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4929,plain,
% 3.81/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.81/0.99      | v2_funct_1(sK3) = iProver_top
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_4927,c_3618]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_46,plain,
% 3.81/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1502,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.81/0.99      | v1_relat_1(sK2) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_797]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1503,plain,
% 3.81/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.81/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1502]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4933,plain,
% 3.81/0.99      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.81/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_4929,c_44,c_46,c_1503]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4937,plain,
% 3.81/0.99      ( v2_funct_1(sK3) = iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1344,c_4933]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_14,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0)
% 3.81/0.99      | ~ v1_relat_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.81/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_800,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0_49)
% 3.81/0.99      | ~ v1_relat_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | k2_funct_1(k2_funct_1(X0_49)) = X0_49 ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1354,plain,
% 3.81/0.99      ( k2_funct_1(k2_funct_1(X0_49)) = X0_49
% 3.81/0.99      | v2_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5244,plain,
% 3.81/0.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_4937,c_1354]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1744,plain,
% 3.81/0.99      ( ~ v2_funct_1(sK3)
% 3.81/0.99      | ~ v1_relat_1(sK3)
% 3.81/0.99      | ~ v1_funct_1(sK3)
% 3.81/0.99      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_800]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1745,plain,
% 3.81/0.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 3.81/0.99      | v2_funct_1(sK3) != iProver_top
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1744]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6016,plain,
% 3.81/0.99      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_5244,c_47,c_49,c_1456,c_1745,c_4937]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_13,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0)
% 3.81/0.99      | ~ v1_relat_1(X0)
% 3.81/0.99      | ~ v1_relat_1(X1)
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X1)
% 3.81/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 3.81/0.99      | k1_relat_1(X0) != k2_relat_1(X1)
% 3.81/0.99      | k2_funct_1(X0) = X1 ),
% 3.81/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_801,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0_49)
% 3.81/0.99      | ~ v1_relat_1(X0_49)
% 3.81/0.99      | ~ v1_relat_1(X1_49)
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X1_49)
% 3.81/0.99      | k5_relat_1(X1_49,X0_49) != k6_partfun1(k2_relat_1(X0_49))
% 3.81/0.99      | k1_relat_1(X0_49) != k2_relat_1(X1_49)
% 3.81/0.99      | k2_funct_1(X0_49) = X1_49 ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1353,plain,
% 3.81/0.99      ( k5_relat_1(X0_49,X1_49) != k6_partfun1(k2_relat_1(X1_49))
% 3.81/0.99      | k1_relat_1(X1_49) != k2_relat_1(X0_49)
% 3.81/0.99      | k2_funct_1(X1_49) = X0_49
% 3.81/0.99      | v2_funct_1(X1_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X1_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X1_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3712,plain,
% 3.81/0.99      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.81/0.99      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.81/0.99      | k2_funct_1(sK3) = sK2
% 3.81/0.99      | v2_funct_1(sK3) != iProver_top
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_3618,c_1353]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3714,plain,
% 3.81/0.99      ( k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.81/0.99      | k2_funct_1(sK3) = sK2
% 3.81/0.99      | sK1 != sK1
% 3.81/0.99      | v2_funct_1(sK3) != iProver_top
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_3712,c_2163,c_2233]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3715,plain,
% 3.81/0.99      ( k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 3.81/0.99      | k2_funct_1(sK3) = sK2
% 3.81/0.99      | v2_funct_1(sK3) != iProver_top
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(equality_resolution_simp,[status(thm)],[c_3714]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_35,negated_conjecture,
% 3.81/0.99      ( v2_funct_1(sK2) ),
% 3.81/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_51,plain,
% 3.81/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1,plain,
% 3.81/0.99      ( ~ v1_relat_1(X0)
% 3.81/0.99      | v1_relat_1(k2_funct_1(X0))
% 3.81/0.99      | ~ v1_funct_1(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_811,plain,
% 3.81/0.99      ( ~ v1_relat_1(X0_49)
% 3.81/0.99      | v1_relat_1(k2_funct_1(X0_49))
% 3.81/0.99      | ~ v1_funct_1(X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1720,plain,
% 3.81/0.99      ( v1_relat_1(k2_funct_1(sK2))
% 3.81/0.99      | ~ v1_relat_1(sK2)
% 3.81/0.99      | ~ v1_funct_1(sK2) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_811]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1721,plain,
% 3.81/0.99      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1720]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1723,plain,
% 3.81/0.99      ( v1_relat_1(k2_funct_1(sK3))
% 3.81/0.99      | ~ v1_relat_1(sK3)
% 3.81/0.99      | ~ v1_funct_1(sK3) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_811]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1724,plain,
% 3.81/0.99      ( v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_1723]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_0,plain,
% 3.81/0.99      ( ~ v1_relat_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | v1_funct_1(k2_funct_1(X0)) ),
% 3.81/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_812,plain,
% 3.81/0.99      ( ~ v1_relat_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | v1_funct_1(k2_funct_1(X0_49)) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2694,plain,
% 3.81/0.99      ( ~ v1_relat_1(sK3)
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK3))
% 3.81/0.99      | ~ v1_funct_1(sK3) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_812]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2695,plain,
% 3.81/0.99      ( v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_2694]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4189,plain,
% 3.81/0.99      ( ~ v1_relat_1(sK2)
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.81/0.99      | ~ v1_funct_1(sK2) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_812]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4190,plain,
% 3.81/0.99      ( v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_4189]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0)
% 3.81/0.99      | v2_funct_1(k2_funct_1(X0))
% 3.81/0.99      | ~ v1_relat_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_808,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0_49)
% 3.81/0.99      | v2_funct_1(k2_funct_1(X0_49))
% 3.81/0.99      | ~ v1_relat_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4224,plain,
% 3.81/0.99      ( v2_funct_1(k2_funct_1(sK2))
% 3.81/0.99      | ~ v2_funct_1(sK2)
% 3.81/0.99      | ~ v1_relat_1(sK2)
% 3.81/0.99      | ~ v1_funct_1(sK2) ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_808]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4225,plain,
% 3.81/0.99      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.81/0.99      | v2_funct_1(sK2) != iProver_top
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_4224]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_9,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0)
% 3.81/0.99      | ~ v1_relat_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_805,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0_49)
% 3.81/0.99      | ~ v1_relat_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | k2_relat_1(k2_funct_1(X0_49)) = k1_relat_1(X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1349,plain,
% 3.81/0.99      ( k2_relat_1(k2_funct_1(X0_49)) = k1_relat_1(X0_49)
% 3.81/0.99      | v2_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_805]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5243,plain,
% 3.81/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_4937,c_1349]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5246,plain,
% 3.81/0.99      ( k2_relat_1(k2_funct_1(sK3)) = sK1
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_5243,c_2163]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_787,negated_conjecture,
% 3.81/0.99      ( v2_funct_1(sK2) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_35]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1363,plain,
% 3.81/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_15,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0)
% 3.81/0.99      | ~ v2_funct_1(X1)
% 3.81/0.99      | ~ v1_relat_1(X0)
% 3.81/0.99      | ~ v1_relat_1(X1)
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X1)
% 3.81/0.99      | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
% 3.81/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_799,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0_49)
% 3.81/0.99      | ~ v2_funct_1(X1_49)
% 3.81/0.99      | ~ v1_relat_1(X0_49)
% 3.81/0.99      | ~ v1_relat_1(X1_49)
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X1_49)
% 3.81/0.99      | k5_relat_1(k2_funct_1(X1_49),k2_funct_1(X0_49)) = k2_funct_1(k5_relat_1(X0_49,X1_49)) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1355,plain,
% 3.81/0.99      ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(X1_49)) = k2_funct_1(k5_relat_1(X1_49,X0_49))
% 3.81/0.99      | v2_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v2_funct_1(X1_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X1_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X1_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_3811,plain,
% 3.81/0.99      ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,X0_49))
% 3.81/0.99      | v2_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1363,c_1355]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4094,plain,
% 3.81/0.99      ( v1_funct_1(X0_49) != iProver_top
% 3.81/0.99      | k5_relat_1(k2_funct_1(X0_49),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,X0_49))
% 3.81/0.99      | v2_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_3811,c_44,c_46,c_1503]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_4095,plain,
% 3.81/0.99      ( k5_relat_1(k2_funct_1(X0_49),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,X0_49))
% 3.81/0.99      | v2_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(renaming,[status(thm)],[c_4094]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5239,plain,
% 3.81/0.99      ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,sK3))
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_4937,c_4095]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5248,plain,
% 3.81/0.99      ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) = k2_funct_1(k6_partfun1(sK0))
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_5239,c_3618]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_16,plain,
% 3.81/0.99      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_798,plain,
% 3.81/0.99      ( k2_funct_1(k6_partfun1(X0_49)) = k6_partfun1(X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5249,plain,
% 3.81/0.99      ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.81/0.99      | v1_relat_1(sK3) != iProver_top
% 3.81/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.81/0.99      inference(demodulation,[status(thm)],[c_5248,c_798]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5262,plain,
% 3.81/0.99      ( k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_5249,c_47,c_49,c_1456]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5264,plain,
% 3.81/0.99      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK3))
% 3.81/0.99      | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(sK0)
% 3.81/0.99      | k2_funct_1(k2_funct_1(sK2)) = k2_funct_1(sK3)
% 3.81/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.81/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 3.81/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_5262,c_1353]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2593,plain,
% 3.81/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1363,c_1354]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2049,plain,
% 3.81/0.99      ( ~ v2_funct_1(sK2)
% 3.81/0.99      | ~ v1_relat_1(sK2)
% 3.81/0.99      | ~ v1_funct_1(sK2)
% 3.81/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.81/0.99      inference(instantiation,[status(thm)],[c_800]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2732,plain,
% 3.81/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_2593,c_43,c_41,c_35,c_1502,c_2049]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_10,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0)
% 3.81/0.99      | ~ v1_relat_1(X0)
% 3.81/0.99      | ~ v1_funct_1(X0)
% 3.81/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.81/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_804,plain,
% 3.81/0.99      ( ~ v2_funct_1(X0_49)
% 3.81/0.99      | ~ v1_relat_1(X0_49)
% 3.81/0.99      | ~ v1_funct_1(X0_49)
% 3.81/0.99      | k1_relat_1(k2_funct_1(X0_49)) = k2_relat_1(X0_49) ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_1350,plain,
% 3.81/0.99      ( k1_relat_1(k2_funct_1(X0_49)) = k2_relat_1(X0_49)
% 3.81/0.99      | v2_funct_1(X0_49) != iProver_top
% 3.81/0.99      | v1_relat_1(X0_49) != iProver_top
% 3.81/0.99      | v1_funct_1(X0_49) != iProver_top ),
% 3.81/0.99      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2675,plain,
% 3.81/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1363,c_1350]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2679,plain,
% 3.81/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_2675,c_2233]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2738,plain,
% 3.81/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_2679,c_44,c_46,c_1503]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2602,plain,
% 3.81/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1363,c_1349]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2160,plain,
% 3.81/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.81/0.99      inference(superposition,[status(thm)],[c_1366,c_1357]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_42,negated_conjecture,
% 3.81/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.81/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_542,plain,
% 3.81/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.81/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.81/0.99      | sK0 != X1
% 3.81/0.99      | sK1 != X2
% 3.81/0.99      | sK2 != X0
% 3.81/0.99      | k1_xboole_0 = X2 ),
% 3.81/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_42]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_543,plain,
% 3.81/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.81/0.99      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.81/0.99      | k1_xboole_0 = sK1 ),
% 3.81/0.99      inference(unflattening,[status(thm)],[c_542]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_33,negated_conjecture,
% 3.81/0.99      ( k1_xboole_0 != sK1 ),
% 3.81/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_545,plain,
% 3.81/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_543,c_41,c_33]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_775,plain,
% 3.81/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_545]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2162,plain,
% 3.81/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_2160,c_775]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2606,plain,
% 3.81/0.99      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 3.81/0.99      | v1_relat_1(sK2) != iProver_top
% 3.81/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_2602,c_2162]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_2850,plain,
% 3.81/0.99      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_2606,c_44,c_46,c_1503]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5265,plain,
% 3.81/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.81/0.99      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 3.81/0.99      | k2_funct_1(sK3) = sK2
% 3.81/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.81/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 3.81/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.81/0.99      inference(light_normalisation,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_5264,c_2732,c_2738,c_2850]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5266,plain,
% 3.81/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.81/0.99      | k2_funct_1(sK3) = sK2
% 3.81/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.81/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 3.81/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.81/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.81/0.99      inference(equality_resolution_simp,[status(thm)],[c_5265]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_5508,plain,
% 3.81/0.99      ( k2_funct_1(sK3) = sK2 ),
% 3.81/0.99      inference(global_propositional_subsumption,
% 3.81/0.99                [status(thm)],
% 3.81/0.99                [c_3715,c_44,c_46,c_47,c_49,c_51,c_1456,c_1503,c_1721,
% 3.81/0.99                 c_1724,c_2695,c_4190,c_4225,c_5246,c_5266]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_6018,plain,
% 3.81/0.99      ( k2_funct_1(sK2) = sK3 ),
% 3.81/0.99      inference(light_normalisation,[status(thm)],[c_6016,c_5508]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_32,negated_conjecture,
% 3.81/0.99      ( k2_funct_1(sK2) != sK3 ),
% 3.81/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(c_790,negated_conjecture,
% 3.81/0.99      ( k2_funct_1(sK2) != sK3 ),
% 3.81/0.99      inference(subtyping,[status(esa)],[c_32]) ).
% 3.81/0.99  
% 3.81/0.99  cnf(contradiction,plain,
% 3.81/0.99      ( $false ),
% 3.81/0.99      inference(minisat,[status(thm)],[c_6018,c_790]) ).
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/0.99  
% 3.81/0.99  ------                               Statistics
% 3.81/0.99  
% 3.81/0.99  ------ General
% 3.81/0.99  
% 3.81/0.99  abstr_ref_over_cycles:                  0
% 3.81/0.99  abstr_ref_under_cycles:                 0
% 3.81/0.99  gc_basic_clause_elim:                   0
% 3.81/0.99  forced_gc_time:                         0
% 3.81/0.99  parsing_time:                           0.01
% 3.81/0.99  unif_index_cands_time:                  0.
% 3.81/0.99  unif_index_add_time:                    0.
% 3.81/0.99  orderings_time:                         0.
% 3.81/0.99  out_proof_time:                         0.016
% 3.81/0.99  total_time:                             0.23
% 3.81/0.99  num_of_symbols:                         55
% 3.81/0.99  num_of_terms:                           7818
% 3.81/0.99  
% 3.81/0.99  ------ Preprocessing
% 3.81/0.99  
% 3.81/0.99  num_of_splits:                          0
% 3.81/0.99  num_of_split_atoms:                     0
% 3.81/0.99  num_of_reused_defs:                     0
% 3.81/0.99  num_eq_ax_congr_red:                    2
% 3.81/0.99  num_of_sem_filtered_clauses:            1
% 3.81/0.99  num_of_subtypes:                        3
% 3.81/0.99  monotx_restored_types:                  0
% 3.81/0.99  sat_num_of_epr_types:                   0
% 3.81/0.99  sat_num_of_non_cyclic_types:            0
% 3.81/0.99  sat_guarded_non_collapsed_types:        1
% 3.81/0.99  num_pure_diseq_elim:                    0
% 3.81/0.99  simp_replaced_by:                       0
% 3.81/0.99  res_preprocessed:                       193
% 3.81/0.99  prep_upred:                             0
% 3.81/0.99  prep_unflattend:                        42
% 3.81/0.99  smt_new_axioms:                         0
% 3.81/0.99  pred_elim_cands:                        4
% 3.81/0.99  pred_elim:                              2
% 3.81/0.99  pred_elim_cl:                           4
% 3.81/0.99  pred_elim_cycles:                       4
% 3.81/0.99  merged_defs:                            0
% 3.81/0.99  merged_defs_ncl:                        0
% 3.81/0.99  bin_hyper_res:                          0
% 3.81/0.99  prep_cycles:                            4
% 3.81/0.99  pred_elim_time:                         0.005
% 3.81/0.99  splitting_time:                         0.
% 3.81/0.99  sem_filter_time:                        0.
% 3.81/0.99  monotx_time:                            0.
% 3.81/0.99  subtype_inf_time:                       0.
% 3.81/0.99  
% 3.81/0.99  ------ Problem properties
% 3.81/0.99  
% 3.81/0.99  clauses:                                38
% 3.81/0.99  conjectures:                            9
% 3.81/0.99  epr:                                    5
% 3.81/0.99  horn:                                   38
% 3.81/0.99  ground:                                 16
% 3.81/0.99  unary:                                  15
% 3.81/0.99  binary:                                 4
% 3.81/0.99  lits:                                   109
% 3.81/0.99  lits_eq:                                30
% 3.81/0.99  fd_pure:                                0
% 3.81/0.99  fd_pseudo:                              0
% 3.81/0.99  fd_cond:                                0
% 3.81/0.99  fd_pseudo_cond:                         1
% 3.81/0.99  ac_symbols:                             0
% 3.81/0.99  
% 3.81/0.99  ------ Propositional Solver
% 3.81/0.99  
% 3.81/0.99  prop_solver_calls:                      32
% 3.81/0.99  prop_fast_solver_calls:                 1557
% 3.81/0.99  smt_solver_calls:                       0
% 3.81/0.99  smt_fast_solver_calls:                  0
% 3.81/0.99  prop_num_of_clauses:                    2848
% 3.81/0.99  prop_preprocess_simplified:             7268
% 3.81/0.99  prop_fo_subsumed:                       104
% 3.81/0.99  prop_solver_time:                       0.
% 3.81/0.99  smt_solver_time:                        0.
% 3.81/0.99  smt_fast_solver_time:                   0.
% 3.81/0.99  prop_fast_solver_time:                  0.
% 3.81/0.99  prop_unsat_core_time:                   0.
% 3.81/0.99  
% 3.81/0.99  ------ QBF
% 3.81/0.99  
% 3.81/0.99  qbf_q_res:                              0
% 3.81/0.99  qbf_num_tautologies:                    0
% 3.81/0.99  qbf_prep_cycles:                        0
% 3.81/0.99  
% 3.81/0.99  ------ BMC1
% 3.81/0.99  
% 3.81/0.99  bmc1_current_bound:                     -1
% 3.81/0.99  bmc1_last_solved_bound:                 -1
% 3.81/0.99  bmc1_unsat_core_size:                   -1
% 3.81/0.99  bmc1_unsat_core_parents_size:           -1
% 3.81/0.99  bmc1_merge_next_fun:                    0
% 3.81/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.81/0.99  
% 3.81/0.99  ------ Instantiation
% 3.81/0.99  
% 3.81/0.99  inst_num_of_clauses:                    853
% 3.81/0.99  inst_num_in_passive:                    136
% 3.81/0.99  inst_num_in_active:                     471
% 3.81/0.99  inst_num_in_unprocessed:                246
% 3.81/0.99  inst_num_of_loops:                      500
% 3.81/0.99  inst_num_of_learning_restarts:          0
% 3.81/0.99  inst_num_moves_active_passive:          23
% 3.81/0.99  inst_lit_activity:                      0
% 3.81/0.99  inst_lit_activity_moves:                0
% 3.81/0.99  inst_num_tautologies:                   0
% 3.81/0.99  inst_num_prop_implied:                  0
% 3.81/0.99  inst_num_existing_simplified:           0
% 3.81/0.99  inst_num_eq_res_simplified:             0
% 3.81/0.99  inst_num_child_elim:                    0
% 3.81/0.99  inst_num_of_dismatching_blockings:      357
% 3.81/0.99  inst_num_of_non_proper_insts:           894
% 3.81/0.99  inst_num_of_duplicates:                 0
% 3.81/0.99  inst_inst_num_from_inst_to_res:         0
% 3.81/0.99  inst_dismatching_checking_time:         0.
% 3.81/0.99  
% 3.81/0.99  ------ Resolution
% 3.81/0.99  
% 3.81/0.99  res_num_of_clauses:                     0
% 3.81/0.99  res_num_in_passive:                     0
% 3.81/0.99  res_num_in_active:                      0
% 3.81/0.99  res_num_of_loops:                       197
% 3.81/0.99  res_forward_subset_subsumed:            93
% 3.81/0.99  res_backward_subset_subsumed:           0
% 3.81/0.99  res_forward_subsumed:                   0
% 3.81/0.99  res_backward_subsumed:                  0
% 3.81/0.99  res_forward_subsumption_resolution:     1
% 3.81/0.99  res_backward_subsumption_resolution:    0
% 3.81/0.99  res_clause_to_clause_subsumption:       302
% 3.81/0.99  res_orphan_elimination:                 0
% 3.81/0.99  res_tautology_del:                      102
% 3.81/0.99  res_num_eq_res_simplified:              0
% 3.81/0.99  res_num_sel_changes:                    0
% 3.81/0.99  res_moves_from_active_to_pass:          0
% 3.81/0.99  
% 3.81/0.99  ------ Superposition
% 3.81/0.99  
% 3.81/0.99  sup_time_total:                         0.
% 3.81/0.99  sup_time_generating:                    0.
% 3.81/0.99  sup_time_sim_full:                      0.
% 3.81/0.99  sup_time_sim_immed:                     0.
% 3.81/0.99  
% 3.81/0.99  sup_num_of_clauses:                     139
% 3.81/0.99  sup_num_in_active:                      93
% 3.81/0.99  sup_num_in_passive:                     46
% 3.81/0.99  sup_num_of_loops:                       98
% 3.81/0.99  sup_fw_superposition:                   90
% 3.81/0.99  sup_bw_superposition:                   62
% 3.81/0.99  sup_immediate_simplified:               67
% 3.81/0.99  sup_given_eliminated:                   0
% 3.81/0.99  comparisons_done:                       0
% 3.81/0.99  comparisons_avoided:                    0
% 3.81/0.99  
% 3.81/0.99  ------ Simplifications
% 3.81/0.99  
% 3.81/0.99  
% 3.81/0.99  sim_fw_subset_subsumed:                 17
% 3.81/0.99  sim_bw_subset_subsumed:                 0
% 3.81/0.99  sim_fw_subsumed:                        2
% 3.81/0.99  sim_bw_subsumed:                        2
% 3.81/0.99  sim_fw_subsumption_res:                 0
% 3.81/0.99  sim_bw_subsumption_res:                 0
% 3.81/0.99  sim_tautology_del:                      1
% 3.81/0.99  sim_eq_tautology_del:                   20
% 3.81/0.99  sim_eq_res_simp:                        3
% 3.81/0.99  sim_fw_demodulated:                     5
% 3.81/0.99  sim_bw_demodulated:                     3
% 3.81/0.99  sim_light_normalised:                   50
% 3.81/0.99  sim_joinable_taut:                      0
% 3.81/0.99  sim_joinable_simp:                      0
% 3.81/0.99  sim_ac_normalised:                      0
% 3.81/0.99  sim_smt_subsumption:                    0
% 3.81/0.99  
%------------------------------------------------------------------------------
