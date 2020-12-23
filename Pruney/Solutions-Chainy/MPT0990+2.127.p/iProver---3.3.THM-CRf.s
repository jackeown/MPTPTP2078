%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:23 EST 2020

% Result     : Theorem 11.28s
% Output     : CNFRefutation 11.28s
% Verified   : 
% Statistics : Number of formulae       :  206 (1667 expanded)
%              Number of clauses        :  127 ( 478 expanded)
%              Number of leaves         :   22 ( 435 expanded)
%              Depth                    :   24
%              Number of atoms          :  730 (13860 expanded)
%              Number of equality atoms :  358 (5030 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

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
    inference(ennf_transformation,[],[f23])).

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

fof(f89,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f77,f81])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f104,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f81])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f70,f81])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f81])).

fof(f97,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f99,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f56])).

fof(f100,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1398,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1420,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1426,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1400,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1427,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3062,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_1427])).

cnf(c_3176,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_3062])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1403,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3061,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1427])).

cnf(c_3161,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1426,c_3061])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1424,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3289,plain,
    ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3161,c_1424])).

cnf(c_9583,plain,
    ( k5_relat_1(sK3,k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(sK3,sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3176,c_3289])).

cnf(c_10317,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(X0)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_9583])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1401,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3290,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3176,c_1424])).

cnf(c_12372,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3161,c_3290])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1411,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4674,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1411])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4902,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4674,c_46])).

cnf(c_4903,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4902])).

cnf(c_4911,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_4903])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_504,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_512,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_504,c_20])).

cnf(c_1395,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1513,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2230,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1395,c_42,c_40,c_39,c_37,c_512,c_1513])).

cnf(c_4912,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4911,c_2230])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5021,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4912,c_43])).

cnf(c_12377,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12372,c_5021])).

cnf(c_19997,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_12377])).

cnf(c_22664,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_19997])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1422,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3206,plain,
    ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_3176,c_1422])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1415,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2443,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1400,c_1415])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2444,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2443,c_36])).

cnf(c_3207,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3206,c_2444])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_516,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_517,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_605,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_517])).

cnf(c_1394,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_1912,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1394])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_44,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2237,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1912,c_43,c_44,c_45,c_46,c_47,c_48])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1405,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3210,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_1405])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_829,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_862,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_830,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1511,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_1512,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_12,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3080,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3081,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3080])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1409,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5157,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_1409])).

cnf(c_5164,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5157,c_43,c_44,c_45])).

cnf(c_5165,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5164])).

cnf(c_5168,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2230,c_5165])).

cnf(c_9021,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3210,c_46,c_47,c_48,c_33,c_862,c_1512,c_3081,c_5168])).

cnf(c_5204,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5168,c_46,c_47,c_48,c_33,c_862,c_1512,c_3081])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1416,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5209,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5204,c_1416])).

cnf(c_2442,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1403,c_1415])).

cnf(c_2445,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2442,c_2237])).

cnf(c_5210,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5209,c_2445])).

cnf(c_9789,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5210,c_46,c_3161])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1423,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3009,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1420,c_1423])).

cnf(c_5430,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_3009])).

cnf(c_5965,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5430,c_3161])).

cnf(c_9791,plain,
    ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
    inference(demodulation,[status(thm)],[c_9789,c_5965])).

cnf(c_22670,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22664,c_3207,c_9021,c_9791])).

cnf(c_23102,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22670,c_3161])).

cnf(c_23162,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_23102,c_9021])).

cnf(c_23420,plain,
    ( k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10317,c_23162])).

cnf(c_23427,plain,
    ( k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_23420])).

cnf(c_3202,plain,
    ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_3161,c_1422])).

cnf(c_3203,plain,
    ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3202,c_2445])).

cnf(c_3209,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_36,c_1405])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1474,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1590,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_1779,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_3483,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3209,c_42,c_41,c_40,c_36,c_34,c_32,c_1779])).

cnf(c_5431,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_3009])).

cnf(c_1404,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3131,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_1416])).

cnf(c_3132,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3131,c_2444])).

cnf(c_3195,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3132,c_43,c_3176])).

cnf(c_5434,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5431,c_3195])).

cnf(c_6062,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5434,c_3176])).

cnf(c_23433,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23427,c_3203,c_3483,c_6062])).

cnf(c_31,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23433,c_3176,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:39:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.28/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.28/2.01  
% 11.28/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.28/2.01  
% 11.28/2.01  ------  iProver source info
% 11.28/2.01  
% 11.28/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.28/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.28/2.01  git: non_committed_changes: false
% 11.28/2.01  git: last_make_outside_of_git: false
% 11.28/2.01  
% 11.28/2.01  ------ 
% 11.28/2.01  
% 11.28/2.01  ------ Input Options
% 11.28/2.01  
% 11.28/2.01  --out_options                           all
% 11.28/2.01  --tptp_safe_out                         true
% 11.28/2.01  --problem_path                          ""
% 11.28/2.01  --include_path                          ""
% 11.28/2.01  --clausifier                            res/vclausify_rel
% 11.28/2.01  --clausifier_options                    ""
% 11.28/2.01  --stdin                                 false
% 11.28/2.01  --stats_out                             all
% 11.28/2.01  
% 11.28/2.01  ------ General Options
% 11.28/2.01  
% 11.28/2.01  --fof                                   false
% 11.28/2.01  --time_out_real                         305.
% 11.28/2.01  --time_out_virtual                      -1.
% 11.28/2.01  --symbol_type_check                     false
% 11.28/2.01  --clausify_out                          false
% 11.28/2.01  --sig_cnt_out                           false
% 11.28/2.01  --trig_cnt_out                          false
% 11.28/2.01  --trig_cnt_out_tolerance                1.
% 11.28/2.01  --trig_cnt_out_sk_spl                   false
% 11.28/2.01  --abstr_cl_out                          false
% 11.28/2.01  
% 11.28/2.01  ------ Global Options
% 11.28/2.01  
% 11.28/2.01  --schedule                              default
% 11.28/2.01  --add_important_lit                     false
% 11.28/2.01  --prop_solver_per_cl                    1000
% 11.28/2.01  --min_unsat_core                        false
% 11.28/2.01  --soft_assumptions                      false
% 11.28/2.01  --soft_lemma_size                       3
% 11.28/2.01  --prop_impl_unit_size                   0
% 11.28/2.01  --prop_impl_unit                        []
% 11.28/2.01  --share_sel_clauses                     true
% 11.28/2.01  --reset_solvers                         false
% 11.28/2.01  --bc_imp_inh                            [conj_cone]
% 11.28/2.01  --conj_cone_tolerance                   3.
% 11.28/2.01  --extra_neg_conj                        none
% 11.28/2.01  --large_theory_mode                     true
% 11.28/2.01  --prolific_symb_bound                   200
% 11.28/2.01  --lt_threshold                          2000
% 11.28/2.01  --clause_weak_htbl                      true
% 11.28/2.01  --gc_record_bc_elim                     false
% 11.28/2.01  
% 11.28/2.01  ------ Preprocessing Options
% 11.28/2.01  
% 11.28/2.01  --preprocessing_flag                    true
% 11.28/2.01  --time_out_prep_mult                    0.1
% 11.28/2.01  --splitting_mode                        input
% 11.28/2.01  --splitting_grd                         true
% 11.28/2.01  --splitting_cvd                         false
% 11.28/2.01  --splitting_cvd_svl                     false
% 11.28/2.01  --splitting_nvd                         32
% 11.28/2.01  --sub_typing                            true
% 11.28/2.01  --prep_gs_sim                           true
% 11.28/2.01  --prep_unflatten                        true
% 11.28/2.01  --prep_res_sim                          true
% 11.28/2.01  --prep_upred                            true
% 11.28/2.01  --prep_sem_filter                       exhaustive
% 11.28/2.01  --prep_sem_filter_out                   false
% 11.28/2.01  --pred_elim                             true
% 11.28/2.01  --res_sim_input                         true
% 11.28/2.01  --eq_ax_congr_red                       true
% 11.28/2.01  --pure_diseq_elim                       true
% 11.28/2.01  --brand_transform                       false
% 11.28/2.01  --non_eq_to_eq                          false
% 11.28/2.01  --prep_def_merge                        true
% 11.28/2.01  --prep_def_merge_prop_impl              false
% 11.28/2.01  --prep_def_merge_mbd                    true
% 11.28/2.01  --prep_def_merge_tr_red                 false
% 11.28/2.01  --prep_def_merge_tr_cl                  false
% 11.28/2.01  --smt_preprocessing                     true
% 11.28/2.01  --smt_ac_axioms                         fast
% 11.28/2.01  --preprocessed_out                      false
% 11.28/2.01  --preprocessed_stats                    false
% 11.28/2.01  
% 11.28/2.01  ------ Abstraction refinement Options
% 11.28/2.01  
% 11.28/2.01  --abstr_ref                             []
% 11.28/2.01  --abstr_ref_prep                        false
% 11.28/2.01  --abstr_ref_until_sat                   false
% 11.28/2.01  --abstr_ref_sig_restrict                funpre
% 11.28/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.28/2.01  --abstr_ref_under                       []
% 11.28/2.01  
% 11.28/2.01  ------ SAT Options
% 11.28/2.01  
% 11.28/2.01  --sat_mode                              false
% 11.28/2.01  --sat_fm_restart_options                ""
% 11.28/2.01  --sat_gr_def                            false
% 11.28/2.01  --sat_epr_types                         true
% 11.28/2.01  --sat_non_cyclic_types                  false
% 11.28/2.01  --sat_finite_models                     false
% 11.28/2.01  --sat_fm_lemmas                         false
% 11.28/2.01  --sat_fm_prep                           false
% 11.28/2.01  --sat_fm_uc_incr                        true
% 11.28/2.01  --sat_out_model                         small
% 11.28/2.01  --sat_out_clauses                       false
% 11.28/2.01  
% 11.28/2.01  ------ QBF Options
% 11.28/2.01  
% 11.28/2.01  --qbf_mode                              false
% 11.28/2.01  --qbf_elim_univ                         false
% 11.28/2.01  --qbf_dom_inst                          none
% 11.28/2.01  --qbf_dom_pre_inst                      false
% 11.28/2.01  --qbf_sk_in                             false
% 11.28/2.01  --qbf_pred_elim                         true
% 11.28/2.01  --qbf_split                             512
% 11.28/2.01  
% 11.28/2.01  ------ BMC1 Options
% 11.28/2.01  
% 11.28/2.01  --bmc1_incremental                      false
% 11.28/2.01  --bmc1_axioms                           reachable_all
% 11.28/2.01  --bmc1_min_bound                        0
% 11.28/2.01  --bmc1_max_bound                        -1
% 11.28/2.01  --bmc1_max_bound_default                -1
% 11.28/2.01  --bmc1_symbol_reachability              true
% 11.28/2.01  --bmc1_property_lemmas                  false
% 11.28/2.01  --bmc1_k_induction                      false
% 11.28/2.01  --bmc1_non_equiv_states                 false
% 11.28/2.01  --bmc1_deadlock                         false
% 11.28/2.01  --bmc1_ucm                              false
% 11.28/2.01  --bmc1_add_unsat_core                   none
% 11.28/2.01  --bmc1_unsat_core_children              false
% 11.28/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.28/2.01  --bmc1_out_stat                         full
% 11.28/2.01  --bmc1_ground_init                      false
% 11.28/2.01  --bmc1_pre_inst_next_state              false
% 11.28/2.01  --bmc1_pre_inst_state                   false
% 11.28/2.01  --bmc1_pre_inst_reach_state             false
% 11.28/2.01  --bmc1_out_unsat_core                   false
% 11.28/2.01  --bmc1_aig_witness_out                  false
% 11.28/2.01  --bmc1_verbose                          false
% 11.28/2.01  --bmc1_dump_clauses_tptp                false
% 11.28/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.28/2.01  --bmc1_dump_file                        -
% 11.28/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.28/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.28/2.01  --bmc1_ucm_extend_mode                  1
% 11.28/2.01  --bmc1_ucm_init_mode                    2
% 11.28/2.01  --bmc1_ucm_cone_mode                    none
% 11.28/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.28/2.01  --bmc1_ucm_relax_model                  4
% 11.28/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.28/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.28/2.01  --bmc1_ucm_layered_model                none
% 11.28/2.01  --bmc1_ucm_max_lemma_size               10
% 11.28/2.01  
% 11.28/2.01  ------ AIG Options
% 11.28/2.01  
% 11.28/2.01  --aig_mode                              false
% 11.28/2.01  
% 11.28/2.01  ------ Instantiation Options
% 11.28/2.01  
% 11.28/2.01  --instantiation_flag                    true
% 11.28/2.01  --inst_sos_flag                         true
% 11.28/2.01  --inst_sos_phase                        true
% 11.28/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.28/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.28/2.01  --inst_lit_sel_side                     num_symb
% 11.28/2.01  --inst_solver_per_active                1400
% 11.28/2.01  --inst_solver_calls_frac                1.
% 11.28/2.01  --inst_passive_queue_type               priority_queues
% 11.28/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.28/2.01  --inst_passive_queues_freq              [25;2]
% 11.28/2.01  --inst_dismatching                      true
% 11.28/2.01  --inst_eager_unprocessed_to_passive     true
% 11.28/2.01  --inst_prop_sim_given                   true
% 11.28/2.01  --inst_prop_sim_new                     false
% 11.28/2.01  --inst_subs_new                         false
% 11.28/2.01  --inst_eq_res_simp                      false
% 11.28/2.01  --inst_subs_given                       false
% 11.28/2.01  --inst_orphan_elimination               true
% 11.28/2.01  --inst_learning_loop_flag               true
% 11.28/2.01  --inst_learning_start                   3000
% 11.28/2.01  --inst_learning_factor                  2
% 11.28/2.01  --inst_start_prop_sim_after_learn       3
% 11.28/2.01  --inst_sel_renew                        solver
% 11.28/2.01  --inst_lit_activity_flag                true
% 11.28/2.01  --inst_restr_to_given                   false
% 11.28/2.01  --inst_activity_threshold               500
% 11.28/2.01  --inst_out_proof                        true
% 11.28/2.01  
% 11.28/2.01  ------ Resolution Options
% 11.28/2.01  
% 11.28/2.01  --resolution_flag                       true
% 11.28/2.01  --res_lit_sel                           adaptive
% 11.28/2.01  --res_lit_sel_side                      none
% 11.28/2.01  --res_ordering                          kbo
% 11.28/2.01  --res_to_prop_solver                    active
% 11.28/2.01  --res_prop_simpl_new                    false
% 11.28/2.01  --res_prop_simpl_given                  true
% 11.28/2.01  --res_passive_queue_type                priority_queues
% 11.28/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.28/2.01  --res_passive_queues_freq               [15;5]
% 11.28/2.01  --res_forward_subs                      full
% 11.28/2.01  --res_backward_subs                     full
% 11.28/2.01  --res_forward_subs_resolution           true
% 11.28/2.01  --res_backward_subs_resolution          true
% 11.28/2.01  --res_orphan_elimination                true
% 11.28/2.01  --res_time_limit                        2.
% 11.28/2.01  --res_out_proof                         true
% 11.28/2.01  
% 11.28/2.01  ------ Superposition Options
% 11.28/2.01  
% 11.28/2.01  --superposition_flag                    true
% 11.28/2.01  --sup_passive_queue_type                priority_queues
% 11.28/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.28/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.28/2.01  --demod_completeness_check              fast
% 11.28/2.01  --demod_use_ground                      true
% 11.28/2.01  --sup_to_prop_solver                    passive
% 11.28/2.01  --sup_prop_simpl_new                    true
% 11.28/2.01  --sup_prop_simpl_given                  true
% 11.28/2.01  --sup_fun_splitting                     true
% 11.28/2.01  --sup_smt_interval                      50000
% 11.28/2.01  
% 11.28/2.01  ------ Superposition Simplification Setup
% 11.28/2.01  
% 11.28/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.28/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.28/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.28/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.28/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.28/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.28/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.28/2.01  --sup_immed_triv                        [TrivRules]
% 11.28/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.01  --sup_immed_bw_main                     []
% 11.28/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.28/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.28/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.01  --sup_input_bw                          []
% 11.28/2.01  
% 11.28/2.01  ------ Combination Options
% 11.28/2.01  
% 11.28/2.01  --comb_res_mult                         3
% 11.28/2.01  --comb_sup_mult                         2
% 11.28/2.01  --comb_inst_mult                        10
% 11.28/2.01  
% 11.28/2.01  ------ Debug Options
% 11.28/2.01  
% 11.28/2.01  --dbg_backtrace                         false
% 11.28/2.01  --dbg_dump_prop_clauses                 false
% 11.28/2.01  --dbg_dump_prop_clauses_file            -
% 11.28/2.01  --dbg_out_stat                          false
% 11.28/2.01  ------ Parsing...
% 11.28/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.28/2.01  
% 11.28/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.28/2.01  
% 11.28/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.28/2.01  
% 11.28/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.28/2.01  ------ Proving...
% 11.28/2.01  ------ Problem Properties 
% 11.28/2.01  
% 11.28/2.01  
% 11.28/2.01  clauses                                 40
% 11.28/2.01  conjectures                             11
% 11.28/2.01  EPR                                     7
% 11.28/2.01  Horn                                    36
% 11.28/2.01  unary                                   17
% 11.28/2.01  binary                                  4
% 11.28/2.01  lits                                    136
% 11.28/2.01  lits eq                                 31
% 11.28/2.01  fd_pure                                 0
% 11.28/2.01  fd_pseudo                               0
% 11.28/2.01  fd_cond                                 4
% 11.28/2.01  fd_pseudo_cond                          0
% 11.28/2.01  AC symbols                              0
% 11.28/2.01  
% 11.28/2.01  ------ Schedule dynamic 5 is on 
% 11.28/2.01  
% 11.28/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.28/2.01  
% 11.28/2.01  
% 11.28/2.01  ------ 
% 11.28/2.01  Current options:
% 11.28/2.01  ------ 
% 11.28/2.01  
% 11.28/2.01  ------ Input Options
% 11.28/2.01  
% 11.28/2.01  --out_options                           all
% 11.28/2.01  --tptp_safe_out                         true
% 11.28/2.01  --problem_path                          ""
% 11.28/2.01  --include_path                          ""
% 11.28/2.01  --clausifier                            res/vclausify_rel
% 11.28/2.01  --clausifier_options                    ""
% 11.28/2.01  --stdin                                 false
% 11.28/2.01  --stats_out                             all
% 11.28/2.01  
% 11.28/2.01  ------ General Options
% 11.28/2.01  
% 11.28/2.01  --fof                                   false
% 11.28/2.01  --time_out_real                         305.
% 11.28/2.01  --time_out_virtual                      -1.
% 11.28/2.01  --symbol_type_check                     false
% 11.28/2.01  --clausify_out                          false
% 11.28/2.01  --sig_cnt_out                           false
% 11.28/2.01  --trig_cnt_out                          false
% 11.28/2.01  --trig_cnt_out_tolerance                1.
% 11.28/2.01  --trig_cnt_out_sk_spl                   false
% 11.28/2.01  --abstr_cl_out                          false
% 11.28/2.01  
% 11.28/2.01  ------ Global Options
% 11.28/2.01  
% 11.28/2.01  --schedule                              default
% 11.28/2.01  --add_important_lit                     false
% 11.28/2.01  --prop_solver_per_cl                    1000
% 11.28/2.01  --min_unsat_core                        false
% 11.28/2.01  --soft_assumptions                      false
% 11.28/2.01  --soft_lemma_size                       3
% 11.28/2.01  --prop_impl_unit_size                   0
% 11.28/2.01  --prop_impl_unit                        []
% 11.28/2.01  --share_sel_clauses                     true
% 11.28/2.01  --reset_solvers                         false
% 11.28/2.01  --bc_imp_inh                            [conj_cone]
% 11.28/2.01  --conj_cone_tolerance                   3.
% 11.28/2.01  --extra_neg_conj                        none
% 11.28/2.01  --large_theory_mode                     true
% 11.28/2.01  --prolific_symb_bound                   200
% 11.28/2.01  --lt_threshold                          2000
% 11.28/2.01  --clause_weak_htbl                      true
% 11.28/2.01  --gc_record_bc_elim                     false
% 11.28/2.01  
% 11.28/2.01  ------ Preprocessing Options
% 11.28/2.01  
% 11.28/2.01  --preprocessing_flag                    true
% 11.28/2.01  --time_out_prep_mult                    0.1
% 11.28/2.01  --splitting_mode                        input
% 11.28/2.01  --splitting_grd                         true
% 11.28/2.01  --splitting_cvd                         false
% 11.28/2.01  --splitting_cvd_svl                     false
% 11.28/2.01  --splitting_nvd                         32
% 11.28/2.01  --sub_typing                            true
% 11.28/2.01  --prep_gs_sim                           true
% 11.28/2.01  --prep_unflatten                        true
% 11.28/2.01  --prep_res_sim                          true
% 11.28/2.01  --prep_upred                            true
% 11.28/2.01  --prep_sem_filter                       exhaustive
% 11.28/2.01  --prep_sem_filter_out                   false
% 11.28/2.01  --pred_elim                             true
% 11.28/2.01  --res_sim_input                         true
% 11.28/2.01  --eq_ax_congr_red                       true
% 11.28/2.01  --pure_diseq_elim                       true
% 11.28/2.01  --brand_transform                       false
% 11.28/2.01  --non_eq_to_eq                          false
% 11.28/2.01  --prep_def_merge                        true
% 11.28/2.01  --prep_def_merge_prop_impl              false
% 11.28/2.01  --prep_def_merge_mbd                    true
% 11.28/2.01  --prep_def_merge_tr_red                 false
% 11.28/2.01  --prep_def_merge_tr_cl                  false
% 11.28/2.01  --smt_preprocessing                     true
% 11.28/2.01  --smt_ac_axioms                         fast
% 11.28/2.01  --preprocessed_out                      false
% 11.28/2.01  --preprocessed_stats                    false
% 11.28/2.01  
% 11.28/2.01  ------ Abstraction refinement Options
% 11.28/2.01  
% 11.28/2.01  --abstr_ref                             []
% 11.28/2.01  --abstr_ref_prep                        false
% 11.28/2.01  --abstr_ref_until_sat                   false
% 11.28/2.01  --abstr_ref_sig_restrict                funpre
% 11.28/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.28/2.01  --abstr_ref_under                       []
% 11.28/2.01  
% 11.28/2.01  ------ SAT Options
% 11.28/2.01  
% 11.28/2.01  --sat_mode                              false
% 11.28/2.01  --sat_fm_restart_options                ""
% 11.28/2.01  --sat_gr_def                            false
% 11.28/2.01  --sat_epr_types                         true
% 11.28/2.01  --sat_non_cyclic_types                  false
% 11.28/2.01  --sat_finite_models                     false
% 11.28/2.01  --sat_fm_lemmas                         false
% 11.28/2.01  --sat_fm_prep                           false
% 11.28/2.01  --sat_fm_uc_incr                        true
% 11.28/2.01  --sat_out_model                         small
% 11.28/2.01  --sat_out_clauses                       false
% 11.28/2.01  
% 11.28/2.01  ------ QBF Options
% 11.28/2.01  
% 11.28/2.01  --qbf_mode                              false
% 11.28/2.01  --qbf_elim_univ                         false
% 11.28/2.01  --qbf_dom_inst                          none
% 11.28/2.01  --qbf_dom_pre_inst                      false
% 11.28/2.01  --qbf_sk_in                             false
% 11.28/2.01  --qbf_pred_elim                         true
% 11.28/2.01  --qbf_split                             512
% 11.28/2.01  
% 11.28/2.01  ------ BMC1 Options
% 11.28/2.01  
% 11.28/2.01  --bmc1_incremental                      false
% 11.28/2.01  --bmc1_axioms                           reachable_all
% 11.28/2.01  --bmc1_min_bound                        0
% 11.28/2.01  --bmc1_max_bound                        -1
% 11.28/2.01  --bmc1_max_bound_default                -1
% 11.28/2.01  --bmc1_symbol_reachability              true
% 11.28/2.01  --bmc1_property_lemmas                  false
% 11.28/2.01  --bmc1_k_induction                      false
% 11.28/2.01  --bmc1_non_equiv_states                 false
% 11.28/2.01  --bmc1_deadlock                         false
% 11.28/2.01  --bmc1_ucm                              false
% 11.28/2.01  --bmc1_add_unsat_core                   none
% 11.28/2.01  --bmc1_unsat_core_children              false
% 11.28/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.28/2.01  --bmc1_out_stat                         full
% 11.28/2.01  --bmc1_ground_init                      false
% 11.28/2.01  --bmc1_pre_inst_next_state              false
% 11.28/2.01  --bmc1_pre_inst_state                   false
% 11.28/2.01  --bmc1_pre_inst_reach_state             false
% 11.28/2.01  --bmc1_out_unsat_core                   false
% 11.28/2.01  --bmc1_aig_witness_out                  false
% 11.28/2.01  --bmc1_verbose                          false
% 11.28/2.01  --bmc1_dump_clauses_tptp                false
% 11.28/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.28/2.01  --bmc1_dump_file                        -
% 11.28/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.28/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.28/2.01  --bmc1_ucm_extend_mode                  1
% 11.28/2.01  --bmc1_ucm_init_mode                    2
% 11.28/2.01  --bmc1_ucm_cone_mode                    none
% 11.28/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.28/2.01  --bmc1_ucm_relax_model                  4
% 11.28/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.28/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.28/2.01  --bmc1_ucm_layered_model                none
% 11.28/2.01  --bmc1_ucm_max_lemma_size               10
% 11.28/2.01  
% 11.28/2.01  ------ AIG Options
% 11.28/2.01  
% 11.28/2.01  --aig_mode                              false
% 11.28/2.01  
% 11.28/2.01  ------ Instantiation Options
% 11.28/2.01  
% 11.28/2.01  --instantiation_flag                    true
% 11.28/2.01  --inst_sos_flag                         true
% 11.28/2.01  --inst_sos_phase                        true
% 11.28/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.28/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.28/2.01  --inst_lit_sel_side                     none
% 11.28/2.01  --inst_solver_per_active                1400
% 11.28/2.01  --inst_solver_calls_frac                1.
% 11.28/2.01  --inst_passive_queue_type               priority_queues
% 11.28/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.28/2.01  --inst_passive_queues_freq              [25;2]
% 11.28/2.01  --inst_dismatching                      true
% 11.28/2.01  --inst_eager_unprocessed_to_passive     true
% 11.28/2.01  --inst_prop_sim_given                   true
% 11.28/2.01  --inst_prop_sim_new                     false
% 11.28/2.01  --inst_subs_new                         false
% 11.28/2.01  --inst_eq_res_simp                      false
% 11.28/2.01  --inst_subs_given                       false
% 11.28/2.01  --inst_orphan_elimination               true
% 11.28/2.01  --inst_learning_loop_flag               true
% 11.28/2.01  --inst_learning_start                   3000
% 11.28/2.01  --inst_learning_factor                  2
% 11.28/2.01  --inst_start_prop_sim_after_learn       3
% 11.28/2.01  --inst_sel_renew                        solver
% 11.28/2.01  --inst_lit_activity_flag                true
% 11.28/2.01  --inst_restr_to_given                   false
% 11.28/2.01  --inst_activity_threshold               500
% 11.28/2.01  --inst_out_proof                        true
% 11.28/2.01  
% 11.28/2.01  ------ Resolution Options
% 11.28/2.01  
% 11.28/2.01  --resolution_flag                       false
% 11.28/2.01  --res_lit_sel                           adaptive
% 11.28/2.01  --res_lit_sel_side                      none
% 11.28/2.01  --res_ordering                          kbo
% 11.28/2.01  --res_to_prop_solver                    active
% 11.28/2.01  --res_prop_simpl_new                    false
% 11.28/2.01  --res_prop_simpl_given                  true
% 11.28/2.01  --res_passive_queue_type                priority_queues
% 11.28/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.28/2.01  --res_passive_queues_freq               [15;5]
% 11.28/2.01  --res_forward_subs                      full
% 11.28/2.01  --res_backward_subs                     full
% 11.28/2.01  --res_forward_subs_resolution           true
% 11.28/2.01  --res_backward_subs_resolution          true
% 11.28/2.01  --res_orphan_elimination                true
% 11.28/2.01  --res_time_limit                        2.
% 11.28/2.01  --res_out_proof                         true
% 11.28/2.01  
% 11.28/2.01  ------ Superposition Options
% 11.28/2.01  
% 11.28/2.01  --superposition_flag                    true
% 11.28/2.01  --sup_passive_queue_type                priority_queues
% 11.28/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.28/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.28/2.01  --demod_completeness_check              fast
% 11.28/2.01  --demod_use_ground                      true
% 11.28/2.01  --sup_to_prop_solver                    passive
% 11.28/2.01  --sup_prop_simpl_new                    true
% 11.28/2.01  --sup_prop_simpl_given                  true
% 11.28/2.01  --sup_fun_splitting                     true
% 11.28/2.01  --sup_smt_interval                      50000
% 11.28/2.01  
% 11.28/2.01  ------ Superposition Simplification Setup
% 11.28/2.01  
% 11.28/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.28/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.28/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.28/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.28/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.28/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.28/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.28/2.01  --sup_immed_triv                        [TrivRules]
% 11.28/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.01  --sup_immed_bw_main                     []
% 11.28/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.28/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.28/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/2.01  --sup_input_bw                          []
% 11.28/2.01  
% 11.28/2.01  ------ Combination Options
% 11.28/2.01  
% 11.28/2.01  --comb_res_mult                         3
% 11.28/2.01  --comb_sup_mult                         2
% 11.28/2.01  --comb_inst_mult                        10
% 11.28/2.01  
% 11.28/2.01  ------ Debug Options
% 11.28/2.01  
% 11.28/2.01  --dbg_backtrace                         false
% 11.28/2.01  --dbg_dump_prop_clauses                 false
% 11.28/2.01  --dbg_dump_prop_clauses_file            -
% 11.28/2.01  --dbg_out_stat                          false
% 11.28/2.01  
% 11.28/2.01  
% 11.28/2.01  
% 11.28/2.01  
% 11.28/2.01  ------ Proving...
% 11.28/2.01  
% 11.28/2.01  
% 11.28/2.01  % SZS status Theorem for theBenchmark.p
% 11.28/2.01  
% 11.28/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.28/2.01  
% 11.28/2.01  fof(f22,conjecture,(
% 11.28/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f23,negated_conjecture,(
% 11.28/2.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.28/2.01    inference(negated_conjecture,[],[f22])).
% 11.28/2.01  
% 11.28/2.01  fof(f50,plain,(
% 11.28/2.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.28/2.01    inference(ennf_transformation,[],[f23])).
% 11.28/2.01  
% 11.28/2.01  fof(f51,plain,(
% 11.28/2.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.28/2.01    inference(flattening,[],[f50])).
% 11.28/2.01  
% 11.28/2.01  fof(f55,plain,(
% 11.28/2.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.28/2.01    introduced(choice_axiom,[])).
% 11.28/2.01  
% 11.28/2.01  fof(f54,plain,(
% 11.28/2.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.28/2.01    introduced(choice_axiom,[])).
% 11.28/2.01  
% 11.28/2.01  fof(f56,plain,(
% 11.28/2.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.28/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f51,f55,f54])).
% 11.28/2.01  
% 11.28/2.01  fof(f89,plain,(
% 11.28/2.01    v1_funct_1(sK2)),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f9,axiom,(
% 11.28/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f32,plain,(
% 11.28/2.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.28/2.01    inference(ennf_transformation,[],[f9])).
% 11.28/2.01  
% 11.28/2.01  fof(f33,plain,(
% 11.28/2.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.28/2.01    inference(flattening,[],[f32])).
% 11.28/2.01  
% 11.28/2.01  fof(f67,plain,(
% 11.28/2.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f33])).
% 11.28/2.01  
% 11.28/2.01  fof(f3,axiom,(
% 11.28/2.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f60,plain,(
% 11.28/2.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.28/2.01    inference(cnf_transformation,[],[f3])).
% 11.28/2.01  
% 11.28/2.01  fof(f91,plain,(
% 11.28/2.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f1,axiom,(
% 11.28/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f25,plain,(
% 11.28/2.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.28/2.01    inference(ennf_transformation,[],[f1])).
% 11.28/2.01  
% 11.28/2.01  fof(f57,plain,(
% 11.28/2.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f25])).
% 11.28/2.01  
% 11.28/2.01  fof(f94,plain,(
% 11.28/2.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f5,axiom,(
% 11.28/2.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f29,plain,(
% 11.28/2.01    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.28/2.01    inference(ennf_transformation,[],[f5])).
% 11.28/2.01  
% 11.28/2.01  fof(f62,plain,(
% 11.28/2.01    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f29])).
% 11.28/2.01  
% 11.28/2.01  fof(f92,plain,(
% 11.28/2.01    v1_funct_1(sK3)),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f17,axiom,(
% 11.28/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f42,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.28/2.01    inference(ennf_transformation,[],[f17])).
% 11.28/2.01  
% 11.28/2.01  fof(f43,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.28/2.01    inference(flattening,[],[f42])).
% 11.28/2.01  
% 11.28/2.01  fof(f80,plain,(
% 11.28/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f43])).
% 11.28/2.01  
% 11.28/2.01  fof(f14,axiom,(
% 11.28/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f38,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.28/2.01    inference(ennf_transformation,[],[f14])).
% 11.28/2.01  
% 11.28/2.01  fof(f39,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.28/2.01    inference(flattening,[],[f38])).
% 11.28/2.01  
% 11.28/2.01  fof(f53,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.28/2.01    inference(nnf_transformation,[],[f39])).
% 11.28/2.01  
% 11.28/2.01  fof(f75,plain,(
% 11.28/2.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.28/2.01    inference(cnf_transformation,[],[f53])).
% 11.28/2.01  
% 11.28/2.01  fof(f96,plain,(
% 11.28/2.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f15,axiom,(
% 11.28/2.01    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f77,plain,(
% 11.28/2.01    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.28/2.01    inference(cnf_transformation,[],[f15])).
% 11.28/2.01  
% 11.28/2.01  fof(f18,axiom,(
% 11.28/2.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f81,plain,(
% 11.28/2.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f18])).
% 11.28/2.01  
% 11.28/2.01  fof(f107,plain,(
% 11.28/2.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.28/2.01    inference(definition_unfolding,[],[f77,f81])).
% 11.28/2.01  
% 11.28/2.01  fof(f16,axiom,(
% 11.28/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f40,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.28/2.01    inference(ennf_transformation,[],[f16])).
% 11.28/2.01  
% 11.28/2.01  fof(f41,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.28/2.01    inference(flattening,[],[f40])).
% 11.28/2.01  
% 11.28/2.01  fof(f79,plain,(
% 11.28/2.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f41])).
% 11.28/2.01  
% 11.28/2.01  fof(f8,axiom,(
% 11.28/2.01    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f31,plain,(
% 11.28/2.01    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 11.28/2.01    inference(ennf_transformation,[],[f8])).
% 11.28/2.01  
% 11.28/2.01  fof(f66,plain,(
% 11.28/2.01    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f31])).
% 11.28/2.01  
% 11.28/2.01  fof(f104,plain,(
% 11.28/2.01    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 11.28/2.01    inference(definition_unfolding,[],[f66,f81])).
% 11.28/2.01  
% 11.28/2.01  fof(f13,axiom,(
% 11.28/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f37,plain,(
% 11.28/2.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.28/2.01    inference(ennf_transformation,[],[f13])).
% 11.28/2.01  
% 11.28/2.01  fof(f74,plain,(
% 11.28/2.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.28/2.01    inference(cnf_transformation,[],[f37])).
% 11.28/2.01  
% 11.28/2.01  fof(f95,plain,(
% 11.28/2.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f19,axiom,(
% 11.28/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f44,plain,(
% 11.28/2.01    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.28/2.01    inference(ennf_transformation,[],[f19])).
% 11.28/2.01  
% 11.28/2.01  fof(f45,plain,(
% 11.28/2.01    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.28/2.01    inference(flattening,[],[f44])).
% 11.28/2.01  
% 11.28/2.01  fof(f82,plain,(
% 11.28/2.01    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f45])).
% 11.28/2.01  
% 11.28/2.01  fof(f90,plain,(
% 11.28/2.01    v1_funct_2(sK2,sK0,sK1)),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f93,plain,(
% 11.28/2.01    v1_funct_2(sK3,sK1,sK0)),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f21,axiom,(
% 11.28/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f48,plain,(
% 11.28/2.01    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.28/2.01    inference(ennf_transformation,[],[f21])).
% 11.28/2.01  
% 11.28/2.01  fof(f49,plain,(
% 11.28/2.01    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.28/2.01    inference(flattening,[],[f48])).
% 11.28/2.01  
% 11.28/2.01  fof(f87,plain,(
% 11.28/2.01    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f49])).
% 11.28/2.01  
% 11.28/2.01  fof(f98,plain,(
% 11.28/2.01    k1_xboole_0 != sK0),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f10,axiom,(
% 11.28/2.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f70,plain,(
% 11.28/2.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.28/2.01    inference(cnf_transformation,[],[f10])).
% 11.28/2.01  
% 11.28/2.01  fof(f105,plain,(
% 11.28/2.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.28/2.01    inference(definition_unfolding,[],[f70,f81])).
% 11.28/2.01  
% 11.28/2.01  fof(f20,axiom,(
% 11.28/2.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f46,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.28/2.01    inference(ennf_transformation,[],[f20])).
% 11.28/2.01  
% 11.28/2.01  fof(f47,plain,(
% 11.28/2.01    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.28/2.01    inference(flattening,[],[f46])).
% 11.28/2.01  
% 11.28/2.01  fof(f85,plain,(
% 11.28/2.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f47])).
% 11.28/2.01  
% 11.28/2.01  fof(f11,axiom,(
% 11.28/2.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f34,plain,(
% 11.28/2.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.28/2.01    inference(ennf_transformation,[],[f11])).
% 11.28/2.01  
% 11.28/2.01  fof(f35,plain,(
% 11.28/2.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.28/2.01    inference(flattening,[],[f34])).
% 11.28/2.01  
% 11.28/2.01  fof(f71,plain,(
% 11.28/2.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f35])).
% 11.28/2.01  
% 11.28/2.01  fof(f7,axiom,(
% 11.28/2.01    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 11.28/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.28/2.01  
% 11.28/2.01  fof(f30,plain,(
% 11.28/2.01    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 11.28/2.01    inference(ennf_transformation,[],[f7])).
% 11.28/2.01  
% 11.28/2.01  fof(f65,plain,(
% 11.28/2.01    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.28/2.01    inference(cnf_transformation,[],[f30])).
% 11.28/2.01  
% 11.28/2.01  fof(f103,plain,(
% 11.28/2.01    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 11.28/2.01    inference(definition_unfolding,[],[f65,f81])).
% 11.28/2.01  
% 11.28/2.01  fof(f97,plain,(
% 11.28/2.01    v2_funct_1(sK2)),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f99,plain,(
% 11.28/2.01    k1_xboole_0 != sK1),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  fof(f100,plain,(
% 11.28/2.01    k2_funct_1(sK2) != sK3),
% 11.28/2.01    inference(cnf_transformation,[],[f56])).
% 11.28/2.01  
% 11.28/2.01  cnf(c_42,negated_conjecture,
% 11.28/2.01      ( v1_funct_1(sK2) ),
% 11.28/2.01      inference(cnf_transformation,[],[f89]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1398,plain,
% 11.28/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_11,plain,
% 11.28/2.01      ( ~ v1_funct_1(X0)
% 11.28/2.01      | ~ v1_relat_1(X0)
% 11.28/2.01      | v1_relat_1(k2_funct_1(X0)) ),
% 11.28/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1420,plain,
% 11.28/2.01      ( v1_funct_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3,plain,
% 11.28/2.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.28/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1426,plain,
% 11.28/2.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_40,negated_conjecture,
% 11.28/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.28/2.01      inference(cnf_transformation,[],[f91]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1400,plain,
% 11.28/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_0,plain,
% 11.28/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.28/2.01      | ~ v1_relat_1(X1)
% 11.28/2.01      | v1_relat_1(X0) ),
% 11.28/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1427,plain,
% 11.28/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.28/2.01      | v1_relat_1(X1) != iProver_top
% 11.28/2.01      | v1_relat_1(X0) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3062,plain,
% 11.28/2.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.28/2.01      | v1_relat_1(sK2) = iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1400,c_1427]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3176,plain,
% 11.28/2.01      ( v1_relat_1(sK2) = iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1426,c_3062]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_37,negated_conjecture,
% 11.28/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.28/2.01      inference(cnf_transformation,[],[f94]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1403,plain,
% 11.28/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3061,plain,
% 11.28/2.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 11.28/2.01      | v1_relat_1(sK3) = iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1403,c_1427]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3161,plain,
% 11.28/2.01      ( v1_relat_1(sK3) = iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1426,c_3061]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5,plain,
% 11.28/2.01      ( ~ v1_relat_1(X0)
% 11.28/2.01      | ~ v1_relat_1(X1)
% 11.28/2.01      | ~ v1_relat_1(X2)
% 11.28/2.01      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 11.28/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1424,plain,
% 11.28/2.01      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 11.28/2.01      | v1_relat_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X1) != iProver_top
% 11.28/2.01      | v1_relat_1(X2) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3289,plain,
% 11.28/2.01      ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
% 11.28/2.01      | v1_relat_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_3161,c_1424]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_9583,plain,
% 11.28/2.01      ( k5_relat_1(sK3,k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(sK3,sK2),X0)
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_3176,c_3289]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_10317,plain,
% 11.28/2.01      ( k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(X0)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(X0)))
% 11.28/2.01      | v1_funct_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1420,c_9583]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_39,negated_conjecture,
% 11.28/2.01      ( v1_funct_1(sK3) ),
% 11.28/2.01      inference(cnf_transformation,[],[f92]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1401,plain,
% 11.28/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3290,plain,
% 11.28/2.01      ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
% 11.28/2.01      | v1_relat_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X1) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_3176,c_1424]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_12372,plain,
% 11.28/2.01      ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_3161,c_3290]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_23,plain,
% 11.28/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.28/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | ~ v1_funct_1(X3)
% 11.28/2.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.28/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1411,plain,
% 11.28/2.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.28/2.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.28/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.28/2.01      | v1_funct_1(X5) != iProver_top
% 11.28/2.01      | v1_funct_1(X4) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_4674,plain,
% 11.28/2.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.28/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.28/2.01      | v1_funct_1(X2) != iProver_top
% 11.28/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1403,c_1411]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_46,plain,
% 11.28/2.01      ( v1_funct_1(sK3) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_4902,plain,
% 11.28/2.01      ( v1_funct_1(X2) != iProver_top
% 11.28/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.28/2.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_4674,c_46]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_4903,plain,
% 11.28/2.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.28/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.28/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.28/2.01      inference(renaming,[status(thm)],[c_4902]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_4911,plain,
% 11.28/2.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.28/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1400,c_4903]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_19,plain,
% 11.28/2.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.28/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.28/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.28/2.01      | X3 = X2 ),
% 11.28/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_35,negated_conjecture,
% 11.28/2.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.28/2.01      inference(cnf_transformation,[],[f96]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_503,plain,
% 11.28/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.28/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.28/2.01      | X3 = X0
% 11.28/2.01      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.28/2.01      | k6_partfun1(sK0) != X3
% 11.28/2.01      | sK0 != X2
% 11.28/2.01      | sK0 != X1 ),
% 11.28/2.01      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_504,plain,
% 11.28/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.28/2.01      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.28/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.28/2.01      inference(unflattening,[status(thm)],[c_503]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_20,plain,
% 11.28/2.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.28/2.01      inference(cnf_transformation,[],[f107]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_512,plain,
% 11.28/2.01      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.28/2.01      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.28/2.01      inference(forward_subsumption_resolution,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_504,c_20]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1395,plain,
% 11.28/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.28/2.01      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_21,plain,
% 11.28/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.28/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.28/2.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | ~ v1_funct_1(X3) ),
% 11.28/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1513,plain,
% 11.28/2.01      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.28/2.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.28/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.28/2.01      | ~ v1_funct_1(sK3)
% 11.28/2.01      | ~ v1_funct_1(sK2) ),
% 11.28/2.01      inference(instantiation,[status(thm)],[c_21]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_2230,plain,
% 11.28/2.01      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_1395,c_42,c_40,c_39,c_37,c_512,c_1513]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_4912,plain,
% 11.28/2.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.28/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_4911,c_2230]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_43,plain,
% 11.28/2.01      ( v1_funct_1(sK2) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5021,plain,
% 11.28/2.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_4912,c_43]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_12377,plain,
% 11.28/2.01      ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_12372,c_5021]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_19997,plain,
% 11.28/2.01      ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(X0))
% 11.28/2.01      | v1_funct_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1420,c_12377]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_22664,plain,
% 11.28/2.01      ( k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
% 11.28/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1401,c_19997]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_9,plain,
% 11.28/2.01      ( ~ v1_relat_1(X0)
% 11.28/2.01      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 11.28/2.01      inference(cnf_transformation,[],[f104]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1422,plain,
% 11.28/2.01      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3206,plain,
% 11.28/2.01      ( k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) = sK2 ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_3176,c_1422]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_17,plain,
% 11.28/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.28/2.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.28/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1415,plain,
% 11.28/2.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.28/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_2443,plain,
% 11.28/2.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1400,c_1415]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_36,negated_conjecture,
% 11.28/2.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.28/2.01      inference(cnf_transformation,[],[f95]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_2444,plain,
% 11.28/2.01      ( k2_relat_1(sK2) = sK1 ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_2443,c_36]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3207,plain,
% 11.28/2.01      ( k5_relat_1(sK2,k6_partfun1(sK1)) = sK2 ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_3206,c_2444]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_24,plain,
% 11.28/2.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.28/2.01      | ~ v1_funct_2(X2,X0,X1)
% 11.28/2.01      | ~ v1_funct_2(X3,X1,X0)
% 11.28/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.28/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.28/2.01      | ~ v1_funct_1(X2)
% 11.28/2.01      | ~ v1_funct_1(X3)
% 11.28/2.01      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.28/2.01      inference(cnf_transformation,[],[f82]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_516,plain,
% 11.28/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.28/2.01      | ~ v1_funct_2(X3,X2,X1)
% 11.28/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.28/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.28/2.01      | ~ v1_funct_1(X3)
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.28/2.01      | k2_relset_1(X2,X1,X3) = X1
% 11.28/2.01      | k6_partfun1(X1) != k6_partfun1(sK0)
% 11.28/2.01      | sK0 != X1 ),
% 11.28/2.01      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_517,plain,
% 11.28/2.01      ( ~ v1_funct_2(X0,X1,sK0)
% 11.28/2.01      | ~ v1_funct_2(X2,sK0,X1)
% 11.28/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.28/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.28/2.01      | ~ v1_funct_1(X2)
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.28/2.01      | k2_relset_1(X1,sK0,X0) = sK0
% 11.28/2.01      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 11.28/2.01      inference(unflattening,[status(thm)],[c_516]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_605,plain,
% 11.28/2.01      ( ~ v1_funct_2(X0,X1,sK0)
% 11.28/2.01      | ~ v1_funct_2(X2,sK0,X1)
% 11.28/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.28/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | ~ v1_funct_1(X2)
% 11.28/2.01      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.28/2.01      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 11.28/2.01      inference(equality_resolution_simp,[status(thm)],[c_517]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1394,plain,
% 11.28/2.01      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.28/2.01      | k2_relset_1(X0,sK0,X2) = sK0
% 11.28/2.01      | v1_funct_2(X2,X0,sK0) != iProver_top
% 11.28/2.01      | v1_funct_2(X1,sK0,X0) != iProver_top
% 11.28/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 11.28/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 11.28/2.01      | v1_funct_1(X2) != iProver_top
% 11.28/2.01      | v1_funct_1(X1) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1912,plain,
% 11.28/2.01      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 11.28/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.28/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.28/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.28/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.28/2.01      | v1_funct_1(sK3) != iProver_top
% 11.28/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.28/2.01      inference(equality_resolution,[status(thm)],[c_1394]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_41,negated_conjecture,
% 11.28/2.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.28/2.01      inference(cnf_transformation,[],[f90]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_44,plain,
% 11.28/2.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_45,plain,
% 11.28/2.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_38,negated_conjecture,
% 11.28/2.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 11.28/2.01      inference(cnf_transformation,[],[f93]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_47,plain,
% 11.28/2.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_48,plain,
% 11.28/2.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_2237,plain,
% 11.28/2.01      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_1912,c_43,c_44,c_45,c_46,c_47,c_48]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_30,plain,
% 11.28/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.28/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.28/2.01      | ~ v2_funct_1(X0)
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | k2_relset_1(X1,X2,X0) != X2
% 11.28/2.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.28/2.01      | k1_xboole_0 = X2 ),
% 11.28/2.01      inference(cnf_transformation,[],[f87]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1405,plain,
% 11.28/2.01      ( k2_relset_1(X0,X1,X2) != X1
% 11.28/2.01      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 11.28/2.01      | k1_xboole_0 = X1
% 11.28/2.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.28/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.28/2.01      | v2_funct_1(X2) != iProver_top
% 11.28/2.01      | v1_funct_1(X2) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3210,plain,
% 11.28/2.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.28/2.01      | sK0 = k1_xboole_0
% 11.28/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.28/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.28/2.01      | v2_funct_1(sK3) != iProver_top
% 11.28/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_2237,c_1405]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_33,negated_conjecture,
% 11.28/2.01      ( k1_xboole_0 != sK0 ),
% 11.28/2.01      inference(cnf_transformation,[],[f98]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_829,plain,( X0 = X0 ),theory(equality) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_862,plain,
% 11.28/2.01      ( k1_xboole_0 = k1_xboole_0 ),
% 11.28/2.01      inference(instantiation,[status(thm)],[c_829]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_830,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1511,plain,
% 11.28/2.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 11.28/2.01      inference(instantiation,[status(thm)],[c_830]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1512,plain,
% 11.28/2.01      ( sK0 != k1_xboole_0
% 11.28/2.01      | k1_xboole_0 = sK0
% 11.28/2.01      | k1_xboole_0 != k1_xboole_0 ),
% 11.28/2.01      inference(instantiation,[status(thm)],[c_1511]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_12,plain,
% 11.28/2.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.28/2.01      inference(cnf_transformation,[],[f105]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3080,plain,
% 11.28/2.01      ( v2_funct_1(k6_partfun1(sK0)) ),
% 11.28/2.01      inference(instantiation,[status(thm)],[c_12]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3081,plain,
% 11.28/2.01      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_3080]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_26,plain,
% 11.28/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.28/2.01      | ~ v1_funct_2(X3,X2,X4)
% 11.28/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.28/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 11.28/2.01      | v2_funct_1(X3)
% 11.28/2.01      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 11.28/2.01      | ~ v1_funct_1(X3)
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | k2_relset_1(X1,X2,X0) != X2
% 11.28/2.01      | k1_xboole_0 = X4 ),
% 11.28/2.01      inference(cnf_transformation,[],[f85]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1409,plain,
% 11.28/2.01      ( k2_relset_1(X0,X1,X2) != X1
% 11.28/2.01      | k1_xboole_0 = X3
% 11.28/2.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.28/2.01      | v1_funct_2(X4,X1,X3) != iProver_top
% 11.28/2.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.28/2.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 11.28/2.01      | v2_funct_1(X4) = iProver_top
% 11.28/2.01      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 11.28/2.01      | v1_funct_1(X2) != iProver_top
% 11.28/2.01      | v1_funct_1(X4) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5157,plain,
% 11.28/2.01      ( k1_xboole_0 = X0
% 11.28/2.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.28/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.28/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.28/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.28/2.01      | v2_funct_1(X1) = iProver_top
% 11.28/2.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 11.28/2.01      | v1_funct_1(X1) != iProver_top
% 11.28/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_36,c_1409]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5164,plain,
% 11.28/2.01      ( v1_funct_1(X1) != iProver_top
% 11.28/2.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 11.28/2.01      | v2_funct_1(X1) = iProver_top
% 11.28/2.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.28/2.01      | k1_xboole_0 = X0
% 11.28/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_5157,c_43,c_44,c_45]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5165,plain,
% 11.28/2.01      ( k1_xboole_0 = X0
% 11.28/2.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.28/2.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.28/2.01      | v2_funct_1(X1) = iProver_top
% 11.28/2.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 11.28/2.01      | v1_funct_1(X1) != iProver_top ),
% 11.28/2.01      inference(renaming,[status(thm)],[c_5164]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5168,plain,
% 11.28/2.01      ( sK0 = k1_xboole_0
% 11.28/2.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.28/2.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.28/2.01      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 11.28/2.01      | v2_funct_1(sK3) = iProver_top
% 11.28/2.01      | v1_funct_1(sK3) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_2230,c_5165]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_9021,plain,
% 11.28/2.01      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_3210,c_46,c_47,c_48,c_33,c_862,c_1512,c_3081,c_5168]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5204,plain,
% 11.28/2.01      ( v2_funct_1(sK3) = iProver_top ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_5168,c_46,c_47,c_48,c_33,c_862,c_1512,c_3081]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_15,plain,
% 11.28/2.01      ( ~ v2_funct_1(X0)
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | ~ v1_relat_1(X0)
% 11.28/2.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.28/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1416,plain,
% 11.28/2.01      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 11.28/2.01      | v2_funct_1(X0) != iProver_top
% 11.28/2.01      | v1_funct_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5209,plain,
% 11.28/2.01      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 11.28/2.01      | v1_funct_1(sK3) != iProver_top
% 11.28/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_5204,c_1416]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_2442,plain,
% 11.28/2.01      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1403,c_1415]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_2445,plain,
% 11.28/2.01      ( k2_relat_1(sK3) = sK0 ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_2442,c_2237]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5210,plain,
% 11.28/2.01      ( k1_relat_1(k2_funct_1(sK3)) = sK0
% 11.28/2.01      | v1_funct_1(sK3) != iProver_top
% 11.28/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_5209,c_2445]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_9789,plain,
% 11.28/2.01      ( k1_relat_1(k2_funct_1(sK3)) = sK0 ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_5210,c_46,c_3161]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_8,plain,
% 11.28/2.01      ( ~ v1_relat_1(X0)
% 11.28/2.01      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 11.28/2.01      inference(cnf_transformation,[],[f103]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1423,plain,
% 11.28/2.01      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3009,plain,
% 11.28/2.01      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
% 11.28/2.01      | v1_funct_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1420,c_1423]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5430,plain,
% 11.28/2.01      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3)
% 11.28/2.01      | v1_relat_1(sK3) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1401,c_3009]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5965,plain,
% 11.28/2.01      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_5430,c_3161]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_9791,plain,
% 11.28/2.01      ( k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k2_funct_1(sK3) ),
% 11.28/2.01      inference(demodulation,[status(thm)],[c_9789,c_5965]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_22670,plain,
% 11.28/2.01      ( k2_funct_1(sK3) = sK2 | v1_relat_1(sK3) != iProver_top ),
% 11.28/2.01      inference(light_normalisation,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_22664,c_3207,c_9021,c_9791]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_23102,plain,
% 11.28/2.01      ( k2_funct_1(sK3) = sK2 ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_22670,c_3161]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_23162,plain,
% 11.28/2.01      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 11.28/2.01      inference(demodulation,[status(thm)],[c_23102,c_9021]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_23420,plain,
% 11.28/2.01      ( k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(X0))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(X0))
% 11.28/2.01      | v1_funct_1(X0) != iProver_top
% 11.28/2.01      | v1_relat_1(X0) != iProver_top ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_10317,c_23162]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_23427,plain,
% 11.28/2.01      ( k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2))) = k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2))
% 11.28/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1398,c_23420]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3202,plain,
% 11.28/2.01      ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_3161,c_1422]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3203,plain,
% 11.28/2.01      ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_3202,c_2445]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3209,plain,
% 11.28/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 11.28/2.01      | sK1 = k1_xboole_0
% 11.28/2.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.28/2.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.28/2.01      | v2_funct_1(sK2) != iProver_top
% 11.28/2.01      | v1_funct_1(sK2) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_36,c_1405]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_34,negated_conjecture,
% 11.28/2.01      ( v2_funct_1(sK2) ),
% 11.28/2.01      inference(cnf_transformation,[],[f97]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_32,negated_conjecture,
% 11.28/2.01      ( k1_xboole_0 != sK1 ),
% 11.28/2.01      inference(cnf_transformation,[],[f99]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1474,plain,
% 11.28/2.01      ( ~ v1_funct_2(X0,X1,sK1)
% 11.28/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 11.28/2.01      | ~ v2_funct_1(X0)
% 11.28/2.01      | ~ v1_funct_1(X0)
% 11.28/2.01      | k2_relset_1(X1,sK1,X0) != sK1
% 11.28/2.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.28/2.01      | k1_xboole_0 = sK1 ),
% 11.28/2.01      inference(instantiation,[status(thm)],[c_30]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1590,plain,
% 11.28/2.01      ( ~ v1_funct_2(sK2,X0,sK1)
% 11.28/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 11.28/2.01      | ~ v2_funct_1(sK2)
% 11.28/2.01      | ~ v1_funct_1(sK2)
% 11.28/2.01      | k2_relset_1(X0,sK1,sK2) != sK1
% 11.28/2.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 11.28/2.01      | k1_xboole_0 = sK1 ),
% 11.28/2.01      inference(instantiation,[status(thm)],[c_1474]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1779,plain,
% 11.28/2.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 11.28/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.28/2.01      | ~ v2_funct_1(sK2)
% 11.28/2.01      | ~ v1_funct_1(sK2)
% 11.28/2.01      | k2_relset_1(sK0,sK1,sK2) != sK1
% 11.28/2.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 11.28/2.01      | k1_xboole_0 = sK1 ),
% 11.28/2.01      inference(instantiation,[status(thm)],[c_1590]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3483,plain,
% 11.28/2.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_3209,c_42,c_41,c_40,c_36,c_34,c_32,c_1779]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5431,plain,
% 11.28/2.01      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2)
% 11.28/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1398,c_3009]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_1404,plain,
% 11.28/2.01      ( v2_funct_1(sK2) = iProver_top ),
% 11.28/2.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3131,plain,
% 11.28/2.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.28/2.01      | v1_funct_1(sK2) != iProver_top
% 11.28/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.28/2.01      inference(superposition,[status(thm)],[c_1404,c_1416]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3132,plain,
% 11.28/2.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 11.28/2.01      | v1_funct_1(sK2) != iProver_top
% 11.28/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_3131,c_2444]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_3195,plain,
% 11.28/2.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_3132,c_43,c_3176]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_5434,plain,
% 11.28/2.01      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2)
% 11.28/2.01      | v1_relat_1(sK2) != iProver_top ),
% 11.28/2.01      inference(light_normalisation,[status(thm)],[c_5431,c_3195]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_6062,plain,
% 11.28/2.01      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
% 11.28/2.01      inference(global_propositional_subsumption,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_5434,c_3176]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_23433,plain,
% 11.28/2.01      ( k2_funct_1(sK2) = sK3 | v1_relat_1(sK2) != iProver_top ),
% 11.28/2.01      inference(light_normalisation,
% 11.28/2.01                [status(thm)],
% 11.28/2.01                [c_23427,c_3203,c_3483,c_6062]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(c_31,negated_conjecture,
% 11.28/2.01      ( k2_funct_1(sK2) != sK3 ),
% 11.28/2.01      inference(cnf_transformation,[],[f100]) ).
% 11.28/2.01  
% 11.28/2.01  cnf(contradiction,plain,
% 11.28/2.01      ( $false ),
% 11.28/2.01      inference(minisat,[status(thm)],[c_23433,c_3176,c_31]) ).
% 11.28/2.01  
% 11.28/2.01  
% 11.28/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.28/2.01  
% 11.28/2.01  ------                               Statistics
% 11.28/2.01  
% 11.28/2.01  ------ General
% 11.28/2.01  
% 11.28/2.01  abstr_ref_over_cycles:                  0
% 11.28/2.01  abstr_ref_under_cycles:                 0
% 11.28/2.01  gc_basic_clause_elim:                   0
% 11.28/2.01  forced_gc_time:                         0
% 11.28/2.01  parsing_time:                           0.014
% 11.28/2.01  unif_index_cands_time:                  0.
% 11.28/2.01  unif_index_add_time:                    0.
% 11.28/2.01  orderings_time:                         0.
% 11.28/2.01  out_proof_time:                         0.018
% 11.28/2.01  total_time:                             1.012
% 11.28/2.01  num_of_symbols:                         53
% 11.28/2.01  num_of_terms:                           36673
% 11.28/2.01  
% 11.28/2.01  ------ Preprocessing
% 11.28/2.01  
% 11.28/2.01  num_of_splits:                          0
% 11.28/2.01  num_of_split_atoms:                     0
% 11.28/2.01  num_of_reused_defs:                     0
% 11.28/2.01  num_eq_ax_congr_red:                    2
% 11.28/2.01  num_of_sem_filtered_clauses:            1
% 11.28/2.01  num_of_subtypes:                        0
% 11.28/2.01  monotx_restored_types:                  0
% 11.28/2.01  sat_num_of_epr_types:                   0
% 11.28/2.01  sat_num_of_non_cyclic_types:            0
% 11.28/2.01  sat_guarded_non_collapsed_types:        0
% 11.28/2.01  num_pure_diseq_elim:                    0
% 11.28/2.01  simp_replaced_by:                       0
% 11.28/2.01  res_preprocessed:                       198
% 11.28/2.01  prep_upred:                             0
% 11.28/2.01  prep_unflattend:                        14
% 11.28/2.01  smt_new_axioms:                         0
% 11.28/2.01  pred_elim_cands:                        6
% 11.28/2.01  pred_elim:                              2
% 11.28/2.01  pred_elim_cl:                           3
% 11.28/2.01  pred_elim_cycles:                       5
% 11.28/2.01  merged_defs:                            0
% 11.28/2.01  merged_defs_ncl:                        0
% 11.28/2.01  bin_hyper_res:                          0
% 11.28/2.01  prep_cycles:                            4
% 11.28/2.01  pred_elim_time:                         0.006
% 11.28/2.01  splitting_time:                         0.
% 11.28/2.01  sem_filter_time:                        0.
% 11.28/2.01  monotx_time:                            0.001
% 11.28/2.01  subtype_inf_time:                       0.
% 11.28/2.01  
% 11.28/2.01  ------ Problem properties
% 11.28/2.01  
% 11.28/2.01  clauses:                                40
% 11.28/2.01  conjectures:                            11
% 11.28/2.01  epr:                                    7
% 11.28/2.01  horn:                                   36
% 11.28/2.01  ground:                                 12
% 11.28/2.01  unary:                                  17
% 11.28/2.01  binary:                                 4
% 11.28/2.01  lits:                                   136
% 11.28/2.01  lits_eq:                                31
% 11.28/2.01  fd_pure:                                0
% 11.28/2.01  fd_pseudo:                              0
% 11.28/2.01  fd_cond:                                4
% 11.28/2.01  fd_pseudo_cond:                         0
% 11.28/2.01  ac_symbols:                             0
% 11.28/2.01  
% 11.28/2.01  ------ Propositional Solver
% 11.28/2.01  
% 11.28/2.01  prop_solver_calls:                      33
% 11.28/2.01  prop_fast_solver_calls:                 2409
% 11.28/2.01  smt_solver_calls:                       0
% 11.28/2.01  smt_fast_solver_calls:                  0
% 11.28/2.01  prop_num_of_clauses:                    11663
% 11.28/2.01  prop_preprocess_simplified:             20651
% 11.28/2.01  prop_fo_subsumed:                       157
% 11.28/2.01  prop_solver_time:                       0.
% 11.28/2.01  smt_solver_time:                        0.
% 11.28/2.01  smt_fast_solver_time:                   0.
% 11.28/2.01  prop_fast_solver_time:                  0.
% 11.28/2.01  prop_unsat_core_time:                   0.001
% 11.28/2.01  
% 11.28/2.01  ------ QBF
% 11.28/2.01  
% 11.28/2.01  qbf_q_res:                              0
% 11.28/2.01  qbf_num_tautologies:                    0
% 11.28/2.01  qbf_prep_cycles:                        0
% 11.28/2.01  
% 11.28/2.01  ------ BMC1
% 11.28/2.01  
% 11.28/2.01  bmc1_current_bound:                     -1
% 11.28/2.01  bmc1_last_solved_bound:                 -1
% 11.28/2.01  bmc1_unsat_core_size:                   -1
% 11.28/2.01  bmc1_unsat_core_parents_size:           -1
% 11.28/2.01  bmc1_merge_next_fun:                    0
% 11.28/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.28/2.01  
% 11.28/2.01  ------ Instantiation
% 11.28/2.01  
% 11.28/2.01  inst_num_of_clauses:                    2908
% 11.28/2.01  inst_num_in_passive:                    608
% 11.28/2.01  inst_num_in_active:                     1715
% 11.28/2.01  inst_num_in_unprocessed:                585
% 11.28/2.01  inst_num_of_loops:                      1910
% 11.28/2.01  inst_num_of_learning_restarts:          0
% 11.28/2.01  inst_num_moves_active_passive:          191
% 11.28/2.01  inst_lit_activity:                      0
% 11.28/2.01  inst_lit_activity_moves:                1
% 11.28/2.01  inst_num_tautologies:                   0
% 11.28/2.01  inst_num_prop_implied:                  0
% 11.28/2.01  inst_num_existing_simplified:           0
% 11.28/2.01  inst_num_eq_res_simplified:             0
% 11.28/2.01  inst_num_child_elim:                    0
% 11.28/2.01  inst_num_of_dismatching_blockings:      1976
% 11.28/2.01  inst_num_of_non_proper_insts:           2677
% 11.28/2.01  inst_num_of_duplicates:                 0
% 11.28/2.01  inst_inst_num_from_inst_to_res:         0
% 11.28/2.01  inst_dismatching_checking_time:         0.
% 11.28/2.01  
% 11.28/2.01  ------ Resolution
% 11.28/2.01  
% 11.28/2.01  res_num_of_clauses:                     0
% 11.28/2.01  res_num_in_passive:                     0
% 11.28/2.01  res_num_in_active:                      0
% 11.28/2.01  res_num_of_loops:                       202
% 11.28/2.01  res_forward_subset_subsumed:            160
% 11.28/2.01  res_backward_subset_subsumed:           0
% 11.28/2.01  res_forward_subsumed:                   0
% 11.28/2.01  res_backward_subsumed:                  0
% 11.28/2.01  res_forward_subsumption_resolution:     2
% 11.28/2.01  res_backward_subsumption_resolution:    0
% 11.28/2.01  res_clause_to_clause_subsumption:       1740
% 11.28/2.01  res_orphan_elimination:                 0
% 11.28/2.01  res_tautology_del:                      91
% 11.28/2.01  res_num_eq_res_simplified:              1
% 11.28/2.01  res_num_sel_changes:                    0
% 11.28/2.01  res_moves_from_active_to_pass:          0
% 11.28/2.01  
% 11.28/2.01  ------ Superposition
% 11.28/2.01  
% 11.28/2.01  sup_time_total:                         0.
% 11.28/2.01  sup_time_generating:                    0.
% 11.28/2.01  sup_time_sim_full:                      0.
% 11.28/2.01  sup_time_sim_immed:                     0.
% 11.28/2.01  
% 11.28/2.01  sup_num_of_clauses:                     742
% 11.28/2.01  sup_num_in_active:                      267
% 11.28/2.01  sup_num_in_passive:                     475
% 11.28/2.01  sup_num_of_loops:                       381
% 11.28/2.01  sup_fw_superposition:                   677
% 11.28/2.01  sup_bw_superposition:                   209
% 11.28/2.01  sup_immediate_simplified:               275
% 11.28/2.01  sup_given_eliminated:                   0
% 11.28/2.01  comparisons_done:                       0
% 11.28/2.01  comparisons_avoided:                    4
% 11.28/2.01  
% 11.28/2.01  ------ Simplifications
% 11.28/2.01  
% 11.28/2.01  
% 11.28/2.01  sim_fw_subset_subsumed:                 20
% 11.28/2.01  sim_bw_subset_subsumed:                 38
% 11.28/2.01  sim_fw_subsumed:                        17
% 11.28/2.01  sim_bw_subsumed:                        3
% 11.28/2.01  sim_fw_subsumption_res:                 0
% 11.28/2.01  sim_bw_subsumption_res:                 0
% 11.28/2.01  sim_tautology_del:                      4
% 11.28/2.01  sim_eq_tautology_del:                   72
% 11.28/2.01  sim_eq_res_simp:                        0
% 11.28/2.01  sim_fw_demodulated:                     29
% 11.28/2.01  sim_bw_demodulated:                     96
% 11.28/2.01  sim_light_normalised:                   236
% 11.28/2.01  sim_joinable_taut:                      0
% 11.28/2.01  sim_joinable_simp:                      0
% 11.28/2.01  sim_ac_normalised:                      0
% 11.28/2.01  sim_smt_subsumption:                    0
% 11.28/2.01  
%------------------------------------------------------------------------------
