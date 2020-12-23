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
% DateTime   : Thu Dec  3 12:03:34 EST 2020

% Result     : Theorem 7.43s
% Output     : CNFRefutation 7.43s
% Verified   : 
% Statistics : Number of formulae       :  230 (1774 expanded)
%              Number of clauses        :  140 ( 524 expanded)
%              Number of leaves         :   25 ( 458 expanded)
%              Depth                    :   20
%              Number of atoms          :  816 (14517 expanded)
%              Number of equality atoms :  412 (5292 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f52,f51])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f20,axiom,(
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

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f86,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f95,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f92,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f100,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f98,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f77])).

fof(f18,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f101,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f68,f77])).

fof(f19,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f96,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1348,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1324,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1350,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3066,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1350])).

cnf(c_3187,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_3066])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1321,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3067,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_1350])).

cnf(c_3190,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_3067])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1319,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1340,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1345,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4023,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1345])).

cnf(c_13579,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_4023])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1342,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3136,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_1342])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_49,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3349,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3136,c_49,c_3190])).

cnf(c_13588,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13579,c_3349])).

cnf(c_13787,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13588,c_3190])).

cnf(c_13788,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_13787])).

cnf(c_13798,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_13788])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1327,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3816,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1327])).

cnf(c_3818,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3816,c_3349])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_43,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_748,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_779,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_749,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1415,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1416,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_4414,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3818,c_42,c_43,c_44,c_49,c_31,c_779,c_1416])).

cnf(c_13804,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13798,c_4414])).

cnf(c_13958,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3187,c_13804])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1332,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6264,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1324,c_1332])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_45,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6357,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6264,c_45])).

cnf(c_6358,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6357])).

cnf(c_6366,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1321,c_6358])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_34])).

cnf(c_444,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_452,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_444,c_21])).

cnf(c_1317,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1437,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2077,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1317,c_41,c_39,c_38,c_36,c_452,c_1437])).

cnf(c_6367,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6366,c_2077])).

cnf(c_6520,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6367,c_42])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1349,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1343,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2374,plain,
    ( k5_relat_1(k4_relat_1(X0),k6_partfun1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1349,c_1343])).

cnf(c_6956,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3190,c_2374])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1347,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4420,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3190,c_1347])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1336,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3919,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1319,c_1336])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1326,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3012,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1326])).

cnf(c_1398,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1533,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_1733,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1533])).

cnf(c_3143,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3012,c_41,c_40,c_39,c_35,c_33,c_31,c_1733])).

cnf(c_3351,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_3349,c_3143])).

cnf(c_3920,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3919,c_3349,c_3351])).

cnf(c_7,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3921,plain,
    ( k1_relat_1(sK2) = sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3920,c_7])).

cnf(c_3928,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3921,c_49,c_3190])).

cnf(c_4422,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_4420,c_3928])).

cnf(c_6957,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6956,c_4422])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_456,plain,
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
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_456])).

cnf(c_546,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_457])).

cnf(c_1316,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_1828,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1316])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2084,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1828,c_42,c_43,c_44,c_45,c_46,c_47])).

cnf(c_3013,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1326])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1435,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1436,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_13,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6643,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6644,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6643])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1330,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6631,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1330])).

cnf(c_6654,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6631,c_42,c_43,c_44])).

cnf(c_6655,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6654])).

cnf(c_6658,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2077,c_6655])).

cnf(c_7750,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3013,c_45,c_46,c_47,c_32,c_779,c_1436,c_6644,c_6658])).

cnf(c_6728,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6658,c_45,c_46,c_47,c_32,c_779,c_1436,c_6644])).

cnf(c_1322,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3135,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1342])).

cnf(c_3344,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3135,c_3187])).

cnf(c_3345,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3344])).

cnf(c_6734,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6728,c_3345])).

cnf(c_7752,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_7750,c_6734])).

cnf(c_3918,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_1336])).

cnf(c_4256,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3918,c_3187])).

cnf(c_4257,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4256])).

cnf(c_6733,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6728,c_4257])).

cnf(c_6735,plain,
    ( k1_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_6733,c_6734])).

cnf(c_7754,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_7752,c_6735])).

cnf(c_7755,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_7754,c_7])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1344,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3811,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_3187,c_1344])).

cnf(c_7757,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_7755,c_3811])).

cnf(c_13969,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_13958,c_6520,c_6957,c_7757])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3352,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_3349,c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13969,c_3352])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:15:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.43/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.43/1.49  
% 7.43/1.49  ------  iProver source info
% 7.43/1.49  
% 7.43/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.43/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.43/1.49  git: non_committed_changes: false
% 7.43/1.49  git: last_make_outside_of_git: false
% 7.43/1.49  
% 7.43/1.49  ------ 
% 7.43/1.49  
% 7.43/1.49  ------ Input Options
% 7.43/1.49  
% 7.43/1.49  --out_options                           all
% 7.43/1.49  --tptp_safe_out                         true
% 7.43/1.49  --problem_path                          ""
% 7.43/1.49  --include_path                          ""
% 7.43/1.49  --clausifier                            res/vclausify_rel
% 7.43/1.49  --clausifier_options                    ""
% 7.43/1.49  --stdin                                 false
% 7.43/1.49  --stats_out                             all
% 7.43/1.49  
% 7.43/1.49  ------ General Options
% 7.43/1.49  
% 7.43/1.49  --fof                                   false
% 7.43/1.49  --time_out_real                         305.
% 7.43/1.49  --time_out_virtual                      -1.
% 7.43/1.49  --symbol_type_check                     false
% 7.43/1.49  --clausify_out                          false
% 7.43/1.49  --sig_cnt_out                           false
% 7.43/1.49  --trig_cnt_out                          false
% 7.43/1.49  --trig_cnt_out_tolerance                1.
% 7.43/1.49  --trig_cnt_out_sk_spl                   false
% 7.43/1.49  --abstr_cl_out                          false
% 7.43/1.49  
% 7.43/1.49  ------ Global Options
% 7.43/1.49  
% 7.43/1.49  --schedule                              default
% 7.43/1.49  --add_important_lit                     false
% 7.43/1.49  --prop_solver_per_cl                    1000
% 7.43/1.49  --min_unsat_core                        false
% 7.43/1.49  --soft_assumptions                      false
% 7.43/1.49  --soft_lemma_size                       3
% 7.43/1.49  --prop_impl_unit_size                   0
% 7.43/1.49  --prop_impl_unit                        []
% 7.43/1.49  --share_sel_clauses                     true
% 7.43/1.49  --reset_solvers                         false
% 7.43/1.49  --bc_imp_inh                            [conj_cone]
% 7.43/1.49  --conj_cone_tolerance                   3.
% 7.43/1.49  --extra_neg_conj                        none
% 7.43/1.49  --large_theory_mode                     true
% 7.43/1.49  --prolific_symb_bound                   200
% 7.43/1.49  --lt_threshold                          2000
% 7.43/1.49  --clause_weak_htbl                      true
% 7.43/1.49  --gc_record_bc_elim                     false
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing Options
% 7.43/1.49  
% 7.43/1.49  --preprocessing_flag                    true
% 7.43/1.49  --time_out_prep_mult                    0.1
% 7.43/1.49  --splitting_mode                        input
% 7.43/1.49  --splitting_grd                         true
% 7.43/1.49  --splitting_cvd                         false
% 7.43/1.49  --splitting_cvd_svl                     false
% 7.43/1.49  --splitting_nvd                         32
% 7.43/1.49  --sub_typing                            true
% 7.43/1.49  --prep_gs_sim                           true
% 7.43/1.49  --prep_unflatten                        true
% 7.43/1.49  --prep_res_sim                          true
% 7.43/1.49  --prep_upred                            true
% 7.43/1.49  --prep_sem_filter                       exhaustive
% 7.43/1.49  --prep_sem_filter_out                   false
% 7.43/1.49  --pred_elim                             true
% 7.43/1.49  --res_sim_input                         true
% 7.43/1.49  --eq_ax_congr_red                       true
% 7.43/1.49  --pure_diseq_elim                       true
% 7.43/1.49  --brand_transform                       false
% 7.43/1.49  --non_eq_to_eq                          false
% 7.43/1.49  --prep_def_merge                        true
% 7.43/1.49  --prep_def_merge_prop_impl              false
% 7.43/1.49  --prep_def_merge_mbd                    true
% 7.43/1.49  --prep_def_merge_tr_red                 false
% 7.43/1.49  --prep_def_merge_tr_cl                  false
% 7.43/1.49  --smt_preprocessing                     true
% 7.43/1.49  --smt_ac_axioms                         fast
% 7.43/1.49  --preprocessed_out                      false
% 7.43/1.49  --preprocessed_stats                    false
% 7.43/1.49  
% 7.43/1.49  ------ Abstraction refinement Options
% 7.43/1.49  
% 7.43/1.49  --abstr_ref                             []
% 7.43/1.49  --abstr_ref_prep                        false
% 7.43/1.49  --abstr_ref_until_sat                   false
% 7.43/1.49  --abstr_ref_sig_restrict                funpre
% 7.43/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.43/1.49  --abstr_ref_under                       []
% 7.43/1.49  
% 7.43/1.49  ------ SAT Options
% 7.43/1.49  
% 7.43/1.49  --sat_mode                              false
% 7.43/1.49  --sat_fm_restart_options                ""
% 7.43/1.49  --sat_gr_def                            false
% 7.43/1.49  --sat_epr_types                         true
% 7.43/1.49  --sat_non_cyclic_types                  false
% 7.43/1.49  --sat_finite_models                     false
% 7.43/1.49  --sat_fm_lemmas                         false
% 7.43/1.49  --sat_fm_prep                           false
% 7.43/1.49  --sat_fm_uc_incr                        true
% 7.43/1.49  --sat_out_model                         small
% 7.43/1.49  --sat_out_clauses                       false
% 7.43/1.49  
% 7.43/1.49  ------ QBF Options
% 7.43/1.49  
% 7.43/1.49  --qbf_mode                              false
% 7.43/1.49  --qbf_elim_univ                         false
% 7.43/1.49  --qbf_dom_inst                          none
% 7.43/1.49  --qbf_dom_pre_inst                      false
% 7.43/1.49  --qbf_sk_in                             false
% 7.43/1.49  --qbf_pred_elim                         true
% 7.43/1.49  --qbf_split                             512
% 7.43/1.49  
% 7.43/1.49  ------ BMC1 Options
% 7.43/1.49  
% 7.43/1.49  --bmc1_incremental                      false
% 7.43/1.49  --bmc1_axioms                           reachable_all
% 7.43/1.49  --bmc1_min_bound                        0
% 7.43/1.49  --bmc1_max_bound                        -1
% 7.43/1.49  --bmc1_max_bound_default                -1
% 7.43/1.49  --bmc1_symbol_reachability              true
% 7.43/1.49  --bmc1_property_lemmas                  false
% 7.43/1.49  --bmc1_k_induction                      false
% 7.43/1.49  --bmc1_non_equiv_states                 false
% 7.43/1.49  --bmc1_deadlock                         false
% 7.43/1.49  --bmc1_ucm                              false
% 7.43/1.49  --bmc1_add_unsat_core                   none
% 7.43/1.49  --bmc1_unsat_core_children              false
% 7.43/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.43/1.49  --bmc1_out_stat                         full
% 7.43/1.49  --bmc1_ground_init                      false
% 7.43/1.49  --bmc1_pre_inst_next_state              false
% 7.43/1.49  --bmc1_pre_inst_state                   false
% 7.43/1.49  --bmc1_pre_inst_reach_state             false
% 7.43/1.49  --bmc1_out_unsat_core                   false
% 7.43/1.49  --bmc1_aig_witness_out                  false
% 7.43/1.49  --bmc1_verbose                          false
% 7.43/1.49  --bmc1_dump_clauses_tptp                false
% 7.43/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.43/1.49  --bmc1_dump_file                        -
% 7.43/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.43/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.43/1.49  --bmc1_ucm_extend_mode                  1
% 7.43/1.49  --bmc1_ucm_init_mode                    2
% 7.43/1.49  --bmc1_ucm_cone_mode                    none
% 7.43/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.43/1.49  --bmc1_ucm_relax_model                  4
% 7.43/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.43/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.43/1.49  --bmc1_ucm_layered_model                none
% 7.43/1.49  --bmc1_ucm_max_lemma_size               10
% 7.43/1.49  
% 7.43/1.49  ------ AIG Options
% 7.43/1.49  
% 7.43/1.49  --aig_mode                              false
% 7.43/1.49  
% 7.43/1.49  ------ Instantiation Options
% 7.43/1.49  
% 7.43/1.49  --instantiation_flag                    true
% 7.43/1.49  --inst_sos_flag                         true
% 7.43/1.49  --inst_sos_phase                        true
% 7.43/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.43/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.43/1.49  --inst_lit_sel_side                     num_symb
% 7.43/1.49  --inst_solver_per_active                1400
% 7.43/1.49  --inst_solver_calls_frac                1.
% 7.43/1.49  --inst_passive_queue_type               priority_queues
% 7.43/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.43/1.49  --inst_passive_queues_freq              [25;2]
% 7.43/1.49  --inst_dismatching                      true
% 7.43/1.49  --inst_eager_unprocessed_to_passive     true
% 7.43/1.49  --inst_prop_sim_given                   true
% 7.43/1.49  --inst_prop_sim_new                     false
% 7.43/1.49  --inst_subs_new                         false
% 7.43/1.49  --inst_eq_res_simp                      false
% 7.43/1.49  --inst_subs_given                       false
% 7.43/1.49  --inst_orphan_elimination               true
% 7.43/1.49  --inst_learning_loop_flag               true
% 7.43/1.49  --inst_learning_start                   3000
% 7.43/1.49  --inst_learning_factor                  2
% 7.43/1.49  --inst_start_prop_sim_after_learn       3
% 7.43/1.49  --inst_sel_renew                        solver
% 7.43/1.49  --inst_lit_activity_flag                true
% 7.43/1.49  --inst_restr_to_given                   false
% 7.43/1.49  --inst_activity_threshold               500
% 7.43/1.49  --inst_out_proof                        true
% 7.43/1.49  
% 7.43/1.49  ------ Resolution Options
% 7.43/1.49  
% 7.43/1.49  --resolution_flag                       true
% 7.43/1.49  --res_lit_sel                           adaptive
% 7.43/1.49  --res_lit_sel_side                      none
% 7.43/1.49  --res_ordering                          kbo
% 7.43/1.49  --res_to_prop_solver                    active
% 7.43/1.49  --res_prop_simpl_new                    false
% 7.43/1.49  --res_prop_simpl_given                  true
% 7.43/1.49  --res_passive_queue_type                priority_queues
% 7.43/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.43/1.49  --res_passive_queues_freq               [15;5]
% 7.43/1.49  --res_forward_subs                      full
% 7.43/1.49  --res_backward_subs                     full
% 7.43/1.49  --res_forward_subs_resolution           true
% 7.43/1.49  --res_backward_subs_resolution          true
% 7.43/1.49  --res_orphan_elimination                true
% 7.43/1.49  --res_time_limit                        2.
% 7.43/1.49  --res_out_proof                         true
% 7.43/1.49  
% 7.43/1.49  ------ Superposition Options
% 7.43/1.49  
% 7.43/1.49  --superposition_flag                    true
% 7.43/1.49  --sup_passive_queue_type                priority_queues
% 7.43/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.43/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.43/1.49  --demod_completeness_check              fast
% 7.43/1.49  --demod_use_ground                      true
% 7.43/1.49  --sup_to_prop_solver                    passive
% 7.43/1.49  --sup_prop_simpl_new                    true
% 7.43/1.49  --sup_prop_simpl_given                  true
% 7.43/1.49  --sup_fun_splitting                     true
% 7.43/1.49  --sup_smt_interval                      50000
% 7.43/1.49  
% 7.43/1.49  ------ Superposition Simplification Setup
% 7.43/1.49  
% 7.43/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.43/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.43/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.43/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.43/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.43/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.43/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.43/1.49  --sup_immed_triv                        [TrivRules]
% 7.43/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.49  --sup_immed_bw_main                     []
% 7.43/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.43/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.43/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.49  --sup_input_bw                          []
% 7.43/1.49  
% 7.43/1.49  ------ Combination Options
% 7.43/1.49  
% 7.43/1.49  --comb_res_mult                         3
% 7.43/1.49  --comb_sup_mult                         2
% 7.43/1.49  --comb_inst_mult                        10
% 7.43/1.49  
% 7.43/1.49  ------ Debug Options
% 7.43/1.49  
% 7.43/1.49  --dbg_backtrace                         false
% 7.43/1.49  --dbg_dump_prop_clauses                 false
% 7.43/1.49  --dbg_dump_prop_clauses_file            -
% 7.43/1.49  --dbg_out_stat                          false
% 7.43/1.49  ------ Parsing...
% 7.43/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.43/1.49  ------ Proving...
% 7.43/1.49  ------ Problem Properties 
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  clauses                                 41
% 7.43/1.49  conjectures                             11
% 7.43/1.49  EPR                                     7
% 7.43/1.49  Horn                                    37
% 7.43/1.49  unary                                   17
% 7.43/1.49  binary                                  6
% 7.43/1.49  lits                                    137
% 7.43/1.49  lits eq                                 32
% 7.43/1.49  fd_pure                                 0
% 7.43/1.49  fd_pseudo                               0
% 7.43/1.49  fd_cond                                 4
% 7.43/1.49  fd_pseudo_cond                          0
% 7.43/1.49  AC symbols                              0
% 7.43/1.49  
% 7.43/1.49  ------ Schedule dynamic 5 is on 
% 7.43/1.49  
% 7.43/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  ------ 
% 7.43/1.49  Current options:
% 7.43/1.49  ------ 
% 7.43/1.49  
% 7.43/1.49  ------ Input Options
% 7.43/1.49  
% 7.43/1.49  --out_options                           all
% 7.43/1.49  --tptp_safe_out                         true
% 7.43/1.49  --problem_path                          ""
% 7.43/1.49  --include_path                          ""
% 7.43/1.49  --clausifier                            res/vclausify_rel
% 7.43/1.49  --clausifier_options                    ""
% 7.43/1.49  --stdin                                 false
% 7.43/1.49  --stats_out                             all
% 7.43/1.49  
% 7.43/1.49  ------ General Options
% 7.43/1.49  
% 7.43/1.49  --fof                                   false
% 7.43/1.49  --time_out_real                         305.
% 7.43/1.49  --time_out_virtual                      -1.
% 7.43/1.49  --symbol_type_check                     false
% 7.43/1.49  --clausify_out                          false
% 7.43/1.49  --sig_cnt_out                           false
% 7.43/1.49  --trig_cnt_out                          false
% 7.43/1.49  --trig_cnt_out_tolerance                1.
% 7.43/1.49  --trig_cnt_out_sk_spl                   false
% 7.43/1.49  --abstr_cl_out                          false
% 7.43/1.49  
% 7.43/1.49  ------ Global Options
% 7.43/1.49  
% 7.43/1.49  --schedule                              default
% 7.43/1.49  --add_important_lit                     false
% 7.43/1.49  --prop_solver_per_cl                    1000
% 7.43/1.49  --min_unsat_core                        false
% 7.43/1.49  --soft_assumptions                      false
% 7.43/1.49  --soft_lemma_size                       3
% 7.43/1.49  --prop_impl_unit_size                   0
% 7.43/1.49  --prop_impl_unit                        []
% 7.43/1.49  --share_sel_clauses                     true
% 7.43/1.49  --reset_solvers                         false
% 7.43/1.49  --bc_imp_inh                            [conj_cone]
% 7.43/1.49  --conj_cone_tolerance                   3.
% 7.43/1.49  --extra_neg_conj                        none
% 7.43/1.49  --large_theory_mode                     true
% 7.43/1.49  --prolific_symb_bound                   200
% 7.43/1.49  --lt_threshold                          2000
% 7.43/1.49  --clause_weak_htbl                      true
% 7.43/1.49  --gc_record_bc_elim                     false
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing Options
% 7.43/1.49  
% 7.43/1.49  --preprocessing_flag                    true
% 7.43/1.49  --time_out_prep_mult                    0.1
% 7.43/1.49  --splitting_mode                        input
% 7.43/1.49  --splitting_grd                         true
% 7.43/1.49  --splitting_cvd                         false
% 7.43/1.49  --splitting_cvd_svl                     false
% 7.43/1.49  --splitting_nvd                         32
% 7.43/1.49  --sub_typing                            true
% 7.43/1.49  --prep_gs_sim                           true
% 7.43/1.49  --prep_unflatten                        true
% 7.43/1.49  --prep_res_sim                          true
% 7.43/1.49  --prep_upred                            true
% 7.43/1.49  --prep_sem_filter                       exhaustive
% 7.43/1.49  --prep_sem_filter_out                   false
% 7.43/1.49  --pred_elim                             true
% 7.43/1.49  --res_sim_input                         true
% 7.43/1.49  --eq_ax_congr_red                       true
% 7.43/1.49  --pure_diseq_elim                       true
% 7.43/1.49  --brand_transform                       false
% 7.43/1.49  --non_eq_to_eq                          false
% 7.43/1.49  --prep_def_merge                        true
% 7.43/1.49  --prep_def_merge_prop_impl              false
% 7.43/1.49  --prep_def_merge_mbd                    true
% 7.43/1.49  --prep_def_merge_tr_red                 false
% 7.43/1.49  --prep_def_merge_tr_cl                  false
% 7.43/1.49  --smt_preprocessing                     true
% 7.43/1.49  --smt_ac_axioms                         fast
% 7.43/1.49  --preprocessed_out                      false
% 7.43/1.49  --preprocessed_stats                    false
% 7.43/1.49  
% 7.43/1.49  ------ Abstraction refinement Options
% 7.43/1.49  
% 7.43/1.49  --abstr_ref                             []
% 7.43/1.49  --abstr_ref_prep                        false
% 7.43/1.49  --abstr_ref_until_sat                   false
% 7.43/1.49  --abstr_ref_sig_restrict                funpre
% 7.43/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.43/1.49  --abstr_ref_under                       []
% 7.43/1.49  
% 7.43/1.49  ------ SAT Options
% 7.43/1.49  
% 7.43/1.49  --sat_mode                              false
% 7.43/1.49  --sat_fm_restart_options                ""
% 7.43/1.49  --sat_gr_def                            false
% 7.43/1.49  --sat_epr_types                         true
% 7.43/1.49  --sat_non_cyclic_types                  false
% 7.43/1.49  --sat_finite_models                     false
% 7.43/1.49  --sat_fm_lemmas                         false
% 7.43/1.49  --sat_fm_prep                           false
% 7.43/1.49  --sat_fm_uc_incr                        true
% 7.43/1.49  --sat_out_model                         small
% 7.43/1.49  --sat_out_clauses                       false
% 7.43/1.49  
% 7.43/1.49  ------ QBF Options
% 7.43/1.49  
% 7.43/1.49  --qbf_mode                              false
% 7.43/1.49  --qbf_elim_univ                         false
% 7.43/1.49  --qbf_dom_inst                          none
% 7.43/1.49  --qbf_dom_pre_inst                      false
% 7.43/1.49  --qbf_sk_in                             false
% 7.43/1.49  --qbf_pred_elim                         true
% 7.43/1.49  --qbf_split                             512
% 7.43/1.49  
% 7.43/1.49  ------ BMC1 Options
% 7.43/1.49  
% 7.43/1.49  --bmc1_incremental                      false
% 7.43/1.49  --bmc1_axioms                           reachable_all
% 7.43/1.49  --bmc1_min_bound                        0
% 7.43/1.49  --bmc1_max_bound                        -1
% 7.43/1.49  --bmc1_max_bound_default                -1
% 7.43/1.49  --bmc1_symbol_reachability              true
% 7.43/1.49  --bmc1_property_lemmas                  false
% 7.43/1.49  --bmc1_k_induction                      false
% 7.43/1.49  --bmc1_non_equiv_states                 false
% 7.43/1.49  --bmc1_deadlock                         false
% 7.43/1.49  --bmc1_ucm                              false
% 7.43/1.49  --bmc1_add_unsat_core                   none
% 7.43/1.49  --bmc1_unsat_core_children              false
% 7.43/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.43/1.49  --bmc1_out_stat                         full
% 7.43/1.49  --bmc1_ground_init                      false
% 7.43/1.49  --bmc1_pre_inst_next_state              false
% 7.43/1.49  --bmc1_pre_inst_state                   false
% 7.43/1.49  --bmc1_pre_inst_reach_state             false
% 7.43/1.49  --bmc1_out_unsat_core                   false
% 7.43/1.49  --bmc1_aig_witness_out                  false
% 7.43/1.49  --bmc1_verbose                          false
% 7.43/1.49  --bmc1_dump_clauses_tptp                false
% 7.43/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.43/1.49  --bmc1_dump_file                        -
% 7.43/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.43/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.43/1.49  --bmc1_ucm_extend_mode                  1
% 7.43/1.49  --bmc1_ucm_init_mode                    2
% 7.43/1.49  --bmc1_ucm_cone_mode                    none
% 7.43/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.43/1.49  --bmc1_ucm_relax_model                  4
% 7.43/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.43/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.43/1.49  --bmc1_ucm_layered_model                none
% 7.43/1.49  --bmc1_ucm_max_lemma_size               10
% 7.43/1.49  
% 7.43/1.49  ------ AIG Options
% 7.43/1.49  
% 7.43/1.49  --aig_mode                              false
% 7.43/1.49  
% 7.43/1.49  ------ Instantiation Options
% 7.43/1.49  
% 7.43/1.49  --instantiation_flag                    true
% 7.43/1.49  --inst_sos_flag                         true
% 7.43/1.49  --inst_sos_phase                        true
% 7.43/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.43/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.43/1.49  --inst_lit_sel_side                     none
% 7.43/1.49  --inst_solver_per_active                1400
% 7.43/1.49  --inst_solver_calls_frac                1.
% 7.43/1.49  --inst_passive_queue_type               priority_queues
% 7.43/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.43/1.49  --inst_passive_queues_freq              [25;2]
% 7.43/1.49  --inst_dismatching                      true
% 7.43/1.49  --inst_eager_unprocessed_to_passive     true
% 7.43/1.49  --inst_prop_sim_given                   true
% 7.43/1.49  --inst_prop_sim_new                     false
% 7.43/1.49  --inst_subs_new                         false
% 7.43/1.49  --inst_eq_res_simp                      false
% 7.43/1.49  --inst_subs_given                       false
% 7.43/1.49  --inst_orphan_elimination               true
% 7.43/1.49  --inst_learning_loop_flag               true
% 7.43/1.49  --inst_learning_start                   3000
% 7.43/1.49  --inst_learning_factor                  2
% 7.43/1.49  --inst_start_prop_sim_after_learn       3
% 7.43/1.49  --inst_sel_renew                        solver
% 7.43/1.49  --inst_lit_activity_flag                true
% 7.43/1.49  --inst_restr_to_given                   false
% 7.43/1.49  --inst_activity_threshold               500
% 7.43/1.49  --inst_out_proof                        true
% 7.43/1.49  
% 7.43/1.49  ------ Resolution Options
% 7.43/1.49  
% 7.43/1.49  --resolution_flag                       false
% 7.43/1.49  --res_lit_sel                           adaptive
% 7.43/1.49  --res_lit_sel_side                      none
% 7.43/1.49  --res_ordering                          kbo
% 7.43/1.49  --res_to_prop_solver                    active
% 7.43/1.49  --res_prop_simpl_new                    false
% 7.43/1.49  --res_prop_simpl_given                  true
% 7.43/1.49  --res_passive_queue_type                priority_queues
% 7.43/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.43/1.49  --res_passive_queues_freq               [15;5]
% 7.43/1.49  --res_forward_subs                      full
% 7.43/1.49  --res_backward_subs                     full
% 7.43/1.49  --res_forward_subs_resolution           true
% 7.43/1.49  --res_backward_subs_resolution          true
% 7.43/1.49  --res_orphan_elimination                true
% 7.43/1.49  --res_time_limit                        2.
% 7.43/1.49  --res_out_proof                         true
% 7.43/1.49  
% 7.43/1.49  ------ Superposition Options
% 7.43/1.49  
% 7.43/1.49  --superposition_flag                    true
% 7.43/1.49  --sup_passive_queue_type                priority_queues
% 7.43/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.43/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.43/1.49  --demod_completeness_check              fast
% 7.43/1.49  --demod_use_ground                      true
% 7.43/1.49  --sup_to_prop_solver                    passive
% 7.43/1.49  --sup_prop_simpl_new                    true
% 7.43/1.49  --sup_prop_simpl_given                  true
% 7.43/1.49  --sup_fun_splitting                     true
% 7.43/1.49  --sup_smt_interval                      50000
% 7.43/1.49  
% 7.43/1.49  ------ Superposition Simplification Setup
% 7.43/1.49  
% 7.43/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.43/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.43/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.43/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.43/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.43/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.43/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.43/1.49  --sup_immed_triv                        [TrivRules]
% 7.43/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.49  --sup_immed_bw_main                     []
% 7.43/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.43/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.43/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.43/1.49  --sup_input_bw                          []
% 7.43/1.49  
% 7.43/1.49  ------ Combination Options
% 7.43/1.49  
% 7.43/1.49  --comb_res_mult                         3
% 7.43/1.49  --comb_sup_mult                         2
% 7.43/1.49  --comb_inst_mult                        10
% 7.43/1.49  
% 7.43/1.49  ------ Debug Options
% 7.43/1.49  
% 7.43/1.49  --dbg_backtrace                         false
% 7.43/1.49  --dbg_dump_prop_clauses                 false
% 7.43/1.49  --dbg_dump_prop_clauses_file            -
% 7.43/1.49  --dbg_out_stat                          false
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  ------ Proving...
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  % SZS status Theorem for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  fof(f3,axiom,(
% 7.43/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f56,plain,(
% 7.43/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.43/1.49    inference(cnf_transformation,[],[f3])).
% 7.43/1.49  
% 7.43/1.49  fof(f21,conjecture,(
% 7.43/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f22,negated_conjecture,(
% 7.43/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.43/1.49    inference(negated_conjecture,[],[f21])).
% 7.43/1.49  
% 7.43/1.49  fof(f48,plain,(
% 7.43/1.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.43/1.49    inference(ennf_transformation,[],[f22])).
% 7.43/1.49  
% 7.43/1.49  fof(f49,plain,(
% 7.43/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.43/1.49    inference(flattening,[],[f48])).
% 7.43/1.49  
% 7.43/1.49  fof(f52,plain,(
% 7.43/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f51,plain,(
% 7.43/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.43/1.49    introduced(choice_axiom,[])).
% 7.43/1.49  
% 7.43/1.49  fof(f53,plain,(
% 7.43/1.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.43/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f52,f51])).
% 7.43/1.49  
% 7.43/1.49  fof(f90,plain,(
% 7.43/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f1,axiom,(
% 7.43/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f24,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f1])).
% 7.43/1.49  
% 7.43/1.49  fof(f54,plain,(
% 7.43/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f24])).
% 7.43/1.49  
% 7.43/1.49  fof(f87,plain,(
% 7.43/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f85,plain,(
% 7.43/1.49    v1_funct_1(sK2)),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f10,axiom,(
% 7.43/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f32,plain,(
% 7.43/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f10])).
% 7.43/1.49  
% 7.43/1.49  fof(f33,plain,(
% 7.43/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.43/1.49    inference(flattening,[],[f32])).
% 7.43/1.49  
% 7.43/1.49  fof(f65,plain,(
% 7.43/1.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f33])).
% 7.43/1.49  
% 7.43/1.49  fof(f5,axiom,(
% 7.43/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f27,plain,(
% 7.43/1.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f5])).
% 7.43/1.49  
% 7.43/1.49  fof(f59,plain,(
% 7.43/1.49    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f27])).
% 7.43/1.49  
% 7.43/1.49  fof(f9,axiom,(
% 7.43/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f30,plain,(
% 7.43/1.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f9])).
% 7.43/1.49  
% 7.43/1.49  fof(f31,plain,(
% 7.43/1.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.43/1.49    inference(flattening,[],[f30])).
% 7.43/1.49  
% 7.43/1.49  fof(f64,plain,(
% 7.43/1.49    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f31])).
% 7.43/1.49  
% 7.43/1.49  fof(f93,plain,(
% 7.43/1.49    v2_funct_1(sK2)),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f91,plain,(
% 7.43/1.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f20,axiom,(
% 7.43/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f46,plain,(
% 7.43/1.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.43/1.49    inference(ennf_transformation,[],[f20])).
% 7.43/1.49  
% 7.43/1.49  fof(f47,plain,(
% 7.43/1.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.43/1.49    inference(flattening,[],[f46])).
% 7.43/1.49  
% 7.43/1.49  fof(f84,plain,(
% 7.43/1.49    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f47])).
% 7.43/1.49  
% 7.43/1.49  fof(f86,plain,(
% 7.43/1.49    v1_funct_2(sK2,sK0,sK1)),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f95,plain,(
% 7.43/1.49    k1_xboole_0 != sK1),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f16,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f40,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.43/1.49    inference(ennf_transformation,[],[f16])).
% 7.43/1.49  
% 7.43/1.49  fof(f41,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.43/1.49    inference(flattening,[],[f40])).
% 7.43/1.49  
% 7.43/1.49  fof(f76,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f41])).
% 7.43/1.49  
% 7.43/1.49  fof(f88,plain,(
% 7.43/1.49    v1_funct_1(sK3)),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f13,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f36,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.43/1.49    inference(ennf_transformation,[],[f13])).
% 7.43/1.49  
% 7.43/1.49  fof(f37,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.43/1.49    inference(flattening,[],[f36])).
% 7.43/1.49  
% 7.43/1.49  fof(f50,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.43/1.49    inference(nnf_transformation,[],[f37])).
% 7.43/1.49  
% 7.43/1.49  fof(f71,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.43/1.49    inference(cnf_transformation,[],[f50])).
% 7.43/1.49  
% 7.43/1.49  fof(f92,plain,(
% 7.43/1.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f15,axiom,(
% 7.43/1.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f23,plain,(
% 7.43/1.49    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.43/1.49    inference(pure_predicate_removal,[],[f15])).
% 7.43/1.49  
% 7.43/1.49  fof(f75,plain,(
% 7.43/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.43/1.49    inference(cnf_transformation,[],[f23])).
% 7.43/1.49  
% 7.43/1.49  fof(f14,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f38,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.43/1.49    inference(ennf_transformation,[],[f14])).
% 7.43/1.49  
% 7.43/1.49  fof(f39,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.43/1.49    inference(flattening,[],[f38])).
% 7.43/1.49  
% 7.43/1.49  fof(f74,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f39])).
% 7.43/1.49  
% 7.43/1.49  fof(f2,axiom,(
% 7.43/1.49    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f25,plain,(
% 7.43/1.49    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f2])).
% 7.43/1.49  
% 7.43/1.49  fof(f55,plain,(
% 7.43/1.49    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f25])).
% 7.43/1.49  
% 7.43/1.49  fof(f8,axiom,(
% 7.43/1.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f29,plain,(
% 7.43/1.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f8])).
% 7.43/1.49  
% 7.43/1.49  fof(f63,plain,(
% 7.43/1.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f29])).
% 7.43/1.49  
% 7.43/1.49  fof(f17,axiom,(
% 7.43/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f77,plain,(
% 7.43/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f17])).
% 7.43/1.49  
% 7.43/1.49  fof(f100,plain,(
% 7.43/1.49    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f63,f77])).
% 7.43/1.49  
% 7.43/1.49  fof(f4,axiom,(
% 7.43/1.49    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f26,plain,(
% 7.43/1.49    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f4])).
% 7.43/1.49  
% 7.43/1.49  fof(f58,plain,(
% 7.43/1.49    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f26])).
% 7.43/1.49  
% 7.43/1.49  fof(f12,axiom,(
% 7.43/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f34,plain,(
% 7.43/1.49    ! [X0] : (((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.43/1.49    inference(ennf_transformation,[],[f12])).
% 7.43/1.49  
% 7.43/1.49  fof(f35,plain,(
% 7.43/1.49    ! [X0] : ((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.43/1.49    inference(flattening,[],[f34])).
% 7.43/1.49  
% 7.43/1.49  fof(f69,plain,(
% 7.43/1.49    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f35])).
% 7.43/1.49  
% 7.43/1.49  fof(f83,plain,(
% 7.43/1.49    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f47])).
% 7.43/1.49  
% 7.43/1.49  fof(f6,axiom,(
% 7.43/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f60,plain,(
% 7.43/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.43/1.49    inference(cnf_transformation,[],[f6])).
% 7.43/1.49  
% 7.43/1.49  fof(f98,plain,(
% 7.43/1.49    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.43/1.49    inference(definition_unfolding,[],[f60,f77])).
% 7.43/1.49  
% 7.43/1.49  fof(f18,axiom,(
% 7.43/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f42,plain,(
% 7.43/1.49    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.43/1.49    inference(ennf_transformation,[],[f18])).
% 7.43/1.49  
% 7.43/1.49  fof(f43,plain,(
% 7.43/1.49    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.43/1.49    inference(flattening,[],[f42])).
% 7.43/1.49  
% 7.43/1.49  fof(f78,plain,(
% 7.43/1.49    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f43])).
% 7.43/1.49  
% 7.43/1.49  fof(f89,plain,(
% 7.43/1.49    v1_funct_2(sK3,sK1,sK0)),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f94,plain,(
% 7.43/1.49    k1_xboole_0 != sK0),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  fof(f11,axiom,(
% 7.43/1.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f68,plain,(
% 7.43/1.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.43/1.49    inference(cnf_transformation,[],[f11])).
% 7.43/1.49  
% 7.43/1.49  fof(f101,plain,(
% 7.43/1.49    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.43/1.49    inference(definition_unfolding,[],[f68,f77])).
% 7.43/1.49  
% 7.43/1.49  fof(f19,axiom,(
% 7.43/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f44,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.43/1.49    inference(ennf_transformation,[],[f19])).
% 7.43/1.49  
% 7.43/1.49  fof(f45,plain,(
% 7.43/1.49    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.43/1.49    inference(flattening,[],[f44])).
% 7.43/1.49  
% 7.43/1.49  fof(f81,plain,(
% 7.43/1.49    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f45])).
% 7.43/1.49  
% 7.43/1.49  fof(f7,axiom,(
% 7.43/1.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.43/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.43/1.49  
% 7.43/1.49  fof(f28,plain,(
% 7.43/1.49    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.43/1.49    inference(ennf_transformation,[],[f7])).
% 7.43/1.49  
% 7.43/1.49  fof(f62,plain,(
% 7.43/1.49    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(cnf_transformation,[],[f28])).
% 7.43/1.49  
% 7.43/1.49  fof(f99,plain,(
% 7.43/1.49    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.43/1.49    inference(definition_unfolding,[],[f62,f77])).
% 7.43/1.49  
% 7.43/1.49  fof(f96,plain,(
% 7.43/1.49    k2_funct_1(sK2) != sK3),
% 7.43/1.49    inference(cnf_transformation,[],[f53])).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2,plain,
% 7.43/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1348,plain,
% 7.43/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_36,negated_conjecture,
% 7.43/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.43/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1324,plain,
% 7.43/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_0,plain,
% 7.43/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.43/1.49      | ~ v1_relat_1(X1)
% 7.43/1.49      | v1_relat_1(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1350,plain,
% 7.43/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.43/1.49      | v1_relat_1(X1) != iProver_top
% 7.43/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3066,plain,
% 7.43/1.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.43/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1324,c_1350]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3187,plain,
% 7.43/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1348,c_3066]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_39,negated_conjecture,
% 7.43/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.43/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1321,plain,
% 7.43/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3067,plain,
% 7.43/1.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.43/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1321,c_1350]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3190,plain,
% 7.43/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1348,c_3067]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_41,negated_conjecture,
% 7.43/1.49      ( v1_funct_1(sK2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1319,plain,
% 7.43/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_12,plain,
% 7.43/1.49      ( ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v1_relat_1(X0)
% 7.43/1.49      | v1_relat_1(k2_funct_1(X0)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1340,plain,
% 7.43/1.49      ( v1_funct_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_5,plain,
% 7.43/1.49      ( ~ v1_relat_1(X0)
% 7.43/1.49      | ~ v1_relat_1(X1)
% 7.43/1.49      | ~ v1_relat_1(X2)
% 7.43/1.49      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1345,plain,
% 7.43/1.49      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.43/1.49      | v1_relat_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X1) != iProver_top
% 7.43/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4023,plain,
% 7.43/1.49      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.43/1.49      | v1_funct_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X1) != iProver_top
% 7.43/1.49      | v1_relat_1(X2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1340,c_1345]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13579,plain,
% 7.43/1.49      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.43/1.49      | v1_relat_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X1) != iProver_top
% 7.43/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1319,c_4023]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_10,plain,
% 7.43/1.49      ( ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v2_funct_1(X0)
% 7.43/1.49      | ~ v1_relat_1(X0)
% 7.43/1.49      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1342,plain,
% 7.43/1.49      ( k2_funct_1(X0) = k4_relat_1(X0)
% 7.43/1.49      | v1_funct_1(X0) != iProver_top
% 7.43/1.49      | v2_funct_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3136,plain,
% 7.43/1.49      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 7.43/1.49      | v2_funct_1(sK2) != iProver_top
% 7.43/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1319,c_1342]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_33,negated_conjecture,
% 7.43/1.49      ( v2_funct_1(sK2) ),
% 7.43/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_49,plain,
% 7.43/1.49      ( v2_funct_1(sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3349,plain,
% 7.43/1.49      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3136,c_49,c_3190]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13588,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
% 7.43/1.49      | v1_relat_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X1) != iProver_top
% 7.43/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_13579,c_3349]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13787,plain,
% 7.43/1.49      ( v1_relat_1(X1) != iProver_top
% 7.43/1.49      | v1_relat_1(X0) != iProver_top
% 7.43/1.49      | k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_13588,c_3190]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13788,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
% 7.43/1.49      | v1_relat_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_13787]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13798,plain,
% 7.43/1.49      ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0))
% 7.43/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_3190,c_13788]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_35,negated_conjecture,
% 7.43/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.43/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_28,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v2_funct_1(X0)
% 7.43/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.43/1.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.43/1.49      | k1_xboole_0 = X2 ),
% 7.43/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1327,plain,
% 7.43/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 7.43/1.49      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.43/1.49      | k1_xboole_0 = X1
% 7.43/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.43/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.43/1.49      | v1_funct_1(X2) != iProver_top
% 7.43/1.49      | v2_funct_1(X2) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3816,plain,
% 7.43/1.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.43/1.49      | sK1 = k1_xboole_0
% 7.43/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.43/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.43/1.49      | v1_funct_1(sK2) != iProver_top
% 7.43/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_35,c_1327]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3818,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1)
% 7.43/1.49      | sK1 = k1_xboole_0
% 7.43/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.43/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.43/1.49      | v1_funct_1(sK2) != iProver_top
% 7.43/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_3816,c_3349]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_42,plain,
% 7.43/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_40,negated_conjecture,
% 7.43/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.43/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_43,plain,
% 7.43/1.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_44,plain,
% 7.43/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_31,negated_conjecture,
% 7.43/1.49      ( k1_xboole_0 != sK1 ),
% 7.43/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_748,plain,( X0 = X0 ),theory(equality) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_779,plain,
% 7.43/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_748]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_749,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1415,plain,
% 7.43/1.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_749]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1416,plain,
% 7.43/1.49      ( sK1 != k1_xboole_0
% 7.43/1.49      | k1_xboole_0 = sK1
% 7.43/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_1415]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4414,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3818,c_42,c_43,c_44,c_49,c_31,c_779,c_1416]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13804,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.43/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_13798,c_4414]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13958,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_3187,c_13804]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_22,plain,
% 7.43/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.43/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v1_funct_1(X3)
% 7.43/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1332,plain,
% 7.43/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.43/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.43/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.43/1.49      | v1_funct_1(X5) != iProver_top
% 7.43/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6264,plain,
% 7.43/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.43/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.43/1.49      | v1_funct_1(X2) != iProver_top
% 7.43/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1324,c_1332]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_38,negated_conjecture,
% 7.43/1.49      ( v1_funct_1(sK3) ),
% 7.43/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_45,plain,
% 7.43/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6357,plain,
% 7.43/1.49      ( v1_funct_1(X2) != iProver_top
% 7.43/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.43/1.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_6264,c_45]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6358,plain,
% 7.43/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.43/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.43/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_6357]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6366,plain,
% 7.43/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.43/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1321,c_6358]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_18,plain,
% 7.43/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.43/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.43/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.43/1.49      | X3 = X2 ),
% 7.43/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_34,negated_conjecture,
% 7.43/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_443,plain,
% 7.43/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.43/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.43/1.49      | X3 = X0
% 7.43/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.43/1.49      | k6_partfun1(sK0) != X3
% 7.43/1.49      | sK0 != X2
% 7.43/1.49      | sK0 != X1 ),
% 7.43/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_34]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_444,plain,
% 7.43/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.43/1.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.43/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.43/1.49      inference(unflattening,[status(thm)],[c_443]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_21,plain,
% 7.43/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.43/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_452,plain,
% 7.43/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.43/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.43/1.49      inference(forward_subsumption_resolution,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_444,c_21]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1317,plain,
% 7.43/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.43/1.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_19,plain,
% 7.43/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.43/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.43/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v1_funct_1(X3) ),
% 7.43/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1437,plain,
% 7.43/1.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.43/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.43/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.43/1.49      | ~ v1_funct_1(sK3)
% 7.43/1.49      | ~ v1_funct_1(sK2) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2077,plain,
% 7.43/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1317,c_41,c_39,c_38,c_36,c_452,c_1437]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6367,plain,
% 7.43/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.43/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_6366,c_2077]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6520,plain,
% 7.43/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_6367,c_42]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1,plain,
% 7.43/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1349,plain,
% 7.43/1.49      ( v1_relat_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_9,plain,
% 7.43/1.49      ( ~ v1_relat_1(X0)
% 7.43/1.49      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.43/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1343,plain,
% 7.43/1.49      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.43/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2374,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(X0),k6_partfun1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
% 7.43/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1349,c_1343]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6956,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) = k4_relat_1(sK2) ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_3190,c_2374]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3,plain,
% 7.43/1.49      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1347,plain,
% 7.43/1.49      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 7.43/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4420,plain,
% 7.43/1.49      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_3190,c_1347]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_16,plain,
% 7.43/1.49      ( ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v2_funct_1(X0)
% 7.43/1.49      | ~ v1_relat_1(X0)
% 7.43/1.49      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1336,plain,
% 7.43/1.49      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 7.43/1.49      | v1_funct_1(X0) != iProver_top
% 7.43/1.49      | v2_funct_1(X0) != iProver_top
% 7.43/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3919,plain,
% 7.43/1.49      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 7.43/1.49      | v2_funct_1(sK2) != iProver_top
% 7.43/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1319,c_1336]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_29,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v2_funct_1(X0)
% 7.43/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.43/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.43/1.49      | k1_xboole_0 = X2 ),
% 7.43/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1326,plain,
% 7.43/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 7.43/1.49      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.43/1.49      | k1_xboole_0 = X1
% 7.43/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.43/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.43/1.49      | v1_funct_1(X2) != iProver_top
% 7.43/1.49      | v2_funct_1(X2) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3012,plain,
% 7.43/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.43/1.49      | sK1 = k1_xboole_0
% 7.43/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.43/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.43/1.49      | v1_funct_1(sK2) != iProver_top
% 7.43/1.49      | v2_funct_1(sK2) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_35,c_1326]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1398,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,X1,sK1)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v2_funct_1(X0)
% 7.43/1.49      | k2_relset_1(X1,sK1,X0) != sK1
% 7.43/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.43/1.49      | k1_xboole_0 = sK1 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1533,plain,
% 7.43/1.49      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.43/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.43/1.49      | ~ v1_funct_1(sK2)
% 7.43/1.49      | ~ v2_funct_1(sK2)
% 7.43/1.49      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.43/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 7.43/1.49      | k1_xboole_0 = sK1 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_1398]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1733,plain,
% 7.43/1.49      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.43/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.43/1.49      | ~ v1_funct_1(sK2)
% 7.43/1.49      | ~ v2_funct_1(sK2)
% 7.43/1.49      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.43/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.43/1.49      | k1_xboole_0 = sK1 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_1533]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3143,plain,
% 7.43/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3012,c_41,c_40,c_39,c_35,c_33,c_31,c_1733]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3351,plain,
% 7.43/1.49      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 7.43/1.49      inference(demodulation,[status(thm)],[c_3349,c_3143]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3920,plain,
% 7.43/1.49      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 7.43/1.49      | v2_funct_1(sK2) != iProver_top
% 7.43/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_3919,c_3349,c_3351]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7,plain,
% 7.43/1.49      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.43/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3921,plain,
% 7.43/1.49      ( k1_relat_1(sK2) = sK0
% 7.43/1.49      | v2_funct_1(sK2) != iProver_top
% 7.43/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.43/1.49      inference(demodulation,[status(thm)],[c_3920,c_7]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3928,plain,
% 7.43/1.49      ( k1_relat_1(sK2) = sK0 ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3921,c_49,c_3190]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4422,plain,
% 7.43/1.49      ( k2_relat_1(k4_relat_1(sK2)) = sK0 ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_4420,c_3928]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6957,plain,
% 7.43/1.49      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k4_relat_1(sK2) ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_6956,c_4422]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_23,plain,
% 7.43/1.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.43/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.43/1.49      | ~ v1_funct_2(X3,X1,X0)
% 7.43/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.43/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.43/1.49      | ~ v1_funct_1(X2)
% 7.43/1.49      | ~ v1_funct_1(X3)
% 7.43/1.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.43/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_456,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.43/1.49      | ~ v1_funct_2(X3,X2,X1)
% 7.43/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.43/1.49      | ~ v1_funct_1(X3)
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.43/1.49      | k2_relset_1(X2,X1,X3) = X1
% 7.43/1.49      | k6_partfun1(X1) != k6_partfun1(sK0)
% 7.43/1.49      | sK0 != X1 ),
% 7.43/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_457,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.43/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.43/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.43/1.49      | ~ v1_funct_1(X2)
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.43/1.49      | k2_relset_1(X1,sK0,X0) = sK0
% 7.43/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.43/1.49      inference(unflattening,[status(thm)],[c_456]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_546,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.43/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.43/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | ~ v1_funct_1(X2)
% 7.43/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.43/1.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.43/1.49      inference(equality_resolution_simp,[status(thm)],[c_457]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1316,plain,
% 7.43/1.49      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.43/1.49      | k2_relset_1(X0,sK0,X2) = sK0
% 7.43/1.49      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.43/1.49      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.43/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.43/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.43/1.49      | v1_funct_1(X2) != iProver_top
% 7.43/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1828,plain,
% 7.43/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.43/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.43/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.43/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.43/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.43/1.49      | v1_funct_1(sK3) != iProver_top
% 7.43/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.43/1.49      inference(equality_resolution,[status(thm)],[c_1316]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_37,negated_conjecture,
% 7.43/1.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.43/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_46,plain,
% 7.43/1.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_47,plain,
% 7.43/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_2084,plain,
% 7.43/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_1828,c_42,c_43,c_44,c_45,c_46,c_47]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3013,plain,
% 7.43/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.43/1.49      | sK0 = k1_xboole_0
% 7.43/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.43/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.43/1.49      | v1_funct_1(sK3) != iProver_top
% 7.43/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_2084,c_1326]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_32,negated_conjecture,
% 7.43/1.49      ( k1_xboole_0 != sK0 ),
% 7.43/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1435,plain,
% 7.43/1.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_749]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1436,plain,
% 7.43/1.49      ( sK0 != k1_xboole_0
% 7.43/1.49      | k1_xboole_0 = sK0
% 7.43/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_1435]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13,plain,
% 7.43/1.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.43/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6643,plain,
% 7.43/1.49      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.43/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6644,plain,
% 7.43/1.49      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_6643]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_25,plain,
% 7.43/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.43/1.49      | ~ v1_funct_2(X3,X2,X4)
% 7.43/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.43/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 7.43/1.49      | ~ v1_funct_1(X3)
% 7.43/1.49      | ~ v1_funct_1(X0)
% 7.43/1.49      | v2_funct_1(X3)
% 7.43/1.49      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 7.43/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.43/1.49      | k1_xboole_0 = X4 ),
% 7.43/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1330,plain,
% 7.43/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 7.43/1.49      | k1_xboole_0 = X3
% 7.43/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.43/1.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.43/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.43/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.43/1.49      | v1_funct_1(X2) != iProver_top
% 7.43/1.49      | v1_funct_1(X4) != iProver_top
% 7.43/1.49      | v2_funct_1(X4) = iProver_top
% 7.43/1.49      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6631,plain,
% 7.43/1.49      ( k1_xboole_0 = X0
% 7.43/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.43/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.43/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.43/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.43/1.49      | v1_funct_1(X1) != iProver_top
% 7.43/1.49      | v1_funct_1(sK2) != iProver_top
% 7.43/1.49      | v2_funct_1(X1) = iProver_top
% 7.43/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_35,c_1330]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6654,plain,
% 7.43/1.49      ( v1_funct_1(X1) != iProver_top
% 7.43/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.43/1.49      | k1_xboole_0 = X0
% 7.43/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.43/1.49      | v2_funct_1(X1) = iProver_top
% 7.43/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_6631,c_42,c_43,c_44]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6655,plain,
% 7.43/1.49      ( k1_xboole_0 = X0
% 7.43/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.43/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.43/1.49      | v1_funct_1(X1) != iProver_top
% 7.43/1.49      | v2_funct_1(X1) = iProver_top
% 7.43/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_6654]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6658,plain,
% 7.43/1.49      ( sK0 = k1_xboole_0
% 7.43/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.43/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.43/1.49      | v1_funct_1(sK3) != iProver_top
% 7.43/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.43/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_2077,c_6655]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7750,plain,
% 7.43/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3013,c_45,c_46,c_47,c_32,c_779,c_1436,c_6644,c_6658]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6728,plain,
% 7.43/1.49      ( v2_funct_1(sK3) = iProver_top ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_6658,c_45,c_46,c_47,c_32,c_779,c_1436,c_6644]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1322,plain,
% 7.43/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3135,plain,
% 7.43/1.49      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 7.43/1.49      | v2_funct_1(sK3) != iProver_top
% 7.43/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1322,c_1342]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3344,plain,
% 7.43/1.49      ( v2_funct_1(sK3) != iProver_top
% 7.43/1.49      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3135,c_3187]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3345,plain,
% 7.43/1.49      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 7.43/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_3344]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6734,plain,
% 7.43/1.49      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_6728,c_3345]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7752,plain,
% 7.43/1.49      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
% 7.43/1.49      inference(light_normalisation,[status(thm)],[c_7750,c_6734]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3918,plain,
% 7.43/1.49      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 7.43/1.49      | v2_funct_1(sK3) != iProver_top
% 7.43/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_1322,c_1336]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4256,plain,
% 7.43/1.49      ( v2_funct_1(sK3) != iProver_top
% 7.43/1.49      | k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 7.43/1.49      inference(global_propositional_subsumption,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_3918,c_3187]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_4257,plain,
% 7.43/1.49      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 7.43/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.43/1.49      inference(renaming,[status(thm)],[c_4256]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6733,plain,
% 7.43/1.49      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_6728,c_4257]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_6735,plain,
% 7.43/1.49      ( k1_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))) = k1_relat_1(sK3) ),
% 7.43/1.49      inference(demodulation,[status(thm)],[c_6733,c_6734]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7754,plain,
% 7.43/1.49      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 7.43/1.49      inference(demodulation,[status(thm)],[c_7752,c_6735]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7755,plain,
% 7.43/1.49      ( k1_relat_1(sK3) = sK1 ),
% 7.43/1.49      inference(demodulation,[status(thm)],[c_7754,c_7]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_8,plain,
% 7.43/1.49      ( ~ v1_relat_1(X0)
% 7.43/1.49      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.43/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_1344,plain,
% 7.43/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.43/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.43/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3811,plain,
% 7.43/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 7.43/1.49      inference(superposition,[status(thm)],[c_3187,c_1344]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_7757,plain,
% 7.43/1.49      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.43/1.49      inference(demodulation,[status(thm)],[c_7755,c_3811]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_13969,plain,
% 7.43/1.49      ( k4_relat_1(sK2) = sK3 ),
% 7.43/1.49      inference(light_normalisation,
% 7.43/1.49                [status(thm)],
% 7.43/1.49                [c_13958,c_6520,c_6957,c_7757]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_30,negated_conjecture,
% 7.43/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.43/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(c_3352,plain,
% 7.43/1.49      ( k4_relat_1(sK2) != sK3 ),
% 7.43/1.49      inference(demodulation,[status(thm)],[c_3349,c_30]) ).
% 7.43/1.49  
% 7.43/1.49  cnf(contradiction,plain,
% 7.43/1.49      ( $false ),
% 7.43/1.49      inference(minisat,[status(thm)],[c_13969,c_3352]) ).
% 7.43/1.49  
% 7.43/1.49  
% 7.43/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.43/1.49  
% 7.43/1.49  ------                               Statistics
% 7.43/1.49  
% 7.43/1.49  ------ General
% 7.43/1.49  
% 7.43/1.49  abstr_ref_over_cycles:                  0
% 7.43/1.49  abstr_ref_under_cycles:                 0
% 7.43/1.49  gc_basic_clause_elim:                   0
% 7.43/1.49  forced_gc_time:                         0
% 7.43/1.49  parsing_time:                           0.01
% 7.43/1.49  unif_index_cands_time:                  0.
% 7.43/1.49  unif_index_add_time:                    0.
% 7.43/1.49  orderings_time:                         0.
% 7.43/1.49  out_proof_time:                         0.016
% 7.43/1.49  total_time:                             0.601
% 7.43/1.49  num_of_symbols:                         52
% 7.43/1.49  num_of_terms:                           21809
% 7.43/1.49  
% 7.43/1.49  ------ Preprocessing
% 7.43/1.49  
% 7.43/1.49  num_of_splits:                          0
% 7.43/1.49  num_of_split_atoms:                     0
% 7.43/1.49  num_of_reused_defs:                     0
% 7.43/1.49  num_eq_ax_congr_red:                    3
% 7.43/1.49  num_of_sem_filtered_clauses:            1
% 7.43/1.49  num_of_subtypes:                        0
% 7.43/1.49  monotx_restored_types:                  0
% 7.43/1.49  sat_num_of_epr_types:                   0
% 7.43/1.49  sat_num_of_non_cyclic_types:            0
% 7.43/1.49  sat_guarded_non_collapsed_types:        0
% 7.43/1.49  num_pure_diseq_elim:                    0
% 7.43/1.49  simp_replaced_by:                       0
% 7.43/1.49  res_preprocessed:                       198
% 7.43/1.49  prep_upred:                             0
% 7.43/1.49  prep_unflattend:                        12
% 7.43/1.49  smt_new_axioms:                         0
% 7.43/1.49  pred_elim_cands:                        5
% 7.43/1.49  pred_elim:                              1
% 7.43/1.49  pred_elim_cl:                           1
% 7.43/1.49  pred_elim_cycles:                       3
% 7.43/1.49  merged_defs:                            0
% 7.43/1.49  merged_defs_ncl:                        0
% 7.43/1.49  bin_hyper_res:                          0
% 7.43/1.49  prep_cycles:                            4
% 7.43/1.49  pred_elim_time:                         0.005
% 7.43/1.49  splitting_time:                         0.
% 7.43/1.49  sem_filter_time:                        0.
% 7.43/1.49  monotx_time:                            0.001
% 7.43/1.49  subtype_inf_time:                       0.
% 7.43/1.49  
% 7.43/1.49  ------ Problem properties
% 7.43/1.49  
% 7.43/1.49  clauses:                                41
% 7.43/1.49  conjectures:                            11
% 7.43/1.49  epr:                                    7
% 7.43/1.49  horn:                                   37
% 7.43/1.49  ground:                                 12
% 7.43/1.49  unary:                                  17
% 7.43/1.49  binary:                                 6
% 7.43/1.49  lits:                                   137
% 7.43/1.49  lits_eq:                                32
% 7.43/1.49  fd_pure:                                0
% 7.43/1.49  fd_pseudo:                              0
% 7.43/1.49  fd_cond:                                4
% 7.43/1.49  fd_pseudo_cond:                         0
% 7.43/1.49  ac_symbols:                             0
% 7.43/1.49  
% 7.43/1.49  ------ Propositional Solver
% 7.43/1.49  
% 7.43/1.49  prop_solver_calls:                      31
% 7.43/1.49  prop_fast_solver_calls:                 2081
% 7.43/1.49  smt_solver_calls:                       0
% 7.43/1.49  smt_fast_solver_calls:                  0
% 7.43/1.49  prop_num_of_clauses:                    7116
% 7.43/1.49  prop_preprocess_simplified:             13630
% 7.43/1.49  prop_fo_subsumed:                       166
% 7.43/1.49  prop_solver_time:                       0.
% 7.43/1.49  smt_solver_time:                        0.
% 7.43/1.49  smt_fast_solver_time:                   0.
% 7.43/1.49  prop_fast_solver_time:                  0.
% 7.43/1.49  prop_unsat_core_time:                   0.001
% 7.43/1.49  
% 7.43/1.49  ------ QBF
% 7.43/1.49  
% 7.43/1.49  qbf_q_res:                              0
% 7.43/1.49  qbf_num_tautologies:                    0
% 7.43/1.49  qbf_prep_cycles:                        0
% 7.43/1.49  
% 7.43/1.49  ------ BMC1
% 7.43/1.49  
% 7.43/1.49  bmc1_current_bound:                     -1
% 7.43/1.49  bmc1_last_solved_bound:                 -1
% 7.43/1.49  bmc1_unsat_core_size:                   -1
% 7.43/1.49  bmc1_unsat_core_parents_size:           -1
% 7.43/1.49  bmc1_merge_next_fun:                    0
% 7.43/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.43/1.49  
% 7.43/1.49  ------ Instantiation
% 7.43/1.49  
% 7.43/1.49  inst_num_of_clauses:                    1767
% 7.43/1.49  inst_num_in_passive:                    32
% 7.43/1.49  inst_num_in_active:                     1139
% 7.43/1.49  inst_num_in_unprocessed:                596
% 7.43/1.49  inst_num_of_loops:                      1250
% 7.43/1.49  inst_num_of_learning_restarts:          0
% 7.43/1.49  inst_num_moves_active_passive:          108
% 7.43/1.49  inst_lit_activity:                      0
% 7.43/1.49  inst_lit_activity_moves:                1
% 7.43/1.49  inst_num_tautologies:                   0
% 7.43/1.49  inst_num_prop_implied:                  0
% 7.43/1.49  inst_num_existing_simplified:           0
% 7.43/1.49  inst_num_eq_res_simplified:             0
% 7.43/1.49  inst_num_child_elim:                    0
% 7.43/1.49  inst_num_of_dismatching_blockings:      1029
% 7.43/1.49  inst_num_of_non_proper_insts:           1645
% 7.43/1.49  inst_num_of_duplicates:                 0
% 7.43/1.49  inst_inst_num_from_inst_to_res:         0
% 7.43/1.49  inst_dismatching_checking_time:         0.
% 7.43/1.49  
% 7.43/1.49  ------ Resolution
% 7.43/1.49  
% 7.43/1.49  res_num_of_clauses:                     0
% 7.43/1.49  res_num_in_passive:                     0
% 7.43/1.49  res_num_in_active:                      0
% 7.43/1.49  res_num_of_loops:                       202
% 7.43/1.49  res_forward_subset_subsumed:            110
% 7.43/1.49  res_backward_subset_subsumed:           0
% 7.43/1.49  res_forward_subsumed:                   0
% 7.43/1.49  res_backward_subsumed:                  0
% 7.43/1.49  res_forward_subsumption_resolution:     2
% 7.43/1.49  res_backward_subsumption_resolution:    0
% 7.43/1.49  res_clause_to_clause_subsumption:       1412
% 7.43/1.49  res_orphan_elimination:                 0
% 7.43/1.49  res_tautology_del:                      103
% 7.43/1.49  res_num_eq_res_simplified:              1
% 7.43/1.49  res_num_sel_changes:                    0
% 7.43/1.49  res_moves_from_active_to_pass:          0
% 7.43/1.49  
% 7.43/1.49  ------ Superposition
% 7.43/1.49  
% 7.43/1.49  sup_time_total:                         0.
% 7.43/1.49  sup_time_generating:                    0.
% 7.43/1.49  sup_time_sim_full:                      0.
% 7.43/1.49  sup_time_sim_immed:                     0.
% 7.43/1.49  
% 7.43/1.49  sup_num_of_clauses:                     564
% 7.43/1.50  sup_num_in_active:                      226
% 7.43/1.50  sup_num_in_passive:                     338
% 7.43/1.50  sup_num_of_loops:                       248
% 7.43/1.50  sup_fw_superposition:                   359
% 7.43/1.50  sup_bw_superposition:                   233
% 7.43/1.50  sup_immediate_simplified:               172
% 7.43/1.50  sup_given_eliminated:                   1
% 7.43/1.50  comparisons_done:                       0
% 7.43/1.50  comparisons_avoided:                    0
% 7.43/1.50  
% 7.43/1.50  ------ Simplifications
% 7.43/1.50  
% 7.43/1.50  
% 7.43/1.50  sim_fw_subset_subsumed:                 9
% 7.43/1.50  sim_bw_subset_subsumed:                 19
% 7.43/1.50  sim_fw_subsumed:                        6
% 7.43/1.50  sim_bw_subsumed:                        2
% 7.43/1.50  sim_fw_subsumption_res:                 0
% 7.43/1.50  sim_bw_subsumption_res:                 0
% 7.43/1.50  sim_tautology_del:                      2
% 7.43/1.50  sim_eq_tautology_del:                   15
% 7.43/1.50  sim_eq_res_simp:                        0
% 7.43/1.50  sim_fw_demodulated:                     22
% 7.43/1.50  sim_bw_demodulated:                     21
% 7.43/1.50  sim_light_normalised:                   143
% 7.43/1.50  sim_joinable_taut:                      0
% 7.43/1.50  sim_joinable_simp:                      0
% 7.43/1.50  sim_ac_normalised:                      0
% 7.43/1.50  sim_smt_subsumption:                    0
% 7.43/1.50  
%------------------------------------------------------------------------------
