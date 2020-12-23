%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:03 EST 2020

% Result     : Theorem 35.36s
% Output     : CNFRefutation 35.36s
% Verified   : 
% Statistics : Number of formulae       :  175 (1390 expanded)
%              Number of clauses        :  104 ( 404 expanded)
%              Number of leaves         :   19 ( 361 expanded)
%              Depth                    :   23
%              Number of atoms          :  708 (12004 expanded)
%              Number of equality atoms :  361 (4441 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f3,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f13,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
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

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1176,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2198,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1159,c_1176])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2199,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2198,c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1170,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2790,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1170])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1177,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2329,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1162,c_1177])).

cnf(c_2793,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2790,c_2329])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_657,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_686,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_658,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1282,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_1283,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_3022,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_39,c_25,c_686,c_1283])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1181,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3566,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3022,c_1181])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1302,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1564,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1302])).

cnf(c_1565,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_9336,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3566,c_38,c_40,c_1565])).

cnf(c_9337,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_9336])).

cnf(c_9342,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2199,c_9337])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1166,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3419,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1166])).

cnf(c_3611,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3419,c_38])).

cnf(c_3612,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3611])).

cnf(c_3619,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_3612])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_386,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_386,c_18])).

cnf(c_1155,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1417,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1926,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1155,c_34,c_32,c_31,c_29,c_394,c_1417])).

cnf(c_3620,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3619,c_1926])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3825,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3620,c_35])).

cnf(c_9344,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9342,c_3825])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1936,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1937,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_0,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4316,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4317,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4316])).

cnf(c_9787,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9344,c_35,c_37,c_1937,c_4317])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1179,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4015,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3825,c_1179])).

cnf(c_2197,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1162,c_1176])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_398,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_399,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_483,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_399])).

cnf(c_1154,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_1610,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1154])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1933,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1610,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_2200,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2197,c_1933])).

cnf(c_4016,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4015,c_2199,c_2200,c_3022])).

cnf(c_4017,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4016])).

cnf(c_4583,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4017,c_35,c_37,c_38,c_40,c_1565,c_1937])).

cnf(c_9792,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_9787,c_4583])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1164,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2692,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1933,c_1164])).

cnf(c_3108,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_38,c_39,c_40,c_25,c_686,c_1283])).

cnf(c_9793,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_9787,c_3108])).

cnf(c_9794,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_9792,c_9793])).

cnf(c_107664,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9794,c_1179])).

cnf(c_2791,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1159,c_1170])).

cnf(c_2330,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1159,c_1177])).

cnf(c_2792,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2791,c_2330])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1254,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_1255,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_2916,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2792,c_36,c_24,c_686,c_1255])).

cnf(c_107665,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_107664,c_2199,c_2200,c_2916])).

cnf(c_107666,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_107665])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_107666,c_1937,c_1565,c_23,c_42,c_40,c_38,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n016.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:14:19 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 35.36/4.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.36/4.98  
% 35.36/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.36/4.98  
% 35.36/4.98  ------  iProver source info
% 35.36/4.98  
% 35.36/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.36/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.36/4.98  git: non_committed_changes: false
% 35.36/4.98  git: last_make_outside_of_git: false
% 35.36/4.98  
% 35.36/4.98  ------ 
% 35.36/4.98  
% 35.36/4.98  ------ Input Options
% 35.36/4.98  
% 35.36/4.98  --out_options                           all
% 35.36/4.98  --tptp_safe_out                         true
% 35.36/4.98  --problem_path                          ""
% 35.36/4.98  --include_path                          ""
% 35.36/4.98  --clausifier                            res/vclausify_rel
% 35.36/4.98  --clausifier_options                    ""
% 35.36/4.98  --stdin                                 false
% 35.36/4.98  --stats_out                             all
% 35.36/4.98  
% 35.36/4.98  ------ General Options
% 35.36/4.98  
% 35.36/4.98  --fof                                   false
% 35.36/4.98  --time_out_real                         305.
% 35.36/4.98  --time_out_virtual                      -1.
% 35.36/4.98  --symbol_type_check                     false
% 35.36/4.98  --clausify_out                          false
% 35.36/4.98  --sig_cnt_out                           false
% 35.36/4.98  --trig_cnt_out                          false
% 35.36/4.98  --trig_cnt_out_tolerance                1.
% 35.36/4.98  --trig_cnt_out_sk_spl                   false
% 35.36/4.98  --abstr_cl_out                          false
% 35.36/4.98  
% 35.36/4.98  ------ Global Options
% 35.36/4.98  
% 35.36/4.98  --schedule                              default
% 35.36/4.98  --add_important_lit                     false
% 35.36/4.98  --prop_solver_per_cl                    1000
% 35.36/4.98  --min_unsat_core                        false
% 35.36/4.98  --soft_assumptions                      false
% 35.36/4.98  --soft_lemma_size                       3
% 35.36/4.98  --prop_impl_unit_size                   0
% 35.36/4.98  --prop_impl_unit                        []
% 35.36/4.98  --share_sel_clauses                     true
% 35.36/4.98  --reset_solvers                         false
% 35.36/4.98  --bc_imp_inh                            [conj_cone]
% 35.36/4.98  --conj_cone_tolerance                   3.
% 35.36/4.98  --extra_neg_conj                        none
% 35.36/4.98  --large_theory_mode                     true
% 35.36/4.98  --prolific_symb_bound                   200
% 35.36/4.98  --lt_threshold                          2000
% 35.36/4.98  --clause_weak_htbl                      true
% 35.36/4.98  --gc_record_bc_elim                     false
% 35.36/4.98  
% 35.36/4.98  ------ Preprocessing Options
% 35.36/4.98  
% 35.36/4.98  --preprocessing_flag                    true
% 35.36/4.98  --time_out_prep_mult                    0.1
% 35.36/4.98  --splitting_mode                        input
% 35.36/4.98  --splitting_grd                         true
% 35.36/4.98  --splitting_cvd                         false
% 35.36/4.98  --splitting_cvd_svl                     false
% 35.36/4.98  --splitting_nvd                         32
% 35.36/4.98  --sub_typing                            true
% 35.36/4.98  --prep_gs_sim                           true
% 35.36/4.98  --prep_unflatten                        true
% 35.36/4.98  --prep_res_sim                          true
% 35.36/4.98  --prep_upred                            true
% 35.36/4.98  --prep_sem_filter                       exhaustive
% 35.36/4.98  --prep_sem_filter_out                   false
% 35.36/4.98  --pred_elim                             true
% 35.36/4.98  --res_sim_input                         true
% 35.36/4.98  --eq_ax_congr_red                       true
% 35.36/4.98  --pure_diseq_elim                       true
% 35.36/4.98  --brand_transform                       false
% 35.36/4.98  --non_eq_to_eq                          false
% 35.36/4.98  --prep_def_merge                        true
% 35.36/4.98  --prep_def_merge_prop_impl              false
% 35.36/4.98  --prep_def_merge_mbd                    true
% 35.36/4.98  --prep_def_merge_tr_red                 false
% 35.36/4.98  --prep_def_merge_tr_cl                  false
% 35.36/4.98  --smt_preprocessing                     true
% 35.36/4.98  --smt_ac_axioms                         fast
% 35.36/4.98  --preprocessed_out                      false
% 35.36/4.98  --preprocessed_stats                    false
% 35.36/4.98  
% 35.36/4.98  ------ Abstraction refinement Options
% 35.36/4.98  
% 35.36/4.98  --abstr_ref                             []
% 35.36/4.98  --abstr_ref_prep                        false
% 35.36/4.98  --abstr_ref_until_sat                   false
% 35.36/4.98  --abstr_ref_sig_restrict                funpre
% 35.36/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.36/4.98  --abstr_ref_under                       []
% 35.36/4.98  
% 35.36/4.98  ------ SAT Options
% 35.36/4.98  
% 35.36/4.98  --sat_mode                              false
% 35.36/4.98  --sat_fm_restart_options                ""
% 35.36/4.98  --sat_gr_def                            false
% 35.36/4.98  --sat_epr_types                         true
% 35.36/4.98  --sat_non_cyclic_types                  false
% 35.36/4.98  --sat_finite_models                     false
% 35.36/4.98  --sat_fm_lemmas                         false
% 35.36/4.98  --sat_fm_prep                           false
% 35.36/4.98  --sat_fm_uc_incr                        true
% 35.36/4.98  --sat_out_model                         small
% 35.36/4.98  --sat_out_clauses                       false
% 35.36/4.98  
% 35.36/4.98  ------ QBF Options
% 35.36/4.98  
% 35.36/4.98  --qbf_mode                              false
% 35.36/4.98  --qbf_elim_univ                         false
% 35.36/4.98  --qbf_dom_inst                          none
% 35.36/4.98  --qbf_dom_pre_inst                      false
% 35.36/4.98  --qbf_sk_in                             false
% 35.36/4.98  --qbf_pred_elim                         true
% 35.36/4.98  --qbf_split                             512
% 35.36/4.98  
% 35.36/4.98  ------ BMC1 Options
% 35.36/4.98  
% 35.36/4.98  --bmc1_incremental                      false
% 35.36/4.98  --bmc1_axioms                           reachable_all
% 35.36/4.98  --bmc1_min_bound                        0
% 35.36/4.98  --bmc1_max_bound                        -1
% 35.36/4.98  --bmc1_max_bound_default                -1
% 35.36/4.98  --bmc1_symbol_reachability              true
% 35.36/4.98  --bmc1_property_lemmas                  false
% 35.36/4.98  --bmc1_k_induction                      false
% 35.36/4.98  --bmc1_non_equiv_states                 false
% 35.36/4.98  --bmc1_deadlock                         false
% 35.36/4.98  --bmc1_ucm                              false
% 35.36/4.98  --bmc1_add_unsat_core                   none
% 35.36/4.98  --bmc1_unsat_core_children              false
% 35.36/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.36/4.98  --bmc1_out_stat                         full
% 35.36/4.98  --bmc1_ground_init                      false
% 35.36/4.98  --bmc1_pre_inst_next_state              false
% 35.36/4.98  --bmc1_pre_inst_state                   false
% 35.36/4.98  --bmc1_pre_inst_reach_state             false
% 35.36/4.98  --bmc1_out_unsat_core                   false
% 35.36/4.98  --bmc1_aig_witness_out                  false
% 35.36/4.98  --bmc1_verbose                          false
% 35.36/4.98  --bmc1_dump_clauses_tptp                false
% 35.36/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.36/4.98  --bmc1_dump_file                        -
% 35.36/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.36/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.36/4.98  --bmc1_ucm_extend_mode                  1
% 35.36/4.98  --bmc1_ucm_init_mode                    2
% 35.36/4.98  --bmc1_ucm_cone_mode                    none
% 35.36/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.36/4.98  --bmc1_ucm_relax_model                  4
% 35.36/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.36/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.36/4.98  --bmc1_ucm_layered_model                none
% 35.36/4.98  --bmc1_ucm_max_lemma_size               10
% 35.36/4.98  
% 35.36/4.98  ------ AIG Options
% 35.36/4.98  
% 35.36/4.98  --aig_mode                              false
% 35.36/4.98  
% 35.36/4.98  ------ Instantiation Options
% 35.36/4.98  
% 35.36/4.98  --instantiation_flag                    true
% 35.36/4.98  --inst_sos_flag                         true
% 35.36/4.98  --inst_sos_phase                        true
% 35.36/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.36/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.36/4.98  --inst_lit_sel_side                     num_symb
% 35.36/4.98  --inst_solver_per_active                1400
% 35.36/4.98  --inst_solver_calls_frac                1.
% 35.36/4.98  --inst_passive_queue_type               priority_queues
% 35.36/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.36/4.98  --inst_passive_queues_freq              [25;2]
% 35.36/4.98  --inst_dismatching                      true
% 35.36/4.98  --inst_eager_unprocessed_to_passive     true
% 35.36/4.98  --inst_prop_sim_given                   true
% 35.36/4.98  --inst_prop_sim_new                     false
% 35.36/4.98  --inst_subs_new                         false
% 35.36/4.98  --inst_eq_res_simp                      false
% 35.36/4.98  --inst_subs_given                       false
% 35.36/4.98  --inst_orphan_elimination               true
% 35.36/4.98  --inst_learning_loop_flag               true
% 35.36/4.98  --inst_learning_start                   3000
% 35.36/4.98  --inst_learning_factor                  2
% 35.36/4.98  --inst_start_prop_sim_after_learn       3
% 35.36/4.98  --inst_sel_renew                        solver
% 35.36/4.98  --inst_lit_activity_flag                true
% 35.36/4.98  --inst_restr_to_given                   false
% 35.36/4.98  --inst_activity_threshold               500
% 35.36/4.98  --inst_out_proof                        true
% 35.36/4.98  
% 35.36/4.98  ------ Resolution Options
% 35.36/4.98  
% 35.36/4.98  --resolution_flag                       true
% 35.36/4.98  --res_lit_sel                           adaptive
% 35.36/4.98  --res_lit_sel_side                      none
% 35.36/4.98  --res_ordering                          kbo
% 35.36/4.98  --res_to_prop_solver                    active
% 35.36/4.98  --res_prop_simpl_new                    false
% 35.36/4.98  --res_prop_simpl_given                  true
% 35.36/4.98  --res_passive_queue_type                priority_queues
% 35.36/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.36/4.98  --res_passive_queues_freq               [15;5]
% 35.36/4.98  --res_forward_subs                      full
% 35.36/4.98  --res_backward_subs                     full
% 35.36/4.98  --res_forward_subs_resolution           true
% 35.36/4.98  --res_backward_subs_resolution          true
% 35.36/4.98  --res_orphan_elimination                true
% 35.36/4.98  --res_time_limit                        2.
% 35.36/4.98  --res_out_proof                         true
% 35.36/4.98  
% 35.36/4.98  ------ Superposition Options
% 35.36/4.98  
% 35.36/4.98  --superposition_flag                    true
% 35.36/4.98  --sup_passive_queue_type                priority_queues
% 35.36/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.36/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.36/4.98  --demod_completeness_check              fast
% 35.36/4.98  --demod_use_ground                      true
% 35.36/4.98  --sup_to_prop_solver                    passive
% 35.36/4.98  --sup_prop_simpl_new                    true
% 35.36/4.98  --sup_prop_simpl_given                  true
% 35.36/4.98  --sup_fun_splitting                     true
% 35.36/4.98  --sup_smt_interval                      50000
% 35.36/4.98  
% 35.36/4.98  ------ Superposition Simplification Setup
% 35.36/4.98  
% 35.36/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.36/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.36/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.36/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.36/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.36/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.36/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.36/4.98  --sup_immed_triv                        [TrivRules]
% 35.36/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.36/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.36/4.98  --sup_immed_bw_main                     []
% 35.36/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.36/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.36/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.36/4.98  --sup_input_bw                          []
% 35.36/4.98  
% 35.36/4.98  ------ Combination Options
% 35.36/4.98  
% 35.36/4.98  --comb_res_mult                         3
% 35.36/4.98  --comb_sup_mult                         2
% 35.36/4.98  --comb_inst_mult                        10
% 35.36/4.98  
% 35.36/4.98  ------ Debug Options
% 35.36/4.98  
% 35.36/4.98  --dbg_backtrace                         false
% 35.36/4.98  --dbg_dump_prop_clauses                 false
% 35.36/4.98  --dbg_dump_prop_clauses_file            -
% 35.36/4.98  --dbg_out_stat                          false
% 35.36/4.98  ------ Parsing...
% 35.36/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.36/4.98  
% 35.36/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.36/4.98  
% 35.36/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.36/4.98  
% 35.36/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.36/4.98  ------ Proving...
% 35.36/4.98  ------ Problem Properties 
% 35.36/4.98  
% 35.36/4.98  
% 35.36/4.98  clauses                                 34
% 35.36/4.98  conjectures                             11
% 35.36/4.98  EPR                                     7
% 35.36/4.98  Horn                                    28
% 35.36/4.98  unary                                   14
% 35.36/4.98  binary                                  4
% 35.36/4.98  lits                                    110
% 35.36/4.98  lits eq                                 32
% 35.36/4.98  fd_pure                                 0
% 35.36/4.98  fd_pseudo                               0
% 35.36/4.98  fd_cond                                 5
% 35.36/4.98  fd_pseudo_cond                          1
% 35.36/4.98  AC symbols                              0
% 35.36/4.98  
% 35.36/4.98  ------ Schedule dynamic 5 is on 
% 35.36/4.98  
% 35.36/4.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.36/4.98  
% 35.36/4.98  
% 35.36/4.98  ------ 
% 35.36/4.98  Current options:
% 35.36/4.98  ------ 
% 35.36/4.98  
% 35.36/4.98  ------ Input Options
% 35.36/4.98  
% 35.36/4.98  --out_options                           all
% 35.36/4.98  --tptp_safe_out                         true
% 35.36/4.98  --problem_path                          ""
% 35.36/4.98  --include_path                          ""
% 35.36/4.98  --clausifier                            res/vclausify_rel
% 35.36/4.98  --clausifier_options                    ""
% 35.36/4.98  --stdin                                 false
% 35.36/4.98  --stats_out                             all
% 35.36/4.98  
% 35.36/4.98  ------ General Options
% 35.36/4.98  
% 35.36/4.98  --fof                                   false
% 35.36/4.98  --time_out_real                         305.
% 35.36/4.98  --time_out_virtual                      -1.
% 35.36/4.98  --symbol_type_check                     false
% 35.36/4.98  --clausify_out                          false
% 35.36/4.98  --sig_cnt_out                           false
% 35.36/4.98  --trig_cnt_out                          false
% 35.36/4.98  --trig_cnt_out_tolerance                1.
% 35.36/4.98  --trig_cnt_out_sk_spl                   false
% 35.36/4.98  --abstr_cl_out                          false
% 35.36/4.98  
% 35.36/4.98  ------ Global Options
% 35.36/4.98  
% 35.36/4.98  --schedule                              default
% 35.36/4.98  --add_important_lit                     false
% 35.36/4.98  --prop_solver_per_cl                    1000
% 35.36/4.98  --min_unsat_core                        false
% 35.36/4.98  --soft_assumptions                      false
% 35.36/4.98  --soft_lemma_size                       3
% 35.36/4.98  --prop_impl_unit_size                   0
% 35.36/4.98  --prop_impl_unit                        []
% 35.36/4.98  --share_sel_clauses                     true
% 35.36/4.98  --reset_solvers                         false
% 35.36/4.98  --bc_imp_inh                            [conj_cone]
% 35.36/4.98  --conj_cone_tolerance                   3.
% 35.36/4.98  --extra_neg_conj                        none
% 35.36/4.98  --large_theory_mode                     true
% 35.36/4.98  --prolific_symb_bound                   200
% 35.36/4.98  --lt_threshold                          2000
% 35.36/4.98  --clause_weak_htbl                      true
% 35.36/4.98  --gc_record_bc_elim                     false
% 35.36/4.98  
% 35.36/4.98  ------ Preprocessing Options
% 35.36/4.98  
% 35.36/4.98  --preprocessing_flag                    true
% 35.36/4.98  --time_out_prep_mult                    0.1
% 35.36/4.98  --splitting_mode                        input
% 35.36/4.98  --splitting_grd                         true
% 35.36/4.98  --splitting_cvd                         false
% 35.36/4.98  --splitting_cvd_svl                     false
% 35.36/4.98  --splitting_nvd                         32
% 35.36/4.98  --sub_typing                            true
% 35.36/4.98  --prep_gs_sim                           true
% 35.36/4.98  --prep_unflatten                        true
% 35.36/4.98  --prep_res_sim                          true
% 35.36/4.98  --prep_upred                            true
% 35.36/4.98  --prep_sem_filter                       exhaustive
% 35.36/4.98  --prep_sem_filter_out                   false
% 35.36/4.98  --pred_elim                             true
% 35.36/4.98  --res_sim_input                         true
% 35.36/4.98  --eq_ax_congr_red                       true
% 35.36/4.98  --pure_diseq_elim                       true
% 35.36/4.98  --brand_transform                       false
% 35.36/4.98  --non_eq_to_eq                          false
% 35.36/4.98  --prep_def_merge                        true
% 35.36/4.98  --prep_def_merge_prop_impl              false
% 35.36/4.98  --prep_def_merge_mbd                    true
% 35.36/4.98  --prep_def_merge_tr_red                 false
% 35.36/4.98  --prep_def_merge_tr_cl                  false
% 35.36/4.98  --smt_preprocessing                     true
% 35.36/4.98  --smt_ac_axioms                         fast
% 35.36/4.98  --preprocessed_out                      false
% 35.36/4.98  --preprocessed_stats                    false
% 35.36/4.98  
% 35.36/4.98  ------ Abstraction refinement Options
% 35.36/4.98  
% 35.36/4.98  --abstr_ref                             []
% 35.36/4.98  --abstr_ref_prep                        false
% 35.36/4.98  --abstr_ref_until_sat                   false
% 35.36/4.98  --abstr_ref_sig_restrict                funpre
% 35.36/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.36/4.98  --abstr_ref_under                       []
% 35.36/4.98  
% 35.36/4.98  ------ SAT Options
% 35.36/4.98  
% 35.36/4.98  --sat_mode                              false
% 35.36/4.98  --sat_fm_restart_options                ""
% 35.36/4.98  --sat_gr_def                            false
% 35.36/4.98  --sat_epr_types                         true
% 35.36/4.98  --sat_non_cyclic_types                  false
% 35.36/4.98  --sat_finite_models                     false
% 35.36/4.98  --sat_fm_lemmas                         false
% 35.36/4.98  --sat_fm_prep                           false
% 35.36/4.98  --sat_fm_uc_incr                        true
% 35.36/4.98  --sat_out_model                         small
% 35.36/4.98  --sat_out_clauses                       false
% 35.36/4.98  
% 35.36/4.98  ------ QBF Options
% 35.36/4.98  
% 35.36/4.98  --qbf_mode                              false
% 35.36/4.98  --qbf_elim_univ                         false
% 35.36/4.98  --qbf_dom_inst                          none
% 35.36/4.98  --qbf_dom_pre_inst                      false
% 35.36/4.98  --qbf_sk_in                             false
% 35.36/4.98  --qbf_pred_elim                         true
% 35.36/4.98  --qbf_split                             512
% 35.36/4.98  
% 35.36/4.98  ------ BMC1 Options
% 35.36/4.98  
% 35.36/4.98  --bmc1_incremental                      false
% 35.36/4.98  --bmc1_axioms                           reachable_all
% 35.36/4.98  --bmc1_min_bound                        0
% 35.36/4.98  --bmc1_max_bound                        -1
% 35.36/4.98  --bmc1_max_bound_default                -1
% 35.36/4.98  --bmc1_symbol_reachability              true
% 35.36/4.98  --bmc1_property_lemmas                  false
% 35.36/4.98  --bmc1_k_induction                      false
% 35.36/4.98  --bmc1_non_equiv_states                 false
% 35.36/4.98  --bmc1_deadlock                         false
% 35.36/4.98  --bmc1_ucm                              false
% 35.36/4.98  --bmc1_add_unsat_core                   none
% 35.36/4.98  --bmc1_unsat_core_children              false
% 35.36/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.36/4.98  --bmc1_out_stat                         full
% 35.36/4.98  --bmc1_ground_init                      false
% 35.36/4.98  --bmc1_pre_inst_next_state              false
% 35.36/4.98  --bmc1_pre_inst_state                   false
% 35.36/4.98  --bmc1_pre_inst_reach_state             false
% 35.36/4.98  --bmc1_out_unsat_core                   false
% 35.36/4.98  --bmc1_aig_witness_out                  false
% 35.36/4.98  --bmc1_verbose                          false
% 35.36/4.98  --bmc1_dump_clauses_tptp                false
% 35.36/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.36/4.98  --bmc1_dump_file                        -
% 35.36/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.36/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.36/4.98  --bmc1_ucm_extend_mode                  1
% 35.36/4.98  --bmc1_ucm_init_mode                    2
% 35.36/4.98  --bmc1_ucm_cone_mode                    none
% 35.36/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.36/4.98  --bmc1_ucm_relax_model                  4
% 35.36/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.36/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.36/4.98  --bmc1_ucm_layered_model                none
% 35.36/4.98  --bmc1_ucm_max_lemma_size               10
% 35.36/4.98  
% 35.36/4.98  ------ AIG Options
% 35.36/4.98  
% 35.36/4.98  --aig_mode                              false
% 35.36/4.98  
% 35.36/4.98  ------ Instantiation Options
% 35.36/4.98  
% 35.36/4.98  --instantiation_flag                    true
% 35.36/4.98  --inst_sos_flag                         true
% 35.36/4.98  --inst_sos_phase                        true
% 35.36/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.36/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.36/4.98  --inst_lit_sel_side                     none
% 35.36/4.98  --inst_solver_per_active                1400
% 35.36/4.98  --inst_solver_calls_frac                1.
% 35.36/4.98  --inst_passive_queue_type               priority_queues
% 35.36/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.36/4.98  --inst_passive_queues_freq              [25;2]
% 35.36/4.98  --inst_dismatching                      true
% 35.36/4.98  --inst_eager_unprocessed_to_passive     true
% 35.36/4.98  --inst_prop_sim_given                   true
% 35.36/4.98  --inst_prop_sim_new                     false
% 35.36/4.98  --inst_subs_new                         false
% 35.36/4.98  --inst_eq_res_simp                      false
% 35.36/4.98  --inst_subs_given                       false
% 35.36/4.98  --inst_orphan_elimination               true
% 35.36/4.98  --inst_learning_loop_flag               true
% 35.36/4.98  --inst_learning_start                   3000
% 35.36/4.98  --inst_learning_factor                  2
% 35.36/4.98  --inst_start_prop_sim_after_learn       3
% 35.36/4.98  --inst_sel_renew                        solver
% 35.36/4.98  --inst_lit_activity_flag                true
% 35.36/4.98  --inst_restr_to_given                   false
% 35.36/4.98  --inst_activity_threshold               500
% 35.36/4.98  --inst_out_proof                        true
% 35.36/4.98  
% 35.36/4.98  ------ Resolution Options
% 35.36/4.98  
% 35.36/4.98  --resolution_flag                       false
% 35.36/4.98  --res_lit_sel                           adaptive
% 35.36/4.98  --res_lit_sel_side                      none
% 35.36/4.98  --res_ordering                          kbo
% 35.36/4.98  --res_to_prop_solver                    active
% 35.36/4.98  --res_prop_simpl_new                    false
% 35.36/4.98  --res_prop_simpl_given                  true
% 35.36/4.98  --res_passive_queue_type                priority_queues
% 35.36/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.36/4.98  --res_passive_queues_freq               [15;5]
% 35.36/4.98  --res_forward_subs                      full
% 35.36/4.98  --res_backward_subs                     full
% 35.36/4.98  --res_forward_subs_resolution           true
% 35.36/4.98  --res_backward_subs_resolution          true
% 35.36/4.98  --res_orphan_elimination                true
% 35.36/4.98  --res_time_limit                        2.
% 35.36/4.98  --res_out_proof                         true
% 35.36/4.98  
% 35.36/4.98  ------ Superposition Options
% 35.36/4.98  
% 35.36/4.98  --superposition_flag                    true
% 35.36/4.98  --sup_passive_queue_type                priority_queues
% 35.36/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.36/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.36/4.98  --demod_completeness_check              fast
% 35.36/4.98  --demod_use_ground                      true
% 35.36/4.98  --sup_to_prop_solver                    passive
% 35.36/4.98  --sup_prop_simpl_new                    true
% 35.36/4.98  --sup_prop_simpl_given                  true
% 35.36/4.98  --sup_fun_splitting                     true
% 35.36/4.98  --sup_smt_interval                      50000
% 35.36/4.98  
% 35.36/4.98  ------ Superposition Simplification Setup
% 35.36/4.98  
% 35.36/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.36/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.36/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.36/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.36/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.36/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.36/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.36/4.98  --sup_immed_triv                        [TrivRules]
% 35.36/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.36/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.36/4.98  --sup_immed_bw_main                     []
% 35.36/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.36/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.36/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.36/4.98  --sup_input_bw                          []
% 35.36/4.98  
% 35.36/4.98  ------ Combination Options
% 35.36/4.98  
% 35.36/4.98  --comb_res_mult                         3
% 35.36/4.98  --comb_sup_mult                         2
% 35.36/4.98  --comb_inst_mult                        10
% 35.36/4.98  
% 35.36/4.98  ------ Debug Options
% 35.36/4.98  
% 35.36/4.98  --dbg_backtrace                         false
% 35.36/4.98  --dbg_dump_prop_clauses                 false
% 35.36/4.98  --dbg_dump_prop_clauses_file            -
% 35.36/4.98  --dbg_out_stat                          false
% 35.36/4.98  
% 35.36/4.98  
% 35.36/4.98  
% 35.36/4.98  
% 35.36/4.98  ------ Proving...
% 35.36/4.98  
% 35.36/4.98  
% 35.36/4.98  % SZS status Theorem for theBenchmark.p
% 35.36/4.98  
% 35.36/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.36/4.98  
% 35.36/4.98  fof(f15,conjecture,(
% 35.36/4.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f16,negated_conjecture,(
% 35.36/4.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.36/4.98    inference(negated_conjecture,[],[f15])).
% 35.36/4.98  
% 35.36/4.98  fof(f37,plain,(
% 35.36/4.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 35.36/4.98    inference(ennf_transformation,[],[f16])).
% 35.36/4.98  
% 35.36/4.98  fof(f38,plain,(
% 35.36/4.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 35.36/4.98    inference(flattening,[],[f37])).
% 35.36/4.98  
% 35.36/4.98  fof(f42,plain,(
% 35.36/4.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 35.36/4.98    introduced(choice_axiom,[])).
% 35.36/4.98  
% 35.36/4.98  fof(f41,plain,(
% 35.36/4.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 35.36/4.98    introduced(choice_axiom,[])).
% 35.36/4.98  
% 35.36/4.98  fof(f43,plain,(
% 35.36/4.98    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 35.36/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 35.36/4.98  
% 35.36/4.98  fof(f70,plain,(
% 35.36/4.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f6,axiom,(
% 35.36/4.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f24,plain,(
% 35.36/4.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.36/4.98    inference(ennf_transformation,[],[f6])).
% 35.36/4.98  
% 35.36/4.98  fof(f51,plain,(
% 35.36/4.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.36/4.98    inference(cnf_transformation,[],[f24])).
% 35.36/4.98  
% 35.36/4.98  fof(f74,plain,(
% 35.36/4.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f73,plain,(
% 35.36/4.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f8,axiom,(
% 35.36/4.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f27,plain,(
% 35.36/4.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.36/4.98    inference(ennf_transformation,[],[f8])).
% 35.36/4.98  
% 35.36/4.98  fof(f28,plain,(
% 35.36/4.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.36/4.98    inference(flattening,[],[f27])).
% 35.36/4.98  
% 35.36/4.98  fof(f40,plain,(
% 35.36/4.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.36/4.98    inference(nnf_transformation,[],[f28])).
% 35.36/4.98  
% 35.36/4.98  fof(f54,plain,(
% 35.36/4.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.36/4.98    inference(cnf_transformation,[],[f40])).
% 35.36/4.98  
% 35.36/4.98  fof(f5,axiom,(
% 35.36/4.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f23,plain,(
% 35.36/4.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.36/4.98    inference(ennf_transformation,[],[f5])).
% 35.36/4.98  
% 35.36/4.98  fof(f50,plain,(
% 35.36/4.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.36/4.98    inference(cnf_transformation,[],[f23])).
% 35.36/4.98  
% 35.36/4.98  fof(f72,plain,(
% 35.36/4.98    v1_funct_2(sK3,sK1,sK0)),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f77,plain,(
% 35.36/4.98    k1_xboole_0 != sK0),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f2,axiom,(
% 35.36/4.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f18,plain,(
% 35.36/4.98    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.36/4.98    inference(ennf_transformation,[],[f2])).
% 35.36/4.98  
% 35.36/4.98  fof(f19,plain,(
% 35.36/4.98    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.36/4.98    inference(flattening,[],[f18])).
% 35.36/4.98  
% 35.36/4.98  fof(f47,plain,(
% 35.36/4.98    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.36/4.98    inference(cnf_transformation,[],[f19])).
% 35.36/4.98  
% 35.36/4.98  fof(f71,plain,(
% 35.36/4.98    v1_funct_1(sK3)),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f4,axiom,(
% 35.36/4.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f22,plain,(
% 35.36/4.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.36/4.98    inference(ennf_transformation,[],[f4])).
% 35.36/4.98  
% 35.36/4.98  fof(f49,plain,(
% 35.36/4.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.36/4.98    inference(cnf_transformation,[],[f22])).
% 35.36/4.98  
% 35.36/4.98  fof(f11,axiom,(
% 35.36/4.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f31,plain,(
% 35.36/4.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.36/4.98    inference(ennf_transformation,[],[f11])).
% 35.36/4.98  
% 35.36/4.98  fof(f32,plain,(
% 35.36/4.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.36/4.98    inference(flattening,[],[f31])).
% 35.36/4.98  
% 35.36/4.98  fof(f63,plain,(
% 35.36/4.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.36/4.98    inference(cnf_transformation,[],[f32])).
% 35.36/4.98  
% 35.36/4.98  fof(f7,axiom,(
% 35.36/4.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f25,plain,(
% 35.36/4.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 35.36/4.98    inference(ennf_transformation,[],[f7])).
% 35.36/4.98  
% 35.36/4.98  fof(f26,plain,(
% 35.36/4.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.36/4.98    inference(flattening,[],[f25])).
% 35.36/4.98  
% 35.36/4.98  fof(f39,plain,(
% 35.36/4.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.36/4.98    inference(nnf_transformation,[],[f26])).
% 35.36/4.98  
% 35.36/4.98  fof(f52,plain,(
% 35.36/4.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.36/4.98    inference(cnf_transformation,[],[f39])).
% 35.36/4.98  
% 35.36/4.98  fof(f75,plain,(
% 35.36/4.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f10,axiom,(
% 35.36/4.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f17,plain,(
% 35.36/4.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 35.36/4.98    inference(pure_predicate_removal,[],[f10])).
% 35.36/4.98  
% 35.36/4.98  fof(f62,plain,(
% 35.36/4.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.36/4.98    inference(cnf_transformation,[],[f17])).
% 35.36/4.98  
% 35.36/4.98  fof(f68,plain,(
% 35.36/4.98    v1_funct_1(sK2)),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f9,axiom,(
% 35.36/4.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f29,plain,(
% 35.36/4.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.36/4.98    inference(ennf_transformation,[],[f9])).
% 35.36/4.98  
% 35.36/4.98  fof(f30,plain,(
% 35.36/4.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.36/4.98    inference(flattening,[],[f29])).
% 35.36/4.98  
% 35.36/4.98  fof(f61,plain,(
% 35.36/4.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.36/4.98    inference(cnf_transformation,[],[f30])).
% 35.36/4.98  
% 35.36/4.98  fof(f1,axiom,(
% 35.36/4.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f45,plain,(
% 35.36/4.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 35.36/4.98    inference(cnf_transformation,[],[f1])).
% 35.36/4.98  
% 35.36/4.98  fof(f12,axiom,(
% 35.36/4.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f64,plain,(
% 35.36/4.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 35.36/4.98    inference(cnf_transformation,[],[f12])).
% 35.36/4.98  
% 35.36/4.98  fof(f80,plain,(
% 35.36/4.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 35.36/4.98    inference(definition_unfolding,[],[f45,f64])).
% 35.36/4.98  
% 35.36/4.98  fof(f3,axiom,(
% 35.36/4.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f20,plain,(
% 35.36/4.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.36/4.98    inference(ennf_transformation,[],[f3])).
% 35.36/4.98  
% 35.36/4.98  fof(f21,plain,(
% 35.36/4.98    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.36/4.98    inference(flattening,[],[f20])).
% 35.36/4.98  
% 35.36/4.98  fof(f48,plain,(
% 35.36/4.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.36/4.98    inference(cnf_transformation,[],[f21])).
% 35.36/4.98  
% 35.36/4.98  fof(f82,plain,(
% 35.36/4.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.36/4.98    inference(definition_unfolding,[],[f48,f64])).
% 35.36/4.98  
% 35.36/4.98  fof(f13,axiom,(
% 35.36/4.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f33,plain,(
% 35.36/4.98    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 35.36/4.98    inference(ennf_transformation,[],[f13])).
% 35.36/4.98  
% 35.36/4.98  fof(f34,plain,(
% 35.36/4.98    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.36/4.98    inference(flattening,[],[f33])).
% 35.36/4.98  
% 35.36/4.98  fof(f65,plain,(
% 35.36/4.98    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.36/4.98    inference(cnf_transformation,[],[f34])).
% 35.36/4.98  
% 35.36/4.98  fof(f69,plain,(
% 35.36/4.98    v1_funct_2(sK2,sK0,sK1)),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f14,axiom,(
% 35.36/4.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 35.36/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.36/4.98  
% 35.36/4.98  fof(f35,plain,(
% 35.36/4.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 35.36/4.98    inference(ennf_transformation,[],[f14])).
% 35.36/4.98  
% 35.36/4.98  fof(f36,plain,(
% 35.36/4.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.36/4.98    inference(flattening,[],[f35])).
% 35.36/4.98  
% 35.36/4.98  fof(f66,plain,(
% 35.36/4.98    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.36/4.98    inference(cnf_transformation,[],[f36])).
% 35.36/4.98  
% 35.36/4.98  fof(f78,plain,(
% 35.36/4.98    k1_xboole_0 != sK1),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f79,plain,(
% 35.36/4.98    k2_funct_1(sK2) != sK3),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  fof(f76,plain,(
% 35.36/4.98    v2_funct_1(sK2)),
% 35.36/4.98    inference(cnf_transformation,[],[f43])).
% 35.36/4.98  
% 35.36/4.98  cnf(c_32,negated_conjecture,
% 35.36/4.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 35.36/4.98      inference(cnf_transformation,[],[f70]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1159,plain,
% 35.36/4.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_7,plain,
% 35.36/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 35.36/4.98      inference(cnf_transformation,[],[f51]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1176,plain,
% 35.36/4.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 35.36/4.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2198,plain,
% 35.36/4.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1159,c_1176]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_28,negated_conjecture,
% 35.36/4.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 35.36/4.98      inference(cnf_transformation,[],[f74]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2199,plain,
% 35.36/4.98      ( k2_relat_1(sK2) = sK1 ),
% 35.36/4.98      inference(light_normalisation,[status(thm)],[c_2198,c_28]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_29,negated_conjecture,
% 35.36/4.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 35.36/4.98      inference(cnf_transformation,[],[f73]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1162,plain,
% 35.36/4.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_15,plain,
% 35.36/4.98      ( ~ v1_funct_2(X0,X1,X2)
% 35.36/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | k1_relset_1(X1,X2,X0) = X1
% 35.36/4.98      | k1_xboole_0 = X2 ),
% 35.36/4.98      inference(cnf_transformation,[],[f54]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1170,plain,
% 35.36/4.98      ( k1_relset_1(X0,X1,X2) = X0
% 35.36/4.98      | k1_xboole_0 = X1
% 35.36/4.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.36/4.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2790,plain,
% 35.36/4.98      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 35.36/4.98      | sK0 = k1_xboole_0
% 35.36/4.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1162,c_1170]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_6,plain,
% 35.36/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 35.36/4.98      inference(cnf_transformation,[],[f50]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1177,plain,
% 35.36/4.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 35.36/4.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2329,plain,
% 35.36/4.98      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1162,c_1177]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2793,plain,
% 35.36/4.98      ( k1_relat_1(sK3) = sK1
% 35.36/4.98      | sK0 = k1_xboole_0
% 35.36/4.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 35.36/4.98      inference(demodulation,[status(thm)],[c_2790,c_2329]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_30,negated_conjecture,
% 35.36/4.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 35.36/4.98      inference(cnf_transformation,[],[f72]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_39,plain,
% 35.36/4.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_25,negated_conjecture,
% 35.36/4.98      ( k1_xboole_0 != sK0 ),
% 35.36/4.98      inference(cnf_transformation,[],[f77]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_657,plain,( X0 = X0 ),theory(equality) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_686,plain,
% 35.36/4.98      ( k1_xboole_0 = k1_xboole_0 ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_657]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_658,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1282,plain,
% 35.36/4.98      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_658]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1283,plain,
% 35.36/4.98      ( sK0 != k1_xboole_0
% 35.36/4.98      | k1_xboole_0 = sK0
% 35.36/4.98      | k1_xboole_0 != k1_xboole_0 ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_1282]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3022,plain,
% 35.36/4.98      ( k1_relat_1(sK3) = sK1 ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_2793,c_39,c_25,c_686,c_1283]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2,plain,
% 35.36/4.98      ( ~ v1_funct_1(X0)
% 35.36/4.98      | ~ v1_funct_1(X1)
% 35.36/4.98      | ~ v1_relat_1(X0)
% 35.36/4.98      | ~ v1_relat_1(X1)
% 35.36/4.98      | v2_funct_1(X1)
% 35.36/4.98      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 35.36/4.98      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 35.36/4.98      inference(cnf_transformation,[],[f47]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1181,plain,
% 35.36/4.98      ( k1_relat_1(X0) != k2_relat_1(X1)
% 35.36/4.98      | v1_funct_1(X1) != iProver_top
% 35.36/4.98      | v1_funct_1(X0) != iProver_top
% 35.36/4.98      | v1_relat_1(X1) != iProver_top
% 35.36/4.98      | v1_relat_1(X0) != iProver_top
% 35.36/4.98      | v2_funct_1(X0) = iProver_top
% 35.36/4.98      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3566,plain,
% 35.36/4.98      ( k2_relat_1(X0) != sK1
% 35.36/4.98      | v1_funct_1(X0) != iProver_top
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v1_relat_1(X0) != iProver_top
% 35.36/4.98      | v1_relat_1(sK3) != iProver_top
% 35.36/4.98      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) = iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_3022,c_1181]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_31,negated_conjecture,
% 35.36/4.98      ( v1_funct_1(sK3) ),
% 35.36/4.98      inference(cnf_transformation,[],[f71]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_38,plain,
% 35.36/4.98      ( v1_funct_1(sK3) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_40,plain,
% 35.36/4.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_5,plain,
% 35.36/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | v1_relat_1(X0) ),
% 35.36/4.98      inference(cnf_transformation,[],[f49]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1302,plain,
% 35.36/4.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.36/4.98      | v1_relat_1(sK3) ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_5]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1564,plain,
% 35.36/4.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.36/4.98      | v1_relat_1(sK3) ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_1302]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1565,plain,
% 35.36/4.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.36/4.98      | v1_relat_1(sK3) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9336,plain,
% 35.36/4.98      ( v1_relat_1(X0) != iProver_top
% 35.36/4.98      | k2_relat_1(X0) != sK1
% 35.36/4.98      | v1_funct_1(X0) != iProver_top
% 35.36/4.98      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) = iProver_top ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_3566,c_38,c_40,c_1565]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9337,plain,
% 35.36/4.98      ( k2_relat_1(X0) != sK1
% 35.36/4.98      | v1_funct_1(X0) != iProver_top
% 35.36/4.98      | v1_relat_1(X0) != iProver_top
% 35.36/4.98      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) = iProver_top ),
% 35.36/4.98      inference(renaming,[status(thm)],[c_9336]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9342,plain,
% 35.36/4.98      ( v1_funct_1(sK2) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) != iProver_top
% 35.36/4.98      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) = iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_2199,c_9337]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_19,plain,
% 35.36/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.36/4.98      | ~ v1_funct_1(X0)
% 35.36/4.98      | ~ v1_funct_1(X3)
% 35.36/4.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 35.36/4.98      inference(cnf_transformation,[],[f63]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1166,plain,
% 35.36/4.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 35.36/4.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 35.36/4.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.36/4.98      | v1_funct_1(X5) != iProver_top
% 35.36/4.98      | v1_funct_1(X4) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3419,plain,
% 35.36/4.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.36/4.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.36/4.98      | v1_funct_1(X2) != iProver_top
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1162,c_1166]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3611,plain,
% 35.36/4.98      ( v1_funct_1(X2) != iProver_top
% 35.36/4.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.36/4.98      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_3419,c_38]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3612,plain,
% 35.36/4.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.36/4.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.36/4.98      | v1_funct_1(X2) != iProver_top ),
% 35.36/4.98      inference(renaming,[status(thm)],[c_3611]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3619,plain,
% 35.36/4.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1159,c_3612]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9,plain,
% 35.36/4.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 35.36/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.36/4.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.36/4.98      | X3 = X2 ),
% 35.36/4.98      inference(cnf_transformation,[],[f52]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_27,negated_conjecture,
% 35.36/4.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 35.36/4.98      inference(cnf_transformation,[],[f75]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_385,plain,
% 35.36/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | X3 = X0
% 35.36/4.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 35.36/4.98      | k6_partfun1(sK0) != X3
% 35.36/4.98      | sK0 != X2
% 35.36/4.98      | sK0 != X1 ),
% 35.36/4.98      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_386,plain,
% 35.36/4.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.36/4.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.36/4.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.36/4.98      inference(unflattening,[status(thm)],[c_385]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_18,plain,
% 35.36/4.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 35.36/4.98      inference(cnf_transformation,[],[f62]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_394,plain,
% 35.36/4.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.36/4.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.36/4.98      inference(forward_subsumption_resolution,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_386,c_18]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1155,plain,
% 35.36/4.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.36/4.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_34,negated_conjecture,
% 35.36/4.98      ( v1_funct_1(sK2) ),
% 35.36/4.98      inference(cnf_transformation,[],[f68]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_16,plain,
% 35.36/4.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.36/4.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 35.36/4.98      | ~ v1_funct_1(X0)
% 35.36/4.98      | ~ v1_funct_1(X3) ),
% 35.36/4.98      inference(cnf_transformation,[],[f61]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1417,plain,
% 35.36/4.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.36/4.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.36/4.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.36/4.98      | ~ v1_funct_1(sK3)
% 35.36/4.98      | ~ v1_funct_1(sK2) ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_16]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1926,plain,
% 35.36/4.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_1155,c_34,c_32,c_31,c_29,c_394,c_1417]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3620,plain,
% 35.36/4.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top ),
% 35.36/4.98      inference(light_normalisation,[status(thm)],[c_3619,c_1926]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_35,plain,
% 35.36/4.98      ( v1_funct_1(sK2) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3825,plain,
% 35.36/4.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_3620,c_35]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9344,plain,
% 35.36/4.98      ( v1_funct_1(sK2) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) != iProver_top
% 35.36/4.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) = iProver_top ),
% 35.36/4.98      inference(light_normalisation,[status(thm)],[c_9342,c_3825]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_37,plain,
% 35.36/4.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1936,plain,
% 35.36/4.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.36/4.98      | v1_relat_1(sK2) ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_5]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1937,plain,
% 35.36/4.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_0,plain,
% 35.36/4.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 35.36/4.98      inference(cnf_transformation,[],[f80]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_4316,plain,
% 35.36/4.98      ( v2_funct_1(k6_partfun1(sK0)) ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_0]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_4317,plain,
% 35.36/4.98      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_4316]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9787,plain,
% 35.36/4.98      ( v2_funct_1(sK3) = iProver_top ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_9344,c_35,c_37,c_1937,c_4317]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_4,plain,
% 35.36/4.98      ( ~ v1_funct_1(X0)
% 35.36/4.98      | ~ v1_funct_1(X1)
% 35.36/4.98      | ~ v1_relat_1(X0)
% 35.36/4.98      | ~ v1_relat_1(X1)
% 35.36/4.98      | ~ v2_funct_1(X1)
% 35.36/4.98      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 35.36/4.98      | k2_funct_1(X1) = X0
% 35.36/4.98      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 35.36/4.98      inference(cnf_transformation,[],[f82]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1179,plain,
% 35.36/4.98      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 35.36/4.98      | k2_funct_1(X1) = X0
% 35.36/4.98      | k1_relat_1(X1) != k2_relat_1(X0)
% 35.36/4.98      | v1_funct_1(X0) != iProver_top
% 35.36/4.98      | v1_funct_1(X1) != iProver_top
% 35.36/4.98      | v1_relat_1(X0) != iProver_top
% 35.36/4.98      | v1_relat_1(X1) != iProver_top
% 35.36/4.98      | v2_funct_1(X1) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_4015,plain,
% 35.36/4.98      ( k2_funct_1(sK3) = sK2
% 35.36/4.98      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 35.36/4.98      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top
% 35.36/4.98      | v1_relat_1(sK3) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) != iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_3825,c_1179]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2197,plain,
% 35.36/4.98      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1162,c_1176]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_20,plain,
% 35.36/4.98      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 35.36/4.98      | ~ v1_funct_2(X3,X1,X0)
% 35.36/4.98      | ~ v1_funct_2(X2,X0,X1)
% 35.36/4.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 35.36/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.36/4.98      | ~ v1_funct_1(X2)
% 35.36/4.98      | ~ v1_funct_1(X3)
% 35.36/4.98      | k2_relset_1(X1,X0,X3) = X0 ),
% 35.36/4.98      inference(cnf_transformation,[],[f65]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_398,plain,
% 35.36/4.98      ( ~ v1_funct_2(X0,X1,X2)
% 35.36/4.98      | ~ v1_funct_2(X3,X2,X1)
% 35.36/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 35.36/4.98      | ~ v1_funct_1(X3)
% 35.36/4.98      | ~ v1_funct_1(X0)
% 35.36/4.98      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.36/4.98      | k2_relset_1(X2,X1,X3) = X1
% 35.36/4.98      | k6_partfun1(X1) != k6_partfun1(sK0)
% 35.36/4.98      | sK0 != X1 ),
% 35.36/4.98      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_399,plain,
% 35.36/4.98      ( ~ v1_funct_2(X0,X1,sK0)
% 35.36/4.98      | ~ v1_funct_2(X2,sK0,X1)
% 35.36/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 35.36/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 35.36/4.98      | ~ v1_funct_1(X2)
% 35.36/4.98      | ~ v1_funct_1(X0)
% 35.36/4.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.36/4.98      | k2_relset_1(X1,sK0,X0) = sK0
% 35.36/4.98      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 35.36/4.98      inference(unflattening,[status(thm)],[c_398]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_483,plain,
% 35.36/4.98      ( ~ v1_funct_2(X0,X1,sK0)
% 35.36/4.98      | ~ v1_funct_2(X2,sK0,X1)
% 35.36/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 35.36/4.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 35.36/4.98      | ~ v1_funct_1(X0)
% 35.36/4.98      | ~ v1_funct_1(X2)
% 35.36/4.98      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.36/4.98      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 35.36/4.98      inference(equality_resolution_simp,[status(thm)],[c_399]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1154,plain,
% 35.36/4.98      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.36/4.98      | k2_relset_1(X0,sK0,X2) = sK0
% 35.36/4.98      | v1_funct_2(X2,X0,sK0) != iProver_top
% 35.36/4.98      | v1_funct_2(X1,sK0,X0) != iProver_top
% 35.36/4.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 35.36/4.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 35.36/4.98      | v1_funct_1(X2) != iProver_top
% 35.36/4.98      | v1_funct_1(X1) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1610,plain,
% 35.36/4.98      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 35.36/4.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 35.36/4.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 35.36/4.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.36/4.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top ),
% 35.36/4.98      inference(equality_resolution,[status(thm)],[c_1154]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_33,negated_conjecture,
% 35.36/4.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 35.36/4.98      inference(cnf_transformation,[],[f69]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_36,plain,
% 35.36/4.98      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1933,plain,
% 35.36/4.98      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_1610,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2200,plain,
% 35.36/4.98      ( k2_relat_1(sK3) = sK0 ),
% 35.36/4.98      inference(light_normalisation,[status(thm)],[c_2197,c_1933]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_4016,plain,
% 35.36/4.98      ( k2_funct_1(sK3) = sK2
% 35.36/4.98      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 35.36/4.98      | sK1 != sK1
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top
% 35.36/4.98      | v1_relat_1(sK3) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) != iProver_top ),
% 35.36/4.98      inference(light_normalisation,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_4015,c_2199,c_2200,c_3022]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_4017,plain,
% 35.36/4.98      ( k2_funct_1(sK3) = sK2
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top
% 35.36/4.98      | v1_relat_1(sK3) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) != iProver_top ),
% 35.36/4.98      inference(equality_resolution_simp,[status(thm)],[c_4016]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_4583,plain,
% 35.36/4.98      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_4017,c_35,c_37,c_38,c_40,c_1565,c_1937]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9792,plain,
% 35.36/4.98      ( k2_funct_1(sK3) = sK2 ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_9787,c_4583]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_22,plain,
% 35.36/4.98      ( ~ v1_funct_2(X0,X1,X2)
% 35.36/4.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.36/4.98      | ~ v1_funct_1(X0)
% 35.36/4.98      | ~ v2_funct_1(X0)
% 35.36/4.98      | k2_relset_1(X1,X2,X0) != X2
% 35.36/4.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 35.36/4.98      | k1_xboole_0 = X2 ),
% 35.36/4.98      inference(cnf_transformation,[],[f66]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1164,plain,
% 35.36/4.98      ( k2_relset_1(X0,X1,X2) != X1
% 35.36/4.98      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 35.36/4.98      | k1_xboole_0 = X1
% 35.36/4.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.36/4.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.36/4.98      | v1_funct_1(X2) != iProver_top
% 35.36/4.98      | v2_funct_1(X2) != iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2692,plain,
% 35.36/4.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 35.36/4.98      | sK0 = k1_xboole_0
% 35.36/4.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 35.36/4.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v2_funct_1(sK3) != iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1933,c_1164]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_3108,plain,
% 35.36/4.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 35.36/4.98      | v2_funct_1(sK3) != iProver_top ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_2692,c_38,c_39,c_40,c_25,c_686,c_1283]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9793,plain,
% 35.36/4.98      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_9787,c_3108]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_9794,plain,
% 35.36/4.98      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 35.36/4.98      inference(demodulation,[status(thm)],[c_9792,c_9793]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_107664,plain,
% 35.36/4.98      ( k2_funct_1(sK2) = sK3
% 35.36/4.98      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 35.36/4.98      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top
% 35.36/4.98      | v1_relat_1(sK3) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) != iProver_top
% 35.36/4.98      | v2_funct_1(sK2) != iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_9794,c_1179]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2791,plain,
% 35.36/4.98      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 35.36/4.98      | sK1 = k1_xboole_0
% 35.36/4.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1159,c_1170]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2330,plain,
% 35.36/4.98      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 35.36/4.98      inference(superposition,[status(thm)],[c_1159,c_1177]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2792,plain,
% 35.36/4.98      ( k1_relat_1(sK2) = sK0
% 35.36/4.98      | sK1 = k1_xboole_0
% 35.36/4.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 35.36/4.98      inference(demodulation,[status(thm)],[c_2791,c_2330]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_24,negated_conjecture,
% 35.36/4.98      ( k1_xboole_0 != sK1 ),
% 35.36/4.98      inference(cnf_transformation,[],[f78]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1254,plain,
% 35.36/4.98      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_658]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_1255,plain,
% 35.36/4.98      ( sK1 != k1_xboole_0
% 35.36/4.98      | k1_xboole_0 = sK1
% 35.36/4.98      | k1_xboole_0 != k1_xboole_0 ),
% 35.36/4.98      inference(instantiation,[status(thm)],[c_1254]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_2916,plain,
% 35.36/4.98      ( k1_relat_1(sK2) = sK0 ),
% 35.36/4.98      inference(global_propositional_subsumption,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_2792,c_36,c_24,c_686,c_1255]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_107665,plain,
% 35.36/4.98      ( k2_funct_1(sK2) = sK3
% 35.36/4.98      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 35.36/4.98      | sK0 != sK0
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top
% 35.36/4.98      | v1_relat_1(sK3) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) != iProver_top
% 35.36/4.98      | v2_funct_1(sK2) != iProver_top ),
% 35.36/4.98      inference(light_normalisation,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_107664,c_2199,c_2200,c_2916]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_107666,plain,
% 35.36/4.98      ( k2_funct_1(sK2) = sK3
% 35.36/4.98      | v1_funct_1(sK3) != iProver_top
% 35.36/4.98      | v1_funct_1(sK2) != iProver_top
% 35.36/4.98      | v1_relat_1(sK3) != iProver_top
% 35.36/4.98      | v1_relat_1(sK2) != iProver_top
% 35.36/4.98      | v2_funct_1(sK2) != iProver_top ),
% 35.36/4.98      inference(equality_resolution_simp,[status(thm)],[c_107665]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_23,negated_conjecture,
% 35.36/4.98      ( k2_funct_1(sK2) != sK3 ),
% 35.36/4.98      inference(cnf_transformation,[],[f79]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_26,negated_conjecture,
% 35.36/4.98      ( v2_funct_1(sK2) ),
% 35.36/4.98      inference(cnf_transformation,[],[f76]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(c_42,plain,
% 35.36/4.98      ( v2_funct_1(sK2) = iProver_top ),
% 35.36/4.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.36/4.98  
% 35.36/4.98  cnf(contradiction,plain,
% 35.36/4.98      ( $false ),
% 35.36/4.98      inference(minisat,
% 35.36/4.98                [status(thm)],
% 35.36/4.98                [c_107666,c_1937,c_1565,c_23,c_42,c_40,c_38,c_37,c_35]) ).
% 35.36/4.98  
% 35.36/4.98  
% 35.36/4.98  % SZS output end CNFRefutation for theBenchmark.p
% 35.36/4.98  
% 35.36/4.98  ------                               Statistics
% 35.36/4.98  
% 35.36/4.98  ------ General
% 35.36/4.98  
% 35.36/4.98  abstr_ref_over_cycles:                  0
% 35.36/4.98  abstr_ref_under_cycles:                 0
% 35.36/4.98  gc_basic_clause_elim:                   0
% 35.36/4.98  forced_gc_time:                         0
% 35.36/4.98  parsing_time:                           0.011
% 35.36/4.98  unif_index_cands_time:                  0.
% 35.36/4.98  unif_index_add_time:                    0.
% 35.36/4.98  orderings_time:                         0.
% 35.36/4.98  out_proof_time:                         0.023
% 35.36/4.98  total_time:                             4.017
% 35.36/4.98  num_of_symbols:                         52
% 35.36/4.98  num_of_terms:                           113856
% 35.36/4.98  
% 35.36/4.98  ------ Preprocessing
% 35.36/4.98  
% 35.36/4.98  num_of_splits:                          0
% 35.36/4.98  num_of_split_atoms:                     0
% 35.36/4.98  num_of_reused_defs:                     0
% 35.36/4.98  num_eq_ax_congr_red:                    12
% 35.36/4.98  num_of_sem_filtered_clauses:            1
% 35.36/4.98  num_of_subtypes:                        0
% 35.36/4.98  monotx_restored_types:                  0
% 35.36/4.98  sat_num_of_epr_types:                   0
% 35.36/4.98  sat_num_of_non_cyclic_types:            0
% 35.36/4.98  sat_guarded_non_collapsed_types:        0
% 35.36/4.98  num_pure_diseq_elim:                    0
% 35.36/4.98  simp_replaced_by:                       0
% 35.36/4.98  res_preprocessed:                       168
% 35.36/4.98  prep_upred:                             0
% 35.36/4.98  prep_unflattend:                        12
% 35.36/4.98  smt_new_axioms:                         0
% 35.36/4.98  pred_elim_cands:                        5
% 35.36/4.98  pred_elim:                              1
% 35.36/4.98  pred_elim_cl:                           1
% 35.36/4.98  pred_elim_cycles:                       3
% 35.36/4.98  merged_defs:                            0
% 35.36/4.98  merged_defs_ncl:                        0
% 35.36/4.98  bin_hyper_res:                          0
% 35.36/4.98  prep_cycles:                            4
% 35.36/4.98  pred_elim_time:                         0.005
% 35.36/4.98  splitting_time:                         0.
% 35.36/4.98  sem_filter_time:                        0.
% 35.36/4.98  monotx_time:                            0.001
% 35.36/4.98  subtype_inf_time:                       0.
% 35.36/4.98  
% 35.36/4.98  ------ Problem properties
% 35.36/4.98  
% 35.36/4.98  clauses:                                34
% 35.36/4.98  conjectures:                            11
% 35.36/4.98  epr:                                    7
% 35.36/4.98  horn:                                   28
% 35.36/4.98  ground:                                 12
% 35.36/4.98  unary:                                  14
% 35.36/4.98  binary:                                 4
% 35.36/4.98  lits:                                   110
% 35.36/4.98  lits_eq:                                32
% 35.36/4.98  fd_pure:                                0
% 35.36/4.98  fd_pseudo:                              0
% 35.36/4.98  fd_cond:                                5
% 35.36/4.98  fd_pseudo_cond:                         1
% 35.36/4.98  ac_symbols:                             0
% 35.36/4.98  
% 35.36/4.98  ------ Propositional Solver
% 35.36/4.98  
% 35.36/4.98  prop_solver_calls:                      49
% 35.36/4.98  prop_fast_solver_calls:                 6648
% 35.36/4.98  smt_solver_calls:                       0
% 35.36/4.98  smt_fast_solver_calls:                  0
% 35.36/4.98  prop_num_of_clauses:                    47464
% 35.36/4.98  prop_preprocess_simplified:             85315
% 35.36/4.98  prop_fo_subsumed:                       1965
% 35.36/4.98  prop_solver_time:                       0.
% 35.36/4.98  smt_solver_time:                        0.
% 35.36/4.98  smt_fast_solver_time:                   0.
% 35.36/4.98  prop_fast_solver_time:                  0.
% 35.36/4.98  prop_unsat_core_time:                   0.008
% 35.36/4.98  
% 35.36/4.98  ------ QBF
% 35.36/4.98  
% 35.36/4.98  qbf_q_res:                              0
% 35.36/4.98  qbf_num_tautologies:                    0
% 35.36/4.98  qbf_prep_cycles:                        0
% 35.36/4.98  
% 35.36/4.98  ------ BMC1
% 35.36/4.98  
% 35.36/4.98  bmc1_current_bound:                     -1
% 35.36/4.98  bmc1_last_solved_bound:                 -1
% 35.36/4.98  bmc1_unsat_core_size:                   -1
% 35.36/4.98  bmc1_unsat_core_parents_size:           -1
% 35.36/4.98  bmc1_merge_next_fun:                    0
% 35.36/4.98  bmc1_unsat_core_clauses_time:           0.
% 35.36/4.98  
% 35.36/4.98  ------ Instantiation
% 35.36/4.98  
% 35.36/4.98  inst_num_of_clauses:                    8255
% 35.36/4.98  inst_num_in_passive:                    3396
% 35.36/4.98  inst_num_in_active:                     6096
% 35.36/4.98  inst_num_in_unprocessed:                1526
% 35.36/4.98  inst_num_of_loops:                      6399
% 35.36/4.98  inst_num_of_learning_restarts:          1
% 35.36/4.98  inst_num_moves_active_passive:          296
% 35.36/4.98  inst_lit_activity:                      0
% 35.36/4.98  inst_lit_activity_moves:                3
% 35.36/4.98  inst_num_tautologies:                   0
% 35.36/4.98  inst_num_prop_implied:                  0
% 35.36/4.98  inst_num_existing_simplified:           0
% 35.36/4.98  inst_num_eq_res_simplified:             0
% 35.36/4.98  inst_num_child_elim:                    0
% 35.36/4.98  inst_num_of_dismatching_blockings:      8711
% 35.36/4.98  inst_num_of_non_proper_insts:           14280
% 35.36/4.98  inst_num_of_duplicates:                 0
% 35.36/4.98  inst_inst_num_from_inst_to_res:         0
% 35.36/4.98  inst_dismatching_checking_time:         0.
% 35.36/4.98  
% 35.36/4.98  ------ Resolution
% 35.36/4.98  
% 35.36/4.98  res_num_of_clauses:                     49
% 35.36/4.98  res_num_in_passive:                     49
% 35.36/4.98  res_num_in_active:                      0
% 35.36/4.98  res_num_of_loops:                       172
% 35.36/4.98  res_forward_subset_subsumed:            774
% 35.36/4.98  res_backward_subset_subsumed:           6
% 35.36/4.98  res_forward_subsumed:                   0
% 35.36/4.98  res_backward_subsumed:                  0
% 35.36/4.98  res_forward_subsumption_resolution:     2
% 35.36/4.98  res_backward_subsumption_resolution:    0
% 35.36/4.98  res_clause_to_clause_subsumption:       14390
% 35.36/4.98  res_orphan_elimination:                 0
% 35.36/4.98  res_tautology_del:                      642
% 35.36/4.98  res_num_eq_res_simplified:              1
% 35.36/4.98  res_num_sel_changes:                    0
% 35.36/4.98  res_moves_from_active_to_pass:          0
% 35.36/4.98  
% 35.36/4.98  ------ Superposition
% 35.36/4.98  
% 35.36/4.98  sup_time_total:                         0.
% 35.36/4.98  sup_time_generating:                    0.
% 35.36/4.98  sup_time_sim_full:                      0.
% 35.36/4.98  sup_time_sim_immed:                     0.
% 35.36/4.98  
% 35.36/4.98  sup_num_of_clauses:                     6608
% 35.36/4.98  sup_num_in_active:                      1246
% 35.36/4.98  sup_num_in_passive:                     5362
% 35.36/4.98  sup_num_of_loops:                       1279
% 35.36/4.98  sup_fw_superposition:                   3053
% 35.36/4.98  sup_bw_superposition:                   3956
% 35.36/4.98  sup_immediate_simplified:               1914
% 35.36/4.98  sup_given_eliminated:                   1
% 35.36/4.98  comparisons_done:                       0
% 35.36/4.98  comparisons_avoided:                    1
% 35.36/4.98  
% 35.36/4.98  ------ Simplifications
% 35.36/4.98  
% 35.36/4.98  
% 35.36/4.98  sim_fw_subset_subsumed:                 98
% 35.36/4.98  sim_bw_subset_subsumed:                 95
% 35.36/4.98  sim_fw_subsumed:                        35
% 35.36/4.98  sim_bw_subsumed:                        41
% 35.36/4.98  sim_fw_subsumption_res:                 0
% 35.36/4.98  sim_bw_subsumption_res:                 0
% 35.36/4.98  sim_tautology_del:                      0
% 35.36/4.98  sim_eq_tautology_del:                   85
% 35.36/4.98  sim_eq_res_simp:                        2
% 35.36/4.98  sim_fw_demodulated:                     151
% 35.36/4.98  sim_bw_demodulated:                     17
% 35.36/4.98  sim_light_normalised:                   2213
% 35.36/4.98  sim_joinable_taut:                      0
% 35.36/4.98  sim_joinable_simp:                      0
% 35.36/4.98  sim_ac_normalised:                      0
% 35.36/4.98  sim_smt_subsumption:                    0
% 35.36/4.98  
%------------------------------------------------------------------------------
