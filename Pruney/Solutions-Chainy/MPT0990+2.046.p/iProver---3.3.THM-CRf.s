%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:06 EST 2020

% Result     : Theorem 35.53s
% Output     : CNFRefutation 35.53s
% Verified   : 
% Statistics : Number of formulae       :  175 (1402 expanded)
%              Number of clauses        :  104 ( 404 expanded)
%              Number of leaves         :   19 ( 367 expanded)
%              Depth                    :   23
%              Number of atoms          :  707 (12010 expanded)
%              Number of equality atoms :  361 (4453 expanded)
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

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f26])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f53,f63])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f63])).

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

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f63])).

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

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1176,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2198,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1159,c_1176])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2199,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2198,c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1162,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1169,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2790,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1169])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(cnf_transformation,[],[f71])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f76])).

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
    inference(cnf_transformation,[],[f46])).

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
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(cnf_transformation,[],[f62])).

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
    inference(cnf_transformation,[],[f51])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

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

cnf(c_10,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_386,c_10])).

cnf(c_1155,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_17,plain,
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
    inference(instantiation,[status(thm)],[c_17])).

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
    inference(cnf_transformation,[],[f79])).

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
    inference(cnf_transformation,[],[f81])).

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
    inference(cnf_transformation,[],[f64])).

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
    inference(cnf_transformation,[],[f68])).

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
    inference(cnf_transformation,[],[f65])).

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
    inference(superposition,[status(thm)],[c_1159,c_1169])).

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
    inference(cnf_transformation,[],[f77])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

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
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.53/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.53/5.00  
% 35.53/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.53/5.00  
% 35.53/5.00  ------  iProver source info
% 35.53/5.00  
% 35.53/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.53/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.53/5.00  git: non_committed_changes: false
% 35.53/5.00  git: last_make_outside_of_git: false
% 35.53/5.00  
% 35.53/5.00  ------ 
% 35.53/5.00  
% 35.53/5.00  ------ Input Options
% 35.53/5.00  
% 35.53/5.00  --out_options                           all
% 35.53/5.00  --tptp_safe_out                         true
% 35.53/5.00  --problem_path                          ""
% 35.53/5.00  --include_path                          ""
% 35.53/5.00  --clausifier                            res/vclausify_rel
% 35.53/5.00  --clausifier_options                    ""
% 35.53/5.00  --stdin                                 false
% 35.53/5.00  --stats_out                             all
% 35.53/5.00  
% 35.53/5.00  ------ General Options
% 35.53/5.00  
% 35.53/5.00  --fof                                   false
% 35.53/5.00  --time_out_real                         305.
% 35.53/5.00  --time_out_virtual                      -1.
% 35.53/5.00  --symbol_type_check                     false
% 35.53/5.00  --clausify_out                          false
% 35.53/5.00  --sig_cnt_out                           false
% 35.53/5.00  --trig_cnt_out                          false
% 35.53/5.00  --trig_cnt_out_tolerance                1.
% 35.53/5.00  --trig_cnt_out_sk_spl                   false
% 35.53/5.00  --abstr_cl_out                          false
% 35.53/5.00  
% 35.53/5.00  ------ Global Options
% 35.53/5.00  
% 35.53/5.00  --schedule                              default
% 35.53/5.00  --add_important_lit                     false
% 35.53/5.00  --prop_solver_per_cl                    1000
% 35.53/5.00  --min_unsat_core                        false
% 35.53/5.00  --soft_assumptions                      false
% 35.53/5.00  --soft_lemma_size                       3
% 35.53/5.00  --prop_impl_unit_size                   0
% 35.53/5.00  --prop_impl_unit                        []
% 35.53/5.00  --share_sel_clauses                     true
% 35.53/5.00  --reset_solvers                         false
% 35.53/5.00  --bc_imp_inh                            [conj_cone]
% 35.53/5.00  --conj_cone_tolerance                   3.
% 35.53/5.00  --extra_neg_conj                        none
% 35.53/5.00  --large_theory_mode                     true
% 35.53/5.00  --prolific_symb_bound                   200
% 35.53/5.00  --lt_threshold                          2000
% 35.53/5.00  --clause_weak_htbl                      true
% 35.53/5.00  --gc_record_bc_elim                     false
% 35.53/5.00  
% 35.53/5.00  ------ Preprocessing Options
% 35.53/5.00  
% 35.53/5.00  --preprocessing_flag                    true
% 35.53/5.00  --time_out_prep_mult                    0.1
% 35.53/5.00  --splitting_mode                        input
% 35.53/5.00  --splitting_grd                         true
% 35.53/5.00  --splitting_cvd                         false
% 35.53/5.00  --splitting_cvd_svl                     false
% 35.53/5.00  --splitting_nvd                         32
% 35.53/5.00  --sub_typing                            true
% 35.53/5.00  --prep_gs_sim                           true
% 35.53/5.00  --prep_unflatten                        true
% 35.53/5.00  --prep_res_sim                          true
% 35.53/5.00  --prep_upred                            true
% 35.53/5.00  --prep_sem_filter                       exhaustive
% 35.53/5.00  --prep_sem_filter_out                   false
% 35.53/5.00  --pred_elim                             true
% 35.53/5.00  --res_sim_input                         true
% 35.53/5.00  --eq_ax_congr_red                       true
% 35.53/5.00  --pure_diseq_elim                       true
% 35.53/5.00  --brand_transform                       false
% 35.53/5.00  --non_eq_to_eq                          false
% 35.53/5.00  --prep_def_merge                        true
% 35.53/5.00  --prep_def_merge_prop_impl              false
% 35.53/5.00  --prep_def_merge_mbd                    true
% 35.53/5.00  --prep_def_merge_tr_red                 false
% 35.53/5.00  --prep_def_merge_tr_cl                  false
% 35.53/5.00  --smt_preprocessing                     true
% 35.53/5.00  --smt_ac_axioms                         fast
% 35.53/5.00  --preprocessed_out                      false
% 35.53/5.00  --preprocessed_stats                    false
% 35.53/5.00  
% 35.53/5.00  ------ Abstraction refinement Options
% 35.53/5.00  
% 35.53/5.00  --abstr_ref                             []
% 35.53/5.00  --abstr_ref_prep                        false
% 35.53/5.00  --abstr_ref_until_sat                   false
% 35.53/5.00  --abstr_ref_sig_restrict                funpre
% 35.53/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.53/5.00  --abstr_ref_under                       []
% 35.53/5.00  
% 35.53/5.00  ------ SAT Options
% 35.53/5.00  
% 35.53/5.00  --sat_mode                              false
% 35.53/5.00  --sat_fm_restart_options                ""
% 35.53/5.00  --sat_gr_def                            false
% 35.53/5.00  --sat_epr_types                         true
% 35.53/5.00  --sat_non_cyclic_types                  false
% 35.53/5.00  --sat_finite_models                     false
% 35.53/5.00  --sat_fm_lemmas                         false
% 35.53/5.00  --sat_fm_prep                           false
% 35.53/5.00  --sat_fm_uc_incr                        true
% 35.53/5.00  --sat_out_model                         small
% 35.53/5.00  --sat_out_clauses                       false
% 35.53/5.00  
% 35.53/5.00  ------ QBF Options
% 35.53/5.00  
% 35.53/5.00  --qbf_mode                              false
% 35.53/5.00  --qbf_elim_univ                         false
% 35.53/5.00  --qbf_dom_inst                          none
% 35.53/5.00  --qbf_dom_pre_inst                      false
% 35.53/5.00  --qbf_sk_in                             false
% 35.53/5.00  --qbf_pred_elim                         true
% 35.53/5.00  --qbf_split                             512
% 35.53/5.00  
% 35.53/5.00  ------ BMC1 Options
% 35.53/5.00  
% 35.53/5.00  --bmc1_incremental                      false
% 35.53/5.00  --bmc1_axioms                           reachable_all
% 35.53/5.00  --bmc1_min_bound                        0
% 35.53/5.00  --bmc1_max_bound                        -1
% 35.53/5.00  --bmc1_max_bound_default                -1
% 35.53/5.00  --bmc1_symbol_reachability              true
% 35.53/5.00  --bmc1_property_lemmas                  false
% 35.53/5.00  --bmc1_k_induction                      false
% 35.53/5.00  --bmc1_non_equiv_states                 false
% 35.53/5.00  --bmc1_deadlock                         false
% 35.53/5.00  --bmc1_ucm                              false
% 35.53/5.00  --bmc1_add_unsat_core                   none
% 35.53/5.00  --bmc1_unsat_core_children              false
% 35.53/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.53/5.00  --bmc1_out_stat                         full
% 35.53/5.00  --bmc1_ground_init                      false
% 35.53/5.00  --bmc1_pre_inst_next_state              false
% 35.53/5.00  --bmc1_pre_inst_state                   false
% 35.53/5.00  --bmc1_pre_inst_reach_state             false
% 35.53/5.00  --bmc1_out_unsat_core                   false
% 35.53/5.00  --bmc1_aig_witness_out                  false
% 35.53/5.00  --bmc1_verbose                          false
% 35.53/5.00  --bmc1_dump_clauses_tptp                false
% 35.53/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.53/5.00  --bmc1_dump_file                        -
% 35.53/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.53/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.53/5.00  --bmc1_ucm_extend_mode                  1
% 35.53/5.00  --bmc1_ucm_init_mode                    2
% 35.53/5.00  --bmc1_ucm_cone_mode                    none
% 35.53/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.53/5.00  --bmc1_ucm_relax_model                  4
% 35.53/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.53/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.53/5.00  --bmc1_ucm_layered_model                none
% 35.53/5.00  --bmc1_ucm_max_lemma_size               10
% 35.53/5.00  
% 35.53/5.00  ------ AIG Options
% 35.53/5.00  
% 35.53/5.00  --aig_mode                              false
% 35.53/5.00  
% 35.53/5.00  ------ Instantiation Options
% 35.53/5.00  
% 35.53/5.00  --instantiation_flag                    true
% 35.53/5.00  --inst_sos_flag                         true
% 35.53/5.00  --inst_sos_phase                        true
% 35.53/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.53/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.53/5.00  --inst_lit_sel_side                     num_symb
% 35.53/5.00  --inst_solver_per_active                1400
% 35.53/5.00  --inst_solver_calls_frac                1.
% 35.53/5.00  --inst_passive_queue_type               priority_queues
% 35.53/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.53/5.00  --inst_passive_queues_freq              [25;2]
% 35.53/5.00  --inst_dismatching                      true
% 35.53/5.00  --inst_eager_unprocessed_to_passive     true
% 35.53/5.00  --inst_prop_sim_given                   true
% 35.53/5.00  --inst_prop_sim_new                     false
% 35.53/5.00  --inst_subs_new                         false
% 35.53/5.00  --inst_eq_res_simp                      false
% 35.53/5.00  --inst_subs_given                       false
% 35.53/5.00  --inst_orphan_elimination               true
% 35.53/5.00  --inst_learning_loop_flag               true
% 35.53/5.00  --inst_learning_start                   3000
% 35.53/5.00  --inst_learning_factor                  2
% 35.53/5.00  --inst_start_prop_sim_after_learn       3
% 35.53/5.00  --inst_sel_renew                        solver
% 35.53/5.00  --inst_lit_activity_flag                true
% 35.53/5.00  --inst_restr_to_given                   false
% 35.53/5.00  --inst_activity_threshold               500
% 35.53/5.00  --inst_out_proof                        true
% 35.53/5.00  
% 35.53/5.00  ------ Resolution Options
% 35.53/5.00  
% 35.53/5.00  --resolution_flag                       true
% 35.53/5.00  --res_lit_sel                           adaptive
% 35.53/5.00  --res_lit_sel_side                      none
% 35.53/5.00  --res_ordering                          kbo
% 35.53/5.00  --res_to_prop_solver                    active
% 35.53/5.00  --res_prop_simpl_new                    false
% 35.53/5.00  --res_prop_simpl_given                  true
% 35.53/5.00  --res_passive_queue_type                priority_queues
% 35.53/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.53/5.00  --res_passive_queues_freq               [15;5]
% 35.53/5.00  --res_forward_subs                      full
% 35.53/5.00  --res_backward_subs                     full
% 35.53/5.00  --res_forward_subs_resolution           true
% 35.53/5.00  --res_backward_subs_resolution          true
% 35.53/5.00  --res_orphan_elimination                true
% 35.53/5.00  --res_time_limit                        2.
% 35.53/5.00  --res_out_proof                         true
% 35.53/5.00  
% 35.53/5.00  ------ Superposition Options
% 35.53/5.00  
% 35.53/5.00  --superposition_flag                    true
% 35.53/5.00  --sup_passive_queue_type                priority_queues
% 35.53/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.53/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.53/5.00  --demod_completeness_check              fast
% 35.53/5.00  --demod_use_ground                      true
% 35.53/5.00  --sup_to_prop_solver                    passive
% 35.53/5.00  --sup_prop_simpl_new                    true
% 35.53/5.00  --sup_prop_simpl_given                  true
% 35.53/5.00  --sup_fun_splitting                     true
% 35.53/5.00  --sup_smt_interval                      50000
% 35.53/5.00  
% 35.53/5.00  ------ Superposition Simplification Setup
% 35.53/5.00  
% 35.53/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.53/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.53/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.53/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.53/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.53/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.53/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.53/5.00  --sup_immed_triv                        [TrivRules]
% 35.53/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/5.00  --sup_immed_bw_main                     []
% 35.53/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.53/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.53/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/5.00  --sup_input_bw                          []
% 35.53/5.00  
% 35.53/5.00  ------ Combination Options
% 35.53/5.00  
% 35.53/5.00  --comb_res_mult                         3
% 35.53/5.00  --comb_sup_mult                         2
% 35.53/5.00  --comb_inst_mult                        10
% 35.53/5.00  
% 35.53/5.00  ------ Debug Options
% 35.53/5.00  
% 35.53/5.00  --dbg_backtrace                         false
% 35.53/5.00  --dbg_dump_prop_clauses                 false
% 35.53/5.00  --dbg_dump_prop_clauses_file            -
% 35.53/5.00  --dbg_out_stat                          false
% 35.53/5.00  ------ Parsing...
% 35.53/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.53/5.00  
% 35.53/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.53/5.00  
% 35.53/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.53/5.00  
% 35.53/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.53/5.00  ------ Proving...
% 35.53/5.00  ------ Problem Properties 
% 35.53/5.00  
% 35.53/5.00  
% 35.53/5.00  clauses                                 34
% 35.53/5.00  conjectures                             11
% 35.53/5.00  EPR                                     7
% 35.53/5.00  Horn                                    28
% 35.53/5.00  unary                                   14
% 35.53/5.00  binary                                  4
% 35.53/5.00  lits                                    110
% 35.53/5.00  lits eq                                 32
% 35.53/5.00  fd_pure                                 0
% 35.53/5.00  fd_pseudo                               0
% 35.53/5.00  fd_cond                                 5
% 35.53/5.00  fd_pseudo_cond                          1
% 35.53/5.00  AC symbols                              0
% 35.53/5.00  
% 35.53/5.00  ------ Schedule dynamic 5 is on 
% 35.53/5.00  
% 35.53/5.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.53/5.00  
% 35.53/5.00  
% 35.53/5.00  ------ 
% 35.53/5.00  Current options:
% 35.53/5.00  ------ 
% 35.53/5.00  
% 35.53/5.00  ------ Input Options
% 35.53/5.00  
% 35.53/5.00  --out_options                           all
% 35.53/5.00  --tptp_safe_out                         true
% 35.53/5.00  --problem_path                          ""
% 35.53/5.00  --include_path                          ""
% 35.53/5.00  --clausifier                            res/vclausify_rel
% 35.53/5.00  --clausifier_options                    ""
% 35.53/5.00  --stdin                                 false
% 35.53/5.00  --stats_out                             all
% 35.53/5.00  
% 35.53/5.00  ------ General Options
% 35.53/5.00  
% 35.53/5.00  --fof                                   false
% 35.53/5.00  --time_out_real                         305.
% 35.53/5.00  --time_out_virtual                      -1.
% 35.53/5.00  --symbol_type_check                     false
% 35.53/5.00  --clausify_out                          false
% 35.53/5.00  --sig_cnt_out                           false
% 35.53/5.00  --trig_cnt_out                          false
% 35.53/5.00  --trig_cnt_out_tolerance                1.
% 35.53/5.00  --trig_cnt_out_sk_spl                   false
% 35.53/5.00  --abstr_cl_out                          false
% 35.53/5.00  
% 35.53/5.00  ------ Global Options
% 35.53/5.00  
% 35.53/5.00  --schedule                              default
% 35.53/5.00  --add_important_lit                     false
% 35.53/5.00  --prop_solver_per_cl                    1000
% 35.53/5.00  --min_unsat_core                        false
% 35.53/5.00  --soft_assumptions                      false
% 35.53/5.00  --soft_lemma_size                       3
% 35.53/5.00  --prop_impl_unit_size                   0
% 35.53/5.00  --prop_impl_unit                        []
% 35.53/5.00  --share_sel_clauses                     true
% 35.53/5.00  --reset_solvers                         false
% 35.53/5.00  --bc_imp_inh                            [conj_cone]
% 35.53/5.00  --conj_cone_tolerance                   3.
% 35.53/5.00  --extra_neg_conj                        none
% 35.53/5.00  --large_theory_mode                     true
% 35.53/5.00  --prolific_symb_bound                   200
% 35.53/5.00  --lt_threshold                          2000
% 35.53/5.00  --clause_weak_htbl                      true
% 35.53/5.00  --gc_record_bc_elim                     false
% 35.53/5.00  
% 35.53/5.00  ------ Preprocessing Options
% 35.53/5.00  
% 35.53/5.00  --preprocessing_flag                    true
% 35.53/5.00  --time_out_prep_mult                    0.1
% 35.53/5.00  --splitting_mode                        input
% 35.53/5.00  --splitting_grd                         true
% 35.53/5.00  --splitting_cvd                         false
% 35.53/5.00  --splitting_cvd_svl                     false
% 35.53/5.00  --splitting_nvd                         32
% 35.53/5.00  --sub_typing                            true
% 35.53/5.00  --prep_gs_sim                           true
% 35.53/5.00  --prep_unflatten                        true
% 35.53/5.00  --prep_res_sim                          true
% 35.53/5.00  --prep_upred                            true
% 35.53/5.00  --prep_sem_filter                       exhaustive
% 35.53/5.00  --prep_sem_filter_out                   false
% 35.53/5.00  --pred_elim                             true
% 35.53/5.00  --res_sim_input                         true
% 35.53/5.00  --eq_ax_congr_red                       true
% 35.53/5.00  --pure_diseq_elim                       true
% 35.53/5.00  --brand_transform                       false
% 35.53/5.00  --non_eq_to_eq                          false
% 35.53/5.00  --prep_def_merge                        true
% 35.53/5.00  --prep_def_merge_prop_impl              false
% 35.53/5.00  --prep_def_merge_mbd                    true
% 35.53/5.00  --prep_def_merge_tr_red                 false
% 35.53/5.00  --prep_def_merge_tr_cl                  false
% 35.53/5.00  --smt_preprocessing                     true
% 35.53/5.00  --smt_ac_axioms                         fast
% 35.53/5.00  --preprocessed_out                      false
% 35.53/5.00  --preprocessed_stats                    false
% 35.53/5.00  
% 35.53/5.00  ------ Abstraction refinement Options
% 35.53/5.00  
% 35.53/5.00  --abstr_ref                             []
% 35.53/5.00  --abstr_ref_prep                        false
% 35.53/5.00  --abstr_ref_until_sat                   false
% 35.53/5.00  --abstr_ref_sig_restrict                funpre
% 35.53/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.53/5.00  --abstr_ref_under                       []
% 35.53/5.00  
% 35.53/5.00  ------ SAT Options
% 35.53/5.00  
% 35.53/5.00  --sat_mode                              false
% 35.53/5.00  --sat_fm_restart_options                ""
% 35.53/5.00  --sat_gr_def                            false
% 35.53/5.00  --sat_epr_types                         true
% 35.53/5.00  --sat_non_cyclic_types                  false
% 35.53/5.00  --sat_finite_models                     false
% 35.53/5.00  --sat_fm_lemmas                         false
% 35.53/5.00  --sat_fm_prep                           false
% 35.53/5.00  --sat_fm_uc_incr                        true
% 35.53/5.00  --sat_out_model                         small
% 35.53/5.00  --sat_out_clauses                       false
% 35.53/5.00  
% 35.53/5.00  ------ QBF Options
% 35.53/5.00  
% 35.53/5.00  --qbf_mode                              false
% 35.53/5.00  --qbf_elim_univ                         false
% 35.53/5.00  --qbf_dom_inst                          none
% 35.53/5.00  --qbf_dom_pre_inst                      false
% 35.53/5.00  --qbf_sk_in                             false
% 35.53/5.00  --qbf_pred_elim                         true
% 35.53/5.00  --qbf_split                             512
% 35.53/5.00  
% 35.53/5.00  ------ BMC1 Options
% 35.53/5.00  
% 35.53/5.00  --bmc1_incremental                      false
% 35.53/5.00  --bmc1_axioms                           reachable_all
% 35.53/5.00  --bmc1_min_bound                        0
% 35.53/5.00  --bmc1_max_bound                        -1
% 35.53/5.00  --bmc1_max_bound_default                -1
% 35.53/5.00  --bmc1_symbol_reachability              true
% 35.53/5.00  --bmc1_property_lemmas                  false
% 35.53/5.00  --bmc1_k_induction                      false
% 35.53/5.00  --bmc1_non_equiv_states                 false
% 35.53/5.00  --bmc1_deadlock                         false
% 35.53/5.00  --bmc1_ucm                              false
% 35.53/5.00  --bmc1_add_unsat_core                   none
% 35.53/5.00  --bmc1_unsat_core_children              false
% 35.53/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.53/5.00  --bmc1_out_stat                         full
% 35.53/5.00  --bmc1_ground_init                      false
% 35.53/5.00  --bmc1_pre_inst_next_state              false
% 35.53/5.00  --bmc1_pre_inst_state                   false
% 35.53/5.00  --bmc1_pre_inst_reach_state             false
% 35.53/5.00  --bmc1_out_unsat_core                   false
% 35.53/5.00  --bmc1_aig_witness_out                  false
% 35.53/5.00  --bmc1_verbose                          false
% 35.53/5.00  --bmc1_dump_clauses_tptp                false
% 35.53/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.53/5.00  --bmc1_dump_file                        -
% 35.53/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.53/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.53/5.00  --bmc1_ucm_extend_mode                  1
% 35.53/5.00  --bmc1_ucm_init_mode                    2
% 35.53/5.00  --bmc1_ucm_cone_mode                    none
% 35.53/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.53/5.00  --bmc1_ucm_relax_model                  4
% 35.53/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.53/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.53/5.00  --bmc1_ucm_layered_model                none
% 35.53/5.00  --bmc1_ucm_max_lemma_size               10
% 35.53/5.00  
% 35.53/5.00  ------ AIG Options
% 35.53/5.00  
% 35.53/5.00  --aig_mode                              false
% 35.53/5.00  
% 35.53/5.00  ------ Instantiation Options
% 35.53/5.00  
% 35.53/5.00  --instantiation_flag                    true
% 35.53/5.00  --inst_sos_flag                         true
% 35.53/5.00  --inst_sos_phase                        true
% 35.53/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.53/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.53/5.00  --inst_lit_sel_side                     none
% 35.53/5.00  --inst_solver_per_active                1400
% 35.53/5.00  --inst_solver_calls_frac                1.
% 35.53/5.00  --inst_passive_queue_type               priority_queues
% 35.53/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.53/5.00  --inst_passive_queues_freq              [25;2]
% 35.53/5.00  --inst_dismatching                      true
% 35.53/5.00  --inst_eager_unprocessed_to_passive     true
% 35.53/5.00  --inst_prop_sim_given                   true
% 35.53/5.00  --inst_prop_sim_new                     false
% 35.53/5.00  --inst_subs_new                         false
% 35.53/5.00  --inst_eq_res_simp                      false
% 35.53/5.00  --inst_subs_given                       false
% 35.53/5.00  --inst_orphan_elimination               true
% 35.53/5.00  --inst_learning_loop_flag               true
% 35.53/5.00  --inst_learning_start                   3000
% 35.53/5.00  --inst_learning_factor                  2
% 35.53/5.00  --inst_start_prop_sim_after_learn       3
% 35.53/5.00  --inst_sel_renew                        solver
% 35.53/5.00  --inst_lit_activity_flag                true
% 35.53/5.00  --inst_restr_to_given                   false
% 35.53/5.00  --inst_activity_threshold               500
% 35.53/5.00  --inst_out_proof                        true
% 35.53/5.00  
% 35.53/5.00  ------ Resolution Options
% 35.53/5.00  
% 35.53/5.00  --resolution_flag                       false
% 35.53/5.00  --res_lit_sel                           adaptive
% 35.53/5.00  --res_lit_sel_side                      none
% 35.53/5.00  --res_ordering                          kbo
% 35.53/5.00  --res_to_prop_solver                    active
% 35.53/5.00  --res_prop_simpl_new                    false
% 35.53/5.00  --res_prop_simpl_given                  true
% 35.53/5.00  --res_passive_queue_type                priority_queues
% 35.53/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.53/5.00  --res_passive_queues_freq               [15;5]
% 35.53/5.00  --res_forward_subs                      full
% 35.53/5.00  --res_backward_subs                     full
% 35.53/5.00  --res_forward_subs_resolution           true
% 35.53/5.00  --res_backward_subs_resolution          true
% 35.53/5.00  --res_orphan_elimination                true
% 35.53/5.00  --res_time_limit                        2.
% 35.53/5.00  --res_out_proof                         true
% 35.53/5.00  
% 35.53/5.00  ------ Superposition Options
% 35.53/5.00  
% 35.53/5.00  --superposition_flag                    true
% 35.53/5.00  --sup_passive_queue_type                priority_queues
% 35.53/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.53/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.53/5.00  --demod_completeness_check              fast
% 35.53/5.00  --demod_use_ground                      true
% 35.53/5.00  --sup_to_prop_solver                    passive
% 35.53/5.00  --sup_prop_simpl_new                    true
% 35.53/5.00  --sup_prop_simpl_given                  true
% 35.53/5.00  --sup_fun_splitting                     true
% 35.53/5.00  --sup_smt_interval                      50000
% 35.53/5.00  
% 35.53/5.00  ------ Superposition Simplification Setup
% 35.53/5.00  
% 35.53/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.53/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.53/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.53/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.53/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.53/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.53/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.53/5.00  --sup_immed_triv                        [TrivRules]
% 35.53/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/5.00  --sup_immed_bw_main                     []
% 35.53/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.53/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.53/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.53/5.00  --sup_input_bw                          []
% 35.53/5.00  
% 35.53/5.00  ------ Combination Options
% 35.53/5.00  
% 35.53/5.00  --comb_res_mult                         3
% 35.53/5.00  --comb_sup_mult                         2
% 35.53/5.00  --comb_inst_mult                        10
% 35.53/5.00  
% 35.53/5.00  ------ Debug Options
% 35.53/5.00  
% 35.53/5.00  --dbg_backtrace                         false
% 35.53/5.00  --dbg_dump_prop_clauses                 false
% 35.53/5.00  --dbg_dump_prop_clauses_file            -
% 35.53/5.00  --dbg_out_stat                          false
% 35.53/5.00  
% 35.53/5.00  
% 35.53/5.00  
% 35.53/5.00  
% 35.53/5.00  ------ Proving...
% 35.53/5.00  
% 35.53/5.00  
% 35.53/5.00  % SZS status Theorem for theBenchmark.p
% 35.53/5.00  
% 35.53/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.53/5.00  
% 35.53/5.00  fof(f15,conjecture,(
% 35.53/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f16,negated_conjecture,(
% 35.53/5.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.53/5.00    inference(negated_conjecture,[],[f15])).
% 35.53/5.00  
% 35.53/5.00  fof(f36,plain,(
% 35.53/5.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 35.53/5.00    inference(ennf_transformation,[],[f16])).
% 35.53/5.00  
% 35.53/5.00  fof(f37,plain,(
% 35.53/5.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 35.53/5.00    inference(flattening,[],[f36])).
% 35.53/5.00  
% 35.53/5.00  fof(f41,plain,(
% 35.53/5.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 35.53/5.00    introduced(choice_axiom,[])).
% 35.53/5.00  
% 35.53/5.00  fof(f40,plain,(
% 35.53/5.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 35.53/5.00    introduced(choice_axiom,[])).
% 35.53/5.00  
% 35.53/5.00  fof(f42,plain,(
% 35.53/5.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 35.53/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40])).
% 35.53/5.00  
% 35.53/5.00  fof(f69,plain,(
% 35.53/5.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f6,axiom,(
% 35.53/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f23,plain,(
% 35.53/5.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.53/5.00    inference(ennf_transformation,[],[f6])).
% 35.53/5.00  
% 35.53/5.00  fof(f50,plain,(
% 35.53/5.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.53/5.00    inference(cnf_transformation,[],[f23])).
% 35.53/5.00  
% 35.53/5.00  fof(f73,plain,(
% 35.53/5.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f72,plain,(
% 35.53/5.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f9,axiom,(
% 35.53/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f26,plain,(
% 35.53/5.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.53/5.00    inference(ennf_transformation,[],[f9])).
% 35.53/5.00  
% 35.53/5.00  fof(f27,plain,(
% 35.53/5.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.53/5.00    inference(flattening,[],[f26])).
% 35.53/5.00  
% 35.53/5.00  fof(f39,plain,(
% 35.53/5.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.53/5.00    inference(nnf_transformation,[],[f27])).
% 35.53/5.00  
% 35.53/5.00  fof(f54,plain,(
% 35.53/5.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.53/5.00    inference(cnf_transformation,[],[f39])).
% 35.53/5.00  
% 35.53/5.00  fof(f5,axiom,(
% 35.53/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f22,plain,(
% 35.53/5.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.53/5.00    inference(ennf_transformation,[],[f5])).
% 35.53/5.00  
% 35.53/5.00  fof(f49,plain,(
% 35.53/5.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.53/5.00    inference(cnf_transformation,[],[f22])).
% 35.53/5.00  
% 35.53/5.00  fof(f71,plain,(
% 35.53/5.00    v1_funct_2(sK3,sK1,sK0)),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f76,plain,(
% 35.53/5.00    k1_xboole_0 != sK0),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f2,axiom,(
% 35.53/5.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f17,plain,(
% 35.53/5.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.53/5.00    inference(ennf_transformation,[],[f2])).
% 35.53/5.00  
% 35.53/5.00  fof(f18,plain,(
% 35.53/5.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.53/5.00    inference(flattening,[],[f17])).
% 35.53/5.00  
% 35.53/5.00  fof(f46,plain,(
% 35.53/5.00    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.53/5.00    inference(cnf_transformation,[],[f18])).
% 35.53/5.00  
% 35.53/5.00  fof(f70,plain,(
% 35.53/5.00    v1_funct_1(sK3)),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f4,axiom,(
% 35.53/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f21,plain,(
% 35.53/5.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.53/5.00    inference(ennf_transformation,[],[f4])).
% 35.53/5.00  
% 35.53/5.00  fof(f48,plain,(
% 35.53/5.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.53/5.00    inference(cnf_transformation,[],[f21])).
% 35.53/5.00  
% 35.53/5.00  fof(f11,axiom,(
% 35.53/5.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f30,plain,(
% 35.53/5.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.53/5.00    inference(ennf_transformation,[],[f11])).
% 35.53/5.00  
% 35.53/5.00  fof(f31,plain,(
% 35.53/5.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.53/5.00    inference(flattening,[],[f30])).
% 35.53/5.00  
% 35.53/5.00  fof(f62,plain,(
% 35.53/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.53/5.00    inference(cnf_transformation,[],[f31])).
% 35.53/5.00  
% 35.53/5.00  fof(f7,axiom,(
% 35.53/5.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f24,plain,(
% 35.53/5.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 35.53/5.00    inference(ennf_transformation,[],[f7])).
% 35.53/5.00  
% 35.53/5.00  fof(f25,plain,(
% 35.53/5.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.53/5.00    inference(flattening,[],[f24])).
% 35.53/5.00  
% 35.53/5.00  fof(f38,plain,(
% 35.53/5.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.53/5.00    inference(nnf_transformation,[],[f25])).
% 35.53/5.00  
% 35.53/5.00  fof(f51,plain,(
% 35.53/5.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.53/5.00    inference(cnf_transformation,[],[f38])).
% 35.53/5.00  
% 35.53/5.00  fof(f74,plain,(
% 35.53/5.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f8,axiom,(
% 35.53/5.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f53,plain,(
% 35.53/5.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.53/5.00    inference(cnf_transformation,[],[f8])).
% 35.53/5.00  
% 35.53/5.00  fof(f12,axiom,(
% 35.53/5.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f63,plain,(
% 35.53/5.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 35.53/5.00    inference(cnf_transformation,[],[f12])).
% 35.53/5.00  
% 35.53/5.00  fof(f82,plain,(
% 35.53/5.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.53/5.00    inference(definition_unfolding,[],[f53,f63])).
% 35.53/5.00  
% 35.53/5.00  fof(f67,plain,(
% 35.53/5.00    v1_funct_1(sK2)),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f10,axiom,(
% 35.53/5.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f28,plain,(
% 35.53/5.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.53/5.00    inference(ennf_transformation,[],[f10])).
% 35.53/5.00  
% 35.53/5.00  fof(f29,plain,(
% 35.53/5.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.53/5.00    inference(flattening,[],[f28])).
% 35.53/5.00  
% 35.53/5.00  fof(f61,plain,(
% 35.53/5.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.53/5.00    inference(cnf_transformation,[],[f29])).
% 35.53/5.00  
% 35.53/5.00  fof(f1,axiom,(
% 35.53/5.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f44,plain,(
% 35.53/5.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 35.53/5.00    inference(cnf_transformation,[],[f1])).
% 35.53/5.00  
% 35.53/5.00  fof(f79,plain,(
% 35.53/5.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 35.53/5.00    inference(definition_unfolding,[],[f44,f63])).
% 35.53/5.00  
% 35.53/5.00  fof(f3,axiom,(
% 35.53/5.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f19,plain,(
% 35.53/5.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.53/5.00    inference(ennf_transformation,[],[f3])).
% 35.53/5.00  
% 35.53/5.00  fof(f20,plain,(
% 35.53/5.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.53/5.00    inference(flattening,[],[f19])).
% 35.53/5.00  
% 35.53/5.00  fof(f47,plain,(
% 35.53/5.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.53/5.00    inference(cnf_transformation,[],[f20])).
% 35.53/5.00  
% 35.53/5.00  fof(f81,plain,(
% 35.53/5.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.53/5.00    inference(definition_unfolding,[],[f47,f63])).
% 35.53/5.00  
% 35.53/5.00  fof(f13,axiom,(
% 35.53/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f32,plain,(
% 35.53/5.00    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 35.53/5.00    inference(ennf_transformation,[],[f13])).
% 35.53/5.00  
% 35.53/5.00  fof(f33,plain,(
% 35.53/5.00    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.53/5.00    inference(flattening,[],[f32])).
% 35.53/5.00  
% 35.53/5.00  fof(f64,plain,(
% 35.53/5.00    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.53/5.00    inference(cnf_transformation,[],[f33])).
% 35.53/5.00  
% 35.53/5.00  fof(f68,plain,(
% 35.53/5.00    v1_funct_2(sK2,sK0,sK1)),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f14,axiom,(
% 35.53/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 35.53/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.53/5.00  
% 35.53/5.00  fof(f34,plain,(
% 35.53/5.00    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 35.53/5.00    inference(ennf_transformation,[],[f14])).
% 35.53/5.00  
% 35.53/5.00  fof(f35,plain,(
% 35.53/5.00    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.53/5.00    inference(flattening,[],[f34])).
% 35.53/5.00  
% 35.53/5.00  fof(f65,plain,(
% 35.53/5.00    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.53/5.00    inference(cnf_transformation,[],[f35])).
% 35.53/5.00  
% 35.53/5.00  fof(f77,plain,(
% 35.53/5.00    k1_xboole_0 != sK1),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f78,plain,(
% 35.53/5.00    k2_funct_1(sK2) != sK3),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  fof(f75,plain,(
% 35.53/5.00    v2_funct_1(sK2)),
% 35.53/5.00    inference(cnf_transformation,[],[f42])).
% 35.53/5.00  
% 35.53/5.00  cnf(c_32,negated_conjecture,
% 35.53/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 35.53/5.00      inference(cnf_transformation,[],[f69]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1159,plain,
% 35.53/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_7,plain,
% 35.53/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 35.53/5.00      inference(cnf_transformation,[],[f50]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1176,plain,
% 35.53/5.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 35.53/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2198,plain,
% 35.53/5.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1159,c_1176]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_28,negated_conjecture,
% 35.53/5.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 35.53/5.00      inference(cnf_transformation,[],[f73]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2199,plain,
% 35.53/5.00      ( k2_relat_1(sK2) = sK1 ),
% 35.53/5.00      inference(light_normalisation,[status(thm)],[c_2198,c_28]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_29,negated_conjecture,
% 35.53/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 35.53/5.00      inference(cnf_transformation,[],[f72]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1162,plain,
% 35.53/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_16,plain,
% 35.53/5.00      ( ~ v1_funct_2(X0,X1,X2)
% 35.53/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | k1_relset_1(X1,X2,X0) = X1
% 35.53/5.00      | k1_xboole_0 = X2 ),
% 35.53/5.00      inference(cnf_transformation,[],[f54]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1169,plain,
% 35.53/5.00      ( k1_relset_1(X0,X1,X2) = X0
% 35.53/5.00      | k1_xboole_0 = X1
% 35.53/5.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.53/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2790,plain,
% 35.53/5.00      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 35.53/5.00      | sK0 = k1_xboole_0
% 35.53/5.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1162,c_1169]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_6,plain,
% 35.53/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 35.53/5.00      inference(cnf_transformation,[],[f49]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1177,plain,
% 35.53/5.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 35.53/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2329,plain,
% 35.53/5.00      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1162,c_1177]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2793,plain,
% 35.53/5.00      ( k1_relat_1(sK3) = sK1
% 35.53/5.00      | sK0 = k1_xboole_0
% 35.53/5.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 35.53/5.00      inference(demodulation,[status(thm)],[c_2790,c_2329]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_30,negated_conjecture,
% 35.53/5.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 35.53/5.00      inference(cnf_transformation,[],[f71]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_39,plain,
% 35.53/5.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_25,negated_conjecture,
% 35.53/5.00      ( k1_xboole_0 != sK0 ),
% 35.53/5.00      inference(cnf_transformation,[],[f76]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_657,plain,( X0 = X0 ),theory(equality) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_686,plain,
% 35.53/5.00      ( k1_xboole_0 = k1_xboole_0 ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_657]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_658,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1282,plain,
% 35.53/5.00      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_658]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1283,plain,
% 35.53/5.00      ( sK0 != k1_xboole_0
% 35.53/5.00      | k1_xboole_0 = sK0
% 35.53/5.00      | k1_xboole_0 != k1_xboole_0 ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_1282]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3022,plain,
% 35.53/5.00      ( k1_relat_1(sK3) = sK1 ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_2793,c_39,c_25,c_686,c_1283]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2,plain,
% 35.53/5.00      ( ~ v1_funct_1(X0)
% 35.53/5.00      | ~ v1_funct_1(X1)
% 35.53/5.00      | ~ v1_relat_1(X0)
% 35.53/5.00      | ~ v1_relat_1(X1)
% 35.53/5.00      | v2_funct_1(X1)
% 35.53/5.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 35.53/5.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 35.53/5.00      inference(cnf_transformation,[],[f46]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1181,plain,
% 35.53/5.00      ( k1_relat_1(X0) != k2_relat_1(X1)
% 35.53/5.00      | v1_funct_1(X1) != iProver_top
% 35.53/5.00      | v1_funct_1(X0) != iProver_top
% 35.53/5.00      | v1_relat_1(X1) != iProver_top
% 35.53/5.00      | v1_relat_1(X0) != iProver_top
% 35.53/5.00      | v2_funct_1(X0) = iProver_top
% 35.53/5.00      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3566,plain,
% 35.53/5.00      ( k2_relat_1(X0) != sK1
% 35.53/5.00      | v1_funct_1(X0) != iProver_top
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v1_relat_1(X0) != iProver_top
% 35.53/5.00      | v1_relat_1(sK3) != iProver_top
% 35.53/5.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) = iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_3022,c_1181]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_31,negated_conjecture,
% 35.53/5.00      ( v1_funct_1(sK3) ),
% 35.53/5.00      inference(cnf_transformation,[],[f70]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_38,plain,
% 35.53/5.00      ( v1_funct_1(sK3) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_40,plain,
% 35.53/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_5,plain,
% 35.53/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | v1_relat_1(X0) ),
% 35.53/5.00      inference(cnf_transformation,[],[f48]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1302,plain,
% 35.53/5.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.53/5.00      | v1_relat_1(sK3) ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1564,plain,
% 35.53/5.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.53/5.00      | v1_relat_1(sK3) ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_1302]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1565,plain,
% 35.53/5.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.53/5.00      | v1_relat_1(sK3) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9336,plain,
% 35.53/5.00      ( v1_relat_1(X0) != iProver_top
% 35.53/5.00      | k2_relat_1(X0) != sK1
% 35.53/5.00      | v1_funct_1(X0) != iProver_top
% 35.53/5.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) = iProver_top ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_3566,c_38,c_40,c_1565]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9337,plain,
% 35.53/5.00      ( k2_relat_1(X0) != sK1
% 35.53/5.00      | v1_funct_1(X0) != iProver_top
% 35.53/5.00      | v1_relat_1(X0) != iProver_top
% 35.53/5.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) = iProver_top ),
% 35.53/5.00      inference(renaming,[status(thm)],[c_9336]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9342,plain,
% 35.53/5.00      ( v1_funct_1(sK2) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) != iProver_top
% 35.53/5.00      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) = iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_2199,c_9337]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_19,plain,
% 35.53/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.53/5.00      | ~ v1_funct_1(X0)
% 35.53/5.00      | ~ v1_funct_1(X3)
% 35.53/5.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 35.53/5.00      inference(cnf_transformation,[],[f62]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1166,plain,
% 35.53/5.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 35.53/5.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 35.53/5.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.53/5.00      | v1_funct_1(X5) != iProver_top
% 35.53/5.00      | v1_funct_1(X4) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3419,plain,
% 35.53/5.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.53/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.53/5.00      | v1_funct_1(X2) != iProver_top
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1162,c_1166]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3611,plain,
% 35.53/5.00      ( v1_funct_1(X2) != iProver_top
% 35.53/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.53/5.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_3419,c_38]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3612,plain,
% 35.53/5.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.53/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.53/5.00      | v1_funct_1(X2) != iProver_top ),
% 35.53/5.00      inference(renaming,[status(thm)],[c_3611]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3619,plain,
% 35.53/5.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1159,c_3612]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9,plain,
% 35.53/5.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 35.53/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.53/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.53/5.00      | X3 = X2 ),
% 35.53/5.00      inference(cnf_transformation,[],[f51]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_27,negated_conjecture,
% 35.53/5.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 35.53/5.00      inference(cnf_transformation,[],[f74]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_385,plain,
% 35.53/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | X3 = X0
% 35.53/5.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 35.53/5.00      | k6_partfun1(sK0) != X3
% 35.53/5.00      | sK0 != X2
% 35.53/5.00      | sK0 != X1 ),
% 35.53/5.00      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_386,plain,
% 35.53/5.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.53/5.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.53/5.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.53/5.00      inference(unflattening,[status(thm)],[c_385]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_10,plain,
% 35.53/5.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 35.53/5.00      inference(cnf_transformation,[],[f82]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_394,plain,
% 35.53/5.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.53/5.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.53/5.00      inference(forward_subsumption_resolution,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_386,c_10]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1155,plain,
% 35.53/5.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.53/5.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_34,negated_conjecture,
% 35.53/5.00      ( v1_funct_1(sK2) ),
% 35.53/5.00      inference(cnf_transformation,[],[f67]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_17,plain,
% 35.53/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.53/5.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 35.53/5.00      | ~ v1_funct_1(X0)
% 35.53/5.00      | ~ v1_funct_1(X3) ),
% 35.53/5.00      inference(cnf_transformation,[],[f61]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1417,plain,
% 35.53/5.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.53/5.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.53/5.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.53/5.00      | ~ v1_funct_1(sK3)
% 35.53/5.00      | ~ v1_funct_1(sK2) ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_17]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1926,plain,
% 35.53/5.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_1155,c_34,c_32,c_31,c_29,c_394,c_1417]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3620,plain,
% 35.53/5.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top ),
% 35.53/5.00      inference(light_normalisation,[status(thm)],[c_3619,c_1926]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_35,plain,
% 35.53/5.00      ( v1_funct_1(sK2) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3825,plain,
% 35.53/5.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_3620,c_35]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9344,plain,
% 35.53/5.00      ( v1_funct_1(sK2) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) != iProver_top
% 35.53/5.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) = iProver_top ),
% 35.53/5.00      inference(light_normalisation,[status(thm)],[c_9342,c_3825]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_37,plain,
% 35.53/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1936,plain,
% 35.53/5.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.53/5.00      | v1_relat_1(sK2) ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_5]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1937,plain,
% 35.53/5.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_0,plain,
% 35.53/5.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 35.53/5.00      inference(cnf_transformation,[],[f79]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_4316,plain,
% 35.53/5.00      ( v2_funct_1(k6_partfun1(sK0)) ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_0]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_4317,plain,
% 35.53/5.00      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_4316]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9787,plain,
% 35.53/5.00      ( v2_funct_1(sK3) = iProver_top ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_9344,c_35,c_37,c_1937,c_4317]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_4,plain,
% 35.53/5.00      ( ~ v1_funct_1(X0)
% 35.53/5.00      | ~ v1_funct_1(X1)
% 35.53/5.00      | ~ v1_relat_1(X0)
% 35.53/5.00      | ~ v1_relat_1(X1)
% 35.53/5.00      | ~ v2_funct_1(X1)
% 35.53/5.00      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 35.53/5.00      | k2_funct_1(X1) = X0
% 35.53/5.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 35.53/5.00      inference(cnf_transformation,[],[f81]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1179,plain,
% 35.53/5.00      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 35.53/5.00      | k2_funct_1(X1) = X0
% 35.53/5.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 35.53/5.00      | v1_funct_1(X0) != iProver_top
% 35.53/5.00      | v1_funct_1(X1) != iProver_top
% 35.53/5.00      | v1_relat_1(X0) != iProver_top
% 35.53/5.00      | v1_relat_1(X1) != iProver_top
% 35.53/5.00      | v2_funct_1(X1) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_4015,plain,
% 35.53/5.00      ( k2_funct_1(sK3) = sK2
% 35.53/5.00      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 35.53/5.00      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top
% 35.53/5.00      | v1_relat_1(sK3) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) != iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_3825,c_1179]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2197,plain,
% 35.53/5.00      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1162,c_1176]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_20,plain,
% 35.53/5.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 35.53/5.00      | ~ v1_funct_2(X3,X1,X0)
% 35.53/5.00      | ~ v1_funct_2(X2,X0,X1)
% 35.53/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 35.53/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.53/5.00      | ~ v1_funct_1(X2)
% 35.53/5.00      | ~ v1_funct_1(X3)
% 35.53/5.00      | k2_relset_1(X1,X0,X3) = X0 ),
% 35.53/5.00      inference(cnf_transformation,[],[f64]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_398,plain,
% 35.53/5.00      ( ~ v1_funct_2(X0,X1,X2)
% 35.53/5.00      | ~ v1_funct_2(X3,X2,X1)
% 35.53/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 35.53/5.00      | ~ v1_funct_1(X3)
% 35.53/5.00      | ~ v1_funct_1(X0)
% 35.53/5.00      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.53/5.00      | k2_relset_1(X2,X1,X3) = X1
% 35.53/5.00      | k6_partfun1(X1) != k6_partfun1(sK0)
% 35.53/5.00      | sK0 != X1 ),
% 35.53/5.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_399,plain,
% 35.53/5.00      ( ~ v1_funct_2(X0,X1,sK0)
% 35.53/5.00      | ~ v1_funct_2(X2,sK0,X1)
% 35.53/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 35.53/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 35.53/5.00      | ~ v1_funct_1(X2)
% 35.53/5.00      | ~ v1_funct_1(X0)
% 35.53/5.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.53/5.00      | k2_relset_1(X1,sK0,X0) = sK0
% 35.53/5.00      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 35.53/5.00      inference(unflattening,[status(thm)],[c_398]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_483,plain,
% 35.53/5.00      ( ~ v1_funct_2(X0,X1,sK0)
% 35.53/5.00      | ~ v1_funct_2(X2,sK0,X1)
% 35.53/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 35.53/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 35.53/5.00      | ~ v1_funct_1(X0)
% 35.53/5.00      | ~ v1_funct_1(X2)
% 35.53/5.00      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.53/5.00      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 35.53/5.00      inference(equality_resolution_simp,[status(thm)],[c_399]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1154,plain,
% 35.53/5.00      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.53/5.00      | k2_relset_1(X0,sK0,X2) = sK0
% 35.53/5.00      | v1_funct_2(X2,X0,sK0) != iProver_top
% 35.53/5.00      | v1_funct_2(X1,sK0,X0) != iProver_top
% 35.53/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 35.53/5.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 35.53/5.00      | v1_funct_1(X2) != iProver_top
% 35.53/5.00      | v1_funct_1(X1) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1610,plain,
% 35.53/5.00      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 35.53/5.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 35.53/5.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 35.53/5.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.53/5.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top ),
% 35.53/5.00      inference(equality_resolution,[status(thm)],[c_1154]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_33,negated_conjecture,
% 35.53/5.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 35.53/5.00      inference(cnf_transformation,[],[f68]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_36,plain,
% 35.53/5.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1933,plain,
% 35.53/5.00      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_1610,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2200,plain,
% 35.53/5.00      ( k2_relat_1(sK3) = sK0 ),
% 35.53/5.00      inference(light_normalisation,[status(thm)],[c_2197,c_1933]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_4016,plain,
% 35.53/5.00      ( k2_funct_1(sK3) = sK2
% 35.53/5.00      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 35.53/5.00      | sK1 != sK1
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top
% 35.53/5.00      | v1_relat_1(sK3) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) != iProver_top ),
% 35.53/5.00      inference(light_normalisation,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_4015,c_2199,c_2200,c_3022]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_4017,plain,
% 35.53/5.00      ( k2_funct_1(sK3) = sK2
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top
% 35.53/5.00      | v1_relat_1(sK3) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) != iProver_top ),
% 35.53/5.00      inference(equality_resolution_simp,[status(thm)],[c_4016]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_4583,plain,
% 35.53/5.00      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_4017,c_35,c_37,c_38,c_40,c_1565,c_1937]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9792,plain,
% 35.53/5.00      ( k2_funct_1(sK3) = sK2 ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_9787,c_4583]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_22,plain,
% 35.53/5.00      ( ~ v1_funct_2(X0,X1,X2)
% 35.53/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.53/5.00      | ~ v1_funct_1(X0)
% 35.53/5.00      | ~ v2_funct_1(X0)
% 35.53/5.00      | k2_relset_1(X1,X2,X0) != X2
% 35.53/5.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 35.53/5.00      | k1_xboole_0 = X2 ),
% 35.53/5.00      inference(cnf_transformation,[],[f65]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1164,plain,
% 35.53/5.00      ( k2_relset_1(X0,X1,X2) != X1
% 35.53/5.00      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 35.53/5.00      | k1_xboole_0 = X1
% 35.53/5.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.53/5.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.53/5.00      | v1_funct_1(X2) != iProver_top
% 35.53/5.00      | v2_funct_1(X2) != iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2692,plain,
% 35.53/5.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 35.53/5.00      | sK0 = k1_xboole_0
% 35.53/5.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 35.53/5.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v2_funct_1(sK3) != iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1933,c_1164]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_3108,plain,
% 35.53/5.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 35.53/5.00      | v2_funct_1(sK3) != iProver_top ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_2692,c_38,c_39,c_40,c_25,c_686,c_1283]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9793,plain,
% 35.53/5.00      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_9787,c_3108]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_9794,plain,
% 35.53/5.00      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 35.53/5.00      inference(demodulation,[status(thm)],[c_9792,c_9793]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_107664,plain,
% 35.53/5.00      ( k2_funct_1(sK2) = sK3
% 35.53/5.00      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 35.53/5.00      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top
% 35.53/5.00      | v1_relat_1(sK3) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) != iProver_top
% 35.53/5.00      | v2_funct_1(sK2) != iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_9794,c_1179]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2791,plain,
% 35.53/5.00      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 35.53/5.00      | sK1 = k1_xboole_0
% 35.53/5.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1159,c_1169]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2330,plain,
% 35.53/5.00      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 35.53/5.00      inference(superposition,[status(thm)],[c_1159,c_1177]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2792,plain,
% 35.53/5.00      ( k1_relat_1(sK2) = sK0
% 35.53/5.00      | sK1 = k1_xboole_0
% 35.53/5.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 35.53/5.00      inference(demodulation,[status(thm)],[c_2791,c_2330]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_24,negated_conjecture,
% 35.53/5.00      ( k1_xboole_0 != sK1 ),
% 35.53/5.00      inference(cnf_transformation,[],[f77]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1254,plain,
% 35.53/5.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_658]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_1255,plain,
% 35.53/5.00      ( sK1 != k1_xboole_0
% 35.53/5.00      | k1_xboole_0 = sK1
% 35.53/5.00      | k1_xboole_0 != k1_xboole_0 ),
% 35.53/5.00      inference(instantiation,[status(thm)],[c_1254]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_2916,plain,
% 35.53/5.00      ( k1_relat_1(sK2) = sK0 ),
% 35.53/5.00      inference(global_propositional_subsumption,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_2792,c_36,c_24,c_686,c_1255]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_107665,plain,
% 35.53/5.00      ( k2_funct_1(sK2) = sK3
% 35.53/5.00      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 35.53/5.00      | sK0 != sK0
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top
% 35.53/5.00      | v1_relat_1(sK3) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) != iProver_top
% 35.53/5.00      | v2_funct_1(sK2) != iProver_top ),
% 35.53/5.00      inference(light_normalisation,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_107664,c_2199,c_2200,c_2916]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_107666,plain,
% 35.53/5.00      ( k2_funct_1(sK2) = sK3
% 35.53/5.00      | v1_funct_1(sK3) != iProver_top
% 35.53/5.00      | v1_funct_1(sK2) != iProver_top
% 35.53/5.00      | v1_relat_1(sK3) != iProver_top
% 35.53/5.00      | v1_relat_1(sK2) != iProver_top
% 35.53/5.00      | v2_funct_1(sK2) != iProver_top ),
% 35.53/5.00      inference(equality_resolution_simp,[status(thm)],[c_107665]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_23,negated_conjecture,
% 35.53/5.00      ( k2_funct_1(sK2) != sK3 ),
% 35.53/5.00      inference(cnf_transformation,[],[f78]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_26,negated_conjecture,
% 35.53/5.00      ( v2_funct_1(sK2) ),
% 35.53/5.00      inference(cnf_transformation,[],[f75]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(c_42,plain,
% 35.53/5.00      ( v2_funct_1(sK2) = iProver_top ),
% 35.53/5.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 35.53/5.00  
% 35.53/5.00  cnf(contradiction,plain,
% 35.53/5.00      ( $false ),
% 35.53/5.00      inference(minisat,
% 35.53/5.00                [status(thm)],
% 35.53/5.00                [c_107666,c_1937,c_1565,c_23,c_42,c_40,c_38,c_37,c_35]) ).
% 35.53/5.00  
% 35.53/5.00  
% 35.53/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.53/5.00  
% 35.53/5.00  ------                               Statistics
% 35.53/5.00  
% 35.53/5.00  ------ General
% 35.53/5.00  
% 35.53/5.00  abstr_ref_over_cycles:                  0
% 35.53/5.00  abstr_ref_under_cycles:                 0
% 35.53/5.00  gc_basic_clause_elim:                   0
% 35.53/5.00  forced_gc_time:                         0
% 35.53/5.00  parsing_time:                           0.014
% 35.53/5.00  unif_index_cands_time:                  0.
% 35.53/5.00  unif_index_add_time:                    0.
% 35.53/5.00  orderings_time:                         0.
% 35.53/5.00  out_proof_time:                         0.023
% 35.53/5.00  total_time:                             4.324
% 35.53/5.00  num_of_symbols:                         52
% 35.53/5.00  num_of_terms:                           113856
% 35.53/5.00  
% 35.53/5.00  ------ Preprocessing
% 35.53/5.00  
% 35.53/5.00  num_of_splits:                          0
% 35.53/5.00  num_of_split_atoms:                     0
% 35.53/5.00  num_of_reused_defs:                     0
% 35.53/5.00  num_eq_ax_congr_red:                    12
% 35.53/5.00  num_of_sem_filtered_clauses:            1
% 35.53/5.00  num_of_subtypes:                        0
% 35.53/5.00  monotx_restored_types:                  0
% 35.53/5.00  sat_num_of_epr_types:                   0
% 35.53/5.00  sat_num_of_non_cyclic_types:            0
% 35.53/5.00  sat_guarded_non_collapsed_types:        0
% 35.53/5.00  num_pure_diseq_elim:                    0
% 35.53/5.00  simp_replaced_by:                       0
% 35.53/5.00  res_preprocessed:                       168
% 35.53/5.00  prep_upred:                             0
% 35.53/5.00  prep_unflattend:                        12
% 35.53/5.00  smt_new_axioms:                         0
% 35.53/5.00  pred_elim_cands:                        5
% 35.53/5.00  pred_elim:                              1
% 35.53/5.00  pred_elim_cl:                           1
% 35.53/5.00  pred_elim_cycles:                       3
% 35.53/5.00  merged_defs:                            0
% 35.53/5.00  merged_defs_ncl:                        0
% 35.53/5.00  bin_hyper_res:                          0
% 35.53/5.00  prep_cycles:                            4
% 35.53/5.00  pred_elim_time:                         0.005
% 35.53/5.00  splitting_time:                         0.
% 35.53/5.00  sem_filter_time:                        0.
% 35.53/5.00  monotx_time:                            0.
% 35.53/5.00  subtype_inf_time:                       0.
% 35.53/5.00  
% 35.53/5.00  ------ Problem properties
% 35.53/5.00  
% 35.53/5.00  clauses:                                34
% 35.53/5.00  conjectures:                            11
% 35.53/5.00  epr:                                    7
% 35.53/5.00  horn:                                   28
% 35.53/5.00  ground:                                 12
% 35.53/5.00  unary:                                  14
% 35.53/5.00  binary:                                 4
% 35.53/5.00  lits:                                   110
% 35.53/5.00  lits_eq:                                32
% 35.53/5.00  fd_pure:                                0
% 35.53/5.00  fd_pseudo:                              0
% 35.53/5.00  fd_cond:                                5
% 35.53/5.00  fd_pseudo_cond:                         1
% 35.53/5.00  ac_symbols:                             0
% 35.53/5.00  
% 35.53/5.00  ------ Propositional Solver
% 35.53/5.00  
% 35.53/5.00  prop_solver_calls:                      49
% 35.53/5.00  prop_fast_solver_calls:                 6648
% 35.53/5.00  smt_solver_calls:                       0
% 35.53/5.00  smt_fast_solver_calls:                  0
% 35.53/5.00  prop_num_of_clauses:                    47466
% 35.53/5.00  prop_preprocess_simplified:             85321
% 35.53/5.00  prop_fo_subsumed:                       1965
% 35.53/5.00  prop_solver_time:                       0.
% 35.53/5.00  smt_solver_time:                        0.
% 35.53/5.00  smt_fast_solver_time:                   0.
% 35.53/5.00  prop_fast_solver_time:                  0.
% 35.53/5.00  prop_unsat_core_time:                   0.008
% 35.53/5.00  
% 35.53/5.00  ------ QBF
% 35.53/5.00  
% 35.53/5.00  qbf_q_res:                              0
% 35.53/5.00  qbf_num_tautologies:                    0
% 35.53/5.00  qbf_prep_cycles:                        0
% 35.53/5.00  
% 35.53/5.00  ------ BMC1
% 35.53/5.00  
% 35.53/5.00  bmc1_current_bound:                     -1
% 35.53/5.00  bmc1_last_solved_bound:                 -1
% 35.53/5.00  bmc1_unsat_core_size:                   -1
% 35.53/5.00  bmc1_unsat_core_parents_size:           -1
% 35.53/5.00  bmc1_merge_next_fun:                    0
% 35.53/5.00  bmc1_unsat_core_clauses_time:           0.
% 35.53/5.00  
% 35.53/5.00  ------ Instantiation
% 35.53/5.00  
% 35.53/5.00  inst_num_of_clauses:                    8255
% 35.53/5.00  inst_num_in_passive:                    3396
% 35.53/5.00  inst_num_in_active:                     6096
% 35.53/5.00  inst_num_in_unprocessed:                1526
% 35.53/5.00  inst_num_of_loops:                      6399
% 35.53/5.00  inst_num_of_learning_restarts:          1
% 35.53/5.00  inst_num_moves_active_passive:          296
% 35.53/5.00  inst_lit_activity:                      0
% 35.53/5.00  inst_lit_activity_moves:                3
% 35.53/5.00  inst_num_tautologies:                   0
% 35.53/5.00  inst_num_prop_implied:                  0
% 35.53/5.00  inst_num_existing_simplified:           0
% 35.53/5.00  inst_num_eq_res_simplified:             0
% 35.53/5.00  inst_num_child_elim:                    0
% 35.53/5.00  inst_num_of_dismatching_blockings:      8705
% 35.53/5.00  inst_num_of_non_proper_insts:           14282
% 35.53/5.00  inst_num_of_duplicates:                 0
% 35.53/5.00  inst_inst_num_from_inst_to_res:         0
% 35.53/5.00  inst_dismatching_checking_time:         0.
% 35.53/5.00  
% 35.53/5.00  ------ Resolution
% 35.53/5.00  
% 35.53/5.00  res_num_of_clauses:                     49
% 35.53/5.00  res_num_in_passive:                     49
% 35.53/5.00  res_num_in_active:                      0
% 35.53/5.00  res_num_of_loops:                       172
% 35.53/5.00  res_forward_subset_subsumed:            774
% 35.53/5.00  res_backward_subset_subsumed:           6
% 35.53/5.00  res_forward_subsumed:                   0
% 35.53/5.00  res_backward_subsumed:                  0
% 35.53/5.00  res_forward_subsumption_resolution:     2
% 35.53/5.00  res_backward_subsumption_resolution:    0
% 35.53/5.00  res_clause_to_clause_subsumption:       14390
% 35.53/5.00  res_orphan_elimination:                 0
% 35.53/5.00  res_tautology_del:                      642
% 35.53/5.00  res_num_eq_res_simplified:              1
% 35.53/5.00  res_num_sel_changes:                    0
% 35.53/5.00  res_moves_from_active_to_pass:          0
% 35.53/5.00  
% 35.53/5.00  ------ Superposition
% 35.53/5.00  
% 35.53/5.00  sup_time_total:                         0.
% 35.53/5.00  sup_time_generating:                    0.
% 35.53/5.00  sup_time_sim_full:                      0.
% 35.53/5.00  sup_time_sim_immed:                     0.
% 35.53/5.00  
% 35.53/5.00  sup_num_of_clauses:                     6608
% 35.53/5.00  sup_num_in_active:                      1246
% 35.53/5.00  sup_num_in_passive:                     5362
% 35.53/5.00  sup_num_of_loops:                       1279
% 35.53/5.00  sup_fw_superposition:                   3053
% 35.53/5.00  sup_bw_superposition:                   3956
% 35.53/5.00  sup_immediate_simplified:               1914
% 35.53/5.00  sup_given_eliminated:                   1
% 35.53/5.00  comparisons_done:                       0
% 35.53/5.00  comparisons_avoided:                    1
% 35.53/5.00  
% 35.53/5.00  ------ Simplifications
% 35.53/5.00  
% 35.53/5.00  
% 35.53/5.00  sim_fw_subset_subsumed:                 98
% 35.53/5.00  sim_bw_subset_subsumed:                 95
% 35.53/5.00  sim_fw_subsumed:                        35
% 35.53/5.00  sim_bw_subsumed:                        41
% 35.53/5.00  sim_fw_subsumption_res:                 0
% 35.53/5.00  sim_bw_subsumption_res:                 0
% 35.53/5.00  sim_tautology_del:                      0
% 35.53/5.00  sim_eq_tautology_del:                   85
% 35.53/5.00  sim_eq_res_simp:                        2
% 35.53/5.00  sim_fw_demodulated:                     151
% 35.53/5.00  sim_bw_demodulated:                     17
% 35.53/5.00  sim_light_normalised:                   2213
% 35.53/5.00  sim_joinable_taut:                      0
% 35.53/5.00  sim_joinable_simp:                      0
% 35.53/5.00  sim_ac_normalised:                      0
% 35.53/5.00  sim_smt_subsumption:                    0
% 35.53/5.00  
%------------------------------------------------------------------------------
