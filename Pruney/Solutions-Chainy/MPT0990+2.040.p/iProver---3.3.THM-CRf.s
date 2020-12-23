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
% DateTime   : Thu Dec  3 12:03:04 EST 2020

% Result     : Theorem 35.68s
% Output     : CNFRefutation 35.68s
% Verified   : 
% Statistics : Number of formulae       :  175 (1390 expanded)
%              Number of clauses        :  104 ( 404 expanded)
%              Number of leaves         :   19 ( 361 expanded)
%              Depth                    :   23
%              Number of atoms          :  706 (11998 expanded)
%              Number of equality atoms :  362 (4445 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f1])).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f62,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
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
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1113,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1130,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2114,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1113,c_1130])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2115,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2114,c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1124,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2679,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_1124])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1131,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2261,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1116,c_1131])).

cnf(c_2682,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2679,c_2261])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_638,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_665,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_639,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1234,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1235,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2912,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2682,c_38,c_24,c_665,c_1235])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1136,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3418,plain,
    ( k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_1136])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1249,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1499,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_1500,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_9542,plain,
    ( v1_funct_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_37,c_39,c_1500])).

cnf(c_9543,plain,
    ( k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_9542])).

cnf(c_9548,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2115,c_9543])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1120,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3342,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1116,c_1120])).

cnf(c_3549,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3342,c_37])).

cnf(c_3550,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3549])).

cnf(c_3557,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_3550])).

cnf(c_8,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_26])).

cnf(c_374,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_382,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_374,c_17])).

cnf(c_1109,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1364,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1705,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1109,c_33,c_31,c_30,c_28,c_382,c_1364])).

cnf(c_3558,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3557,c_1705])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3758,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3558,c_34])).

cnf(c_9550,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9548,c_3758])).

cnf(c_1132,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1985,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1132])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4162,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4163,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4162])).

cnf(c_9710,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9550,c_34,c_1985,c_4163])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1133,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4006,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3758,c_1133])).

cnf(c_2113,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1116,c_1130])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_386,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_387,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_470,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_387])).

cnf(c_1108,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_1545,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1108])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1848,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1545,c_34,c_35,c_36,c_37,c_38,c_39])).

cnf(c_2116,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2113,c_1848])).

cnf(c_4007,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4006,c_2115,c_2116,c_2912])).

cnf(c_4008,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4007])).

cnf(c_4556,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4008,c_34,c_37,c_39,c_1500,c_1985])).

cnf(c_9715,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_9710,c_4556])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1118,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2625,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1118])).

cnf(c_3019,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2625,c_37,c_38,c_39,c_24,c_665,c_1235])).

cnf(c_9716,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_9710,c_3019])).

cnf(c_9717,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_9715,c_9716])).

cnf(c_115656,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9717,c_1133])).

cnf(c_2680,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1124])).

cnf(c_2262,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1113,c_1131])).

cnf(c_2681,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2680,c_2262])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1206,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1207,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1206])).

cnf(c_2796,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2681,c_35,c_23,c_665,c_1207])).

cnf(c_115657,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_115656,c_2115,c_2116,c_2796])).

cnf(c_115658,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_115657])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_115658,c_1985,c_1500,c_22,c_41,c_39,c_37,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:42:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.68/4.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.68/4.97  
% 35.68/4.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.68/4.97  
% 35.68/4.97  ------  iProver source info
% 35.68/4.97  
% 35.68/4.97  git: date: 2020-06-30 10:37:57 +0100
% 35.68/4.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.68/4.97  git: non_committed_changes: false
% 35.68/4.97  git: last_make_outside_of_git: false
% 35.68/4.97  
% 35.68/4.97  ------ 
% 35.68/4.97  
% 35.68/4.97  ------ Input Options
% 35.68/4.97  
% 35.68/4.97  --out_options                           all
% 35.68/4.97  --tptp_safe_out                         true
% 35.68/4.97  --problem_path                          ""
% 35.68/4.97  --include_path                          ""
% 35.68/4.97  --clausifier                            res/vclausify_rel
% 35.68/4.97  --clausifier_options                    ""
% 35.68/4.97  --stdin                                 false
% 35.68/4.97  --stats_out                             all
% 35.68/4.97  
% 35.68/4.97  ------ General Options
% 35.68/4.97  
% 35.68/4.97  --fof                                   false
% 35.68/4.97  --time_out_real                         305.
% 35.68/4.97  --time_out_virtual                      -1.
% 35.68/4.97  --symbol_type_check                     false
% 35.68/4.97  --clausify_out                          false
% 35.68/4.97  --sig_cnt_out                           false
% 35.68/4.97  --trig_cnt_out                          false
% 35.68/4.97  --trig_cnt_out_tolerance                1.
% 35.68/4.97  --trig_cnt_out_sk_spl                   false
% 35.68/4.97  --abstr_cl_out                          false
% 35.68/4.97  
% 35.68/4.97  ------ Global Options
% 35.68/4.97  
% 35.68/4.97  --schedule                              default
% 35.68/4.97  --add_important_lit                     false
% 35.68/4.97  --prop_solver_per_cl                    1000
% 35.68/4.97  --min_unsat_core                        false
% 35.68/4.97  --soft_assumptions                      false
% 35.68/4.97  --soft_lemma_size                       3
% 35.68/4.97  --prop_impl_unit_size                   0
% 35.68/4.97  --prop_impl_unit                        []
% 35.68/4.97  --share_sel_clauses                     true
% 35.68/4.97  --reset_solvers                         false
% 35.68/4.97  --bc_imp_inh                            [conj_cone]
% 35.68/4.97  --conj_cone_tolerance                   3.
% 35.68/4.97  --extra_neg_conj                        none
% 35.68/4.97  --large_theory_mode                     true
% 35.68/4.97  --prolific_symb_bound                   200
% 35.68/4.97  --lt_threshold                          2000
% 35.68/4.97  --clause_weak_htbl                      true
% 35.68/4.97  --gc_record_bc_elim                     false
% 35.68/4.97  
% 35.68/4.97  ------ Preprocessing Options
% 35.68/4.97  
% 35.68/4.97  --preprocessing_flag                    true
% 35.68/4.97  --time_out_prep_mult                    0.1
% 35.68/4.97  --splitting_mode                        input
% 35.68/4.97  --splitting_grd                         true
% 35.68/4.97  --splitting_cvd                         false
% 35.68/4.97  --splitting_cvd_svl                     false
% 35.68/4.97  --splitting_nvd                         32
% 35.68/4.97  --sub_typing                            true
% 35.68/4.97  --prep_gs_sim                           true
% 35.68/4.97  --prep_unflatten                        true
% 35.68/4.97  --prep_res_sim                          true
% 35.68/4.97  --prep_upred                            true
% 35.68/4.97  --prep_sem_filter                       exhaustive
% 35.68/4.97  --prep_sem_filter_out                   false
% 35.68/4.97  --pred_elim                             true
% 35.68/4.97  --res_sim_input                         true
% 35.68/4.97  --eq_ax_congr_red                       true
% 35.68/4.97  --pure_diseq_elim                       true
% 35.68/4.97  --brand_transform                       false
% 35.68/4.97  --non_eq_to_eq                          false
% 35.68/4.97  --prep_def_merge                        true
% 35.68/4.97  --prep_def_merge_prop_impl              false
% 35.68/4.97  --prep_def_merge_mbd                    true
% 35.68/4.97  --prep_def_merge_tr_red                 false
% 35.68/4.97  --prep_def_merge_tr_cl                  false
% 35.68/4.97  --smt_preprocessing                     true
% 35.68/4.97  --smt_ac_axioms                         fast
% 35.68/4.97  --preprocessed_out                      false
% 35.68/4.97  --preprocessed_stats                    false
% 35.68/4.97  
% 35.68/4.97  ------ Abstraction refinement Options
% 35.68/4.97  
% 35.68/4.97  --abstr_ref                             []
% 35.68/4.97  --abstr_ref_prep                        false
% 35.68/4.97  --abstr_ref_until_sat                   false
% 35.68/4.97  --abstr_ref_sig_restrict                funpre
% 35.68/4.97  --abstr_ref_af_restrict_to_split_sk     false
% 35.68/4.97  --abstr_ref_under                       []
% 35.68/4.97  
% 35.68/4.97  ------ SAT Options
% 35.68/4.97  
% 35.68/4.97  --sat_mode                              false
% 35.68/4.97  --sat_fm_restart_options                ""
% 35.68/4.97  --sat_gr_def                            false
% 35.68/4.97  --sat_epr_types                         true
% 35.68/4.97  --sat_non_cyclic_types                  false
% 35.68/4.97  --sat_finite_models                     false
% 35.68/4.97  --sat_fm_lemmas                         false
% 35.68/4.97  --sat_fm_prep                           false
% 35.68/4.97  --sat_fm_uc_incr                        true
% 35.68/4.97  --sat_out_model                         small
% 35.68/4.97  --sat_out_clauses                       false
% 35.68/4.97  
% 35.68/4.97  ------ QBF Options
% 35.68/4.97  
% 35.68/4.97  --qbf_mode                              false
% 35.68/4.97  --qbf_elim_univ                         false
% 35.68/4.97  --qbf_dom_inst                          none
% 35.68/4.97  --qbf_dom_pre_inst                      false
% 35.68/4.97  --qbf_sk_in                             false
% 35.68/4.97  --qbf_pred_elim                         true
% 35.68/4.97  --qbf_split                             512
% 35.68/4.97  
% 35.68/4.97  ------ BMC1 Options
% 35.68/4.97  
% 35.68/4.97  --bmc1_incremental                      false
% 35.68/4.97  --bmc1_axioms                           reachable_all
% 35.68/4.97  --bmc1_min_bound                        0
% 35.68/4.97  --bmc1_max_bound                        -1
% 35.68/4.97  --bmc1_max_bound_default                -1
% 35.68/4.97  --bmc1_symbol_reachability              true
% 35.68/4.97  --bmc1_property_lemmas                  false
% 35.68/4.97  --bmc1_k_induction                      false
% 35.68/4.97  --bmc1_non_equiv_states                 false
% 35.68/4.97  --bmc1_deadlock                         false
% 35.68/4.97  --bmc1_ucm                              false
% 35.68/4.97  --bmc1_add_unsat_core                   none
% 35.68/4.97  --bmc1_unsat_core_children              false
% 35.68/4.97  --bmc1_unsat_core_extrapolate_axioms    false
% 35.68/4.97  --bmc1_out_stat                         full
% 35.68/4.97  --bmc1_ground_init                      false
% 35.68/4.97  --bmc1_pre_inst_next_state              false
% 35.68/4.97  --bmc1_pre_inst_state                   false
% 35.68/4.97  --bmc1_pre_inst_reach_state             false
% 35.68/4.97  --bmc1_out_unsat_core                   false
% 35.68/4.97  --bmc1_aig_witness_out                  false
% 35.68/4.97  --bmc1_verbose                          false
% 35.68/4.97  --bmc1_dump_clauses_tptp                false
% 35.68/4.97  --bmc1_dump_unsat_core_tptp             false
% 35.68/4.97  --bmc1_dump_file                        -
% 35.68/4.97  --bmc1_ucm_expand_uc_limit              128
% 35.68/4.97  --bmc1_ucm_n_expand_iterations          6
% 35.68/4.97  --bmc1_ucm_extend_mode                  1
% 35.68/4.97  --bmc1_ucm_init_mode                    2
% 35.68/4.97  --bmc1_ucm_cone_mode                    none
% 35.68/4.97  --bmc1_ucm_reduced_relation_type        0
% 35.68/4.97  --bmc1_ucm_relax_model                  4
% 35.68/4.97  --bmc1_ucm_full_tr_after_sat            true
% 35.68/4.97  --bmc1_ucm_expand_neg_assumptions       false
% 35.68/4.97  --bmc1_ucm_layered_model                none
% 35.68/4.97  --bmc1_ucm_max_lemma_size               10
% 35.68/4.97  
% 35.68/4.97  ------ AIG Options
% 35.68/4.97  
% 35.68/4.97  --aig_mode                              false
% 35.68/4.97  
% 35.68/4.97  ------ Instantiation Options
% 35.68/4.97  
% 35.68/4.97  --instantiation_flag                    true
% 35.68/4.97  --inst_sos_flag                         true
% 35.68/4.97  --inst_sos_phase                        true
% 35.68/4.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.68/4.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.68/4.97  --inst_lit_sel_side                     num_symb
% 35.68/4.97  --inst_solver_per_active                1400
% 35.68/4.97  --inst_solver_calls_frac                1.
% 35.68/4.97  --inst_passive_queue_type               priority_queues
% 35.68/4.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.68/4.97  --inst_passive_queues_freq              [25;2]
% 35.68/4.97  --inst_dismatching                      true
% 35.68/4.97  --inst_eager_unprocessed_to_passive     true
% 35.68/4.97  --inst_prop_sim_given                   true
% 35.68/4.97  --inst_prop_sim_new                     false
% 35.68/4.97  --inst_subs_new                         false
% 35.68/4.97  --inst_eq_res_simp                      false
% 35.68/4.97  --inst_subs_given                       false
% 35.68/4.97  --inst_orphan_elimination               true
% 35.68/4.97  --inst_learning_loop_flag               true
% 35.68/4.97  --inst_learning_start                   3000
% 35.68/4.97  --inst_learning_factor                  2
% 35.68/4.97  --inst_start_prop_sim_after_learn       3
% 35.68/4.97  --inst_sel_renew                        solver
% 35.68/4.97  --inst_lit_activity_flag                true
% 35.68/4.97  --inst_restr_to_given                   false
% 35.68/4.97  --inst_activity_threshold               500
% 35.68/4.97  --inst_out_proof                        true
% 35.68/4.97  
% 35.68/4.97  ------ Resolution Options
% 35.68/4.97  
% 35.68/4.97  --resolution_flag                       true
% 35.68/4.97  --res_lit_sel                           adaptive
% 35.68/4.97  --res_lit_sel_side                      none
% 35.68/4.97  --res_ordering                          kbo
% 35.68/4.97  --res_to_prop_solver                    active
% 35.68/4.97  --res_prop_simpl_new                    false
% 35.68/4.97  --res_prop_simpl_given                  true
% 35.68/4.97  --res_passive_queue_type                priority_queues
% 35.68/4.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.68/4.97  --res_passive_queues_freq               [15;5]
% 35.68/4.97  --res_forward_subs                      full
% 35.68/4.97  --res_backward_subs                     full
% 35.68/4.97  --res_forward_subs_resolution           true
% 35.68/4.97  --res_backward_subs_resolution          true
% 35.68/4.97  --res_orphan_elimination                true
% 35.68/4.97  --res_time_limit                        2.
% 35.68/4.97  --res_out_proof                         true
% 35.68/4.97  
% 35.68/4.97  ------ Superposition Options
% 35.68/4.97  
% 35.68/4.97  --superposition_flag                    true
% 35.68/4.97  --sup_passive_queue_type                priority_queues
% 35.68/4.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.68/4.97  --sup_passive_queues_freq               [8;1;4]
% 35.68/4.97  --demod_completeness_check              fast
% 35.68/4.97  --demod_use_ground                      true
% 35.68/4.97  --sup_to_prop_solver                    passive
% 35.68/4.97  --sup_prop_simpl_new                    true
% 35.68/4.97  --sup_prop_simpl_given                  true
% 35.68/4.97  --sup_fun_splitting                     true
% 35.68/4.97  --sup_smt_interval                      50000
% 35.68/4.97  
% 35.68/4.97  ------ Superposition Simplification Setup
% 35.68/4.97  
% 35.68/4.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.68/4.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.68/4.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.68/4.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.68/4.97  --sup_full_triv                         [TrivRules;PropSubs]
% 35.68/4.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.68/4.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.68/4.97  --sup_immed_triv                        [TrivRules]
% 35.68/4.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/4.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/4.97  --sup_immed_bw_main                     []
% 35.68/4.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.68/4.97  --sup_input_triv                        [Unflattening;TrivRules]
% 35.68/4.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/4.97  --sup_input_bw                          []
% 35.68/4.97  
% 35.68/4.97  ------ Combination Options
% 35.68/4.97  
% 35.68/4.97  --comb_res_mult                         3
% 35.68/4.97  --comb_sup_mult                         2
% 35.68/4.97  --comb_inst_mult                        10
% 35.68/4.97  
% 35.68/4.97  ------ Debug Options
% 35.68/4.97  
% 35.68/4.97  --dbg_backtrace                         false
% 35.68/4.97  --dbg_dump_prop_clauses                 false
% 35.68/4.97  --dbg_dump_prop_clauses_file            -
% 35.68/4.97  --dbg_out_stat                          false
% 35.68/4.97  ------ Parsing...
% 35.68/4.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.68/4.97  
% 35.68/4.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.68/4.97  
% 35.68/4.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.68/4.97  
% 35.68/4.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.68/4.97  ------ Proving...
% 35.68/4.97  ------ Problem Properties 
% 35.68/4.97  
% 35.68/4.97  
% 35.68/4.97  clauses                                 33
% 35.68/4.97  conjectures                             11
% 35.68/4.97  EPR                                     7
% 35.68/4.97  Horn                                    27
% 35.68/4.97  unary                                   13
% 35.68/4.97  binary                                  4
% 35.68/4.97  lits                                    109
% 35.68/4.97  lits eq                                 32
% 35.68/4.97  fd_pure                                 0
% 35.68/4.97  fd_pseudo                               0
% 35.68/4.97  fd_cond                                 5
% 35.68/4.97  fd_pseudo_cond                          1
% 35.68/4.97  AC symbols                              0
% 35.68/4.97  
% 35.68/4.97  ------ Schedule dynamic 5 is on 
% 35.68/4.97  
% 35.68/4.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.68/4.97  
% 35.68/4.97  
% 35.68/4.97  ------ 
% 35.68/4.97  Current options:
% 35.68/4.97  ------ 
% 35.68/4.97  
% 35.68/4.97  ------ Input Options
% 35.68/4.97  
% 35.68/4.97  --out_options                           all
% 35.68/4.97  --tptp_safe_out                         true
% 35.68/4.97  --problem_path                          ""
% 35.68/4.97  --include_path                          ""
% 35.68/4.97  --clausifier                            res/vclausify_rel
% 35.68/4.97  --clausifier_options                    ""
% 35.68/4.97  --stdin                                 false
% 35.68/4.97  --stats_out                             all
% 35.68/4.97  
% 35.68/4.97  ------ General Options
% 35.68/4.97  
% 35.68/4.97  --fof                                   false
% 35.68/4.97  --time_out_real                         305.
% 35.68/4.97  --time_out_virtual                      -1.
% 35.68/4.97  --symbol_type_check                     false
% 35.68/4.97  --clausify_out                          false
% 35.68/4.97  --sig_cnt_out                           false
% 35.68/4.97  --trig_cnt_out                          false
% 35.68/4.97  --trig_cnt_out_tolerance                1.
% 35.68/4.97  --trig_cnt_out_sk_spl                   false
% 35.68/4.97  --abstr_cl_out                          false
% 35.68/4.97  
% 35.68/4.97  ------ Global Options
% 35.68/4.97  
% 35.68/4.97  --schedule                              default
% 35.68/4.97  --add_important_lit                     false
% 35.68/4.97  --prop_solver_per_cl                    1000
% 35.68/4.97  --min_unsat_core                        false
% 35.68/4.97  --soft_assumptions                      false
% 35.68/4.97  --soft_lemma_size                       3
% 35.68/4.97  --prop_impl_unit_size                   0
% 35.68/4.97  --prop_impl_unit                        []
% 35.68/4.97  --share_sel_clauses                     true
% 35.68/4.97  --reset_solvers                         false
% 35.68/4.97  --bc_imp_inh                            [conj_cone]
% 35.68/4.97  --conj_cone_tolerance                   3.
% 35.68/4.97  --extra_neg_conj                        none
% 35.68/4.97  --large_theory_mode                     true
% 35.68/4.97  --prolific_symb_bound                   200
% 35.68/4.97  --lt_threshold                          2000
% 35.68/4.97  --clause_weak_htbl                      true
% 35.68/4.97  --gc_record_bc_elim                     false
% 35.68/4.97  
% 35.68/4.97  ------ Preprocessing Options
% 35.68/4.97  
% 35.68/4.97  --preprocessing_flag                    true
% 35.68/4.97  --time_out_prep_mult                    0.1
% 35.68/4.97  --splitting_mode                        input
% 35.68/4.97  --splitting_grd                         true
% 35.68/4.97  --splitting_cvd                         false
% 35.68/4.97  --splitting_cvd_svl                     false
% 35.68/4.97  --splitting_nvd                         32
% 35.68/4.97  --sub_typing                            true
% 35.68/4.97  --prep_gs_sim                           true
% 35.68/4.97  --prep_unflatten                        true
% 35.68/4.97  --prep_res_sim                          true
% 35.68/4.97  --prep_upred                            true
% 35.68/4.97  --prep_sem_filter                       exhaustive
% 35.68/4.97  --prep_sem_filter_out                   false
% 35.68/4.97  --pred_elim                             true
% 35.68/4.97  --res_sim_input                         true
% 35.68/4.97  --eq_ax_congr_red                       true
% 35.68/4.97  --pure_diseq_elim                       true
% 35.68/4.97  --brand_transform                       false
% 35.68/4.97  --non_eq_to_eq                          false
% 35.68/4.97  --prep_def_merge                        true
% 35.68/4.97  --prep_def_merge_prop_impl              false
% 35.68/4.97  --prep_def_merge_mbd                    true
% 35.68/4.97  --prep_def_merge_tr_red                 false
% 35.68/4.97  --prep_def_merge_tr_cl                  false
% 35.68/4.97  --smt_preprocessing                     true
% 35.68/4.97  --smt_ac_axioms                         fast
% 35.68/4.97  --preprocessed_out                      false
% 35.68/4.97  --preprocessed_stats                    false
% 35.68/4.97  
% 35.68/4.97  ------ Abstraction refinement Options
% 35.68/4.97  
% 35.68/4.97  --abstr_ref                             []
% 35.68/4.97  --abstr_ref_prep                        false
% 35.68/4.97  --abstr_ref_until_sat                   false
% 35.68/4.97  --abstr_ref_sig_restrict                funpre
% 35.68/4.97  --abstr_ref_af_restrict_to_split_sk     false
% 35.68/4.97  --abstr_ref_under                       []
% 35.68/4.97  
% 35.68/4.97  ------ SAT Options
% 35.68/4.97  
% 35.68/4.97  --sat_mode                              false
% 35.68/4.97  --sat_fm_restart_options                ""
% 35.68/4.97  --sat_gr_def                            false
% 35.68/4.97  --sat_epr_types                         true
% 35.68/4.97  --sat_non_cyclic_types                  false
% 35.68/4.97  --sat_finite_models                     false
% 35.68/4.97  --sat_fm_lemmas                         false
% 35.68/4.97  --sat_fm_prep                           false
% 35.68/4.97  --sat_fm_uc_incr                        true
% 35.68/4.97  --sat_out_model                         small
% 35.68/4.97  --sat_out_clauses                       false
% 35.68/4.97  
% 35.68/4.97  ------ QBF Options
% 35.68/4.97  
% 35.68/4.97  --qbf_mode                              false
% 35.68/4.97  --qbf_elim_univ                         false
% 35.68/4.97  --qbf_dom_inst                          none
% 35.68/4.97  --qbf_dom_pre_inst                      false
% 35.68/4.97  --qbf_sk_in                             false
% 35.68/4.97  --qbf_pred_elim                         true
% 35.68/4.97  --qbf_split                             512
% 35.68/4.97  
% 35.68/4.97  ------ BMC1 Options
% 35.68/4.97  
% 35.68/4.97  --bmc1_incremental                      false
% 35.68/4.97  --bmc1_axioms                           reachable_all
% 35.68/4.97  --bmc1_min_bound                        0
% 35.68/4.97  --bmc1_max_bound                        -1
% 35.68/4.97  --bmc1_max_bound_default                -1
% 35.68/4.97  --bmc1_symbol_reachability              true
% 35.68/4.97  --bmc1_property_lemmas                  false
% 35.68/4.97  --bmc1_k_induction                      false
% 35.68/4.97  --bmc1_non_equiv_states                 false
% 35.68/4.97  --bmc1_deadlock                         false
% 35.68/4.97  --bmc1_ucm                              false
% 35.68/4.97  --bmc1_add_unsat_core                   none
% 35.68/4.97  --bmc1_unsat_core_children              false
% 35.68/4.97  --bmc1_unsat_core_extrapolate_axioms    false
% 35.68/4.97  --bmc1_out_stat                         full
% 35.68/4.97  --bmc1_ground_init                      false
% 35.68/4.97  --bmc1_pre_inst_next_state              false
% 35.68/4.97  --bmc1_pre_inst_state                   false
% 35.68/4.97  --bmc1_pre_inst_reach_state             false
% 35.68/4.97  --bmc1_out_unsat_core                   false
% 35.68/4.97  --bmc1_aig_witness_out                  false
% 35.68/4.97  --bmc1_verbose                          false
% 35.68/4.97  --bmc1_dump_clauses_tptp                false
% 35.68/4.97  --bmc1_dump_unsat_core_tptp             false
% 35.68/4.97  --bmc1_dump_file                        -
% 35.68/4.97  --bmc1_ucm_expand_uc_limit              128
% 35.68/4.97  --bmc1_ucm_n_expand_iterations          6
% 35.68/4.97  --bmc1_ucm_extend_mode                  1
% 35.68/4.97  --bmc1_ucm_init_mode                    2
% 35.68/4.97  --bmc1_ucm_cone_mode                    none
% 35.68/4.97  --bmc1_ucm_reduced_relation_type        0
% 35.68/4.97  --bmc1_ucm_relax_model                  4
% 35.68/4.97  --bmc1_ucm_full_tr_after_sat            true
% 35.68/4.97  --bmc1_ucm_expand_neg_assumptions       false
% 35.68/4.97  --bmc1_ucm_layered_model                none
% 35.68/4.97  --bmc1_ucm_max_lemma_size               10
% 35.68/4.97  
% 35.68/4.97  ------ AIG Options
% 35.68/4.97  
% 35.68/4.97  --aig_mode                              false
% 35.68/4.97  
% 35.68/4.97  ------ Instantiation Options
% 35.68/4.97  
% 35.68/4.97  --instantiation_flag                    true
% 35.68/4.97  --inst_sos_flag                         true
% 35.68/4.97  --inst_sos_phase                        true
% 35.68/4.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.68/4.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.68/4.97  --inst_lit_sel_side                     none
% 35.68/4.97  --inst_solver_per_active                1400
% 35.68/4.97  --inst_solver_calls_frac                1.
% 35.68/4.97  --inst_passive_queue_type               priority_queues
% 35.68/4.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.68/4.97  --inst_passive_queues_freq              [25;2]
% 35.68/4.97  --inst_dismatching                      true
% 35.68/4.97  --inst_eager_unprocessed_to_passive     true
% 35.68/4.97  --inst_prop_sim_given                   true
% 35.68/4.97  --inst_prop_sim_new                     false
% 35.68/4.97  --inst_subs_new                         false
% 35.68/4.97  --inst_eq_res_simp                      false
% 35.68/4.97  --inst_subs_given                       false
% 35.68/4.97  --inst_orphan_elimination               true
% 35.68/4.97  --inst_learning_loop_flag               true
% 35.68/4.97  --inst_learning_start                   3000
% 35.68/4.97  --inst_learning_factor                  2
% 35.68/4.97  --inst_start_prop_sim_after_learn       3
% 35.68/4.97  --inst_sel_renew                        solver
% 35.68/4.97  --inst_lit_activity_flag                true
% 35.68/4.97  --inst_restr_to_given                   false
% 35.68/4.97  --inst_activity_threshold               500
% 35.68/4.97  --inst_out_proof                        true
% 35.68/4.97  
% 35.68/4.97  ------ Resolution Options
% 35.68/4.97  
% 35.68/4.97  --resolution_flag                       false
% 35.68/4.97  --res_lit_sel                           adaptive
% 35.68/4.97  --res_lit_sel_side                      none
% 35.68/4.97  --res_ordering                          kbo
% 35.68/4.97  --res_to_prop_solver                    active
% 35.68/4.97  --res_prop_simpl_new                    false
% 35.68/4.97  --res_prop_simpl_given                  true
% 35.68/4.97  --res_passive_queue_type                priority_queues
% 35.68/4.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.68/4.97  --res_passive_queues_freq               [15;5]
% 35.68/4.97  --res_forward_subs                      full
% 35.68/4.97  --res_backward_subs                     full
% 35.68/4.97  --res_forward_subs_resolution           true
% 35.68/4.97  --res_backward_subs_resolution          true
% 35.68/4.97  --res_orphan_elimination                true
% 35.68/4.97  --res_time_limit                        2.
% 35.68/4.97  --res_out_proof                         true
% 35.68/4.97  
% 35.68/4.97  ------ Superposition Options
% 35.68/4.97  
% 35.68/4.97  --superposition_flag                    true
% 35.68/4.97  --sup_passive_queue_type                priority_queues
% 35.68/4.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.68/4.97  --sup_passive_queues_freq               [8;1;4]
% 35.68/4.97  --demod_completeness_check              fast
% 35.68/4.97  --demod_use_ground                      true
% 35.68/4.97  --sup_to_prop_solver                    passive
% 35.68/4.97  --sup_prop_simpl_new                    true
% 35.68/4.97  --sup_prop_simpl_given                  true
% 35.68/4.97  --sup_fun_splitting                     true
% 35.68/4.97  --sup_smt_interval                      50000
% 35.68/4.97  
% 35.68/4.97  ------ Superposition Simplification Setup
% 35.68/4.97  
% 35.68/4.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.68/4.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.68/4.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.68/4.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.68/4.97  --sup_full_triv                         [TrivRules;PropSubs]
% 35.68/4.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.68/4.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.68/4.97  --sup_immed_triv                        [TrivRules]
% 35.68/4.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/4.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/4.97  --sup_immed_bw_main                     []
% 35.68/4.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.68/4.97  --sup_input_triv                        [Unflattening;TrivRules]
% 35.68/4.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.68/4.97  --sup_input_bw                          []
% 35.68/4.97  
% 35.68/4.97  ------ Combination Options
% 35.68/4.97  
% 35.68/4.97  --comb_res_mult                         3
% 35.68/4.97  --comb_sup_mult                         2
% 35.68/4.97  --comb_inst_mult                        10
% 35.68/4.97  
% 35.68/4.97  ------ Debug Options
% 35.68/4.97  
% 35.68/4.97  --dbg_backtrace                         false
% 35.68/4.97  --dbg_dump_prop_clauses                 false
% 35.68/4.97  --dbg_dump_prop_clauses_file            -
% 35.68/4.97  --dbg_out_stat                          false
% 35.68/4.97  
% 35.68/4.97  
% 35.68/4.97  
% 35.68/4.97  
% 35.68/4.97  ------ Proving...
% 35.68/4.97  
% 35.68/4.97  
% 35.68/4.97  % SZS status Theorem for theBenchmark.p
% 35.68/4.97  
% 35.68/4.97  % SZS output start CNFRefutation for theBenchmark.p
% 35.68/4.97  
% 35.68/4.97  fof(f15,conjecture,(
% 35.68/4.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f16,negated_conjecture,(
% 35.68/4.97    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 35.68/4.97    inference(negated_conjecture,[],[f15])).
% 35.68/4.97  
% 35.68/4.97  fof(f37,plain,(
% 35.68/4.97    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 35.68/4.97    inference(ennf_transformation,[],[f16])).
% 35.68/4.97  
% 35.68/4.97  fof(f38,plain,(
% 35.68/4.97    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 35.68/4.97    inference(flattening,[],[f37])).
% 35.68/4.97  
% 35.68/4.97  fof(f42,plain,(
% 35.68/4.97    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 35.68/4.97    introduced(choice_axiom,[])).
% 35.68/4.97  
% 35.68/4.97  fof(f41,plain,(
% 35.68/4.97    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 35.68/4.97    introduced(choice_axiom,[])).
% 35.68/4.97  
% 35.68/4.97  fof(f43,plain,(
% 35.68/4.97    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 35.68/4.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 35.68/4.97  
% 35.68/4.97  fof(f69,plain,(
% 35.68/4.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f6,axiom,(
% 35.68/4.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f24,plain,(
% 35.68/4.97    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.68/4.97    inference(ennf_transformation,[],[f6])).
% 35.68/4.97  
% 35.68/4.97  fof(f50,plain,(
% 35.68/4.97    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.68/4.97    inference(cnf_transformation,[],[f24])).
% 35.68/4.97  
% 35.68/4.97  fof(f73,plain,(
% 35.68/4.97    k2_relset_1(sK0,sK1,sK2) = sK1),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f72,plain,(
% 35.68/4.97    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f8,axiom,(
% 35.68/4.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f27,plain,(
% 35.68/4.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.68/4.97    inference(ennf_transformation,[],[f8])).
% 35.68/4.97  
% 35.68/4.97  fof(f28,plain,(
% 35.68/4.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.68/4.97    inference(flattening,[],[f27])).
% 35.68/4.97  
% 35.68/4.97  fof(f40,plain,(
% 35.68/4.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.68/4.97    inference(nnf_transformation,[],[f28])).
% 35.68/4.97  
% 35.68/4.97  fof(f53,plain,(
% 35.68/4.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.68/4.97    inference(cnf_transformation,[],[f40])).
% 35.68/4.97  
% 35.68/4.97  fof(f5,axiom,(
% 35.68/4.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f23,plain,(
% 35.68/4.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.68/4.97    inference(ennf_transformation,[],[f5])).
% 35.68/4.97  
% 35.68/4.97  fof(f49,plain,(
% 35.68/4.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.68/4.97    inference(cnf_transformation,[],[f23])).
% 35.68/4.97  
% 35.68/4.97  fof(f71,plain,(
% 35.68/4.97    v1_funct_2(sK3,sK1,sK0)),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f76,plain,(
% 35.68/4.97    k1_xboole_0 != sK0),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f1,axiom,(
% 35.68/4.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f18,plain,(
% 35.68/4.97    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.68/4.97    inference(ennf_transformation,[],[f1])).
% 35.68/4.97  
% 35.68/4.97  fof(f19,plain,(
% 35.68/4.97    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.68/4.97    inference(flattening,[],[f18])).
% 35.68/4.97  
% 35.68/4.97  fof(f45,plain,(
% 35.68/4.97    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.68/4.97    inference(cnf_transformation,[],[f19])).
% 35.68/4.97  
% 35.68/4.97  fof(f70,plain,(
% 35.68/4.97    v1_funct_1(sK3)),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f4,axiom,(
% 35.68/4.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f22,plain,(
% 35.68/4.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.68/4.97    inference(ennf_transformation,[],[f4])).
% 35.68/4.97  
% 35.68/4.97  fof(f48,plain,(
% 35.68/4.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.68/4.97    inference(cnf_transformation,[],[f22])).
% 35.68/4.97  
% 35.68/4.97  fof(f11,axiom,(
% 35.68/4.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f31,plain,(
% 35.68/4.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.68/4.97    inference(ennf_transformation,[],[f11])).
% 35.68/4.97  
% 35.68/4.97  fof(f32,plain,(
% 35.68/4.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.68/4.97    inference(flattening,[],[f31])).
% 35.68/4.97  
% 35.68/4.97  fof(f62,plain,(
% 35.68/4.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.68/4.97    inference(cnf_transformation,[],[f32])).
% 35.68/4.97  
% 35.68/4.97  fof(f7,axiom,(
% 35.68/4.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f25,plain,(
% 35.68/4.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 35.68/4.97    inference(ennf_transformation,[],[f7])).
% 35.68/4.97  
% 35.68/4.97  fof(f26,plain,(
% 35.68/4.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.68/4.97    inference(flattening,[],[f25])).
% 35.68/4.97  
% 35.68/4.97  fof(f39,plain,(
% 35.68/4.97    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.68/4.97    inference(nnf_transformation,[],[f26])).
% 35.68/4.97  
% 35.68/4.97  fof(f51,plain,(
% 35.68/4.97    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.68/4.97    inference(cnf_transformation,[],[f39])).
% 35.68/4.97  
% 35.68/4.97  fof(f74,plain,(
% 35.68/4.97    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f10,axiom,(
% 35.68/4.97    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f17,plain,(
% 35.68/4.97    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 35.68/4.97    inference(pure_predicate_removal,[],[f10])).
% 35.68/4.97  
% 35.68/4.97  fof(f61,plain,(
% 35.68/4.97    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 35.68/4.97    inference(cnf_transformation,[],[f17])).
% 35.68/4.97  
% 35.68/4.97  fof(f67,plain,(
% 35.68/4.97    v1_funct_1(sK2)),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f9,axiom,(
% 35.68/4.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f29,plain,(
% 35.68/4.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 35.68/4.97    inference(ennf_transformation,[],[f9])).
% 35.68/4.97  
% 35.68/4.97  fof(f30,plain,(
% 35.68/4.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 35.68/4.97    inference(flattening,[],[f29])).
% 35.68/4.97  
% 35.68/4.97  fof(f60,plain,(
% 35.68/4.97    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 35.68/4.97    inference(cnf_transformation,[],[f30])).
% 35.68/4.97  
% 35.68/4.97  fof(f2,axiom,(
% 35.68/4.97    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f46,plain,(
% 35.68/4.97    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 35.68/4.97    inference(cnf_transformation,[],[f2])).
% 35.68/4.97  
% 35.68/4.97  fof(f12,axiom,(
% 35.68/4.97    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f63,plain,(
% 35.68/4.97    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 35.68/4.97    inference(cnf_transformation,[],[f12])).
% 35.68/4.97  
% 35.68/4.97  fof(f79,plain,(
% 35.68/4.97    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 35.68/4.97    inference(definition_unfolding,[],[f46,f63])).
% 35.68/4.97  
% 35.68/4.97  fof(f3,axiom,(
% 35.68/4.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f20,plain,(
% 35.68/4.97    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.68/4.97    inference(ennf_transformation,[],[f3])).
% 35.68/4.97  
% 35.68/4.97  fof(f21,plain,(
% 35.68/4.97    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.68/4.97    inference(flattening,[],[f20])).
% 35.68/4.97  
% 35.68/4.97  fof(f47,plain,(
% 35.68/4.97    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.68/4.97    inference(cnf_transformation,[],[f21])).
% 35.68/4.97  
% 35.68/4.97  fof(f80,plain,(
% 35.68/4.97    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.68/4.97    inference(definition_unfolding,[],[f47,f63])).
% 35.68/4.97  
% 35.68/4.97  fof(f13,axiom,(
% 35.68/4.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f33,plain,(
% 35.68/4.97    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 35.68/4.97    inference(ennf_transformation,[],[f13])).
% 35.68/4.97  
% 35.68/4.97  fof(f34,plain,(
% 35.68/4.97    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.68/4.97    inference(flattening,[],[f33])).
% 35.68/4.97  
% 35.68/4.97  fof(f64,plain,(
% 35.68/4.97    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.68/4.97    inference(cnf_transformation,[],[f34])).
% 35.68/4.97  
% 35.68/4.97  fof(f68,plain,(
% 35.68/4.97    v1_funct_2(sK2,sK0,sK1)),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f14,axiom,(
% 35.68/4.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 35.68/4.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/4.97  
% 35.68/4.97  fof(f35,plain,(
% 35.68/4.97    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 35.68/4.97    inference(ennf_transformation,[],[f14])).
% 35.68/4.97  
% 35.68/4.97  fof(f36,plain,(
% 35.68/4.97    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 35.68/4.97    inference(flattening,[],[f35])).
% 35.68/4.97  
% 35.68/4.97  fof(f65,plain,(
% 35.68/4.97    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 35.68/4.97    inference(cnf_transformation,[],[f36])).
% 35.68/4.97  
% 35.68/4.97  fof(f77,plain,(
% 35.68/4.97    k1_xboole_0 != sK1),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f78,plain,(
% 35.68/4.97    k2_funct_1(sK2) != sK3),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  fof(f75,plain,(
% 35.68/4.97    v2_funct_1(sK2)),
% 35.68/4.97    inference(cnf_transformation,[],[f43])).
% 35.68/4.97  
% 35.68/4.97  cnf(c_31,negated_conjecture,
% 35.68/4.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 35.68/4.97      inference(cnf_transformation,[],[f69]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1113,plain,
% 35.68/4.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_6,plain,
% 35.68/4.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 35.68/4.97      inference(cnf_transformation,[],[f50]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1130,plain,
% 35.68/4.97      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 35.68/4.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2114,plain,
% 35.68/4.97      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1113,c_1130]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_27,negated_conjecture,
% 35.68/4.97      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 35.68/4.97      inference(cnf_transformation,[],[f73]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2115,plain,
% 35.68/4.97      ( k2_relat_1(sK2) = sK1 ),
% 35.68/4.97      inference(light_normalisation,[status(thm)],[c_2114,c_27]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_28,negated_conjecture,
% 35.68/4.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 35.68/4.97      inference(cnf_transformation,[],[f72]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1116,plain,
% 35.68/4.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_14,plain,
% 35.68/4.97      ( ~ v1_funct_2(X0,X1,X2)
% 35.68/4.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | k1_relset_1(X1,X2,X0) = X1
% 35.68/4.97      | k1_xboole_0 = X2 ),
% 35.68/4.97      inference(cnf_transformation,[],[f53]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1124,plain,
% 35.68/4.97      ( k1_relset_1(X0,X1,X2) = X0
% 35.68/4.97      | k1_xboole_0 = X1
% 35.68/4.97      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.68/4.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2679,plain,
% 35.68/4.97      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 35.68/4.97      | sK0 = k1_xboole_0
% 35.68/4.97      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1116,c_1124]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_5,plain,
% 35.68/4.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 35.68/4.97      inference(cnf_transformation,[],[f49]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1131,plain,
% 35.68/4.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 35.68/4.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2261,plain,
% 35.68/4.97      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1116,c_1131]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2682,plain,
% 35.68/4.97      ( k1_relat_1(sK3) = sK1
% 35.68/4.97      | sK0 = k1_xboole_0
% 35.68/4.97      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 35.68/4.97      inference(demodulation,[status(thm)],[c_2679,c_2261]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_29,negated_conjecture,
% 35.68/4.97      ( v1_funct_2(sK3,sK1,sK0) ),
% 35.68/4.97      inference(cnf_transformation,[],[f71]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_38,plain,
% 35.68/4.97      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_24,negated_conjecture,
% 35.68/4.97      ( k1_xboole_0 != sK0 ),
% 35.68/4.97      inference(cnf_transformation,[],[f76]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_638,plain,( X0 = X0 ),theory(equality) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_665,plain,
% 35.68/4.97      ( k1_xboole_0 = k1_xboole_0 ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_638]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_639,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1234,plain,
% 35.68/4.97      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_639]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1235,plain,
% 35.68/4.97      ( sK0 != k1_xboole_0
% 35.68/4.97      | k1_xboole_0 = sK0
% 35.68/4.97      | k1_xboole_0 != k1_xboole_0 ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_1234]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2912,plain,
% 35.68/4.97      ( k1_relat_1(sK3) = sK1 ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_2682,c_38,c_24,c_665,c_1235]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_0,plain,
% 35.68/4.97      ( ~ v1_relat_1(X0)
% 35.68/4.97      | ~ v1_relat_1(X1)
% 35.68/4.97      | ~ v1_funct_1(X0)
% 35.68/4.97      | ~ v1_funct_1(X1)
% 35.68/4.97      | v2_funct_1(X1)
% 35.68/4.97      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 35.68/4.97      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 35.68/4.97      inference(cnf_transformation,[],[f45]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1136,plain,
% 35.68/4.97      ( k1_relat_1(X0) != k2_relat_1(X1)
% 35.68/4.97      | v1_relat_1(X1) != iProver_top
% 35.68/4.97      | v1_relat_1(X0) != iProver_top
% 35.68/4.97      | v1_funct_1(X1) != iProver_top
% 35.68/4.97      | v1_funct_1(X0) != iProver_top
% 35.68/4.97      | v2_funct_1(X0) = iProver_top
% 35.68/4.97      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3418,plain,
% 35.68/4.97      ( k2_relat_1(X0) != sK1
% 35.68/4.97      | v1_relat_1(X0) != iProver_top
% 35.68/4.97      | v1_relat_1(sK3) != iProver_top
% 35.68/4.97      | v1_funct_1(X0) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) = iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_2912,c_1136]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_30,negated_conjecture,
% 35.68/4.97      ( v1_funct_1(sK3) ),
% 35.68/4.97      inference(cnf_transformation,[],[f70]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_37,plain,
% 35.68/4.97      ( v1_funct_1(sK3) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_39,plain,
% 35.68/4.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_4,plain,
% 35.68/4.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | v1_relat_1(X0) ),
% 35.68/4.97      inference(cnf_transformation,[],[f48]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1249,plain,
% 35.68/4.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.68/4.97      | v1_relat_1(sK3) ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_4]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1499,plain,
% 35.68/4.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.68/4.97      | v1_relat_1(sK3) ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_1249]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1500,plain,
% 35.68/4.97      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.68/4.97      | v1_relat_1(sK3) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_9542,plain,
% 35.68/4.97      ( v1_funct_1(X0) != iProver_top
% 35.68/4.97      | k2_relat_1(X0) != sK1
% 35.68/4.97      | v1_relat_1(X0) != iProver_top
% 35.68/4.97      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) = iProver_top ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_3418,c_37,c_39,c_1500]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_9543,plain,
% 35.68/4.97      ( k2_relat_1(X0) != sK1
% 35.68/4.97      | v1_relat_1(X0) != iProver_top
% 35.68/4.97      | v1_funct_1(X0) != iProver_top
% 35.68/4.97      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) = iProver_top ),
% 35.68/4.97      inference(renaming,[status(thm)],[c_9542]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_9548,plain,
% 35.68/4.97      ( v1_relat_1(sK2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top
% 35.68/4.97      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) = iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_2115,c_9543]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_18,plain,
% 35.68/4.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.68/4.97      | ~ v1_funct_1(X0)
% 35.68/4.97      | ~ v1_funct_1(X3)
% 35.68/4.97      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 35.68/4.97      inference(cnf_transformation,[],[f62]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1120,plain,
% 35.68/4.97      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 35.68/4.97      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 35.68/4.97      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.68/4.97      | v1_funct_1(X5) != iProver_top
% 35.68/4.97      | v1_funct_1(X4) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3342,plain,
% 35.68/4.97      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.68/4.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.68/4.97      | v1_funct_1(X2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1116,c_1120]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3549,plain,
% 35.68/4.97      ( v1_funct_1(X2) != iProver_top
% 35.68/4.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.68/4.97      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_3342,c_37]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3550,plain,
% 35.68/4.97      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 35.68/4.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.68/4.97      | v1_funct_1(X2) != iProver_top ),
% 35.68/4.97      inference(renaming,[status(thm)],[c_3549]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3557,plain,
% 35.68/4.97      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1113,c_3550]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_8,plain,
% 35.68/4.97      ( ~ r2_relset_1(X0,X1,X2,X3)
% 35.68/4.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.68/4.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.68/4.97      | X3 = X2 ),
% 35.68/4.97      inference(cnf_transformation,[],[f51]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_26,negated_conjecture,
% 35.68/4.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 35.68/4.97      inference(cnf_transformation,[],[f74]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_373,plain,
% 35.68/4.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | X3 = X0
% 35.68/4.97      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 35.68/4.97      | k6_partfun1(sK0) != X3
% 35.68/4.97      | sK0 != X2
% 35.68/4.97      | sK0 != X1 ),
% 35.68/4.97      inference(resolution_lifted,[status(thm)],[c_8,c_26]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_374,plain,
% 35.68/4.97      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.68/4.97      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.68/4.97      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.68/4.97      inference(unflattening,[status(thm)],[c_373]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_17,plain,
% 35.68/4.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 35.68/4.97      inference(cnf_transformation,[],[f61]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_382,plain,
% 35.68/4.97      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.68/4.97      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.68/4.97      inference(forward_subsumption_resolution,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_374,c_17]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1109,plain,
% 35.68/4.97      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.68/4.97      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_33,negated_conjecture,
% 35.68/4.97      ( v1_funct_1(sK2) ),
% 35.68/4.97      inference(cnf_transformation,[],[f67]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_15,plain,
% 35.68/4.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 35.68/4.97      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 35.68/4.97      | ~ v1_funct_1(X0)
% 35.68/4.97      | ~ v1_funct_1(X3) ),
% 35.68/4.97      inference(cnf_transformation,[],[f60]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1364,plain,
% 35.68/4.97      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 35.68/4.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 35.68/4.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.68/4.97      | ~ v1_funct_1(sK3)
% 35.68/4.97      | ~ v1_funct_1(sK2) ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_15]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1705,plain,
% 35.68/4.97      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_1109,c_33,c_31,c_30,c_28,c_382,c_1364]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3558,plain,
% 35.68/4.97      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top ),
% 35.68/4.97      inference(light_normalisation,[status(thm)],[c_3557,c_1705]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_34,plain,
% 35.68/4.97      ( v1_funct_1(sK2) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3758,plain,
% 35.68/4.97      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_3558,c_34]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_9550,plain,
% 35.68/4.97      ( v1_relat_1(sK2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top
% 35.68/4.97      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) = iProver_top ),
% 35.68/4.97      inference(light_normalisation,[status(thm)],[c_9548,c_3758]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1132,plain,
% 35.68/4.97      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.68/4.97      | v1_relat_1(X0) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1985,plain,
% 35.68/4.97      ( v1_relat_1(sK2) = iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1113,c_1132]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2,plain,
% 35.68/4.97      ( v2_funct_1(k6_partfun1(X0)) ),
% 35.68/4.97      inference(cnf_transformation,[],[f79]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_4162,plain,
% 35.68/4.97      ( v2_funct_1(k6_partfun1(sK0)) ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_2]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_4163,plain,
% 35.68/4.97      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_4162]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_9710,plain,
% 35.68/4.97      ( v2_funct_1(sK3) = iProver_top ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_9550,c_34,c_1985,c_4163]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3,plain,
% 35.68/4.97      ( ~ v1_relat_1(X0)
% 35.68/4.97      | ~ v1_relat_1(X1)
% 35.68/4.97      | ~ v1_funct_1(X0)
% 35.68/4.97      | ~ v1_funct_1(X1)
% 35.68/4.97      | ~ v2_funct_1(X1)
% 35.68/4.97      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 35.68/4.97      | k2_funct_1(X1) = X0
% 35.68/4.97      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 35.68/4.97      inference(cnf_transformation,[],[f80]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1133,plain,
% 35.68/4.97      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 35.68/4.97      | k2_funct_1(X1) = X0
% 35.68/4.97      | k1_relat_1(X1) != k2_relat_1(X0)
% 35.68/4.97      | v1_relat_1(X0) != iProver_top
% 35.68/4.97      | v1_relat_1(X1) != iProver_top
% 35.68/4.97      | v1_funct_1(X0) != iProver_top
% 35.68/4.97      | v1_funct_1(X1) != iProver_top
% 35.68/4.97      | v2_funct_1(X1) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_4006,plain,
% 35.68/4.97      ( k2_funct_1(sK3) = sK2
% 35.68/4.97      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 35.68/4.97      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 35.68/4.97      | v1_relat_1(sK3) != iProver_top
% 35.68/4.97      | v1_relat_1(sK2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) != iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_3758,c_1133]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2113,plain,
% 35.68/4.97      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1116,c_1130]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_19,plain,
% 35.68/4.97      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 35.68/4.97      | ~ v1_funct_2(X3,X1,X0)
% 35.68/4.97      | ~ v1_funct_2(X2,X0,X1)
% 35.68/4.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 35.68/4.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.68/4.97      | ~ v1_funct_1(X2)
% 35.68/4.97      | ~ v1_funct_1(X3)
% 35.68/4.97      | k2_relset_1(X1,X0,X3) = X0 ),
% 35.68/4.97      inference(cnf_transformation,[],[f64]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_386,plain,
% 35.68/4.97      ( ~ v1_funct_2(X0,X1,X2)
% 35.68/4.97      | ~ v1_funct_2(X3,X2,X1)
% 35.68/4.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 35.68/4.97      | ~ v1_funct_1(X3)
% 35.68/4.97      | ~ v1_funct_1(X0)
% 35.68/4.97      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.68/4.97      | k2_relset_1(X2,X1,X3) = X1
% 35.68/4.97      | k6_partfun1(X1) != k6_partfun1(sK0)
% 35.68/4.97      | sK0 != X1 ),
% 35.68/4.97      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_387,plain,
% 35.68/4.97      ( ~ v1_funct_2(X0,X1,sK0)
% 35.68/4.97      | ~ v1_funct_2(X2,sK0,X1)
% 35.68/4.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 35.68/4.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 35.68/4.97      | ~ v1_funct_1(X2)
% 35.68/4.97      | ~ v1_funct_1(X0)
% 35.68/4.97      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.68/4.97      | k2_relset_1(X1,sK0,X0) = sK0
% 35.68/4.97      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 35.68/4.97      inference(unflattening,[status(thm)],[c_386]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_470,plain,
% 35.68/4.97      ( ~ v1_funct_2(X0,X1,sK0)
% 35.68/4.97      | ~ v1_funct_2(X2,sK0,X1)
% 35.68/4.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 35.68/4.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 35.68/4.97      | ~ v1_funct_1(X0)
% 35.68/4.97      | ~ v1_funct_1(X2)
% 35.68/4.97      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.68/4.97      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 35.68/4.97      inference(equality_resolution_simp,[status(thm)],[c_387]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1108,plain,
% 35.68/4.97      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 35.68/4.97      | k2_relset_1(X0,sK0,X2) = sK0
% 35.68/4.97      | v1_funct_2(X2,X0,sK0) != iProver_top
% 35.68/4.97      | v1_funct_2(X1,sK0,X0) != iProver_top
% 35.68/4.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 35.68/4.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 35.68/4.97      | v1_funct_1(X2) != iProver_top
% 35.68/4.97      | v1_funct_1(X1) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1545,plain,
% 35.68/4.97      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 35.68/4.97      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 35.68/4.97      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 35.68/4.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.68/4.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top ),
% 35.68/4.97      inference(equality_resolution,[status(thm)],[c_1108]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_32,negated_conjecture,
% 35.68/4.97      ( v1_funct_2(sK2,sK0,sK1) ),
% 35.68/4.97      inference(cnf_transformation,[],[f68]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_35,plain,
% 35.68/4.97      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_36,plain,
% 35.68/4.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1848,plain,
% 35.68/4.97      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_1545,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2116,plain,
% 35.68/4.97      ( k2_relat_1(sK3) = sK0 ),
% 35.68/4.97      inference(light_normalisation,[status(thm)],[c_2113,c_1848]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_4007,plain,
% 35.68/4.97      ( k2_funct_1(sK3) = sK2
% 35.68/4.97      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 35.68/4.97      | sK1 != sK1
% 35.68/4.97      | v1_relat_1(sK3) != iProver_top
% 35.68/4.97      | v1_relat_1(sK2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) != iProver_top ),
% 35.68/4.97      inference(light_normalisation,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_4006,c_2115,c_2116,c_2912]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_4008,plain,
% 35.68/4.97      ( k2_funct_1(sK3) = sK2
% 35.68/4.97      | v1_relat_1(sK3) != iProver_top
% 35.68/4.97      | v1_relat_1(sK2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) != iProver_top ),
% 35.68/4.97      inference(equality_resolution_simp,[status(thm)],[c_4007]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_4556,plain,
% 35.68/4.97      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_4008,c_34,c_37,c_39,c_1500,c_1985]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_9715,plain,
% 35.68/4.97      ( k2_funct_1(sK3) = sK2 ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_9710,c_4556]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_21,plain,
% 35.68/4.97      ( ~ v1_funct_2(X0,X1,X2)
% 35.68/4.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.68/4.97      | ~ v1_funct_1(X0)
% 35.68/4.97      | ~ v2_funct_1(X0)
% 35.68/4.97      | k2_relset_1(X1,X2,X0) != X2
% 35.68/4.97      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 35.68/4.97      | k1_xboole_0 = X2 ),
% 35.68/4.97      inference(cnf_transformation,[],[f65]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1118,plain,
% 35.68/4.97      ( k2_relset_1(X0,X1,X2) != X1
% 35.68/4.97      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 35.68/4.97      | k1_xboole_0 = X1
% 35.68/4.97      | v1_funct_2(X2,X0,X1) != iProver_top
% 35.68/4.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.68/4.97      | v1_funct_1(X2) != iProver_top
% 35.68/4.97      | v2_funct_1(X2) != iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2625,plain,
% 35.68/4.97      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 35.68/4.97      | sK0 = k1_xboole_0
% 35.68/4.97      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 35.68/4.97      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v2_funct_1(sK3) != iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1848,c_1118]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_3019,plain,
% 35.68/4.97      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 35.68/4.97      | v2_funct_1(sK3) != iProver_top ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_2625,c_37,c_38,c_39,c_24,c_665,c_1235]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_9716,plain,
% 35.68/4.97      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_9710,c_3019]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_9717,plain,
% 35.68/4.97      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 35.68/4.97      inference(demodulation,[status(thm)],[c_9715,c_9716]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_115656,plain,
% 35.68/4.97      ( k2_funct_1(sK2) = sK3
% 35.68/4.97      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 35.68/4.97      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 35.68/4.97      | v1_relat_1(sK3) != iProver_top
% 35.68/4.97      | v1_relat_1(sK2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top
% 35.68/4.97      | v2_funct_1(sK2) != iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_9717,c_1133]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2680,plain,
% 35.68/4.97      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 35.68/4.97      | sK1 = k1_xboole_0
% 35.68/4.97      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1113,c_1124]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2262,plain,
% 35.68/4.97      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 35.68/4.97      inference(superposition,[status(thm)],[c_1113,c_1131]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2681,plain,
% 35.68/4.97      ( k1_relat_1(sK2) = sK0
% 35.68/4.97      | sK1 = k1_xboole_0
% 35.68/4.97      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 35.68/4.97      inference(demodulation,[status(thm)],[c_2680,c_2262]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_23,negated_conjecture,
% 35.68/4.97      ( k1_xboole_0 != sK1 ),
% 35.68/4.97      inference(cnf_transformation,[],[f77]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1206,plain,
% 35.68/4.97      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_639]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_1207,plain,
% 35.68/4.97      ( sK1 != k1_xboole_0
% 35.68/4.97      | k1_xboole_0 = sK1
% 35.68/4.97      | k1_xboole_0 != k1_xboole_0 ),
% 35.68/4.97      inference(instantiation,[status(thm)],[c_1206]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_2796,plain,
% 35.68/4.97      ( k1_relat_1(sK2) = sK0 ),
% 35.68/4.97      inference(global_propositional_subsumption,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_2681,c_35,c_23,c_665,c_1207]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_115657,plain,
% 35.68/4.97      ( k2_funct_1(sK2) = sK3
% 35.68/4.97      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 35.68/4.97      | sK0 != sK0
% 35.68/4.97      | v1_relat_1(sK3) != iProver_top
% 35.68/4.97      | v1_relat_1(sK2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top
% 35.68/4.97      | v2_funct_1(sK2) != iProver_top ),
% 35.68/4.97      inference(light_normalisation,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_115656,c_2115,c_2116,c_2796]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_115658,plain,
% 35.68/4.97      ( k2_funct_1(sK2) = sK3
% 35.68/4.97      | v1_relat_1(sK3) != iProver_top
% 35.68/4.97      | v1_relat_1(sK2) != iProver_top
% 35.68/4.97      | v1_funct_1(sK3) != iProver_top
% 35.68/4.97      | v1_funct_1(sK2) != iProver_top
% 35.68/4.97      | v2_funct_1(sK2) != iProver_top ),
% 35.68/4.97      inference(equality_resolution_simp,[status(thm)],[c_115657]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_22,negated_conjecture,
% 35.68/4.97      ( k2_funct_1(sK2) != sK3 ),
% 35.68/4.97      inference(cnf_transformation,[],[f78]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_25,negated_conjecture,
% 35.68/4.97      ( v2_funct_1(sK2) ),
% 35.68/4.97      inference(cnf_transformation,[],[f75]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(c_41,plain,
% 35.68/4.97      ( v2_funct_1(sK2) = iProver_top ),
% 35.68/4.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.68/4.97  
% 35.68/4.97  cnf(contradiction,plain,
% 35.68/4.97      ( $false ),
% 35.68/4.97      inference(minisat,
% 35.68/4.97                [status(thm)],
% 35.68/4.97                [c_115658,c_1985,c_1500,c_22,c_41,c_39,c_37,c_34]) ).
% 35.68/4.97  
% 35.68/4.97  
% 35.68/4.97  % SZS output end CNFRefutation for theBenchmark.p
% 35.68/4.97  
% 35.68/4.97  ------                               Statistics
% 35.68/4.97  
% 35.68/4.97  ------ General
% 35.68/4.97  
% 35.68/4.97  abstr_ref_over_cycles:                  0
% 35.68/4.97  abstr_ref_under_cycles:                 0
% 35.68/4.97  gc_basic_clause_elim:                   0
% 35.68/4.97  forced_gc_time:                         0
% 35.68/4.97  parsing_time:                           0.012
% 35.68/4.97  unif_index_cands_time:                  0.
% 35.68/4.97  unif_index_add_time:                    0.
% 35.68/4.97  orderings_time:                         0.
% 35.68/4.97  out_proof_time:                         0.025
% 35.68/4.97  total_time:                             4.307
% 35.68/4.97  num_of_symbols:                         52
% 35.68/4.97  num_of_terms:                           123777
% 35.68/4.97  
% 35.68/4.97  ------ Preprocessing
% 35.68/4.97  
% 35.68/4.97  num_of_splits:                          0
% 35.68/4.97  num_of_split_atoms:                     0
% 35.68/4.97  num_of_reused_defs:                     0
% 35.68/4.97  num_eq_ax_congr_red:                    15
% 35.68/4.97  num_of_sem_filtered_clauses:            1
% 35.68/4.97  num_of_subtypes:                        0
% 35.68/4.97  monotx_restored_types:                  0
% 35.68/4.97  sat_num_of_epr_types:                   0
% 35.68/4.97  sat_num_of_non_cyclic_types:            0
% 35.68/4.97  sat_guarded_non_collapsed_types:        0
% 35.68/4.97  num_pure_diseq_elim:                    0
% 35.68/4.97  simp_replaced_by:                       0
% 35.68/4.97  res_preprocessed:                       162
% 35.68/4.97  prep_upred:                             0
% 35.68/4.97  prep_unflattend:                        12
% 35.68/4.97  smt_new_axioms:                         0
% 35.68/4.97  pred_elim_cands:                        5
% 35.68/4.97  pred_elim:                              1
% 35.68/4.97  pred_elim_cl:                           1
% 35.68/4.97  pred_elim_cycles:                       3
% 35.68/4.97  merged_defs:                            0
% 35.68/4.97  merged_defs_ncl:                        0
% 35.68/4.97  bin_hyper_res:                          0
% 35.68/4.97  prep_cycles:                            4
% 35.68/4.97  pred_elim_time:                         0.004
% 35.68/4.97  splitting_time:                         0.
% 35.68/4.97  sem_filter_time:                        0.
% 35.68/4.97  monotx_time:                            0.001
% 35.68/4.97  subtype_inf_time:                       0.
% 35.68/4.97  
% 35.68/4.97  ------ Problem properties
% 35.68/4.97  
% 35.68/4.97  clauses:                                33
% 35.68/4.97  conjectures:                            11
% 35.68/4.97  epr:                                    7
% 35.68/4.97  horn:                                   27
% 35.68/4.97  ground:                                 12
% 35.68/4.97  unary:                                  13
% 35.68/4.97  binary:                                 4
% 35.68/4.97  lits:                                   109
% 35.68/4.97  lits_eq:                                32
% 35.68/4.97  fd_pure:                                0
% 35.68/4.97  fd_pseudo:                              0
% 35.68/4.97  fd_cond:                                5
% 35.68/4.97  fd_pseudo_cond:                         1
% 35.68/4.97  ac_symbols:                             0
% 35.68/4.97  
% 35.68/4.97  ------ Propositional Solver
% 35.68/4.97  
% 35.68/4.97  prop_solver_calls:                      53
% 35.68/4.97  prop_fast_solver_calls:                 6631
% 35.68/4.97  smt_solver_calls:                       0
% 35.68/4.97  smt_fast_solver_calls:                  0
% 35.68/4.97  prop_num_of_clauses:                    52466
% 35.68/4.97  prop_preprocess_simplified:             102670
% 35.68/4.97  prop_fo_subsumed:                       1971
% 35.68/4.97  prop_solver_time:                       0.
% 35.68/4.97  smt_solver_time:                        0.
% 35.68/4.97  smt_fast_solver_time:                   0.
% 35.68/4.97  prop_fast_solver_time:                  0.
% 35.68/4.97  prop_unsat_core_time:                   0.01
% 35.68/4.97  
% 35.68/4.97  ------ QBF
% 35.68/4.97  
% 35.68/4.97  qbf_q_res:                              0
% 35.68/4.97  qbf_num_tautologies:                    0
% 35.68/4.97  qbf_prep_cycles:                        0
% 35.68/4.97  
% 35.68/4.97  ------ BMC1
% 35.68/4.97  
% 35.68/4.97  bmc1_current_bound:                     -1
% 35.68/4.97  bmc1_last_solved_bound:                 -1
% 35.68/4.97  bmc1_unsat_core_size:                   -1
% 35.68/4.97  bmc1_unsat_core_parents_size:           -1
% 35.68/4.97  bmc1_merge_next_fun:                    0
% 35.68/4.97  bmc1_unsat_core_clauses_time:           0.
% 35.68/4.97  
% 35.68/4.97  ------ Instantiation
% 35.68/4.97  
% 35.68/4.97  inst_num_of_clauses:                    10150
% 35.68/4.97  inst_num_in_passive:                    5061
% 35.68/4.97  inst_num_in_active:                     6085
% 35.68/4.97  inst_num_in_unprocessed:                1804
% 35.68/4.97  inst_num_of_loops:                      6409
% 35.68/4.97  inst_num_of_learning_restarts:          1
% 35.68/4.97  inst_num_moves_active_passive:          318
% 35.68/4.97  inst_lit_activity:                      0
% 35.68/4.97  inst_lit_activity_moves:                5
% 35.68/4.97  inst_num_tautologies:                   0
% 35.68/4.97  inst_num_prop_implied:                  0
% 35.68/4.97  inst_num_existing_simplified:           0
% 35.68/4.97  inst_num_eq_res_simplified:             0
% 35.68/4.97  inst_num_child_elim:                    0
% 35.68/4.97  inst_num_of_dismatching_blockings:      8148
% 35.68/4.97  inst_num_of_non_proper_insts:           14585
% 35.68/4.97  inst_num_of_duplicates:                 0
% 35.68/4.97  inst_inst_num_from_inst_to_res:         0
% 35.68/4.97  inst_dismatching_checking_time:         0.
% 35.68/4.97  
% 35.68/4.97  ------ Resolution
% 35.68/4.97  
% 35.68/4.97  res_num_of_clauses:                     47
% 35.68/4.97  res_num_in_passive:                     47
% 35.68/4.97  res_num_in_active:                      0
% 35.68/4.97  res_num_of_loops:                       166
% 35.68/4.97  res_forward_subset_subsumed:            716
% 35.68/4.97  res_backward_subset_subsumed:           6
% 35.68/4.97  res_forward_subsumed:                   0
% 35.68/4.97  res_backward_subsumed:                  0
% 35.68/4.97  res_forward_subsumption_resolution:     2
% 35.68/4.97  res_backward_subsumption_resolution:    0
% 35.68/4.97  res_clause_to_clause_subsumption:       14313
% 35.68/4.97  res_orphan_elimination:                 0
% 35.68/4.97  res_tautology_del:                      600
% 35.68/4.97  res_num_eq_res_simplified:              1
% 35.68/4.97  res_num_sel_changes:                    0
% 35.68/4.97  res_moves_from_active_to_pass:          0
% 35.68/4.97  
% 35.68/4.97  ------ Superposition
% 35.68/4.97  
% 35.68/4.97  sup_time_total:                         0.
% 35.68/4.97  sup_time_generating:                    0.
% 35.68/4.97  sup_time_sim_full:                      0.
% 35.68/4.97  sup_time_sim_immed:                     0.
% 35.68/4.97  
% 35.68/4.97  sup_num_of_clauses:                     6596
% 35.68/4.97  sup_num_in_active:                      1247
% 35.68/4.97  sup_num_in_passive:                     5349
% 35.68/4.97  sup_num_of_loops:                       1280
% 35.68/4.97  sup_fw_superposition:                   3035
% 35.68/4.97  sup_bw_superposition:                   3960
% 35.68/4.97  sup_immediate_simplified:               1899
% 35.68/4.97  sup_given_eliminated:                   1
% 35.68/4.97  comparisons_done:                       0
% 35.68/4.97  comparisons_avoided:                    1
% 35.68/4.97  
% 35.68/4.97  ------ Simplifications
% 35.68/4.97  
% 35.68/4.97  
% 35.68/4.97  sim_fw_subset_subsumed:                 100
% 35.68/4.97  sim_bw_subset_subsumed:                 97
% 35.68/4.97  sim_fw_subsumed:                        35
% 35.68/4.97  sim_bw_subsumed:                        41
% 35.68/4.97  sim_fw_subsumption_res:                 0
% 35.68/4.97  sim_bw_subsumption_res:                 0
% 35.68/4.97  sim_tautology_del:                      0
% 35.68/4.97  sim_eq_tautology_del:                   80
% 35.68/4.97  sim_eq_res_simp:                        2
% 35.68/4.97  sim_fw_demodulated:                     151
% 35.68/4.97  sim_bw_demodulated:                     17
% 35.68/4.97  sim_light_normalised:                   2196
% 35.68/4.97  sim_joinable_taut:                      0
% 35.68/4.97  sim_joinable_simp:                      0
% 35.68/4.97  sim_ac_normalised:                      0
% 35.68/4.97  sim_smt_subsumption:                    0
% 35.68/4.97  
%------------------------------------------------------------------------------
