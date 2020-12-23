%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:06 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :  166 (1349 expanded)
%              Number of clauses        :   97 ( 385 expanded)
%              Number of leaves         :   19 ( 351 expanded)
%              Depth                    :   21
%              Number of atoms          :  667 (11779 expanded)
%              Number of equality atoms :  320 (4298 expanded)
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

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
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

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f78,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f64])).

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
    inference(definition_unfolding,[],[f47,f64])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1165,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2081,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1150,c_1165])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2083,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2081,c_27])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1153,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1158,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2711,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_1158])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1166,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2125,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1153,c_1166])).

cnf(c_2723,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2711,c_2125])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f75])).

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

cnf(c_1493,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1494,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1493])).

cnf(c_3468,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2723,c_38,c_24,c_665,c_1494])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1171,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3891,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3468,c_1171])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1456,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1457,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_17751,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3891,c_37,c_39,c_1457])).

cnf(c_17752,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_17751])).

cnf(c_17763,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2083,c_17752])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1155,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3620,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_1155])).

cnf(c_3656,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3620,c_37])).

cnf(c_3657,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3656])).

cnf(c_3667,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_3657])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1630,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1966,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_2149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1966])).

cnf(c_2230,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2149])).

cnf(c_4166,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3667,c_33,c_31,c_30,c_28,c_2230])).

cnf(c_10,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_374,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_11,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_382,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_374,c_11])).

cnf(c_1146,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_4169,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4166,c_1146])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1157,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4195,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4166,c_1157])).

cnf(c_4335,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4169,c_34,c_36,c_37,c_39,c_4195])).

cnf(c_17768,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17763,c_4335])).

cnf(c_1459,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1460,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_17983,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17768,c_34,c_36,c_1460])).

cnf(c_0,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1173,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_17989,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17983,c_1173])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1169,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4339,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4335,c_1169])).

cnf(c_2080,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1153,c_1165])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f65])).

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
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

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

cnf(c_1145,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_1663,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1145])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1869,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1663,c_34,c_35,c_36,c_37,c_38,c_39])).

cnf(c_2086,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2080,c_1869])).

cnf(c_4340,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4339,c_2083,c_2086,c_3468])).

cnf(c_4341,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4340])).

cnf(c_5595,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4341,c_34,c_36,c_37,c_39,c_1457,c_1460])).

cnf(c_17991,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_17989,c_5595])).

cnf(c_1151,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1168,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2202,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1168])).

cnf(c_2292,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2202,c_39,c_1457])).

cnf(c_17992,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_17989,c_2292])).

cnf(c_17996,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_17991,c_17992])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17996,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.05/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.05/1.48  
% 7.05/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.05/1.48  
% 7.05/1.48  ------  iProver source info
% 7.05/1.48  
% 7.05/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.05/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.05/1.48  git: non_committed_changes: false
% 7.05/1.48  git: last_make_outside_of_git: false
% 7.05/1.48  
% 7.05/1.48  ------ 
% 7.05/1.48  
% 7.05/1.48  ------ Input Options
% 7.05/1.48  
% 7.05/1.48  --out_options                           all
% 7.05/1.48  --tptp_safe_out                         true
% 7.05/1.48  --problem_path                          ""
% 7.05/1.48  --include_path                          ""
% 7.05/1.48  --clausifier                            res/vclausify_rel
% 7.05/1.48  --clausifier_options                    --mode clausify
% 7.05/1.48  --stdin                                 false
% 7.05/1.48  --stats_out                             all
% 7.05/1.48  
% 7.05/1.48  ------ General Options
% 7.05/1.48  
% 7.05/1.48  --fof                                   false
% 7.05/1.48  --time_out_real                         305.
% 7.05/1.48  --time_out_virtual                      -1.
% 7.05/1.48  --symbol_type_check                     false
% 7.05/1.48  --clausify_out                          false
% 7.05/1.48  --sig_cnt_out                           false
% 7.05/1.48  --trig_cnt_out                          false
% 7.05/1.48  --trig_cnt_out_tolerance                1.
% 7.05/1.48  --trig_cnt_out_sk_spl                   false
% 7.05/1.48  --abstr_cl_out                          false
% 7.05/1.48  
% 7.05/1.48  ------ Global Options
% 7.05/1.48  
% 7.05/1.48  --schedule                              default
% 7.05/1.48  --add_important_lit                     false
% 7.05/1.48  --prop_solver_per_cl                    1000
% 7.05/1.48  --min_unsat_core                        false
% 7.05/1.48  --soft_assumptions                      false
% 7.05/1.48  --soft_lemma_size                       3
% 7.05/1.48  --prop_impl_unit_size                   0
% 7.05/1.48  --prop_impl_unit                        []
% 7.05/1.48  --share_sel_clauses                     true
% 7.05/1.48  --reset_solvers                         false
% 7.05/1.48  --bc_imp_inh                            [conj_cone]
% 7.05/1.48  --conj_cone_tolerance                   3.
% 7.05/1.48  --extra_neg_conj                        none
% 7.05/1.48  --large_theory_mode                     true
% 7.05/1.48  --prolific_symb_bound                   200
% 7.05/1.48  --lt_threshold                          2000
% 7.05/1.48  --clause_weak_htbl                      true
% 7.05/1.48  --gc_record_bc_elim                     false
% 7.05/1.48  
% 7.05/1.48  ------ Preprocessing Options
% 7.05/1.48  
% 7.05/1.48  --preprocessing_flag                    true
% 7.05/1.48  --time_out_prep_mult                    0.1
% 7.05/1.48  --splitting_mode                        input
% 7.05/1.48  --splitting_grd                         true
% 7.05/1.48  --splitting_cvd                         false
% 7.05/1.48  --splitting_cvd_svl                     false
% 7.05/1.48  --splitting_nvd                         32
% 7.05/1.48  --sub_typing                            true
% 7.05/1.48  --prep_gs_sim                           true
% 7.05/1.48  --prep_unflatten                        true
% 7.05/1.48  --prep_res_sim                          true
% 7.05/1.48  --prep_upred                            true
% 7.05/1.48  --prep_sem_filter                       exhaustive
% 7.05/1.48  --prep_sem_filter_out                   false
% 7.05/1.48  --pred_elim                             true
% 7.05/1.48  --res_sim_input                         true
% 7.05/1.48  --eq_ax_congr_red                       true
% 7.05/1.48  --pure_diseq_elim                       true
% 7.05/1.48  --brand_transform                       false
% 7.05/1.48  --non_eq_to_eq                          false
% 7.05/1.48  --prep_def_merge                        true
% 7.05/1.48  --prep_def_merge_prop_impl              false
% 7.05/1.48  --prep_def_merge_mbd                    true
% 7.05/1.48  --prep_def_merge_tr_red                 false
% 7.05/1.48  --prep_def_merge_tr_cl                  false
% 7.05/1.48  --smt_preprocessing                     true
% 7.05/1.48  --smt_ac_axioms                         fast
% 7.05/1.48  --preprocessed_out                      false
% 7.05/1.48  --preprocessed_stats                    false
% 7.05/1.48  
% 7.05/1.48  ------ Abstraction refinement Options
% 7.05/1.48  
% 7.05/1.48  --abstr_ref                             []
% 7.05/1.48  --abstr_ref_prep                        false
% 7.05/1.48  --abstr_ref_until_sat                   false
% 7.05/1.48  --abstr_ref_sig_restrict                funpre
% 7.05/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.48  --abstr_ref_under                       []
% 7.05/1.48  
% 7.05/1.48  ------ SAT Options
% 7.05/1.48  
% 7.05/1.48  --sat_mode                              false
% 7.05/1.48  --sat_fm_restart_options                ""
% 7.05/1.48  --sat_gr_def                            false
% 7.05/1.48  --sat_epr_types                         true
% 7.05/1.48  --sat_non_cyclic_types                  false
% 7.05/1.48  --sat_finite_models                     false
% 7.05/1.48  --sat_fm_lemmas                         false
% 7.05/1.48  --sat_fm_prep                           false
% 7.05/1.48  --sat_fm_uc_incr                        true
% 7.05/1.48  --sat_out_model                         small
% 7.05/1.48  --sat_out_clauses                       false
% 7.05/1.48  
% 7.05/1.48  ------ QBF Options
% 7.05/1.48  
% 7.05/1.48  --qbf_mode                              false
% 7.05/1.48  --qbf_elim_univ                         false
% 7.05/1.48  --qbf_dom_inst                          none
% 7.05/1.48  --qbf_dom_pre_inst                      false
% 7.05/1.48  --qbf_sk_in                             false
% 7.05/1.48  --qbf_pred_elim                         true
% 7.05/1.48  --qbf_split                             512
% 7.05/1.48  
% 7.05/1.48  ------ BMC1 Options
% 7.05/1.48  
% 7.05/1.48  --bmc1_incremental                      false
% 7.05/1.48  --bmc1_axioms                           reachable_all
% 7.05/1.48  --bmc1_min_bound                        0
% 7.05/1.48  --bmc1_max_bound                        -1
% 7.05/1.48  --bmc1_max_bound_default                -1
% 7.05/1.48  --bmc1_symbol_reachability              true
% 7.05/1.48  --bmc1_property_lemmas                  false
% 7.05/1.48  --bmc1_k_induction                      false
% 7.05/1.48  --bmc1_non_equiv_states                 false
% 7.05/1.48  --bmc1_deadlock                         false
% 7.05/1.48  --bmc1_ucm                              false
% 7.05/1.48  --bmc1_add_unsat_core                   none
% 7.05/1.48  --bmc1_unsat_core_children              false
% 7.05/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.48  --bmc1_out_stat                         full
% 7.05/1.48  --bmc1_ground_init                      false
% 7.05/1.48  --bmc1_pre_inst_next_state              false
% 7.05/1.48  --bmc1_pre_inst_state                   false
% 7.05/1.48  --bmc1_pre_inst_reach_state             false
% 7.05/1.48  --bmc1_out_unsat_core                   false
% 7.05/1.48  --bmc1_aig_witness_out                  false
% 7.05/1.48  --bmc1_verbose                          false
% 7.05/1.48  --bmc1_dump_clauses_tptp                false
% 7.05/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.48  --bmc1_dump_file                        -
% 7.05/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.48  --bmc1_ucm_extend_mode                  1
% 7.05/1.48  --bmc1_ucm_init_mode                    2
% 7.05/1.48  --bmc1_ucm_cone_mode                    none
% 7.05/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.48  --bmc1_ucm_relax_model                  4
% 7.05/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.48  --bmc1_ucm_layered_model                none
% 7.05/1.48  --bmc1_ucm_max_lemma_size               10
% 7.05/1.48  
% 7.05/1.48  ------ AIG Options
% 7.05/1.48  
% 7.05/1.48  --aig_mode                              false
% 7.05/1.48  
% 7.05/1.48  ------ Instantiation Options
% 7.05/1.48  
% 7.05/1.48  --instantiation_flag                    true
% 7.05/1.48  --inst_sos_flag                         false
% 7.05/1.48  --inst_sos_phase                        true
% 7.05/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.48  --inst_lit_sel_side                     num_symb
% 7.05/1.48  --inst_solver_per_active                1400
% 7.05/1.48  --inst_solver_calls_frac                1.
% 7.05/1.48  --inst_passive_queue_type               priority_queues
% 7.05/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.48  --inst_passive_queues_freq              [25;2]
% 7.05/1.48  --inst_dismatching                      true
% 7.05/1.48  --inst_eager_unprocessed_to_passive     true
% 7.05/1.48  --inst_prop_sim_given                   true
% 7.05/1.48  --inst_prop_sim_new                     false
% 7.05/1.48  --inst_subs_new                         false
% 7.05/1.48  --inst_eq_res_simp                      false
% 7.05/1.48  --inst_subs_given                       false
% 7.05/1.48  --inst_orphan_elimination               true
% 7.05/1.48  --inst_learning_loop_flag               true
% 7.05/1.48  --inst_learning_start                   3000
% 7.05/1.48  --inst_learning_factor                  2
% 7.05/1.48  --inst_start_prop_sim_after_learn       3
% 7.05/1.48  --inst_sel_renew                        solver
% 7.05/1.48  --inst_lit_activity_flag                true
% 7.05/1.48  --inst_restr_to_given                   false
% 7.05/1.48  --inst_activity_threshold               500
% 7.05/1.48  --inst_out_proof                        true
% 7.05/1.48  
% 7.05/1.48  ------ Resolution Options
% 7.05/1.48  
% 7.05/1.48  --resolution_flag                       true
% 7.05/1.48  --res_lit_sel                           adaptive
% 7.05/1.48  --res_lit_sel_side                      none
% 7.05/1.48  --res_ordering                          kbo
% 7.05/1.48  --res_to_prop_solver                    active
% 7.05/1.48  --res_prop_simpl_new                    false
% 7.05/1.48  --res_prop_simpl_given                  true
% 7.05/1.48  --res_passive_queue_type                priority_queues
% 7.05/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.48  --res_passive_queues_freq               [15;5]
% 7.05/1.48  --res_forward_subs                      full
% 7.05/1.48  --res_backward_subs                     full
% 7.05/1.48  --res_forward_subs_resolution           true
% 7.05/1.48  --res_backward_subs_resolution          true
% 7.05/1.48  --res_orphan_elimination                true
% 7.05/1.48  --res_time_limit                        2.
% 7.05/1.48  --res_out_proof                         true
% 7.05/1.48  
% 7.05/1.48  ------ Superposition Options
% 7.05/1.48  
% 7.05/1.48  --superposition_flag                    true
% 7.05/1.48  --sup_passive_queue_type                priority_queues
% 7.05/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.48  --demod_completeness_check              fast
% 7.05/1.48  --demod_use_ground                      true
% 7.05/1.48  --sup_to_prop_solver                    passive
% 7.05/1.48  --sup_prop_simpl_new                    true
% 7.05/1.48  --sup_prop_simpl_given                  true
% 7.05/1.48  --sup_fun_splitting                     false
% 7.05/1.48  --sup_smt_interval                      50000
% 7.05/1.48  
% 7.05/1.48  ------ Superposition Simplification Setup
% 7.05/1.48  
% 7.05/1.48  --sup_indices_passive                   []
% 7.05/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.48  --sup_full_bw                           [BwDemod]
% 7.05/1.48  --sup_immed_triv                        [TrivRules]
% 7.05/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.48  --sup_immed_bw_main                     []
% 7.05/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.48  
% 7.05/1.48  ------ Combination Options
% 7.05/1.48  
% 7.05/1.48  --comb_res_mult                         3
% 7.05/1.48  --comb_sup_mult                         2
% 7.05/1.48  --comb_inst_mult                        10
% 7.05/1.48  
% 7.05/1.48  ------ Debug Options
% 7.05/1.48  
% 7.05/1.48  --dbg_backtrace                         false
% 7.05/1.48  --dbg_dump_prop_clauses                 false
% 7.05/1.48  --dbg_dump_prop_clauses_file            -
% 7.05/1.48  --dbg_out_stat                          false
% 7.05/1.48  ------ Parsing...
% 7.05/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.05/1.48  
% 7.05/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.05/1.48  
% 7.05/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.05/1.48  
% 7.05/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.05/1.48  ------ Proving...
% 7.05/1.48  ------ Problem Properties 
% 7.05/1.48  
% 7.05/1.48  
% 7.05/1.48  clauses                                 33
% 7.05/1.48  conjectures                             11
% 7.05/1.48  EPR                                     7
% 7.05/1.48  Horn                                    29
% 7.05/1.48  unary                                   14
% 7.05/1.48  binary                                  4
% 7.05/1.48  lits                                    100
% 7.05/1.48  lits eq                                 27
% 7.05/1.48  fd_pure                                 0
% 7.05/1.48  fd_pseudo                               0
% 7.05/1.48  fd_cond                                 3
% 7.05/1.48  fd_pseudo_cond                          1
% 7.05/1.48  AC symbols                              0
% 7.05/1.48  
% 7.05/1.48  ------ Schedule dynamic 5 is on 
% 7.05/1.48  
% 7.05/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.05/1.48  
% 7.05/1.48  
% 7.05/1.48  ------ 
% 7.05/1.48  Current options:
% 7.05/1.48  ------ 
% 7.05/1.48  
% 7.05/1.48  ------ Input Options
% 7.05/1.48  
% 7.05/1.48  --out_options                           all
% 7.05/1.48  --tptp_safe_out                         true
% 7.05/1.48  --problem_path                          ""
% 7.05/1.48  --include_path                          ""
% 7.05/1.48  --clausifier                            res/vclausify_rel
% 7.05/1.48  --clausifier_options                    --mode clausify
% 7.05/1.48  --stdin                                 false
% 7.05/1.48  --stats_out                             all
% 7.05/1.48  
% 7.05/1.48  ------ General Options
% 7.05/1.48  
% 7.05/1.48  --fof                                   false
% 7.05/1.48  --time_out_real                         305.
% 7.05/1.48  --time_out_virtual                      -1.
% 7.05/1.48  --symbol_type_check                     false
% 7.05/1.48  --clausify_out                          false
% 7.05/1.48  --sig_cnt_out                           false
% 7.05/1.48  --trig_cnt_out                          false
% 7.05/1.48  --trig_cnt_out_tolerance                1.
% 7.05/1.48  --trig_cnt_out_sk_spl                   false
% 7.05/1.48  --abstr_cl_out                          false
% 7.05/1.48  
% 7.05/1.48  ------ Global Options
% 7.05/1.48  
% 7.05/1.48  --schedule                              default
% 7.05/1.48  --add_important_lit                     false
% 7.05/1.48  --prop_solver_per_cl                    1000
% 7.05/1.48  --min_unsat_core                        false
% 7.05/1.48  --soft_assumptions                      false
% 7.05/1.48  --soft_lemma_size                       3
% 7.05/1.48  --prop_impl_unit_size                   0
% 7.05/1.48  --prop_impl_unit                        []
% 7.05/1.48  --share_sel_clauses                     true
% 7.05/1.48  --reset_solvers                         false
% 7.05/1.48  --bc_imp_inh                            [conj_cone]
% 7.05/1.48  --conj_cone_tolerance                   3.
% 7.05/1.48  --extra_neg_conj                        none
% 7.05/1.48  --large_theory_mode                     true
% 7.05/1.48  --prolific_symb_bound                   200
% 7.05/1.48  --lt_threshold                          2000
% 7.05/1.48  --clause_weak_htbl                      true
% 7.05/1.48  --gc_record_bc_elim                     false
% 7.05/1.48  
% 7.05/1.48  ------ Preprocessing Options
% 7.05/1.48  
% 7.05/1.48  --preprocessing_flag                    true
% 7.05/1.48  --time_out_prep_mult                    0.1
% 7.05/1.48  --splitting_mode                        input
% 7.05/1.48  --splitting_grd                         true
% 7.05/1.48  --splitting_cvd                         false
% 7.05/1.48  --splitting_cvd_svl                     false
% 7.05/1.48  --splitting_nvd                         32
% 7.05/1.48  --sub_typing                            true
% 7.05/1.48  --prep_gs_sim                           true
% 7.05/1.48  --prep_unflatten                        true
% 7.05/1.48  --prep_res_sim                          true
% 7.05/1.48  --prep_upred                            true
% 7.05/1.48  --prep_sem_filter                       exhaustive
% 7.05/1.48  --prep_sem_filter_out                   false
% 7.05/1.48  --pred_elim                             true
% 7.05/1.48  --res_sim_input                         true
% 7.05/1.48  --eq_ax_congr_red                       true
% 7.05/1.48  --pure_diseq_elim                       true
% 7.05/1.48  --brand_transform                       false
% 7.05/1.48  --non_eq_to_eq                          false
% 7.05/1.48  --prep_def_merge                        true
% 7.05/1.48  --prep_def_merge_prop_impl              false
% 7.05/1.48  --prep_def_merge_mbd                    true
% 7.05/1.48  --prep_def_merge_tr_red                 false
% 7.05/1.48  --prep_def_merge_tr_cl                  false
% 7.05/1.48  --smt_preprocessing                     true
% 7.05/1.48  --smt_ac_axioms                         fast
% 7.05/1.48  --preprocessed_out                      false
% 7.05/1.48  --preprocessed_stats                    false
% 7.05/1.48  
% 7.05/1.48  ------ Abstraction refinement Options
% 7.05/1.48  
% 7.05/1.48  --abstr_ref                             []
% 7.05/1.48  --abstr_ref_prep                        false
% 7.05/1.48  --abstr_ref_until_sat                   false
% 7.05/1.48  --abstr_ref_sig_restrict                funpre
% 7.05/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.48  --abstr_ref_under                       []
% 7.05/1.48  
% 7.05/1.48  ------ SAT Options
% 7.05/1.48  
% 7.05/1.48  --sat_mode                              false
% 7.05/1.48  --sat_fm_restart_options                ""
% 7.05/1.48  --sat_gr_def                            false
% 7.05/1.48  --sat_epr_types                         true
% 7.05/1.48  --sat_non_cyclic_types                  false
% 7.05/1.48  --sat_finite_models                     false
% 7.05/1.48  --sat_fm_lemmas                         false
% 7.05/1.48  --sat_fm_prep                           false
% 7.05/1.48  --sat_fm_uc_incr                        true
% 7.05/1.48  --sat_out_model                         small
% 7.05/1.48  --sat_out_clauses                       false
% 7.05/1.48  
% 7.05/1.48  ------ QBF Options
% 7.05/1.48  
% 7.05/1.48  --qbf_mode                              false
% 7.05/1.48  --qbf_elim_univ                         false
% 7.05/1.48  --qbf_dom_inst                          none
% 7.05/1.48  --qbf_dom_pre_inst                      false
% 7.05/1.48  --qbf_sk_in                             false
% 7.05/1.48  --qbf_pred_elim                         true
% 7.05/1.48  --qbf_split                             512
% 7.05/1.48  
% 7.05/1.48  ------ BMC1 Options
% 7.05/1.48  
% 7.05/1.48  --bmc1_incremental                      false
% 7.05/1.48  --bmc1_axioms                           reachable_all
% 7.05/1.48  --bmc1_min_bound                        0
% 7.05/1.48  --bmc1_max_bound                        -1
% 7.05/1.48  --bmc1_max_bound_default                -1
% 7.05/1.48  --bmc1_symbol_reachability              true
% 7.05/1.48  --bmc1_property_lemmas                  false
% 7.05/1.48  --bmc1_k_induction                      false
% 7.05/1.48  --bmc1_non_equiv_states                 false
% 7.05/1.48  --bmc1_deadlock                         false
% 7.05/1.48  --bmc1_ucm                              false
% 7.05/1.48  --bmc1_add_unsat_core                   none
% 7.05/1.48  --bmc1_unsat_core_children              false
% 7.05/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.48  --bmc1_out_stat                         full
% 7.05/1.48  --bmc1_ground_init                      false
% 7.05/1.48  --bmc1_pre_inst_next_state              false
% 7.05/1.48  --bmc1_pre_inst_state                   false
% 7.05/1.48  --bmc1_pre_inst_reach_state             false
% 7.05/1.48  --bmc1_out_unsat_core                   false
% 7.05/1.48  --bmc1_aig_witness_out                  false
% 7.05/1.48  --bmc1_verbose                          false
% 7.05/1.48  --bmc1_dump_clauses_tptp                false
% 7.05/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.48  --bmc1_dump_file                        -
% 7.05/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.48  --bmc1_ucm_extend_mode                  1
% 7.05/1.48  --bmc1_ucm_init_mode                    2
% 7.05/1.48  --bmc1_ucm_cone_mode                    none
% 7.05/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.48  --bmc1_ucm_relax_model                  4
% 7.05/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.48  --bmc1_ucm_layered_model                none
% 7.05/1.48  --bmc1_ucm_max_lemma_size               10
% 7.05/1.48  
% 7.05/1.48  ------ AIG Options
% 7.05/1.48  
% 7.05/1.48  --aig_mode                              false
% 7.05/1.48  
% 7.05/1.48  ------ Instantiation Options
% 7.05/1.48  
% 7.05/1.48  --instantiation_flag                    true
% 7.05/1.48  --inst_sos_flag                         false
% 7.05/1.48  --inst_sos_phase                        true
% 7.05/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.48  --inst_lit_sel_side                     none
% 7.05/1.48  --inst_solver_per_active                1400
% 7.05/1.48  --inst_solver_calls_frac                1.
% 7.05/1.48  --inst_passive_queue_type               priority_queues
% 7.05/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.48  --inst_passive_queues_freq              [25;2]
% 7.05/1.48  --inst_dismatching                      true
% 7.05/1.48  --inst_eager_unprocessed_to_passive     true
% 7.05/1.48  --inst_prop_sim_given                   true
% 7.05/1.48  --inst_prop_sim_new                     false
% 7.05/1.48  --inst_subs_new                         false
% 7.05/1.48  --inst_eq_res_simp                      false
% 7.05/1.48  --inst_subs_given                       false
% 7.05/1.48  --inst_orphan_elimination               true
% 7.05/1.48  --inst_learning_loop_flag               true
% 7.05/1.48  --inst_learning_start                   3000
% 7.05/1.48  --inst_learning_factor                  2
% 7.05/1.48  --inst_start_prop_sim_after_learn       3
% 7.05/1.48  --inst_sel_renew                        solver
% 7.05/1.48  --inst_lit_activity_flag                true
% 7.05/1.48  --inst_restr_to_given                   false
% 7.05/1.48  --inst_activity_threshold               500
% 7.05/1.48  --inst_out_proof                        true
% 7.05/1.48  
% 7.05/1.48  ------ Resolution Options
% 7.05/1.48  
% 7.05/1.48  --resolution_flag                       false
% 7.05/1.48  --res_lit_sel                           adaptive
% 7.05/1.48  --res_lit_sel_side                      none
% 7.05/1.48  --res_ordering                          kbo
% 7.05/1.48  --res_to_prop_solver                    active
% 7.05/1.48  --res_prop_simpl_new                    false
% 7.05/1.48  --res_prop_simpl_given                  true
% 7.05/1.48  --res_passive_queue_type                priority_queues
% 7.05/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.48  --res_passive_queues_freq               [15;5]
% 7.05/1.48  --res_forward_subs                      full
% 7.05/1.48  --res_backward_subs                     full
% 7.05/1.48  --res_forward_subs_resolution           true
% 7.05/1.48  --res_backward_subs_resolution          true
% 7.05/1.48  --res_orphan_elimination                true
% 7.05/1.48  --res_time_limit                        2.
% 7.05/1.48  --res_out_proof                         true
% 7.05/1.48  
% 7.05/1.48  ------ Superposition Options
% 7.05/1.48  
% 7.05/1.48  --superposition_flag                    true
% 7.05/1.48  --sup_passive_queue_type                priority_queues
% 7.05/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.48  --demod_completeness_check              fast
% 7.05/1.48  --demod_use_ground                      true
% 7.05/1.48  --sup_to_prop_solver                    passive
% 7.05/1.48  --sup_prop_simpl_new                    true
% 7.05/1.48  --sup_prop_simpl_given                  true
% 7.05/1.48  --sup_fun_splitting                     false
% 7.05/1.48  --sup_smt_interval                      50000
% 7.05/1.48  
% 7.05/1.48  ------ Superposition Simplification Setup
% 7.05/1.48  
% 7.05/1.48  --sup_indices_passive                   []
% 7.05/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.48  --sup_full_bw                           [BwDemod]
% 7.05/1.48  --sup_immed_triv                        [TrivRules]
% 7.05/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.48  --sup_immed_bw_main                     []
% 7.05/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.48  
% 7.05/1.48  ------ Combination Options
% 7.05/1.48  
% 7.05/1.48  --comb_res_mult                         3
% 7.05/1.48  --comb_sup_mult                         2
% 7.05/1.48  --comb_inst_mult                        10
% 7.05/1.48  
% 7.05/1.48  ------ Debug Options
% 7.05/1.48  
% 7.05/1.48  --dbg_backtrace                         false
% 7.05/1.48  --dbg_dump_prop_clauses                 false
% 7.05/1.48  --dbg_dump_prop_clauses_file            -
% 7.05/1.48  --dbg_out_stat                          false
% 7.05/1.48  
% 7.05/1.48  
% 7.05/1.48  
% 7.05/1.48  
% 7.05/1.48  ------ Proving...
% 7.05/1.48  
% 7.05/1.48  
% 7.05/1.48  % SZS status Theorem for theBenchmark.p
% 7.05/1.48  
% 7.05/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.05/1.48  
% 7.05/1.48  fof(f15,conjecture,(
% 7.05/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f16,negated_conjecture,(
% 7.05/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.05/1.48    inference(negated_conjecture,[],[f15])).
% 7.05/1.48  
% 7.05/1.48  fof(f36,plain,(
% 7.05/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.05/1.48    inference(ennf_transformation,[],[f16])).
% 7.05/1.48  
% 7.05/1.48  fof(f37,plain,(
% 7.05/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.05/1.48    inference(flattening,[],[f36])).
% 7.05/1.48  
% 7.05/1.48  fof(f41,plain,(
% 7.05/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.05/1.48    introduced(choice_axiom,[])).
% 7.05/1.48  
% 7.05/1.48  fof(f40,plain,(
% 7.05/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.05/1.48    introduced(choice_axiom,[])).
% 7.05/1.48  
% 7.05/1.48  fof(f42,plain,(
% 7.05/1.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.05/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40])).
% 7.05/1.48  
% 7.05/1.48  fof(f68,plain,(
% 7.05/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f7,axiom,(
% 7.05/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f25,plain,(
% 7.05/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.48    inference(ennf_transformation,[],[f7])).
% 7.05/1.48  
% 7.05/1.48  fof(f51,plain,(
% 7.05/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.48    inference(cnf_transformation,[],[f25])).
% 7.05/1.48  
% 7.05/1.48  fof(f72,plain,(
% 7.05/1.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f71,plain,(
% 7.05/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f10,axiom,(
% 7.05/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f28,plain,(
% 7.05/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.48    inference(ennf_transformation,[],[f10])).
% 7.05/1.48  
% 7.05/1.48  fof(f29,plain,(
% 7.05/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.48    inference(flattening,[],[f28])).
% 7.05/1.48  
% 7.05/1.48  fof(f39,plain,(
% 7.05/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.48    inference(nnf_transformation,[],[f29])).
% 7.05/1.48  
% 7.05/1.48  fof(f55,plain,(
% 7.05/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.48    inference(cnf_transformation,[],[f39])).
% 7.05/1.48  
% 7.05/1.48  fof(f6,axiom,(
% 7.05/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f24,plain,(
% 7.05/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.48    inference(ennf_transformation,[],[f6])).
% 7.05/1.48  
% 7.05/1.48  fof(f50,plain,(
% 7.05/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.48    inference(cnf_transformation,[],[f24])).
% 7.05/1.48  
% 7.05/1.48  fof(f70,plain,(
% 7.05/1.48    v1_funct_2(sK3,sK1,sK0)),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f75,plain,(
% 7.05/1.48    k1_xboole_0 != sK0),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f2,axiom,(
% 7.05/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f17,plain,(
% 7.05/1.48    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.05/1.48    inference(ennf_transformation,[],[f2])).
% 7.05/1.48  
% 7.05/1.48  fof(f18,plain,(
% 7.05/1.48    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.05/1.48    inference(flattening,[],[f17])).
% 7.05/1.48  
% 7.05/1.48  fof(f46,plain,(
% 7.05/1.48    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.05/1.48    inference(cnf_transformation,[],[f18])).
% 7.05/1.48  
% 7.05/1.48  fof(f69,plain,(
% 7.05/1.48    v1_funct_1(sK3)),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f5,axiom,(
% 7.05/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f23,plain,(
% 7.05/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.48    inference(ennf_transformation,[],[f5])).
% 7.05/1.48  
% 7.05/1.48  fof(f49,plain,(
% 7.05/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.48    inference(cnf_transformation,[],[f23])).
% 7.05/1.48  
% 7.05/1.48  fof(f12,axiom,(
% 7.05/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f32,plain,(
% 7.05/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.05/1.48    inference(ennf_transformation,[],[f12])).
% 7.05/1.48  
% 7.05/1.48  fof(f33,plain,(
% 7.05/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.05/1.48    inference(flattening,[],[f32])).
% 7.05/1.48  
% 7.05/1.48  fof(f63,plain,(
% 7.05/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.05/1.48    inference(cnf_transformation,[],[f33])).
% 7.05/1.48  
% 7.05/1.48  fof(f66,plain,(
% 7.05/1.48    v1_funct_1(sK2)),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f8,axiom,(
% 7.05/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f26,plain,(
% 7.05/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.05/1.48    inference(ennf_transformation,[],[f8])).
% 7.05/1.48  
% 7.05/1.48  fof(f27,plain,(
% 7.05/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.48    inference(flattening,[],[f26])).
% 7.05/1.48  
% 7.05/1.48  fof(f38,plain,(
% 7.05/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.48    inference(nnf_transformation,[],[f27])).
% 7.05/1.48  
% 7.05/1.48  fof(f52,plain,(
% 7.05/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.48    inference(cnf_transformation,[],[f38])).
% 7.05/1.48  
% 7.05/1.48  fof(f73,plain,(
% 7.05/1.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f9,axiom,(
% 7.05/1.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f54,plain,(
% 7.05/1.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.05/1.48    inference(cnf_transformation,[],[f9])).
% 7.05/1.48  
% 7.05/1.48  fof(f13,axiom,(
% 7.05/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f64,plain,(
% 7.05/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.05/1.48    inference(cnf_transformation,[],[f13])).
% 7.05/1.48  
% 7.05/1.48  fof(f81,plain,(
% 7.05/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.05/1.48    inference(definition_unfolding,[],[f54,f64])).
% 7.05/1.48  
% 7.05/1.48  fof(f11,axiom,(
% 7.05/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f30,plain,(
% 7.05/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.05/1.48    inference(ennf_transformation,[],[f11])).
% 7.05/1.48  
% 7.05/1.48  fof(f31,plain,(
% 7.05/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.05/1.48    inference(flattening,[],[f30])).
% 7.05/1.48  
% 7.05/1.48  fof(f62,plain,(
% 7.05/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.05/1.48    inference(cnf_transformation,[],[f31])).
% 7.05/1.48  
% 7.05/1.48  fof(f1,axiom,(
% 7.05/1.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f44,plain,(
% 7.05/1.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.05/1.48    inference(cnf_transformation,[],[f1])).
% 7.05/1.48  
% 7.05/1.48  fof(f78,plain,(
% 7.05/1.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.05/1.48    inference(definition_unfolding,[],[f44,f64])).
% 7.05/1.48  
% 7.05/1.48  fof(f3,axiom,(
% 7.05/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f19,plain,(
% 7.05/1.48    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.05/1.48    inference(ennf_transformation,[],[f3])).
% 7.05/1.48  
% 7.05/1.48  fof(f20,plain,(
% 7.05/1.48    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.05/1.48    inference(flattening,[],[f19])).
% 7.05/1.48  
% 7.05/1.48  fof(f47,plain,(
% 7.05/1.48    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.05/1.48    inference(cnf_transformation,[],[f20])).
% 7.05/1.48  
% 7.05/1.48  fof(f80,plain,(
% 7.05/1.48    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.05/1.48    inference(definition_unfolding,[],[f47,f64])).
% 7.05/1.48  
% 7.05/1.48  fof(f14,axiom,(
% 7.05/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f34,plain,(
% 7.05/1.48    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.05/1.48    inference(ennf_transformation,[],[f14])).
% 7.05/1.48  
% 7.05/1.48  fof(f35,plain,(
% 7.05/1.48    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.05/1.48    inference(flattening,[],[f34])).
% 7.05/1.48  
% 7.05/1.48  fof(f65,plain,(
% 7.05/1.48    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.05/1.48    inference(cnf_transformation,[],[f35])).
% 7.05/1.48  
% 7.05/1.48  fof(f67,plain,(
% 7.05/1.48    v1_funct_2(sK2,sK0,sK1)),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  fof(f4,axiom,(
% 7.05/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 7.05/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.05/1.48  
% 7.05/1.48  fof(f21,plain,(
% 7.05/1.48    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.05/1.48    inference(ennf_transformation,[],[f4])).
% 7.05/1.48  
% 7.05/1.48  fof(f22,plain,(
% 7.05/1.48    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.05/1.48    inference(flattening,[],[f21])).
% 7.05/1.48  
% 7.05/1.48  fof(f48,plain,(
% 7.05/1.48    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.05/1.48    inference(cnf_transformation,[],[f22])).
% 7.05/1.48  
% 7.05/1.48  fof(f77,plain,(
% 7.05/1.48    k2_funct_1(sK2) != sK3),
% 7.05/1.48    inference(cnf_transformation,[],[f42])).
% 7.05/1.48  
% 7.05/1.48  cnf(c_31,negated_conjecture,
% 7.05/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.05/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_1150,plain,
% 7.05/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.05/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_8,plain,
% 7.05/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.05/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_1165,plain,
% 7.05/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.05/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_2081,plain,
% 7.05/1.48      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.05/1.48      inference(superposition,[status(thm)],[c_1150,c_1165]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_27,negated_conjecture,
% 7.05/1.48      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.05/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_2083,plain,
% 7.05/1.48      ( k2_relat_1(sK2) = sK1 ),
% 7.05/1.48      inference(light_normalisation,[status(thm)],[c_2081,c_27]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_28,negated_conjecture,
% 7.05/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.05/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_1153,plain,
% 7.05/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.05/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_17,plain,
% 7.05/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.05/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.05/1.48      | k1_xboole_0 = X2 ),
% 7.05/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_1158,plain,
% 7.05/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.05/1.48      | k1_xboole_0 = X1
% 7.05/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.05/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_2711,plain,
% 7.05/1.48      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 7.05/1.48      | sK0 = k1_xboole_0
% 7.05/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.05/1.48      inference(superposition,[status(thm)],[c_1153,c_1158]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_7,plain,
% 7.05/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.05/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_1166,plain,
% 7.05/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.05/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_2125,plain,
% 7.05/1.48      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 7.05/1.48      inference(superposition,[status(thm)],[c_1153,c_1166]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_2723,plain,
% 7.05/1.48      ( k1_relat_1(sK3) = sK1
% 7.05/1.48      | sK0 = k1_xboole_0
% 7.05/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.05/1.48      inference(demodulation,[status(thm)],[c_2711,c_2125]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_29,negated_conjecture,
% 7.05/1.48      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.05/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_38,plain,
% 7.05/1.48      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.05/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_24,negated_conjecture,
% 7.05/1.48      ( k1_xboole_0 != sK0 ),
% 7.05/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_638,plain,( X0 = X0 ),theory(equality) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_665,plain,
% 7.05/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.05/1.48      inference(instantiation,[status(thm)],[c_638]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_639,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_1493,plain,
% 7.05/1.48      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.05/1.48      inference(instantiation,[status(thm)],[c_639]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_1494,plain,
% 7.05/1.48      ( sK0 != k1_xboole_0
% 7.05/1.48      | k1_xboole_0 = sK0
% 7.05/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.05/1.48      inference(instantiation,[status(thm)],[c_1493]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_3468,plain,
% 7.05/1.48      ( k1_relat_1(sK3) = sK1 ),
% 7.05/1.48      inference(global_propositional_subsumption,
% 7.05/1.48                [status(thm)],
% 7.05/1.48                [c_2723,c_38,c_24,c_665,c_1494]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_2,plain,
% 7.05/1.48      ( ~ v1_funct_1(X0)
% 7.05/1.48      | ~ v1_funct_1(X1)
% 7.05/1.48      | ~ v1_relat_1(X0)
% 7.05/1.48      | ~ v1_relat_1(X1)
% 7.05/1.48      | v2_funct_1(X1)
% 7.05/1.48      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 7.05/1.48      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 7.05/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.05/1.48  
% 7.05/1.48  cnf(c_1171,plain,
% 7.05/1.48      ( k1_relat_1(X0) != k2_relat_1(X1)
% 7.05/1.48      | v1_funct_1(X1) != iProver_top
% 7.05/1.48      | v1_funct_1(X0) != iProver_top
% 7.05/1.48      | v1_relat_1(X1) != iProver_top
% 7.05/1.48      | v1_relat_1(X0) != iProver_top
% 7.05/1.48      | v2_funct_1(X0) = iProver_top
% 7.05/1.48      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3891,plain,
% 7.05/1.49      ( k2_relat_1(X0) != sK1
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(sK3) != iProver_top
% 7.05/1.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_3468,c_1171]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_30,negated_conjecture,
% 7.05/1.49      ( v1_funct_1(sK3) ),
% 7.05/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_37,plain,
% 7.05/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_39,plain,
% 7.05/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | v1_relat_1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1456,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.05/1.49      | v1_relat_1(sK3) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1457,plain,
% 7.05/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.05/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17751,plain,
% 7.05/1.49      ( v1_relat_1(X0) != iProver_top
% 7.05/1.49      | k2_relat_1(X0) != sK1
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_3891,c_37,c_39,c_1457]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17752,plain,
% 7.05/1.49      ( k2_relat_1(X0) != sK1
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_17751]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17763,plain,
% 7.05/1.49      ( v1_funct_1(sK2) != iProver_top
% 7.05/1.49      | v1_relat_1(sK2) != iProver_top
% 7.05/1.49      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_2083,c_17752]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_20,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(X3)
% 7.05/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1155,plain,
% 7.05/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.05/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.05/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.49      | v1_funct_1(X4) != iProver_top
% 7.05/1.49      | v1_funct_1(X5) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3620,plain,
% 7.05/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.49      | v1_funct_1(X2) != iProver_top
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1153,c_1155]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3656,plain,
% 7.05/1.49      ( v1_funct_1(X2) != iProver_top
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_3620,c_37]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3657,plain,
% 7.05/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_3656]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3667,plain,
% 7.05/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.05/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1150,c_3657]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_33,negated_conjecture,
% 7.05/1.49      ( v1_funct_1(sK2) ),
% 7.05/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1630,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(sK3)
% 7.05/1.49      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1966,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.05/1.49      | ~ v1_funct_1(sK3)
% 7.05/1.49      | ~ v1_funct_1(sK2)
% 7.05/1.49      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_1630]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2149,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.05/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.49      | ~ v1_funct_1(sK3)
% 7.05/1.49      | ~ v1_funct_1(sK2)
% 7.05/1.49      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_1966]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2230,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.05/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.05/1.49      | ~ v1_funct_1(sK3)
% 7.05/1.49      | ~ v1_funct_1(sK2)
% 7.05/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_2149]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4166,plain,
% 7.05/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_3667,c_33,c_31,c_30,c_28,c_2230]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_10,plain,
% 7.05/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.05/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.49      | X3 = X2 ),
% 7.05/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_26,negated_conjecture,
% 7.05/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.05/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_373,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | X3 = X0
% 7.05/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.05/1.49      | k6_partfun1(sK0) != X3
% 7.05/1.49      | sK0 != X2
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_374,plain,
% 7.05/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.05/1.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.05/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_373]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_11,plain,
% 7.05/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.05/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_382,plain,
% 7.05/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.05/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.05/1.49      inference(forward_subsumption_resolution,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_374,c_11]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1146,plain,
% 7.05/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.05/1.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4169,plain,
% 7.05/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.05/1.49      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.05/1.49      inference(demodulation,[status(thm)],[c_4166,c_1146]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_34,plain,
% 7.05/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_36,plain,
% 7.05/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_18,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.05/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(X3) ),
% 7.05/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1157,plain,
% 7.05/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.05/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.05/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.05/1.49      | v1_funct_1(X3) != iProver_top
% 7.05/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4195,plain,
% 7.05/1.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.05/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.05/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top
% 7.05/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_4166,c_1157]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4335,plain,
% 7.05/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_4169,c_34,c_36,c_37,c_39,c_4195]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17768,plain,
% 7.05/1.49      ( v1_funct_1(sK2) != iProver_top
% 7.05/1.49      | v1_relat_1(sK2) != iProver_top
% 7.05/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(light_normalisation,[status(thm)],[c_17763,c_4335]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1459,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.05/1.49      | v1_relat_1(sK2) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1460,plain,
% 7.05/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.05/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17983,plain,
% 7.05/1.49      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_17768,c_34,c_36,c_1460]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_0,plain,
% 7.05/1.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.05/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1173,plain,
% 7.05/1.49      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17989,plain,
% 7.05/1.49      ( v2_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(forward_subsumption_resolution,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_17983,c_1173]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4,plain,
% 7.05/1.49      ( ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(X1)
% 7.05/1.49      | ~ v1_relat_1(X0)
% 7.05/1.49      | ~ v1_relat_1(X1)
% 7.05/1.49      | ~ v2_funct_1(X1)
% 7.05/1.49      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.05/1.49      | k2_funct_1(X1) = X0
% 7.05/1.49      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1169,plain,
% 7.05/1.49      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.05/1.49      | k2_funct_1(X1) = X0
% 7.05/1.49      | k1_relat_1(X1) != k2_relat_1(X0)
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_funct_1(X1) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X1) != iProver_top
% 7.05/1.49      | v2_funct_1(X1) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4339,plain,
% 7.05/1.49      ( k2_funct_1(sK3) = sK2
% 7.05/1.49      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 7.05/1.49      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top
% 7.05/1.49      | v1_funct_1(sK2) != iProver_top
% 7.05/1.49      | v1_relat_1(sK3) != iProver_top
% 7.05/1.49      | v1_relat_1(sK2) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_4335,c_1169]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2080,plain,
% 7.05/1.49      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1153,c_1165]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_21,plain,
% 7.05/1.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.05/1.49      | ~ v1_funct_2(X3,X1,X0)
% 7.05/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.05/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.49      | ~ v1_funct_1(X2)
% 7.05/1.49      | ~ v1_funct_1(X3)
% 7.05/1.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.05/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_386,plain,
% 7.05/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.05/1.49      | ~ v1_funct_2(X3,X2,X1)
% 7.05/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.05/1.49      | ~ v1_funct_1(X3)
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.05/1.49      | k2_relset_1(X2,X1,X3) = X1
% 7.05/1.49      | k6_partfun1(X1) != k6_partfun1(sK0)
% 7.05/1.49      | sK0 != X1 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_387,plain,
% 7.05/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.05/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.05/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.05/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.05/1.49      | ~ v1_funct_1(X2)
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.05/1.49      | k2_relset_1(X1,sK0,X0) = sK0
% 7.05/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_386]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_470,plain,
% 7.05/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.05/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.05/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.05/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(X2)
% 7.05/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.05/1.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.05/1.49      inference(equality_resolution_simp,[status(thm)],[c_387]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1145,plain,
% 7.05/1.49      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.05/1.49      | k2_relset_1(X0,sK0,X2) = sK0
% 7.05/1.49      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.05/1.49      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.05/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.05/1.49      | v1_funct_1(X1) != iProver_top
% 7.05/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1663,plain,
% 7.05/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.05/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.05/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.05/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.05/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top
% 7.05/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.05/1.49      inference(equality_resolution,[status(thm)],[c_1145]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_32,negated_conjecture,
% 7.05/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.05/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_35,plain,
% 7.05/1.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1869,plain,
% 7.05/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_1663,c_34,c_35,c_36,c_37,c_38,c_39]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2086,plain,
% 7.05/1.49      ( k2_relat_1(sK3) = sK0 ),
% 7.05/1.49      inference(light_normalisation,[status(thm)],[c_2080,c_1869]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4340,plain,
% 7.05/1.49      ( k2_funct_1(sK3) = sK2
% 7.05/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.05/1.49      | sK1 != sK1
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top
% 7.05/1.49      | v1_funct_1(sK2) != iProver_top
% 7.05/1.49      | v1_relat_1(sK3) != iProver_top
% 7.05/1.49      | v1_relat_1(sK2) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.05/1.49      inference(light_normalisation,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_4339,c_2083,c_2086,c_3468]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4341,plain,
% 7.05/1.49      ( k2_funct_1(sK3) = sK2
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top
% 7.05/1.49      | v1_funct_1(sK2) != iProver_top
% 7.05/1.49      | v1_relat_1(sK3) != iProver_top
% 7.05/1.49      | v1_relat_1(sK2) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.05/1.49      inference(equality_resolution_simp,[status(thm)],[c_4340]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5595,plain,
% 7.05/1.49      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_4341,c_34,c_36,c_37,c_39,c_1457,c_1460]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17991,plain,
% 7.05/1.49      ( k2_funct_1(sK3) = sK2 ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_17989,c_5595]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1151,plain,
% 7.05/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5,plain,
% 7.05/1.49      ( ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_relat_1(X0)
% 7.05/1.49      | ~ v2_funct_1(X0)
% 7.05/1.49      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 7.05/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1168,plain,
% 7.05/1.49      ( k2_funct_1(k2_funct_1(X0)) = X0
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v2_funct_1(X0) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2202,plain,
% 7.05/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.05/1.49      | v1_relat_1(sK3) != iProver_top
% 7.05/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1151,c_1168]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2292,plain,
% 7.05/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.05/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_2202,c_39,c_1457]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17992,plain,
% 7.05/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_17989,c_2292]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17996,plain,
% 7.05/1.49      ( k2_funct_1(sK2) = sK3 ),
% 7.05/1.49      inference(demodulation,[status(thm)],[c_17991,c_17992]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_22,negated_conjecture,
% 7.05/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.05/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(contradiction,plain,
% 7.05/1.49      ( $false ),
% 7.05/1.49      inference(minisat,[status(thm)],[c_17996,c_22]) ).
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  ------                               Statistics
% 7.05/1.49  
% 7.05/1.49  ------ General
% 7.05/1.49  
% 7.05/1.49  abstr_ref_over_cycles:                  0
% 7.05/1.49  abstr_ref_under_cycles:                 0
% 7.05/1.49  gc_basic_clause_elim:                   0
% 7.05/1.49  forced_gc_time:                         0
% 7.05/1.49  parsing_time:                           0.01
% 7.05/1.49  unif_index_cands_time:                  0.
% 7.05/1.49  unif_index_add_time:                    0.
% 7.05/1.49  orderings_time:                         0.
% 7.05/1.49  out_proof_time:                         0.011
% 7.05/1.49  total_time:                             0.599
% 7.05/1.49  num_of_symbols:                         52
% 7.05/1.49  num_of_terms:                           20669
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing
% 7.05/1.49  
% 7.05/1.49  num_of_splits:                          0
% 7.05/1.49  num_of_split_atoms:                     0
% 7.05/1.49  num_of_reused_defs:                     0
% 7.05/1.49  num_eq_ax_congr_red:                    18
% 7.05/1.49  num_of_sem_filtered_clauses:            1
% 7.05/1.49  num_of_subtypes:                        0
% 7.05/1.49  monotx_restored_types:                  0
% 7.05/1.49  sat_num_of_epr_types:                   0
% 7.05/1.49  sat_num_of_non_cyclic_types:            0
% 7.05/1.49  sat_guarded_non_collapsed_types:        0
% 7.05/1.49  num_pure_diseq_elim:                    0
% 7.05/1.49  simp_replaced_by:                       0
% 7.05/1.49  res_preprocessed:                       162
% 7.05/1.49  prep_upred:                             0
% 7.05/1.49  prep_unflattend:                        12
% 7.05/1.49  smt_new_axioms:                         0
% 7.05/1.49  pred_elim_cands:                        5
% 7.05/1.49  pred_elim:                              1
% 7.05/1.49  pred_elim_cl:                           1
% 7.05/1.49  pred_elim_cycles:                       3
% 7.05/1.49  merged_defs:                            0
% 7.05/1.49  merged_defs_ncl:                        0
% 7.05/1.49  bin_hyper_res:                          0
% 7.05/1.49  prep_cycles:                            4
% 7.05/1.49  pred_elim_time:                         0.005
% 7.05/1.49  splitting_time:                         0.
% 7.05/1.49  sem_filter_time:                        0.
% 7.05/1.49  monotx_time:                            0.001
% 7.05/1.49  subtype_inf_time:                       0.
% 7.05/1.49  
% 7.05/1.49  ------ Problem properties
% 7.05/1.49  
% 7.05/1.49  clauses:                                33
% 7.05/1.49  conjectures:                            11
% 7.05/1.49  epr:                                    7
% 7.05/1.49  horn:                                   29
% 7.05/1.49  ground:                                 12
% 7.05/1.49  unary:                                  14
% 7.05/1.49  binary:                                 4
% 7.05/1.49  lits:                                   100
% 7.05/1.49  lits_eq:                                27
% 7.05/1.49  fd_pure:                                0
% 7.05/1.49  fd_pseudo:                              0
% 7.05/1.49  fd_cond:                                3
% 7.05/1.49  fd_pseudo_cond:                         1
% 7.05/1.49  ac_symbols:                             0
% 7.05/1.49  
% 7.05/1.49  ------ Propositional Solver
% 7.05/1.49  
% 7.05/1.49  prop_solver_calls:                      30
% 7.05/1.49  prop_fast_solver_calls:                 1949
% 7.05/1.49  smt_solver_calls:                       0
% 7.05/1.49  smt_fast_solver_calls:                  0
% 7.05/1.49  prop_num_of_clauses:                    7310
% 7.05/1.49  prop_preprocess_simplified:             13157
% 7.05/1.49  prop_fo_subsumed:                       219
% 7.05/1.49  prop_solver_time:                       0.
% 7.05/1.49  smt_solver_time:                        0.
% 7.05/1.49  smt_fast_solver_time:                   0.
% 7.05/1.49  prop_fast_solver_time:                  0.
% 7.05/1.49  prop_unsat_core_time:                   0.001
% 7.05/1.49  
% 7.05/1.49  ------ QBF
% 7.05/1.49  
% 7.05/1.49  qbf_q_res:                              0
% 7.05/1.49  qbf_num_tautologies:                    0
% 7.05/1.49  qbf_prep_cycles:                        0
% 7.05/1.49  
% 7.05/1.49  ------ BMC1
% 7.05/1.49  
% 7.05/1.49  bmc1_current_bound:                     -1
% 7.05/1.49  bmc1_last_solved_bound:                 -1
% 7.05/1.49  bmc1_unsat_core_size:                   -1
% 7.05/1.49  bmc1_unsat_core_parents_size:           -1
% 7.05/1.49  bmc1_merge_next_fun:                    0
% 7.05/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation
% 7.05/1.49  
% 7.05/1.49  inst_num_of_clauses:                    2072
% 7.05/1.49  inst_num_in_passive:                    691
% 7.05/1.49  inst_num_in_active:                     977
% 7.05/1.49  inst_num_in_unprocessed:                405
% 7.05/1.49  inst_num_of_loops:                      1080
% 7.05/1.49  inst_num_of_learning_restarts:          0
% 7.05/1.49  inst_num_moves_active_passive:          99
% 7.05/1.49  inst_lit_activity:                      0
% 7.05/1.49  inst_lit_activity_moves:                1
% 7.05/1.49  inst_num_tautologies:                   0
% 7.05/1.49  inst_num_prop_implied:                  0
% 7.05/1.49  inst_num_existing_simplified:           0
% 7.05/1.49  inst_num_eq_res_simplified:             0
% 7.05/1.49  inst_num_child_elim:                    0
% 7.05/1.49  inst_num_of_dismatching_blockings:      143
% 7.05/1.49  inst_num_of_non_proper_insts:           1427
% 7.05/1.49  inst_num_of_duplicates:                 0
% 7.05/1.49  inst_inst_num_from_inst_to_res:         0
% 7.05/1.49  inst_dismatching_checking_time:         0.
% 7.05/1.49  
% 7.05/1.49  ------ Resolution
% 7.05/1.49  
% 7.05/1.49  res_num_of_clauses:                     0
% 7.05/1.49  res_num_in_passive:                     0
% 7.05/1.49  res_num_in_active:                      0
% 7.05/1.49  res_num_of_loops:                       166
% 7.05/1.49  res_forward_subset_subsumed:            127
% 7.05/1.49  res_backward_subset_subsumed:           2
% 7.05/1.49  res_forward_subsumed:                   0
% 7.05/1.49  res_backward_subsumed:                  0
% 7.05/1.49  res_forward_subsumption_resolution:     2
% 7.05/1.49  res_backward_subsumption_resolution:    0
% 7.05/1.49  res_clause_to_clause_subsumption:       1348
% 7.05/1.49  res_orphan_elimination:                 0
% 7.05/1.49  res_tautology_del:                      68
% 7.05/1.49  res_num_eq_res_simplified:              1
% 7.05/1.49  res_num_sel_changes:                    0
% 7.05/1.49  res_moves_from_active_to_pass:          0
% 7.05/1.49  
% 7.05/1.49  ------ Superposition
% 7.05/1.49  
% 7.05/1.49  sup_time_total:                         0.
% 7.05/1.49  sup_time_generating:                    0.
% 7.05/1.49  sup_time_sim_full:                      0.
% 7.05/1.49  sup_time_sim_immed:                     0.
% 7.05/1.49  
% 7.05/1.49  sup_num_of_clauses:                     543
% 7.05/1.49  sup_num_in_active:                      209
% 7.05/1.49  sup_num_in_passive:                     334
% 7.05/1.49  sup_num_of_loops:                       214
% 7.05/1.49  sup_fw_superposition:                   312
% 7.05/1.49  sup_bw_superposition:                   268
% 7.05/1.49  sup_immediate_simplified:               203
% 7.05/1.49  sup_given_eliminated:                   0
% 7.05/1.49  comparisons_done:                       0
% 7.05/1.49  comparisons_avoided:                    1
% 7.05/1.49  
% 7.05/1.49  ------ Simplifications
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  sim_fw_subset_subsumed:                 24
% 7.05/1.49  sim_bw_subset_subsumed:                 9
% 7.05/1.49  sim_fw_subsumed:                        3
% 7.05/1.49  sim_bw_subsumed:                        0
% 7.05/1.49  sim_fw_subsumption_res:                 19
% 7.05/1.49  sim_bw_subsumption_res:                 0
% 7.05/1.49  sim_tautology_del:                      0
% 7.05/1.49  sim_eq_tautology_del:                   23
% 7.05/1.49  sim_eq_res_simp:                        1
% 7.05/1.49  sim_fw_demodulated:                     14
% 7.05/1.49  sim_bw_demodulated:                     6
% 7.05/1.49  sim_light_normalised:                   170
% 7.05/1.49  sim_joinable_taut:                      0
% 7.05/1.49  sim_joinable_simp:                      0
% 7.05/1.49  sim_ac_normalised:                      0
% 7.05/1.49  sim_smt_subsumption:                    0
% 7.05/1.49  
%------------------------------------------------------------------------------
