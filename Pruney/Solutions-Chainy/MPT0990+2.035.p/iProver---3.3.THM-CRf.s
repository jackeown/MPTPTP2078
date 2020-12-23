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
% DateTime   : Thu Dec  3 12:03:03 EST 2020

% Result     : Theorem 39.17s
% Output     : CNFRefutation 39.17s
% Verified   : 
% Statistics : Number of formulae       :  290 (4032 expanded)
%              Number of clauses        :  216 (1138 expanded)
%              Number of leaves         :   19 (1027 expanded)
%              Depth                    :   28
%              Number of atoms          : 1100 (35342 expanded)
%              Number of equality atoms :  686 (13190 expanded)
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

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f4,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f66])).

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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

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

cnf(c_101813,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_101825,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_102444,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_101813,c_101825])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_102446,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_102444,c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_101816,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_101819,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_102809,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_101816,c_101819])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_101826,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_102502,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_101816,c_101826])).

cnf(c_102821,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_102809,c_102502])).

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

cnf(c_7603,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_7604,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7603])).

cnf(c_24536,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24537,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_24589,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24536,c_24537])).

cnf(c_24538,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_24580,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_24536,c_24538])).

cnf(c_24590,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24589,c_24580])).

cnf(c_106832,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_102821,c_39,c_25,c_686,c_7604,c_24590])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_101832,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_106844,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_106832,c_101832])).

cnf(c_66459,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_66124,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
    | ~ iProver_ARSWP_238 ),
    inference(arg_filter_abstr,[status(unp)],[c_29])).

cnf(c_66437,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
    | iProver_ARSWP_238 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66124])).

cnf(c_66119,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_233
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(arg_filter_abstr,[status(unp)],[c_17])).

cnf(c_66442,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_233 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66119])).

cnf(c_67973,plain,
    ( k1_relset_1(sK1,X0,sK3) = sK1
    | k1_xboole_0 = X0
    | v1_funct_2(sK3,sK1,X0) != iProver_top
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_233 != iProver_top ),
    inference(superposition,[status(thm)],[c_66437,c_66442])).

cnf(c_69671,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_233 != iProver_top ),
    inference(superposition,[status(thm)],[c_66459,c_67973])).

cnf(c_24569,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_69704,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_69671,c_30,c_29,c_25,c_24569])).

cnf(c_66112,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_226
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_66449,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_66112])).

cnf(c_67547,plain,
    ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(superposition,[status(thm)],[c_66437,c_66449])).

cnf(c_69709,plain,
    ( k1_relat_1(sK3) = sK1
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(superposition,[status(thm)],[c_69704,c_67547])).

cnf(c_69998,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_69709,c_39,c_25,c_686,c_7604,c_24590])).

cnf(c_66465,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_70031,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_69998,c_66465])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_42719,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_42720,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42719])).

cnf(c_70499,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_70031,c_38,c_40,c_42720])).

cnf(c_70500,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_70499])).

cnf(c_133078,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_106844,c_38,c_40,c_42720,c_70031])).

cnf(c_133079,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_133078])).

cnf(c_133088,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_102446,c_133079])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_101516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ iProver_ARSWP_245 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_101805,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101516])).

cnf(c_103667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(superposition,[status(thm)],[c_101816,c_101805])).

cnf(c_103832,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103667,c_38])).

cnf(c_103833,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(renaming,[status(thm)],[c_103832])).

cnf(c_103844,plain,
    ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(superposition,[status(thm)],[c_101813,c_103833])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_104027,plain,
    ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103844,c_35])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f54])).

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
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_386,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_386,c_20])).

cnf(c_101520,plain,
    ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ iProver_ARSWP_249
    | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_394])).

cnf(c_101801,plain,
    ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | iProver_ARSWP_249 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101520])).

cnf(c_104046,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(superposition,[status(thm)],[c_104027,c_101801])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_101518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ iProver_ARSWP_247
    | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_21])).

cnf(c_101803,plain,
    ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101518])).

cnf(c_102670,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_101813,c_101803])).

cnf(c_103036,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_102670,c_35])).

cnf(c_103037,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(renaming,[status(thm)],[c_103036])).

cnf(c_103047,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_101816,c_103037])).

cnf(c_103084,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103047,c_38])).

cnf(c_104971,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_247 != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(superposition,[status(thm)],[c_104046,c_103084])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_62039,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_62042,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_62044,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_62436,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_62042,c_62044])).

cnf(c_62505,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62436,c_38])).

cnf(c_62506,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_62505])).

cnf(c_62517,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_62039,c_62506])).

cnf(c_62163,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_62256,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_62163])).

cnf(c_62592,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62517,c_34,c_32,c_31,c_29,c_62256])).

cnf(c_62036,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_62595,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62592,c_62036])).

cnf(c_62046,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_62597,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_62592,c_62046])).

cnf(c_108729,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_104971,c_35,c_37,c_38,c_40,c_62595,c_62597])).

cnf(c_133123,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_133088,c_108729])).

cnf(c_62196,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_62197,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62196])).

cnf(c_133255,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_133123,c_35,c_37,c_62197])).

cnf(c_0,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_101834,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_133261,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_133255,c_101834])).

cnf(c_101814,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_101829,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_102748,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_101814,c_101829])).

cnf(c_42601,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_42611,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_42798,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_42601,c_42611])).

cnf(c_102862,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_102748,c_40,c_42720,c_42798])).

cnf(c_106835,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_106832,c_102862])).

cnf(c_133263,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_133261,c_106835])).

cnf(c_103048,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_101813,c_103037])).

cnf(c_103337,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103048,c_35])).

cnf(c_103343,plain,
    ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_103084,c_103337])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_101828,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_103656,plain,
    ( k5_relat_1(sK2,sK2) != k6_partfun1(k2_relat_1(sK3))
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_103343,c_101828])).

cnf(c_102443,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_101816,c_101825])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f67])).

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
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

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

cnf(c_101521,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ iProver_ARSWP_250
    | k2_relset_1(X1,sK0,X0) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_483])).

cnf(c_101800,plain,
    ( k2_relset_1(X0,sK0,X1) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | v1_funct_2(X2,sK0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101521])).

cnf(c_102183,plain,
    ( k2_relset_1(sK1,sK0,X0) = sK0
    | v1_funct_2(X1,sK0,sK1) != iProver_top
    | v1_funct_2(X0,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_101800])).

cnf(c_102268,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(X0,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(superposition,[status(thm)],[c_101816,c_102183])).

cnf(c_62162,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_62243,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_62162])).

cnf(c_97513,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_34,c_32,c_31,c_29,c_62243])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_350,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X2 != X6
    | X2 != X5
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != X4
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_351,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k1_partfun1(X2,X1,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_373,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_351,c_18])).

cnf(c_97597,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X0,X0,X1,X3,X2)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_97893,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_97513,c_97597])).

cnf(c_97603,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_97610,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_97859,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_97603,c_97610])).

cnf(c_97894,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_97893,c_97859])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_98448,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_97894,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_98452,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_98448,c_97859])).

cnf(c_102293,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_102268,c_98452])).

cnf(c_102449,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_102443,c_102293])).

cnf(c_103657,plain,
    ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_103656,c_102446,c_102449])).

cnf(c_97600,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_97605,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_98095,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_97603,c_97605])).

cnf(c_98239,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_98095,c_38,c_62436])).

cnf(c_98240,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_98239])).

cnf(c_98249,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_97600,c_98240])).

cnf(c_98252,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_98249,c_97513])).

cnf(c_98356,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_98252,c_35,c_37,c_38,c_40,c_62595,c_62597])).

cnf(c_97613,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_98359,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_98356,c_97613])).

cnf(c_97860,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_97600,c_97610])).

cnf(c_97862,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_97860,c_28])).

cnf(c_97608,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_97954,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_97603,c_97608])).

cnf(c_98003,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_97954,c_30,c_29,c_25,c_24569])).

cnf(c_97611,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_97900,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_97603,c_97611])).

cnf(c_98006,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_98003,c_97900])).

cnf(c_98360,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_98359,c_97862,c_98006])).

cnf(c_98361,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_98360])).

cnf(c_63106,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62595,c_35,c_37,c_38,c_40,c_62597])).

cnf(c_62051,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_63114,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_63106,c_62051])).

cnf(c_62048,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_62273,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_62039,c_62048])).

cnf(c_62275,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_62273,c_28])).

cnf(c_62047,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_62388,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_62042,c_62047])).

cnf(c_62760,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_62388,c_30,c_29,c_25,c_24569])).

cnf(c_62049,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_62359,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_62042,c_62049])).

cnf(c_62763,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_62760,c_62359])).

cnf(c_63115,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_63114,c_62275,c_62763])).

cnf(c_63116,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_63115])).

cnf(c_64022,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63116,c_35,c_37,c_38,c_40,c_42720,c_62197])).

cnf(c_98723,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_98361,c_35,c_37,c_38,c_40,c_42720,c_62197,c_63116])).

cnf(c_98727,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_98723,c_98448])).

cnf(c_98728,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_98727])).

cnf(c_104446,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_103657,c_98728])).

cnf(c_104447,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_104446])).

cnf(c_133265,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_133261,c_104447])).

cnf(c_133270,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_133263,c_133265])).

cnf(c_169080,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_133270,c_101828])).

cnf(c_102810,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_101813,c_101819])).

cnf(c_102503,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_101813,c_101826])).

cnf(c_102814,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_102810,c_102503])).

cnf(c_62389,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_62039,c_62047])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_62193,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_62768,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_62389,c_33,c_32,c_24,c_62193])).

cnf(c_62360,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_62039,c_62049])).

cnf(c_62771,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_62768,c_62360])).

cnf(c_105922,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_102814,c_62771])).

cnf(c_169081,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_169080,c_102446,c_102449,c_105922])).

cnf(c_169082,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_169081])).

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
    inference(minisat,[status(thm)],[c_169082,c_62197,c_42720,c_23,c_42,c_40,c_38,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:41:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 39.17/5.41  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.17/5.41  
% 39.17/5.41  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.17/5.41  
% 39.17/5.41  ------  iProver source info
% 39.17/5.41  
% 39.17/5.41  git: date: 2020-06-30 10:37:57 +0100
% 39.17/5.41  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.17/5.41  git: non_committed_changes: false
% 39.17/5.41  git: last_make_outside_of_git: false
% 39.17/5.41  
% 39.17/5.41  ------ 
% 39.17/5.41  ------ Parsing...
% 39.17/5.41  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  ------ Proving...
% 39.17/5.41  ------ Problem Properties 
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  clauses                                 34
% 39.17/5.41  conjectures                             11
% 39.17/5.41  EPR                                     7
% 39.17/5.41  Horn                                    30
% 39.17/5.41  unary                                   14
% 39.17/5.41  binary                                  4
% 39.17/5.41  lits                                    104
% 39.17/5.41  lits eq                                 28
% 39.17/5.41  fd_pure                                 0
% 39.17/5.41  fd_pseudo                               0
% 39.17/5.41  fd_cond                                 3
% 39.17/5.41  fd_pseudo_cond                          1
% 39.17/5.41  AC symbols                              0
% 39.17/5.41  
% 39.17/5.41  ------ Input Options Time Limit: Unbounded
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 39.17/5.41  Current options:
% 39.17/5.41  ------ 
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.17/5.41  
% 39.17/5.41  ------ Proving...
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  % SZS status Theorem for theBenchmark.p
% 39.17/5.41  
% 39.17/5.41  % SZS output start CNFRefutation for theBenchmark.p
% 39.17/5.41  
% 39.17/5.41  fof(f15,conjecture,(
% 39.17/5.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f16,negated_conjecture,(
% 39.17/5.41    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 39.17/5.41    inference(negated_conjecture,[],[f15])).
% 39.17/5.41  
% 39.17/5.41  fof(f37,plain,(
% 39.17/5.41    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 39.17/5.41    inference(ennf_transformation,[],[f16])).
% 39.17/5.41  
% 39.17/5.41  fof(f38,plain,(
% 39.17/5.41    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 39.17/5.41    inference(flattening,[],[f37])).
% 39.17/5.41  
% 39.17/5.41  fof(f42,plain,(
% 39.17/5.41    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 39.17/5.41    introduced(choice_axiom,[])).
% 39.17/5.41  
% 39.17/5.41  fof(f41,plain,(
% 39.17/5.41    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 39.17/5.41    introduced(choice_axiom,[])).
% 39.17/5.41  
% 39.17/5.41  fof(f43,plain,(
% 39.17/5.41    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 39.17/5.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 39.17/5.41  
% 39.17/5.41  fof(f70,plain,(
% 39.17/5.41    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f7,axiom,(
% 39.17/5.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f26,plain,(
% 39.17/5.41    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.17/5.41    inference(ennf_transformation,[],[f7])).
% 39.17/5.41  
% 39.17/5.41  fof(f53,plain,(
% 39.17/5.41    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.17/5.41    inference(cnf_transformation,[],[f26])).
% 39.17/5.41  
% 39.17/5.41  fof(f74,plain,(
% 39.17/5.41    k2_relset_1(sK0,sK1,sK2) = sK1),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f73,plain,(
% 39.17/5.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f9,axiom,(
% 39.17/5.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f29,plain,(
% 39.17/5.41    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.17/5.41    inference(ennf_transformation,[],[f9])).
% 39.17/5.41  
% 39.17/5.41  fof(f30,plain,(
% 39.17/5.41    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.17/5.41    inference(flattening,[],[f29])).
% 39.17/5.41  
% 39.17/5.41  fof(f40,plain,(
% 39.17/5.41    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.17/5.41    inference(nnf_transformation,[],[f30])).
% 39.17/5.41  
% 39.17/5.41  fof(f56,plain,(
% 39.17/5.41    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.17/5.41    inference(cnf_transformation,[],[f40])).
% 39.17/5.41  
% 39.17/5.41  fof(f6,axiom,(
% 39.17/5.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f25,plain,(
% 39.17/5.41    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.17/5.41    inference(ennf_transformation,[],[f6])).
% 39.17/5.41  
% 39.17/5.41  fof(f52,plain,(
% 39.17/5.41    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.17/5.41    inference(cnf_transformation,[],[f25])).
% 39.17/5.41  
% 39.17/5.41  fof(f72,plain,(
% 39.17/5.41    v1_funct_2(sK3,sK1,sK0)),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f77,plain,(
% 39.17/5.41    k1_xboole_0 != sK0),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f2,axiom,(
% 39.17/5.41    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f18,plain,(
% 39.17/5.41    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.17/5.41    inference(ennf_transformation,[],[f2])).
% 39.17/5.41  
% 39.17/5.41  fof(f19,plain,(
% 39.17/5.41    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.17/5.41    inference(flattening,[],[f18])).
% 39.17/5.41  
% 39.17/5.41  fof(f47,plain,(
% 39.17/5.41    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.17/5.41    inference(cnf_transformation,[],[f19])).
% 39.17/5.41  
% 39.17/5.41  fof(f71,plain,(
% 39.17/5.41    v1_funct_1(sK3)),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f5,axiom,(
% 39.17/5.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f24,plain,(
% 39.17/5.41    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.17/5.41    inference(ennf_transformation,[],[f5])).
% 39.17/5.41  
% 39.17/5.41  fof(f51,plain,(
% 39.17/5.41    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.17/5.41    inference(cnf_transformation,[],[f24])).
% 39.17/5.41  
% 39.17/5.41  fof(f10,axiom,(
% 39.17/5.41    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f31,plain,(
% 39.17/5.41    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 39.17/5.41    inference(ennf_transformation,[],[f10])).
% 39.17/5.41  
% 39.17/5.41  fof(f32,plain,(
% 39.17/5.41    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 39.17/5.41    inference(flattening,[],[f31])).
% 39.17/5.41  
% 39.17/5.41  fof(f63,plain,(
% 39.17/5.41    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 39.17/5.41    inference(cnf_transformation,[],[f32])).
% 39.17/5.41  
% 39.17/5.41  fof(f68,plain,(
% 39.17/5.41    v1_funct_1(sK2)),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f8,axiom,(
% 39.17/5.41    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f27,plain,(
% 39.17/5.41    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 39.17/5.41    inference(ennf_transformation,[],[f8])).
% 39.17/5.41  
% 39.17/5.41  fof(f28,plain,(
% 39.17/5.41    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.17/5.41    inference(flattening,[],[f27])).
% 39.17/5.41  
% 39.17/5.41  fof(f39,plain,(
% 39.17/5.41    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.17/5.41    inference(nnf_transformation,[],[f28])).
% 39.17/5.41  
% 39.17/5.41  fof(f54,plain,(
% 39.17/5.41    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.17/5.41    inference(cnf_transformation,[],[f39])).
% 39.17/5.41  
% 39.17/5.41  fof(f75,plain,(
% 39.17/5.41    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f11,axiom,(
% 39.17/5.41    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f17,plain,(
% 39.17/5.41    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 39.17/5.41    inference(pure_predicate_removal,[],[f11])).
% 39.17/5.41  
% 39.17/5.41  fof(f64,plain,(
% 39.17/5.41    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 39.17/5.41    inference(cnf_transformation,[],[f17])).
% 39.17/5.41  
% 39.17/5.41  fof(f12,axiom,(
% 39.17/5.41    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f33,plain,(
% 39.17/5.41    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 39.17/5.41    inference(ennf_transformation,[],[f12])).
% 39.17/5.41  
% 39.17/5.41  fof(f34,plain,(
% 39.17/5.41    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 39.17/5.41    inference(flattening,[],[f33])).
% 39.17/5.41  
% 39.17/5.41  fof(f65,plain,(
% 39.17/5.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 39.17/5.41    inference(cnf_transformation,[],[f34])).
% 39.17/5.41  
% 39.17/5.41  fof(f1,axiom,(
% 39.17/5.41    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f45,plain,(
% 39.17/5.41    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 39.17/5.41    inference(cnf_transformation,[],[f1])).
% 39.17/5.41  
% 39.17/5.41  fof(f13,axiom,(
% 39.17/5.41    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f66,plain,(
% 39.17/5.41    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 39.17/5.41    inference(cnf_transformation,[],[f13])).
% 39.17/5.41  
% 39.17/5.41  fof(f80,plain,(
% 39.17/5.41    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 39.17/5.41    inference(definition_unfolding,[],[f45,f66])).
% 39.17/5.41  
% 39.17/5.41  fof(f3,axiom,(
% 39.17/5.41    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f20,plain,(
% 39.17/5.41    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.17/5.41    inference(ennf_transformation,[],[f3])).
% 39.17/5.41  
% 39.17/5.41  fof(f21,plain,(
% 39.17/5.41    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.17/5.41    inference(flattening,[],[f20])).
% 39.17/5.41  
% 39.17/5.41  fof(f48,plain,(
% 39.17/5.41    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.17/5.41    inference(cnf_transformation,[],[f21])).
% 39.17/5.41  
% 39.17/5.41  fof(f83,plain,(
% 39.17/5.41    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.17/5.41    inference(definition_unfolding,[],[f48,f66])).
% 39.17/5.41  
% 39.17/5.41  fof(f4,axiom,(
% 39.17/5.41    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f22,plain,(
% 39.17/5.41    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.17/5.41    inference(ennf_transformation,[],[f4])).
% 39.17/5.41  
% 39.17/5.41  fof(f23,plain,(
% 39.17/5.41    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.17/5.41    inference(flattening,[],[f22])).
% 39.17/5.41  
% 39.17/5.41  fof(f50,plain,(
% 39.17/5.41    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.17/5.41    inference(cnf_transformation,[],[f23])).
% 39.17/5.41  
% 39.17/5.41  fof(f84,plain,(
% 39.17/5.41    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.17/5.41    inference(definition_unfolding,[],[f50,f66])).
% 39.17/5.41  
% 39.17/5.41  fof(f14,axiom,(
% 39.17/5.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 39.17/5.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.17/5.41  
% 39.17/5.41  fof(f35,plain,(
% 39.17/5.41    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 39.17/5.41    inference(ennf_transformation,[],[f14])).
% 39.17/5.41  
% 39.17/5.41  fof(f36,plain,(
% 39.17/5.41    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.17/5.41    inference(flattening,[],[f35])).
% 39.17/5.41  
% 39.17/5.41  fof(f67,plain,(
% 39.17/5.41    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 39.17/5.41    inference(cnf_transformation,[],[f36])).
% 39.17/5.41  
% 39.17/5.41  fof(f55,plain,(
% 39.17/5.41    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.17/5.41    inference(cnf_transformation,[],[f39])).
% 39.17/5.41  
% 39.17/5.41  fof(f85,plain,(
% 39.17/5.41    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.17/5.41    inference(equality_resolution,[],[f55])).
% 39.17/5.41  
% 39.17/5.41  fof(f69,plain,(
% 39.17/5.41    v1_funct_2(sK2,sK0,sK1)),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f78,plain,(
% 39.17/5.41    k1_xboole_0 != sK1),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f79,plain,(
% 39.17/5.41    k2_funct_1(sK2) != sK3),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  fof(f76,plain,(
% 39.17/5.41    v2_funct_1(sK2)),
% 39.17/5.41    inference(cnf_transformation,[],[f43])).
% 39.17/5.41  
% 39.17/5.41  cnf(c_32,negated_conjecture,
% 39.17/5.41      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 39.17/5.41      inference(cnf_transformation,[],[f70]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101813,plain,
% 39.17/5.41      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_9,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 39.17/5.41      inference(cnf_transformation,[],[f53]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101825,plain,
% 39.17/5.41      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102444,plain,
% 39.17/5.41      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101813,c_101825]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_28,negated_conjecture,
% 39.17/5.41      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 39.17/5.41      inference(cnf_transformation,[],[f74]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102446,plain,
% 39.17/5.41      ( k2_relat_1(sK2) = sK1 ),
% 39.17/5.41      inference(light_normalisation,[status(thm)],[c_102444,c_28]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_29,negated_conjecture,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 39.17/5.41      inference(cnf_transformation,[],[f73]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101816,plain,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_17,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,X2)
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | k1_relset_1(X1,X2,X0) = X1
% 39.17/5.41      | k1_xboole_0 = X2 ),
% 39.17/5.41      inference(cnf_transformation,[],[f56]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101819,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = X0
% 39.17/5.41      | k1_xboole_0 = X1
% 39.17/5.41      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102809,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.17/5.41      | sK0 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101816,c_101819]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_8,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 39.17/5.41      inference(cnf_transformation,[],[f52]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101826,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102502,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101816,c_101826]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102821,plain,
% 39.17/5.41      ( k1_relat_1(sK3) = sK1
% 39.17/5.41      | sK0 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_102809,c_102502]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_30,negated_conjecture,
% 39.17/5.41      ( v1_funct_2(sK3,sK1,sK0) ),
% 39.17/5.41      inference(cnf_transformation,[],[f72]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_39,plain,
% 39.17/5.41      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_25,negated_conjecture,
% 39.17/5.41      ( k1_xboole_0 != sK0 ),
% 39.17/5.41      inference(cnf_transformation,[],[f77]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_657,plain,( X0 = X0 ),theory(equality) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_686,plain,
% 39.17/5.41      ( k1_xboole_0 = k1_xboole_0 ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_657]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_658,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_7603,plain,
% 39.17/5.41      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_658]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_7604,plain,
% 39.17/5.41      ( sK0 != k1_xboole_0
% 39.17/5.41      | k1_xboole_0 = sK0
% 39.17/5.41      | k1_xboole_0 != k1_xboole_0 ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_7603]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_24536,plain,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_24537,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = X0
% 39.17/5.41      | k1_xboole_0 = X1
% 39.17/5.41      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_24589,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.17/5.41      | sK0 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_24536,c_24537]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_24538,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_24580,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_24536,c_24538]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_24590,plain,
% 39.17/5.41      ( k1_relat_1(sK3) = sK1
% 39.17/5.41      | sK0 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_24589,c_24580]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_106832,plain,
% 39.17/5.41      ( k1_relat_1(sK3) = sK1 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_102821,c_39,c_25,c_686,c_7604,c_24590]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_2,plain,
% 39.17/5.41      ( ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X1)
% 39.17/5.41      | ~ v1_relat_1(X0)
% 39.17/5.41      | ~ v1_relat_1(X1)
% 39.17/5.41      | v2_funct_1(X1)
% 39.17/5.41      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 39.17/5.41      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 39.17/5.41      inference(cnf_transformation,[],[f47]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101832,plain,
% 39.17/5.41      ( k1_relat_1(X0) != k2_relat_1(X1)
% 39.17/5.41      | v1_funct_1(X1) != iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X1) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v2_funct_1(X0) = iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_106844,plain,
% 39.17/5.41      ( k2_relat_1(X0) != sK1
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_106832,c_101832]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_66459,plain,
% 39.17/5.41      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_66124,negated_conjecture,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
% 39.17/5.41      | ~ iProver_ARSWP_238 ),
% 39.17/5.41      inference(arg_filter_abstr,[status(unp)],[c_29]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_66437,plain,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
% 39.17/5.41      | iProver_ARSWP_238 != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_66124]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_66119,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,X2)
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 39.17/5.41      | ~ iProver_ARSWP_233
% 39.17/5.41      | k1_relset_1(X1,X2,X0) = X1
% 39.17/5.41      | k1_xboole_0 = X2 ),
% 39.17/5.41      inference(arg_filter_abstr,[status(unp)],[c_17]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_66442,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = X0
% 39.17/5.41      | k1_xboole_0 = X1
% 39.17/5.41      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 39.17/5.41      | iProver_ARSWP_233 != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_66119]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_67973,plain,
% 39.17/5.41      ( k1_relset_1(sK1,X0,sK3) = sK1
% 39.17/5.41      | k1_xboole_0 = X0
% 39.17/5.41      | v1_funct_2(sK3,sK1,X0) != iProver_top
% 39.17/5.41      | iProver_ARSWP_238 != iProver_top
% 39.17/5.41      | iProver_ARSWP_233 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_66437,c_66442]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_69671,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.17/5.41      | sK0 = k1_xboole_0
% 39.17/5.41      | iProver_ARSWP_238 != iProver_top
% 39.17/5.41      | iProver_ARSWP_233 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_66459,c_67973]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_24569,plain,
% 39.17/5.41      ( ~ v1_funct_2(sK3,sK1,sK0)
% 39.17/5.41      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.17/5.41      | k1_relset_1(sK1,sK0,sK3) = sK1
% 39.17/5.41      | k1_xboole_0 = sK0 ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_17]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_69704,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_69671,c_30,c_29,c_25,c_24569]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_66112,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 39.17/5.41      | ~ iProver_ARSWP_226
% 39.17/5.41      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 39.17/5.41      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_66449,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 39.17/5.41      | iProver_ARSWP_226 != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_66112]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_67547,plain,
% 39.17/5.41      ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
% 39.17/5.41      | iProver_ARSWP_238 != iProver_top
% 39.17/5.41      | iProver_ARSWP_226 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_66437,c_66449]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_69709,plain,
% 39.17/5.41      ( k1_relat_1(sK3) = sK1
% 39.17/5.41      | iProver_ARSWP_238 != iProver_top
% 39.17/5.41      | iProver_ARSWP_226 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_69704,c_67547]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_69998,plain,
% 39.17/5.41      ( k1_relat_1(sK3) = sK1 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_69709,c_39,c_25,c_686,c_7604,c_24590]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_66465,plain,
% 39.17/5.41      ( k1_relat_1(X0) != k2_relat_1(X1)
% 39.17/5.41      | v1_funct_1(X1) != iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X1) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v2_funct_1(X0) = iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_70031,plain,
% 39.17/5.41      ( k2_relat_1(X0) != sK1
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_69998,c_66465]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_31,negated_conjecture,
% 39.17/5.41      ( v1_funct_1(sK3) ),
% 39.17/5.41      inference(cnf_transformation,[],[f71]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_38,plain,
% 39.17/5.41      ( v1_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_40,plain,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_7,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | v1_relat_1(X0) ),
% 39.17/5.41      inference(cnf_transformation,[],[f51]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_42719,plain,
% 39.17/5.41      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.17/5.41      | v1_relat_1(sK3) ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_7]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_42720,plain,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_42719]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_70499,plain,
% 39.17/5.41      ( v1_relat_1(X0) != iProver_top
% 39.17/5.41      | k2_relat_1(X0) != sK1
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_70031,c_38,c_40,c_42720]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_70500,plain,
% 39.17/5.41      ( k2_relat_1(X0) != sK1
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(renaming,[status(thm)],[c_70499]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133078,plain,
% 39.17/5.41      ( v1_relat_1(X0) != iProver_top
% 39.17/5.41      | k2_relat_1(X0) != sK1
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_106844,c_38,c_40,c_42720,c_70031]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133079,plain,
% 39.17/5.41      ( k2_relat_1(X0) != sK1
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(renaming,[status(thm)],[c_133078]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133088,plain,
% 39.17/5.41      ( v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_102446,c_133079]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_18,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.17/5.41      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X3) ),
% 39.17/5.41      inference(cnf_transformation,[],[f63]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101516,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.17/5.41      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X3)
% 39.17/5.41      | ~ iProver_ARSWP_245 ),
% 39.17/5.41      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101805,plain,
% 39.17/5.41      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.17/5.41      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.17/5.41      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 39.17/5.41      | v1_funct_1(X3) != iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | iProver_ARSWP_245 != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_101516]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103667,plain,
% 39.17/5.41      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.17/5.41      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | iProver_ARSWP_245 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101816,c_101805]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103832,plain,
% 39.17/5.41      ( v1_funct_1(X0) != iProver_top
% 39.17/5.41      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.17/5.41      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.17/5.41      | iProver_ARSWP_245 != iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_103667,c_38]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103833,plain,
% 39.17/5.41      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.17/5.41      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | iProver_ARSWP_245 != iProver_top ),
% 39.17/5.41      inference(renaming,[status(thm)],[c_103832]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103844,plain,
% 39.17/5.41      ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | iProver_ARSWP_245 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101813,c_103833]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_34,negated_conjecture,
% 39.17/5.41      ( v1_funct_1(sK2) ),
% 39.17/5.41      inference(cnf_transformation,[],[f68]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_35,plain,
% 39.17/5.41      ( v1_funct_1(sK2) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_104027,plain,
% 39.17/5.41      ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.17/5.41      | iProver_ARSWP_245 != iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_103844,c_35]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_11,plain,
% 39.17/5.41      ( ~ r2_relset_1(X0,X1,X2,X3)
% 39.17/5.41      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.17/5.41      | X3 = X2 ),
% 39.17/5.41      inference(cnf_transformation,[],[f54]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_27,negated_conjecture,
% 39.17/5.41      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 39.17/5.41      inference(cnf_transformation,[],[f75]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_385,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | X3 = X0
% 39.17/5.41      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 39.17/5.41      | k6_partfun1(sK0) != X3
% 39.17/5.41      | sK0 != X2
% 39.17/5.41      | sK0 != X1 ),
% 39.17/5.41      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_386,plain,
% 39.17/5.41      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.17/5.41      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.17/5.41      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 39.17/5.41      inference(unflattening,[status(thm)],[c_385]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_20,plain,
% 39.17/5.41      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 39.17/5.41      inference(cnf_transformation,[],[f64]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_394,plain,
% 39.17/5.41      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.17/5.41      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 39.17/5.41      inference(forward_subsumption_resolution,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_386,c_20]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101520,plain,
% 39.17/5.41      ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.17/5.41      | ~ iProver_ARSWP_249
% 39.17/5.41      | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 39.17/5.41      inference(arg_filter_abstr,[status(unp)],[c_394]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101801,plain,
% 39.17/5.41      ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.17/5.41      | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 39.17/5.41      | iProver_ARSWP_249 != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_101520]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_104046,plain,
% 39.17/5.41      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
% 39.17/5.41      | iProver_ARSWP_249 != iProver_top
% 39.17/5.41      | iProver_ARSWP_245 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_104027,c_101801]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_21,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X3)
% 39.17/5.41      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 39.17/5.41      inference(cnf_transformation,[],[f65]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101518,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X3)
% 39.17/5.41      | ~ iProver_ARSWP_247
% 39.17/5.41      | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
% 39.17/5.41      inference(arg_filter_abstr,[status(unp)],[c_21]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101803,plain,
% 39.17/5.41      ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
% 39.17/5.41      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | v1_funct_1(X2) != iProver_top
% 39.17/5.41      | v1_funct_1(X3) != iProver_top
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_101518]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102670,plain,
% 39.17/5.41      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.17/5.41      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101813,c_101803]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103036,plain,
% 39.17/5.41      ( v1_funct_1(X0) != iProver_top
% 39.17/5.41      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.17/5.41      | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_102670,c_35]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103037,plain,
% 39.17/5.41      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.17/5.41      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(renaming,[status(thm)],[c_103036]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103047,plain,
% 39.17/5.41      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101816,c_103037]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103084,plain,
% 39.17/5.41      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_103047,c_38]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_104971,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 39.17/5.41      | iProver_ARSWP_249 != iProver_top
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top
% 39.17/5.41      | iProver_ARSWP_245 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_104046,c_103084]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_37,plain,
% 39.17/5.41      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62039,plain,
% 39.17/5.41      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62042,plain,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62044,plain,
% 39.17/5.41      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 39.17/5.41      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 39.17/5.41      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | v1_funct_1(X4) != iProver_top
% 39.17/5.41      | v1_funct_1(X5) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62436,plain,
% 39.17/5.41      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | v1_funct_1(X2) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_62042,c_62044]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62505,plain,
% 39.17/5.41      ( v1_funct_1(X2) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_62436,c_38]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62506,plain,
% 39.17/5.41      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | v1_funct_1(X2) != iProver_top ),
% 39.17/5.41      inference(renaming,[status(thm)],[c_62505]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62517,plain,
% 39.17/5.41      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_62039,c_62506]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62163,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(sK3)
% 39.17/5.41      | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_21]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62256,plain,
% 39.17/5.41      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.17/5.41      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.17/5.41      | ~ v1_funct_1(sK3)
% 39.17/5.41      | ~ v1_funct_1(sK2)
% 39.17/5.41      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_62163]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62592,plain,
% 39.17/5.41      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_62517,c_34,c_32,c_31,c_29,c_62256]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62036,plain,
% 39.17/5.41      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.17/5.41      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62595,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 39.17/5.41      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_62592,c_62036]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62046,plain,
% 39.17/5.41      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.17/5.41      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.17/5.41      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 39.17/5.41      | v1_funct_1(X3) != iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62597,plain,
% 39.17/5.41      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.17/5.41      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.17/5.41      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_62592,c_62046]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_108729,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_104971,c_35,c_37,c_38,c_40,c_62595,c_62597]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133123,plain,
% 39.17/5.41      ( v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(light_normalisation,[status(thm)],[c_133088,c_108729]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62196,plain,
% 39.17/5.41      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.17/5.41      | v1_relat_1(sK2) ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_7]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62197,plain,
% 39.17/5.41      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_62196]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133255,plain,
% 39.17/5.41      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_133123,c_35,c_37,c_62197]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_0,plain,
% 39.17/5.41      ( v2_funct_1(k6_partfun1(X0)) ),
% 39.17/5.41      inference(cnf_transformation,[],[f80]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101834,plain,
% 39.17/5.41      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133261,plain,
% 39.17/5.41      ( v2_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(forward_subsumption_resolution,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_133255,c_101834]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101814,plain,
% 39.17/5.41      ( v1_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_5,plain,
% 39.17/5.41      ( ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_relat_1(X0)
% 39.17/5.41      | ~ v2_funct_1(X0)
% 39.17/5.41      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 39.17/5.41      inference(cnf_transformation,[],[f83]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101829,plain,
% 39.17/5.41      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v2_funct_1(X0) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102748,plain,
% 39.17/5.41      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101814,c_101829]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_42601,plain,
% 39.17/5.41      ( v1_funct_1(sK3) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_42611,plain,
% 39.17/5.41      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v2_funct_1(X0) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_42798,plain,
% 39.17/5.41      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_42601,c_42611]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102862,plain,
% 39.17/5.41      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_102748,c_40,c_42720,c_42798]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_106835,plain,
% 39.17/5.41      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_106832,c_102862]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133263,plain,
% 39.17/5.41      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_133261,c_106835]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103048,plain,
% 39.17/5.41      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101813,c_103037]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103337,plain,
% 39.17/5.41      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_103048,c_35]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103343,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_103084,c_103337]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_6,plain,
% 39.17/5.41      ( ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X1)
% 39.17/5.41      | ~ v1_relat_1(X0)
% 39.17/5.41      | ~ v1_relat_1(X1)
% 39.17/5.41      | ~ v2_funct_1(X1)
% 39.17/5.41      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.17/5.41      | k2_funct_1(X1) = X0
% 39.17/5.41      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 39.17/5.41      inference(cnf_transformation,[],[f84]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101828,plain,
% 39.17/5.41      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.17/5.41      | k2_funct_1(X1) = X0
% 39.17/5.41      | k1_relat_1(X1) != k2_relat_1(X0)
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(X1) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X1) != iProver_top
% 39.17/5.41      | v2_funct_1(X1) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103656,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK2) != k6_partfun1(k2_relat_1(sK3))
% 39.17/5.41      | k2_funct_1(sK3) = sK2
% 39.17/5.41      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_103343,c_101828]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102443,plain,
% 39.17/5.41      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101816,c_101825]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_22,plain,
% 39.17/5.41      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 39.17/5.41      | ~ v1_funct_2(X3,X1,X0)
% 39.17/5.41      | ~ v1_funct_2(X2,X0,X1)
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 39.17/5.41      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.17/5.41      | ~ v1_funct_1(X2)
% 39.17/5.41      | ~ v1_funct_1(X3)
% 39.17/5.41      | k2_relset_1(X1,X0,X3) = X0 ),
% 39.17/5.41      inference(cnf_transformation,[],[f67]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_398,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,X2)
% 39.17/5.41      | ~ v1_funct_2(X3,X2,X1)
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.17/5.41      | ~ v1_funct_1(X3)
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.17/5.41      | k2_relset_1(X2,X1,X3) = X1
% 39.17/5.41      | k6_partfun1(X1) != k6_partfun1(sK0)
% 39.17/5.41      | sK0 != X1 ),
% 39.17/5.41      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_399,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,sK0)
% 39.17/5.41      | ~ v1_funct_2(X2,sK0,X1)
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.17/5.41      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.17/5.41      | ~ v1_funct_1(X2)
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.17/5.41      | k2_relset_1(X1,sK0,X0) = sK0
% 39.17/5.41      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 39.17/5.41      inference(unflattening,[status(thm)],[c_398]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_483,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,sK0)
% 39.17/5.41      | ~ v1_funct_2(X2,sK0,X1)
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.17/5.41      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X2)
% 39.17/5.41      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.17/5.41      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 39.17/5.41      inference(equality_resolution_simp,[status(thm)],[c_399]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101521,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,sK0)
% 39.17/5.41      | ~ v1_funct_2(X2,sK0,X1)
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.17/5.41      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X2)
% 39.17/5.41      | ~ iProver_ARSWP_250
% 39.17/5.41      | k2_relset_1(X1,sK0,X0) = sK0
% 39.17/5.41      | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 39.17/5.41      inference(arg_filter_abstr,[status(unp)],[c_483]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_101800,plain,
% 39.17/5.41      ( k2_relset_1(X0,sK0,X1) = sK0
% 39.17/5.41      | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.17/5.41      | v1_funct_2(X1,X0,sK0) != iProver_top
% 39.17/5.41      | v1_funct_2(X2,sK0,X0) != iProver_top
% 39.17/5.41      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 39.17/5.41      | v1_funct_1(X2) != iProver_top
% 39.17/5.41      | v1_funct_1(X1) != iProver_top
% 39.17/5.41      | iProver_ARSWP_250 != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_101521]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102183,plain,
% 39.17/5.41      ( k2_relset_1(sK1,sK0,X0) = sK0
% 39.17/5.41      | v1_funct_2(X1,sK0,sK1) != iProver_top
% 39.17/5.41      | v1_funct_2(X0,sK1,sK0) != iProver_top
% 39.17/5.41      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.17/5.41      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(X1) != iProver_top
% 39.17/5.41      | iProver_ARSWP_250 != iProver_top ),
% 39.17/5.41      inference(equality_resolution,[status(thm)],[c_101800]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102268,plain,
% 39.17/5.41      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 39.17/5.41      | v1_funct_2(X0,sK0,sK1) != iProver_top
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 39.17/5.41      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | iProver_ARSWP_250 != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101816,c_102183]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62162,plain,
% 39.17/5.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.17/5.41      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(sK3) ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_18]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62243,plain,
% 39.17/5.41      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.17/5.41      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.17/5.41      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.17/5.41      | ~ v1_funct_1(sK3)
% 39.17/5.41      | ~ v1_funct_1(sK2) ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_62162]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97513,plain,
% 39.17/5.41      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_394,c_34,c_32,c_31,c_29,c_62243]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_10,plain,
% 39.17/5.41      ( r2_relset_1(X0,X1,X2,X2)
% 39.17/5.41      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 39.17/5.41      inference(cnf_transformation,[],[f85]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_350,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,X2)
% 39.17/5.41      | ~ v1_funct_2(X3,X2,X1)
% 39.17/5.41      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ v1_funct_1(X3)
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | X2 != X6
% 39.17/5.41      | X2 != X5
% 39.17/5.41      | k1_partfun1(X2,X1,X1,X2,X3,X0) != X4
% 39.17/5.41      | k2_relset_1(X1,X2,X0) = X2
% 39.17/5.41      | k6_partfun1(X2) != X4 ),
% 39.17/5.41      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_351,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,X2)
% 39.17/5.41      | ~ v1_funct_2(X3,X2,X1)
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.17/5.41      | ~ m1_subset_1(k1_partfun1(X2,X1,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X3)
% 39.17/5.41      | k2_relset_1(X1,X2,X0) = X2
% 39.17/5.41      | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
% 39.17/5.41      inference(unflattening,[status(thm)],[c_350]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_373,plain,
% 39.17/5.41      ( ~ v1_funct_2(X0,X1,X2)
% 39.17/5.41      | ~ v1_funct_2(X3,X2,X1)
% 39.17/5.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.17/5.41      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.17/5.41      | ~ v1_funct_1(X0)
% 39.17/5.41      | ~ v1_funct_1(X3)
% 39.17/5.41      | k2_relset_1(X1,X2,X0) = X2
% 39.17/5.41      | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
% 39.17/5.41      inference(forward_subsumption_resolution,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_351,c_18]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97597,plain,
% 39.17/5.41      ( k2_relset_1(X0,X1,X2) = X1
% 39.17/5.41      | k6_partfun1(X1) != k1_partfun1(X1,X0,X0,X1,X3,X2)
% 39.17/5.41      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.17/5.41      | v1_funct_2(X3,X1,X0) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 39.17/5.41      | v1_funct_1(X3) != iProver_top
% 39.17/5.41      | v1_funct_1(X2) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97893,plain,
% 39.17/5.41      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 39.17/5.41      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 39.17/5.41      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.17/5.41      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_97513,c_97597]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97603,plain,
% 39.17/5.41      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97610,plain,
% 39.17/5.41      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97859,plain,
% 39.17/5.41      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_97603,c_97610]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97894,plain,
% 39.17/5.41      ( k2_relat_1(sK3) = sK0
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 39.17/5.41      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 39.17/5.41      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.17/5.41      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_97893,c_97859]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_33,negated_conjecture,
% 39.17/5.41      ( v1_funct_2(sK2,sK0,sK1) ),
% 39.17/5.41      inference(cnf_transformation,[],[f69]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_36,plain,
% 39.17/5.41      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98448,plain,
% 39.17/5.41      ( k2_relat_1(sK3) = sK0 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_97894,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98452,plain,
% 39.17/5.41      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_98448,c_97859]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102293,plain,
% 39.17/5.41      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_102268,c_98452]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102449,plain,
% 39.17/5.41      ( k2_relat_1(sK3) = sK0 ),
% 39.17/5.41      inference(light_normalisation,[status(thm)],[c_102443,c_102293]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_103657,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
% 39.17/5.41      | k2_funct_1(sK3) = sK2
% 39.17/5.41      | k1_relat_1(sK3) != sK1
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top
% 39.17/5.41      | iProver_ARSWP_247 != iProver_top ),
% 39.17/5.41      inference(light_normalisation,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_103656,c_102446,c_102449]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97600,plain,
% 39.17/5.41      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97605,plain,
% 39.17/5.41      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 39.17/5.41      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 39.17/5.41      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | v1_funct_1(X4) != iProver_top
% 39.17/5.41      | v1_funct_1(X5) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98095,plain,
% 39.17/5.41      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | v1_funct_1(X2) != iProver_top
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_97603,c_97605]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98239,plain,
% 39.17/5.41      ( v1_funct_1(X2) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_98095,c_38,c_62436]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98240,plain,
% 39.17/5.41      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.17/5.41      | v1_funct_1(X2) != iProver_top ),
% 39.17/5.41      inference(renaming,[status(thm)],[c_98239]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98249,plain,
% 39.17/5.41      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_97600,c_98240]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98252,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(light_normalisation,[status(thm)],[c_98249,c_97513]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98356,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_98252,c_35,c_37,c_38,c_40,c_62595,c_62597]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97613,plain,
% 39.17/5.41      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.17/5.41      | k2_funct_1(X1) = X0
% 39.17/5.41      | k1_relat_1(X1) != k2_relat_1(X0)
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(X1) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X1) != iProver_top
% 39.17/5.41      | v2_funct_1(X1) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98359,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_98356,c_97613]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97860,plain,
% 39.17/5.41      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_97600,c_97610]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97862,plain,
% 39.17/5.41      ( k2_relat_1(sK2) = sK1 ),
% 39.17/5.41      inference(light_normalisation,[status(thm)],[c_97860,c_28]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97608,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = X0
% 39.17/5.41      | k1_xboole_0 = X1
% 39.17/5.41      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97954,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.17/5.41      | sK0 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_97603,c_97608]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98003,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_97954,c_30,c_29,c_25,c_24569]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97611,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_97900,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_97603,c_97611]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98006,plain,
% 39.17/5.41      ( k1_relat_1(sK3) = sK1 ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_98003,c_97900]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98360,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.17/5.41      | sK1 != sK1
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(light_normalisation,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_98359,c_97862,c_98006]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98361,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(equality_resolution_simp,[status(thm)],[c_98360]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_63106,plain,
% 39.17/5.41      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_62595,c_35,c_37,c_38,c_40,c_62597]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62051,plain,
% 39.17/5.41      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.17/5.41      | k2_funct_1(X1) = X0
% 39.17/5.41      | k1_relat_1(X1) != k2_relat_1(X0)
% 39.17/5.41      | v1_funct_1(X0) != iProver_top
% 39.17/5.41      | v1_funct_1(X1) != iProver_top
% 39.17/5.41      | v1_relat_1(X0) != iProver_top
% 39.17/5.41      | v1_relat_1(X1) != iProver_top
% 39.17/5.41      | v2_funct_1(X1) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_63114,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_63106,c_62051]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62048,plain,
% 39.17/5.41      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62273,plain,
% 39.17/5.41      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_62039,c_62048]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62275,plain,
% 39.17/5.41      ( k2_relat_1(sK2) = sK1 ),
% 39.17/5.41      inference(light_normalisation,[status(thm)],[c_62273,c_28]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62047,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = X0
% 39.17/5.41      | k1_xboole_0 = X1
% 39.17/5.41      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62388,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.17/5.41      | sK0 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_62042,c_62047]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62760,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_62388,c_30,c_29,c_25,c_24569]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62049,plain,
% 39.17/5.41      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.17/5.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62359,plain,
% 39.17/5.41      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_62042,c_62049]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62763,plain,
% 39.17/5.41      ( k1_relat_1(sK3) = sK1 ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_62760,c_62359]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_63115,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.17/5.41      | sK1 != sK1
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(light_normalisation,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_63114,c_62275,c_62763]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_63116,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(equality_resolution_simp,[status(thm)],[c_63115]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_64022,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_63116,c_35,c_37,c_38,c_40,c_42720,c_62197]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98723,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_98361,c_35,c_37,c_38,c_40,c_42720,c_62197,c_63116]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98727,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2
% 39.17/5.41      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 39.17/5.41      | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(light_normalisation,[status(thm)],[c_98723,c_98448]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_98728,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(equality_resolution_simp,[status(thm)],[c_98727]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_104446,plain,
% 39.17/5.41      ( v2_funct_1(sK3) != iProver_top | k2_funct_1(sK3) = sK2 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_103657,c_98728]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_104447,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 39.17/5.41      inference(renaming,[status(thm)],[c_104446]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133265,plain,
% 39.17/5.41      ( k2_funct_1(sK3) = sK2 ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_133261,c_104447]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_133270,plain,
% 39.17/5.41      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 39.17/5.41      inference(light_normalisation,[status(thm)],[c_133263,c_133265]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_169080,plain,
% 39.17/5.41      ( k2_funct_1(sK2) = sK3
% 39.17/5.41      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 39.17/5.41      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_133270,c_101828]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102810,plain,
% 39.17/5.41      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 39.17/5.41      | sK1 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101813,c_101819]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102503,plain,
% 39.17/5.41      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_101813,c_101826]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_102814,plain,
% 39.17/5.41      ( k1_relat_1(sK2) = sK0
% 39.17/5.41      | sK1 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_102810,c_102503]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62389,plain,
% 39.17/5.41      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 39.17/5.41      | sK1 = k1_xboole_0
% 39.17/5.41      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_62039,c_62047]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_24,negated_conjecture,
% 39.17/5.41      ( k1_xboole_0 != sK1 ),
% 39.17/5.41      inference(cnf_transformation,[],[f78]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62193,plain,
% 39.17/5.41      ( ~ v1_funct_2(sK2,sK0,sK1)
% 39.17/5.41      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.17/5.41      | k1_relset_1(sK0,sK1,sK2) = sK0
% 39.17/5.41      | k1_xboole_0 = sK1 ),
% 39.17/5.41      inference(instantiation,[status(thm)],[c_17]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62768,plain,
% 39.17/5.41      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_62389,c_33,c_32,c_24,c_62193]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62360,plain,
% 39.17/5.41      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 39.17/5.41      inference(superposition,[status(thm)],[c_62039,c_62049]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_62771,plain,
% 39.17/5.41      ( k1_relat_1(sK2) = sK0 ),
% 39.17/5.41      inference(demodulation,[status(thm)],[c_62768,c_62360]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_105922,plain,
% 39.17/5.41      ( k1_relat_1(sK2) = sK0 ),
% 39.17/5.41      inference(global_propositional_subsumption,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_102814,c_62771]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_169081,plain,
% 39.17/5.41      ( k2_funct_1(sK2) = sK3
% 39.17/5.41      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 39.17/5.41      | sK0 != sK0
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(light_normalisation,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_169080,c_102446,c_102449,c_105922]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_169082,plain,
% 39.17/5.41      ( k2_funct_1(sK2) = sK3
% 39.17/5.41      | v1_funct_1(sK3) != iProver_top
% 39.17/5.41      | v1_funct_1(sK2) != iProver_top
% 39.17/5.41      | v1_relat_1(sK3) != iProver_top
% 39.17/5.41      | v1_relat_1(sK2) != iProver_top
% 39.17/5.41      | v2_funct_1(sK2) != iProver_top ),
% 39.17/5.41      inference(equality_resolution_simp,[status(thm)],[c_169081]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_23,negated_conjecture,
% 39.17/5.41      ( k2_funct_1(sK2) != sK3 ),
% 39.17/5.41      inference(cnf_transformation,[],[f79]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_26,negated_conjecture,
% 39.17/5.41      ( v2_funct_1(sK2) ),
% 39.17/5.41      inference(cnf_transformation,[],[f76]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(c_42,plain,
% 39.17/5.41      ( v2_funct_1(sK2) = iProver_top ),
% 39.17/5.41      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.17/5.41  
% 39.17/5.41  cnf(contradiction,plain,
% 39.17/5.41      ( $false ),
% 39.17/5.41      inference(minisat,
% 39.17/5.41                [status(thm)],
% 39.17/5.41                [c_169082,c_62197,c_42720,c_23,c_42,c_40,c_38,c_37,c_35]) ).
% 39.17/5.41  
% 39.17/5.41  
% 39.17/5.41  % SZS output end CNFRefutation for theBenchmark.p
% 39.17/5.41  
% 39.17/5.41  ------                               Statistics
% 39.17/5.41  
% 39.17/5.41  ------ Selected
% 39.17/5.41  
% 39.17/5.41  total_time:                             4.512
% 39.17/5.41  
%------------------------------------------------------------------------------
