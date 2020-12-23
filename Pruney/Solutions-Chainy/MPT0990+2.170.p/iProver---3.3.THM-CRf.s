%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:33 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 649 expanded)
%              Number of clauses        :  122 ( 205 expanded)
%              Number of leaves         :   20 ( 163 expanded)
%              Depth                    :   20
%              Number of atoms          :  722 (5341 expanded)
%              Number of equality atoms :  353 (1964 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f45,f44])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f68])).

fof(f80,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( k5_relat_1(X2,X3) = k6_relat_1(X0)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & k2_relat_1(X1) = X0 )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k5_relat_1(X2,X3) != k6_relat_1(X0)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | k2_relat_1(X1) != X0
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_relat_1(X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_partfun1(X0)
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | k2_relat_1(X1) != X0
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f49,f68,f68])).

fof(f87,plain,(
    ! [X2,X3,X1] :
      ( X1 = X3
      | k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1))
      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1230,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1233,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3374,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1233])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1241,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2252,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1230,c_1241])).

cnf(c_3378,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3374,c_2252])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_732,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_763,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_733,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1324,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1325,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1324])).

cnf(c_11099,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3378,c_40,c_26,c_763,c_1325])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1227,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1240,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2158,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1227,c_1240])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2160,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2158,c_29])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_464,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_465,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_467,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_35])).

cnf(c_1219,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_2162,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2160,c_1219])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1347,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_1770,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1771,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1770])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1805,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1806,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_2864,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2162,c_38,c_1771,c_1806])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | X0 = X2
    | k5_relat_1(X2,X1) != k6_partfun1(k1_relat_1(X0))
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1243,plain,
    ( X0 = X1
    | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
    | k5_relat_1(X2,X0) != k6_partfun1(k2_relat_1(X1))
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3680,plain,
    ( k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(sK2,X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2864,c_1243])).

cnf(c_1245,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2259,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1245])).

cnf(c_2580,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2259,c_38,c_1771,c_1806])).

cnf(c_3,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_492,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_27])).

cnf(c_493,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_495,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_35])).

cnf(c_1217,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2585,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2580,c_1217])).

cnf(c_3682,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3680,c_2585])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_378,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_379,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_383,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_35])).

cnf(c_384,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_383])).

cnf(c_1358,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_1359,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_426,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_427,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_431,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_35])).

cnf(c_432,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_431])).

cnf(c_1221,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_1971,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29,c_1221])).

cnf(c_1512,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_1513,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1512])).

cnf(c_2089,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1971,c_37,c_38,c_29,c_1513])).

cnf(c_2260,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2089,c_1245])).

cnf(c_2810,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2811,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2810])).

cnf(c_25453,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3682,c_36,c_37,c_38,c_29,c_1359,c_1771,c_1806,c_2260,c_2811])).

cnf(c_3375,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1233])).

cnf(c_2253,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1227,c_1241])).

cnf(c_3377,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3375,c_2253])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1301,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1302,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1301])).

cnf(c_10219,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3377,c_37,c_25,c_763,c_1302])).

cnf(c_25459,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25453,c_10219])).

cnf(c_25465,plain,
    ( k5_relat_1(sK2,sK3) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11099,c_25459])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1231,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2688,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1231])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3049,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2688,c_39])).

cnf(c_3050,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3049])).

cnf(c_3057,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_3050])).

cnf(c_3151,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3057,c_36])).

cnf(c_12,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_363,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_371,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_19])).

cnf(c_1224,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_3153,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3151,c_1224])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1239,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3506,plain,
    ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1239])).

cnf(c_3769,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1227,c_3506])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1242,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3919,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3769,c_1242])).

cnf(c_6135,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3153,c_38,c_41,c_3919])).

cnf(c_25466,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25465,c_6135])).

cnf(c_25467,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_25466])).

cnf(c_1244,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2258,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1230,c_1245])).

cnf(c_2577,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_2258])).

cnf(c_24,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f83])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25467,c_2577,c_24,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n024.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:42:36 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.79/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.79/1.48  
% 7.79/1.48  ------  iProver source info
% 7.79/1.48  
% 7.79/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.79/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.79/1.48  git: non_committed_changes: false
% 7.79/1.48  git: last_make_outside_of_git: false
% 7.79/1.48  
% 7.79/1.48  ------ 
% 7.79/1.48  
% 7.79/1.48  ------ Input Options
% 7.79/1.48  
% 7.79/1.48  --out_options                           all
% 7.79/1.48  --tptp_safe_out                         true
% 7.79/1.48  --problem_path                          ""
% 7.79/1.48  --include_path                          ""
% 7.79/1.48  --clausifier                            res/vclausify_rel
% 7.79/1.48  --clausifier_options                    ""
% 7.79/1.48  --stdin                                 false
% 7.79/1.48  --stats_out                             all
% 7.79/1.48  
% 7.79/1.48  ------ General Options
% 7.79/1.48  
% 7.79/1.48  --fof                                   false
% 7.79/1.48  --time_out_real                         305.
% 7.79/1.48  --time_out_virtual                      -1.
% 7.79/1.48  --symbol_type_check                     false
% 7.79/1.48  --clausify_out                          false
% 7.79/1.48  --sig_cnt_out                           false
% 7.79/1.48  --trig_cnt_out                          false
% 7.79/1.48  --trig_cnt_out_tolerance                1.
% 7.79/1.48  --trig_cnt_out_sk_spl                   false
% 7.79/1.48  --abstr_cl_out                          false
% 7.79/1.48  
% 7.79/1.48  ------ Global Options
% 7.79/1.48  
% 7.79/1.48  --schedule                              default
% 7.79/1.48  --add_important_lit                     false
% 7.79/1.48  --prop_solver_per_cl                    1000
% 7.79/1.48  --min_unsat_core                        false
% 7.79/1.48  --soft_assumptions                      false
% 7.79/1.48  --soft_lemma_size                       3
% 7.79/1.48  --prop_impl_unit_size                   0
% 7.79/1.48  --prop_impl_unit                        []
% 7.79/1.48  --share_sel_clauses                     true
% 7.79/1.48  --reset_solvers                         false
% 7.79/1.48  --bc_imp_inh                            [conj_cone]
% 7.79/1.48  --conj_cone_tolerance                   3.
% 7.79/1.48  --extra_neg_conj                        none
% 7.79/1.48  --large_theory_mode                     true
% 7.79/1.48  --prolific_symb_bound                   200
% 7.79/1.48  --lt_threshold                          2000
% 7.79/1.48  --clause_weak_htbl                      true
% 7.79/1.48  --gc_record_bc_elim                     false
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing Options
% 7.79/1.48  
% 7.79/1.48  --preprocessing_flag                    true
% 7.79/1.48  --time_out_prep_mult                    0.1
% 7.79/1.48  --splitting_mode                        input
% 7.79/1.48  --splitting_grd                         true
% 7.79/1.48  --splitting_cvd                         false
% 7.79/1.48  --splitting_cvd_svl                     false
% 7.79/1.48  --splitting_nvd                         32
% 7.79/1.48  --sub_typing                            true
% 7.79/1.48  --prep_gs_sim                           true
% 7.79/1.48  --prep_unflatten                        true
% 7.79/1.48  --prep_res_sim                          true
% 7.79/1.48  --prep_upred                            true
% 7.79/1.48  --prep_sem_filter                       exhaustive
% 7.79/1.48  --prep_sem_filter_out                   false
% 7.79/1.48  --pred_elim                             true
% 7.79/1.48  --res_sim_input                         true
% 7.79/1.48  --eq_ax_congr_red                       true
% 7.79/1.48  --pure_diseq_elim                       true
% 7.79/1.48  --brand_transform                       false
% 7.79/1.48  --non_eq_to_eq                          false
% 7.79/1.48  --prep_def_merge                        true
% 7.79/1.48  --prep_def_merge_prop_impl              false
% 7.79/1.48  --prep_def_merge_mbd                    true
% 7.79/1.48  --prep_def_merge_tr_red                 false
% 7.79/1.48  --prep_def_merge_tr_cl                  false
% 7.79/1.48  --smt_preprocessing                     true
% 7.79/1.48  --smt_ac_axioms                         fast
% 7.79/1.48  --preprocessed_out                      false
% 7.79/1.48  --preprocessed_stats                    false
% 7.79/1.48  
% 7.79/1.48  ------ Abstraction refinement Options
% 7.79/1.48  
% 7.79/1.48  --abstr_ref                             []
% 7.79/1.48  --abstr_ref_prep                        false
% 7.79/1.48  --abstr_ref_until_sat                   false
% 7.79/1.48  --abstr_ref_sig_restrict                funpre
% 7.79/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.48  --abstr_ref_under                       []
% 7.79/1.48  
% 7.79/1.48  ------ SAT Options
% 7.79/1.48  
% 7.79/1.48  --sat_mode                              false
% 7.79/1.48  --sat_fm_restart_options                ""
% 7.79/1.48  --sat_gr_def                            false
% 7.79/1.48  --sat_epr_types                         true
% 7.79/1.48  --sat_non_cyclic_types                  false
% 7.79/1.48  --sat_finite_models                     false
% 7.79/1.48  --sat_fm_lemmas                         false
% 7.79/1.48  --sat_fm_prep                           false
% 7.79/1.48  --sat_fm_uc_incr                        true
% 7.79/1.48  --sat_out_model                         small
% 7.79/1.48  --sat_out_clauses                       false
% 7.79/1.48  
% 7.79/1.48  ------ QBF Options
% 7.79/1.48  
% 7.79/1.48  --qbf_mode                              false
% 7.79/1.48  --qbf_elim_univ                         false
% 7.79/1.48  --qbf_dom_inst                          none
% 7.79/1.48  --qbf_dom_pre_inst                      false
% 7.79/1.48  --qbf_sk_in                             false
% 7.79/1.48  --qbf_pred_elim                         true
% 7.79/1.48  --qbf_split                             512
% 7.79/1.48  
% 7.79/1.48  ------ BMC1 Options
% 7.79/1.48  
% 7.79/1.48  --bmc1_incremental                      false
% 7.79/1.48  --bmc1_axioms                           reachable_all
% 7.79/1.48  --bmc1_min_bound                        0
% 7.79/1.48  --bmc1_max_bound                        -1
% 7.79/1.48  --bmc1_max_bound_default                -1
% 7.79/1.48  --bmc1_symbol_reachability              true
% 7.79/1.48  --bmc1_property_lemmas                  false
% 7.79/1.48  --bmc1_k_induction                      false
% 7.79/1.48  --bmc1_non_equiv_states                 false
% 7.79/1.48  --bmc1_deadlock                         false
% 7.79/1.48  --bmc1_ucm                              false
% 7.79/1.48  --bmc1_add_unsat_core                   none
% 7.79/1.48  --bmc1_unsat_core_children              false
% 7.79/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.48  --bmc1_out_stat                         full
% 7.79/1.48  --bmc1_ground_init                      false
% 7.79/1.48  --bmc1_pre_inst_next_state              false
% 7.79/1.48  --bmc1_pre_inst_state                   false
% 7.79/1.48  --bmc1_pre_inst_reach_state             false
% 7.79/1.48  --bmc1_out_unsat_core                   false
% 7.79/1.48  --bmc1_aig_witness_out                  false
% 7.79/1.48  --bmc1_verbose                          false
% 7.79/1.48  --bmc1_dump_clauses_tptp                false
% 7.79/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.48  --bmc1_dump_file                        -
% 7.79/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.48  --bmc1_ucm_extend_mode                  1
% 7.79/1.48  --bmc1_ucm_init_mode                    2
% 7.79/1.48  --bmc1_ucm_cone_mode                    none
% 7.79/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.48  --bmc1_ucm_relax_model                  4
% 7.79/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.48  --bmc1_ucm_layered_model                none
% 7.79/1.48  --bmc1_ucm_max_lemma_size               10
% 7.79/1.48  
% 7.79/1.48  ------ AIG Options
% 7.79/1.48  
% 7.79/1.48  --aig_mode                              false
% 7.79/1.48  
% 7.79/1.48  ------ Instantiation Options
% 7.79/1.48  
% 7.79/1.48  --instantiation_flag                    true
% 7.79/1.48  --inst_sos_flag                         true
% 7.79/1.48  --inst_sos_phase                        true
% 7.79/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel_side                     num_symb
% 7.79/1.48  --inst_solver_per_active                1400
% 7.79/1.48  --inst_solver_calls_frac                1.
% 7.79/1.48  --inst_passive_queue_type               priority_queues
% 7.79/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.48  --inst_passive_queues_freq              [25;2]
% 7.79/1.48  --inst_dismatching                      true
% 7.79/1.48  --inst_eager_unprocessed_to_passive     true
% 7.79/1.48  --inst_prop_sim_given                   true
% 7.79/1.48  --inst_prop_sim_new                     false
% 7.79/1.48  --inst_subs_new                         false
% 7.79/1.48  --inst_eq_res_simp                      false
% 7.79/1.48  --inst_subs_given                       false
% 7.79/1.48  --inst_orphan_elimination               true
% 7.79/1.48  --inst_learning_loop_flag               true
% 7.79/1.48  --inst_learning_start                   3000
% 7.79/1.48  --inst_learning_factor                  2
% 7.79/1.48  --inst_start_prop_sim_after_learn       3
% 7.79/1.48  --inst_sel_renew                        solver
% 7.79/1.48  --inst_lit_activity_flag                true
% 7.79/1.48  --inst_restr_to_given                   false
% 7.79/1.48  --inst_activity_threshold               500
% 7.79/1.48  --inst_out_proof                        true
% 7.79/1.48  
% 7.79/1.48  ------ Resolution Options
% 7.79/1.48  
% 7.79/1.48  --resolution_flag                       true
% 7.79/1.48  --res_lit_sel                           adaptive
% 7.79/1.48  --res_lit_sel_side                      none
% 7.79/1.48  --res_ordering                          kbo
% 7.79/1.48  --res_to_prop_solver                    active
% 7.79/1.48  --res_prop_simpl_new                    false
% 7.79/1.48  --res_prop_simpl_given                  true
% 7.79/1.48  --res_passive_queue_type                priority_queues
% 7.79/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.48  --res_passive_queues_freq               [15;5]
% 7.79/1.48  --res_forward_subs                      full
% 7.79/1.48  --res_backward_subs                     full
% 7.79/1.48  --res_forward_subs_resolution           true
% 7.79/1.48  --res_backward_subs_resolution          true
% 7.79/1.48  --res_orphan_elimination                true
% 7.79/1.48  --res_time_limit                        2.
% 7.79/1.48  --res_out_proof                         true
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Options
% 7.79/1.48  
% 7.79/1.48  --superposition_flag                    true
% 7.79/1.48  --sup_passive_queue_type                priority_queues
% 7.79/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.79/1.48  --demod_completeness_check              fast
% 7.79/1.48  --demod_use_ground                      true
% 7.79/1.48  --sup_to_prop_solver                    passive
% 7.79/1.48  --sup_prop_simpl_new                    true
% 7.79/1.48  --sup_prop_simpl_given                  true
% 7.79/1.48  --sup_fun_splitting                     true
% 7.79/1.48  --sup_smt_interval                      50000
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Simplification Setup
% 7.79/1.48  
% 7.79/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.79/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.79/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.79/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.79/1.48  --sup_immed_triv                        [TrivRules]
% 7.79/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_bw_main                     []
% 7.79/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.79/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_input_bw                          []
% 7.79/1.48  
% 7.79/1.48  ------ Combination Options
% 7.79/1.48  
% 7.79/1.48  --comb_res_mult                         3
% 7.79/1.48  --comb_sup_mult                         2
% 7.79/1.48  --comb_inst_mult                        10
% 7.79/1.48  
% 7.79/1.48  ------ Debug Options
% 7.79/1.48  
% 7.79/1.48  --dbg_backtrace                         false
% 7.79/1.48  --dbg_dump_prop_clauses                 false
% 7.79/1.48  --dbg_dump_prop_clauses_file            -
% 7.79/1.48  --dbg_out_stat                          false
% 7.79/1.48  ------ Parsing...
% 7.79/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.79/1.48  ------ Proving...
% 7.79/1.48  ------ Problem Properties 
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  clauses                                 33
% 7.79/1.48  conjectures                             10
% 7.79/1.48  EPR                                     6
% 7.79/1.48  Horn                                    29
% 7.79/1.48  unary                                   12
% 7.79/1.48  binary                                  7
% 7.79/1.48  lits                                    82
% 7.79/1.48  lits eq                                 28
% 7.79/1.48  fd_pure                                 0
% 7.79/1.48  fd_pseudo                               0
% 7.79/1.48  fd_cond                                 3
% 7.79/1.48  fd_pseudo_cond                          1
% 7.79/1.48  AC symbols                              0
% 7.79/1.48  
% 7.79/1.48  ------ Schedule dynamic 5 is on 
% 7.79/1.48  
% 7.79/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  ------ 
% 7.79/1.48  Current options:
% 7.79/1.48  ------ 
% 7.79/1.48  
% 7.79/1.48  ------ Input Options
% 7.79/1.48  
% 7.79/1.48  --out_options                           all
% 7.79/1.48  --tptp_safe_out                         true
% 7.79/1.48  --problem_path                          ""
% 7.79/1.48  --include_path                          ""
% 7.79/1.48  --clausifier                            res/vclausify_rel
% 7.79/1.48  --clausifier_options                    ""
% 7.79/1.48  --stdin                                 false
% 7.79/1.48  --stats_out                             all
% 7.79/1.48  
% 7.79/1.48  ------ General Options
% 7.79/1.48  
% 7.79/1.48  --fof                                   false
% 7.79/1.48  --time_out_real                         305.
% 7.79/1.48  --time_out_virtual                      -1.
% 7.79/1.48  --symbol_type_check                     false
% 7.79/1.48  --clausify_out                          false
% 7.79/1.48  --sig_cnt_out                           false
% 7.79/1.48  --trig_cnt_out                          false
% 7.79/1.48  --trig_cnt_out_tolerance                1.
% 7.79/1.48  --trig_cnt_out_sk_spl                   false
% 7.79/1.48  --abstr_cl_out                          false
% 7.79/1.48  
% 7.79/1.48  ------ Global Options
% 7.79/1.48  
% 7.79/1.48  --schedule                              default
% 7.79/1.48  --add_important_lit                     false
% 7.79/1.48  --prop_solver_per_cl                    1000
% 7.79/1.48  --min_unsat_core                        false
% 7.79/1.48  --soft_assumptions                      false
% 7.79/1.48  --soft_lemma_size                       3
% 7.79/1.48  --prop_impl_unit_size                   0
% 7.79/1.48  --prop_impl_unit                        []
% 7.79/1.48  --share_sel_clauses                     true
% 7.79/1.48  --reset_solvers                         false
% 7.79/1.48  --bc_imp_inh                            [conj_cone]
% 7.79/1.48  --conj_cone_tolerance                   3.
% 7.79/1.48  --extra_neg_conj                        none
% 7.79/1.48  --large_theory_mode                     true
% 7.79/1.48  --prolific_symb_bound                   200
% 7.79/1.48  --lt_threshold                          2000
% 7.79/1.48  --clause_weak_htbl                      true
% 7.79/1.48  --gc_record_bc_elim                     false
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing Options
% 7.79/1.48  
% 7.79/1.48  --preprocessing_flag                    true
% 7.79/1.48  --time_out_prep_mult                    0.1
% 7.79/1.48  --splitting_mode                        input
% 7.79/1.48  --splitting_grd                         true
% 7.79/1.48  --splitting_cvd                         false
% 7.79/1.48  --splitting_cvd_svl                     false
% 7.79/1.48  --splitting_nvd                         32
% 7.79/1.48  --sub_typing                            true
% 7.79/1.48  --prep_gs_sim                           true
% 7.79/1.48  --prep_unflatten                        true
% 7.79/1.48  --prep_res_sim                          true
% 7.79/1.48  --prep_upred                            true
% 7.79/1.48  --prep_sem_filter                       exhaustive
% 7.79/1.48  --prep_sem_filter_out                   false
% 7.79/1.48  --pred_elim                             true
% 7.79/1.48  --res_sim_input                         true
% 7.79/1.48  --eq_ax_congr_red                       true
% 7.79/1.48  --pure_diseq_elim                       true
% 7.79/1.48  --brand_transform                       false
% 7.79/1.48  --non_eq_to_eq                          false
% 7.79/1.48  --prep_def_merge                        true
% 7.79/1.48  --prep_def_merge_prop_impl              false
% 7.79/1.48  --prep_def_merge_mbd                    true
% 7.79/1.48  --prep_def_merge_tr_red                 false
% 7.79/1.48  --prep_def_merge_tr_cl                  false
% 7.79/1.48  --smt_preprocessing                     true
% 7.79/1.48  --smt_ac_axioms                         fast
% 7.79/1.48  --preprocessed_out                      false
% 7.79/1.48  --preprocessed_stats                    false
% 7.79/1.48  
% 7.79/1.48  ------ Abstraction refinement Options
% 7.79/1.48  
% 7.79/1.48  --abstr_ref                             []
% 7.79/1.48  --abstr_ref_prep                        false
% 7.79/1.48  --abstr_ref_until_sat                   false
% 7.79/1.48  --abstr_ref_sig_restrict                funpre
% 7.79/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.48  --abstr_ref_under                       []
% 7.79/1.48  
% 7.79/1.48  ------ SAT Options
% 7.79/1.48  
% 7.79/1.48  --sat_mode                              false
% 7.79/1.48  --sat_fm_restart_options                ""
% 7.79/1.48  --sat_gr_def                            false
% 7.79/1.48  --sat_epr_types                         true
% 7.79/1.48  --sat_non_cyclic_types                  false
% 7.79/1.48  --sat_finite_models                     false
% 7.79/1.48  --sat_fm_lemmas                         false
% 7.79/1.48  --sat_fm_prep                           false
% 7.79/1.48  --sat_fm_uc_incr                        true
% 7.79/1.48  --sat_out_model                         small
% 7.79/1.48  --sat_out_clauses                       false
% 7.79/1.48  
% 7.79/1.48  ------ QBF Options
% 7.79/1.48  
% 7.79/1.48  --qbf_mode                              false
% 7.79/1.48  --qbf_elim_univ                         false
% 7.79/1.48  --qbf_dom_inst                          none
% 7.79/1.48  --qbf_dom_pre_inst                      false
% 7.79/1.48  --qbf_sk_in                             false
% 7.79/1.48  --qbf_pred_elim                         true
% 7.79/1.48  --qbf_split                             512
% 7.79/1.48  
% 7.79/1.48  ------ BMC1 Options
% 7.79/1.48  
% 7.79/1.48  --bmc1_incremental                      false
% 7.79/1.48  --bmc1_axioms                           reachable_all
% 7.79/1.48  --bmc1_min_bound                        0
% 7.79/1.48  --bmc1_max_bound                        -1
% 7.79/1.48  --bmc1_max_bound_default                -1
% 7.79/1.48  --bmc1_symbol_reachability              true
% 7.79/1.48  --bmc1_property_lemmas                  false
% 7.79/1.48  --bmc1_k_induction                      false
% 7.79/1.48  --bmc1_non_equiv_states                 false
% 7.79/1.48  --bmc1_deadlock                         false
% 7.79/1.48  --bmc1_ucm                              false
% 7.79/1.48  --bmc1_add_unsat_core                   none
% 7.79/1.48  --bmc1_unsat_core_children              false
% 7.79/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.48  --bmc1_out_stat                         full
% 7.79/1.48  --bmc1_ground_init                      false
% 7.79/1.48  --bmc1_pre_inst_next_state              false
% 7.79/1.48  --bmc1_pre_inst_state                   false
% 7.79/1.48  --bmc1_pre_inst_reach_state             false
% 7.79/1.48  --bmc1_out_unsat_core                   false
% 7.79/1.48  --bmc1_aig_witness_out                  false
% 7.79/1.48  --bmc1_verbose                          false
% 7.79/1.48  --bmc1_dump_clauses_tptp                false
% 7.79/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.48  --bmc1_dump_file                        -
% 7.79/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.48  --bmc1_ucm_extend_mode                  1
% 7.79/1.48  --bmc1_ucm_init_mode                    2
% 7.79/1.48  --bmc1_ucm_cone_mode                    none
% 7.79/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.48  --bmc1_ucm_relax_model                  4
% 7.79/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.48  --bmc1_ucm_layered_model                none
% 7.79/1.48  --bmc1_ucm_max_lemma_size               10
% 7.79/1.48  
% 7.79/1.48  ------ AIG Options
% 7.79/1.48  
% 7.79/1.48  --aig_mode                              false
% 7.79/1.48  
% 7.79/1.48  ------ Instantiation Options
% 7.79/1.48  
% 7.79/1.48  --instantiation_flag                    true
% 7.79/1.48  --inst_sos_flag                         true
% 7.79/1.48  --inst_sos_phase                        true
% 7.79/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.48  --inst_lit_sel_side                     none
% 7.79/1.48  --inst_solver_per_active                1400
% 7.79/1.48  --inst_solver_calls_frac                1.
% 7.79/1.48  --inst_passive_queue_type               priority_queues
% 7.79/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.48  --inst_passive_queues_freq              [25;2]
% 7.79/1.48  --inst_dismatching                      true
% 7.79/1.48  --inst_eager_unprocessed_to_passive     true
% 7.79/1.48  --inst_prop_sim_given                   true
% 7.79/1.48  --inst_prop_sim_new                     false
% 7.79/1.48  --inst_subs_new                         false
% 7.79/1.48  --inst_eq_res_simp                      false
% 7.79/1.48  --inst_subs_given                       false
% 7.79/1.48  --inst_orphan_elimination               true
% 7.79/1.48  --inst_learning_loop_flag               true
% 7.79/1.48  --inst_learning_start                   3000
% 7.79/1.48  --inst_learning_factor                  2
% 7.79/1.48  --inst_start_prop_sim_after_learn       3
% 7.79/1.48  --inst_sel_renew                        solver
% 7.79/1.48  --inst_lit_activity_flag                true
% 7.79/1.48  --inst_restr_to_given                   false
% 7.79/1.48  --inst_activity_threshold               500
% 7.79/1.48  --inst_out_proof                        true
% 7.79/1.48  
% 7.79/1.48  ------ Resolution Options
% 7.79/1.48  
% 7.79/1.48  --resolution_flag                       false
% 7.79/1.48  --res_lit_sel                           adaptive
% 7.79/1.48  --res_lit_sel_side                      none
% 7.79/1.48  --res_ordering                          kbo
% 7.79/1.48  --res_to_prop_solver                    active
% 7.79/1.48  --res_prop_simpl_new                    false
% 7.79/1.48  --res_prop_simpl_given                  true
% 7.79/1.48  --res_passive_queue_type                priority_queues
% 7.79/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.48  --res_passive_queues_freq               [15;5]
% 7.79/1.48  --res_forward_subs                      full
% 7.79/1.48  --res_backward_subs                     full
% 7.79/1.48  --res_forward_subs_resolution           true
% 7.79/1.48  --res_backward_subs_resolution          true
% 7.79/1.48  --res_orphan_elimination                true
% 7.79/1.48  --res_time_limit                        2.
% 7.79/1.48  --res_out_proof                         true
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Options
% 7.79/1.48  
% 7.79/1.48  --superposition_flag                    true
% 7.79/1.48  --sup_passive_queue_type                priority_queues
% 7.79/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.79/1.48  --demod_completeness_check              fast
% 7.79/1.48  --demod_use_ground                      true
% 7.79/1.48  --sup_to_prop_solver                    passive
% 7.79/1.48  --sup_prop_simpl_new                    true
% 7.79/1.48  --sup_prop_simpl_given                  true
% 7.79/1.48  --sup_fun_splitting                     true
% 7.79/1.48  --sup_smt_interval                      50000
% 7.79/1.48  
% 7.79/1.48  ------ Superposition Simplification Setup
% 7.79/1.48  
% 7.79/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.79/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.79/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.79/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.79/1.48  --sup_immed_triv                        [TrivRules]
% 7.79/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_immed_bw_main                     []
% 7.79/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.79/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.48  --sup_input_bw                          []
% 7.79/1.48  
% 7.79/1.48  ------ Combination Options
% 7.79/1.48  
% 7.79/1.48  --comb_res_mult                         3
% 7.79/1.48  --comb_sup_mult                         2
% 7.79/1.48  --comb_inst_mult                        10
% 7.79/1.48  
% 7.79/1.48  ------ Debug Options
% 7.79/1.48  
% 7.79/1.48  --dbg_backtrace                         false
% 7.79/1.48  --dbg_dump_prop_clauses                 false
% 7.79/1.48  --dbg_dump_prop_clauses_file            -
% 7.79/1.48  --dbg_out_stat                          false
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  ------ Proving...
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  % SZS status Theorem for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  fof(f16,conjecture,(
% 7.79/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f17,negated_conjecture,(
% 7.79/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.79/1.48    inference(negated_conjecture,[],[f16])).
% 7.79/1.48  
% 7.79/1.48  fof(f40,plain,(
% 7.79/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.79/1.48    inference(ennf_transformation,[],[f17])).
% 7.79/1.48  
% 7.79/1.48  fof(f41,plain,(
% 7.79/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.79/1.48    inference(flattening,[],[f40])).
% 7.79/1.48  
% 7.79/1.48  fof(f45,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f44,plain,(
% 7.79/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.79/1.48    introduced(choice_axiom,[])).
% 7.79/1.48  
% 7.79/1.48  fof(f46,plain,(
% 7.79/1.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.79/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f45,f44])).
% 7.79/1.48  
% 7.79/1.48  fof(f77,plain,(
% 7.79/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f11,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f34,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f11])).
% 7.79/1.48  
% 7.79/1.48  fof(f35,plain,(
% 7.79/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(flattening,[],[f34])).
% 7.79/1.48  
% 7.79/1.48  fof(f43,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(nnf_transformation,[],[f35])).
% 7.79/1.48  
% 7.79/1.48  fof(f60,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f43])).
% 7.79/1.48  
% 7.79/1.48  fof(f7,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f28,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f7])).
% 7.79/1.48  
% 7.79/1.48  fof(f55,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f28])).
% 7.79/1.48  
% 7.79/1.48  fof(f76,plain,(
% 7.79/1.48    v1_funct_2(sK3,sK1,sK0)),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f81,plain,(
% 7.79/1.48    k1_xboole_0 != sK0),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f74,plain,(
% 7.79/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f8,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f29,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(ennf_transformation,[],[f8])).
% 7.79/1.48  
% 7.79/1.48  fof(f56,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f29])).
% 7.79/1.48  
% 7.79/1.48  fof(f78,plain,(
% 7.79/1.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f5,axiom,(
% 7.79/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f24,plain,(
% 7.79/1.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.79/1.48    inference(ennf_transformation,[],[f5])).
% 7.79/1.48  
% 7.79/1.48  fof(f25,plain,(
% 7.79/1.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(flattening,[],[f24])).
% 7.79/1.48  
% 7.79/1.48  fof(f53,plain,(
% 7.79/1.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f25])).
% 7.79/1.48  
% 7.79/1.48  fof(f14,axiom,(
% 7.79/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f68,plain,(
% 7.79/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f14])).
% 7.79/1.48  
% 7.79/1.48  fof(f85,plain,(
% 7.79/1.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(definition_unfolding,[],[f53,f68])).
% 7.79/1.48  
% 7.79/1.48  fof(f80,plain,(
% 7.79/1.48    v2_funct_1(sK2)),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f72,plain,(
% 7.79/1.48    v1_funct_1(sK2)),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f1,axiom,(
% 7.79/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f19,plain,(
% 7.79/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(ennf_transformation,[],[f1])).
% 7.79/1.48  
% 7.79/1.48  fof(f47,plain,(
% 7.79/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f19])).
% 7.79/1.48  
% 7.79/1.48  fof(f2,axiom,(
% 7.79/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f48,plain,(
% 7.79/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f2])).
% 7.79/1.48  
% 7.79/1.48  fof(f3,axiom,(
% 7.79/1.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f20,plain,(
% 7.79/1.48    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.79/1.48    inference(ennf_transformation,[],[f3])).
% 7.79/1.48  
% 7.79/1.48  fof(f21,plain,(
% 7.79/1.48    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.79/1.48    inference(flattening,[],[f20])).
% 7.79/1.48  
% 7.79/1.48  fof(f49,plain,(
% 7.79/1.48    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f21])).
% 7.79/1.48  
% 7.79/1.48  fof(f84,plain,(
% 7.79/1.48    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(X0) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.79/1.48    inference(definition_unfolding,[],[f49,f68,f68])).
% 7.79/1.48  
% 7.79/1.48  fof(f87,plain,(
% 7.79/1.48    ( ! [X2,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1)) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.79/1.48    inference(equality_resolution,[],[f84])).
% 7.79/1.48  
% 7.79/1.48  fof(f4,axiom,(
% 7.79/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f22,plain,(
% 7.79/1.48    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.79/1.48    inference(ennf_transformation,[],[f4])).
% 7.79/1.48  
% 7.79/1.48  fof(f23,plain,(
% 7.79/1.48    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.79/1.48    inference(flattening,[],[f22])).
% 7.79/1.48  
% 7.79/1.48  fof(f51,plain,(
% 7.79/1.48    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f23])).
% 7.79/1.48  
% 7.79/1.48  fof(f73,plain,(
% 7.79/1.48    v1_funct_2(sK2,sK0,sK1)),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f15,axiom,(
% 7.79/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f38,plain,(
% 7.79/1.48    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.79/1.48    inference(ennf_transformation,[],[f15])).
% 7.79/1.48  
% 7.79/1.48  fof(f39,plain,(
% 7.79/1.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.79/1.48    inference(flattening,[],[f38])).
% 7.79/1.48  
% 7.79/1.48  fof(f69,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f39])).
% 7.79/1.48  
% 7.79/1.48  fof(f71,plain,(
% 7.79/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f39])).
% 7.79/1.48  
% 7.79/1.48  fof(f82,plain,(
% 7.79/1.48    k1_xboole_0 != sK1),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f13,axiom,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f36,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.79/1.48    inference(ennf_transformation,[],[f13])).
% 7.79/1.48  
% 7.79/1.48  fof(f37,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.79/1.48    inference(flattening,[],[f36])).
% 7.79/1.48  
% 7.79/1.48  fof(f67,plain,(
% 7.79/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.79/1.48    inference(cnf_transformation,[],[f37])).
% 7.79/1.48  
% 7.79/1.48  fof(f75,plain,(
% 7.79/1.48    v1_funct_1(sK3)),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f10,axiom,(
% 7.79/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f32,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.79/1.48    inference(ennf_transformation,[],[f10])).
% 7.79/1.48  
% 7.79/1.48  fof(f33,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(flattening,[],[f32])).
% 7.79/1.48  
% 7.79/1.48  fof(f42,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(nnf_transformation,[],[f33])).
% 7.79/1.48  
% 7.79/1.48  fof(f58,plain,(
% 7.79/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f42])).
% 7.79/1.48  
% 7.79/1.48  fof(f79,plain,(
% 7.79/1.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  fof(f12,axiom,(
% 7.79/1.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f18,plain,(
% 7.79/1.48    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.79/1.48    inference(pure_predicate_removal,[],[f12])).
% 7.79/1.48  
% 7.79/1.48  fof(f66,plain,(
% 7.79/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f18])).
% 7.79/1.48  
% 7.79/1.48  fof(f9,axiom,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f30,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.79/1.48    inference(ennf_transformation,[],[f9])).
% 7.79/1.48  
% 7.79/1.48  fof(f31,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(flattening,[],[f30])).
% 7.79/1.48  
% 7.79/1.48  fof(f57,plain,(
% 7.79/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f31])).
% 7.79/1.48  
% 7.79/1.48  fof(f6,axiom,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 7.79/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.79/1.48  
% 7.79/1.48  fof(f26,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.79/1.48    inference(ennf_transformation,[],[f6])).
% 7.79/1.48  
% 7.79/1.48  fof(f27,plain,(
% 7.79/1.48    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.79/1.48    inference(flattening,[],[f26])).
% 7.79/1.48  
% 7.79/1.48  fof(f54,plain,(
% 7.79/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.79/1.48    inference(cnf_transformation,[],[f27])).
% 7.79/1.48  
% 7.79/1.48  fof(f83,plain,(
% 7.79/1.48    k2_funct_1(sK2) != sK3),
% 7.79/1.48    inference(cnf_transformation,[],[f46])).
% 7.79/1.48  
% 7.79/1.48  cnf(c_30,negated_conjecture,
% 7.79/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.79/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1230,plain,
% 7.79/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_18,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.79/1.48      | k1_xboole_0 = X2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1233,plain,
% 7.79/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.79/1.48      | k1_xboole_0 = X1
% 7.79/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3374,plain,
% 7.79/1.48      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 7.79/1.48      | sK0 = k1_xboole_0
% 7.79/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1230,c_1233]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_8,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1241,plain,
% 7.79/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2252,plain,
% 7.79/1.48      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1230,c_1241]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3378,plain,
% 7.79/1.48      ( k1_relat_1(sK3) = sK1
% 7.79/1.48      | sK0 = k1_xboole_0
% 7.79/1.48      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.79/1.48      inference(demodulation,[status(thm)],[c_3374,c_2252]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_31,negated_conjecture,
% 7.79/1.48      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_40,plain,
% 7.79/1.48      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_26,negated_conjecture,
% 7.79/1.48      ( k1_xboole_0 != sK0 ),
% 7.79/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_732,plain,( X0 = X0 ),theory(equality) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_763,plain,
% 7.79/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_732]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_733,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1324,plain,
% 7.79/1.48      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_733]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1325,plain,
% 7.79/1.48      ( sK0 != k1_xboole_0
% 7.79/1.48      | k1_xboole_0 = sK0
% 7.79/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1324]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_11099,plain,
% 7.79/1.48      ( k1_relat_1(sK3) = sK1 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3378,c_40,c_26,c_763,c_1325]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_33,negated_conjecture,
% 7.79/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.79/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1227,plain,
% 7.79/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_9,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1240,plain,
% 7.79/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2158,plain,
% 7.79/1.48      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1227,c_1240]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_29,negated_conjecture,
% 7.79/1.48      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.79/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2160,plain,
% 7.79/1.48      ( k2_relat_1(sK2) = sK1 ),
% 7.79/1.48      inference(light_normalisation,[status(thm)],[c_2158,c_29]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_5,plain,
% 7.79/1.48      ( ~ v2_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.79/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_27,negated_conjecture,
% 7.79/1.48      ( v2_funct_1(sK2) ),
% 7.79/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_464,plain,
% 7.79/1.48      ( ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.79/1.48      | sK2 != X0 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_5,c_27]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_465,plain,
% 7.79/1.48      ( ~ v1_funct_1(sK2)
% 7.79/1.48      | ~ v1_relat_1(sK2)
% 7.79/1.48      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_464]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_35,negated_conjecture,
% 7.79/1.48      ( v1_funct_1(sK2) ),
% 7.79/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_467,plain,
% 7.79/1.48      ( ~ v1_relat_1(sK2)
% 7.79/1.48      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_465,c_35]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1219,plain,
% 7.79/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.79/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2162,plain,
% 7.79/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.79/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.79/1.48      inference(demodulation,[status(thm)],[c_2160,c_1219]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_38,plain,
% 7.79/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_0,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.79/1.48      | ~ v1_relat_1(X1)
% 7.79/1.48      | v1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1347,plain,
% 7.79/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | v1_relat_1(sK2) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1529,plain,
% 7.79/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 7.79/1.48      | v1_relat_1(sK2) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1347]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1770,plain,
% 7.79/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.79/1.48      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.79/1.48      | v1_relat_1(sK2) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1529]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1771,plain,
% 7.79/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK2) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1770]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.79/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1805,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1806,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2864,plain,
% 7.79/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_2162,c_38,c_1771,c_1806]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2,plain,
% 7.79/1.48      ( ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X1)
% 7.79/1.48      | ~ v1_funct_1(X2)
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | ~ v1_relat_1(X1)
% 7.79/1.48      | ~ v1_relat_1(X2)
% 7.79/1.48      | X0 = X2
% 7.79/1.48      | k5_relat_1(X2,X1) != k6_partfun1(k1_relat_1(X0))
% 7.79/1.48      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X2)) ),
% 7.79/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1243,plain,
% 7.79/1.48      ( X0 = X1
% 7.79/1.48      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
% 7.79/1.48      | k5_relat_1(X2,X0) != k6_partfun1(k2_relat_1(X1))
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(X1) != iProver_top
% 7.79/1.48      | v1_funct_1(X2) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(X2) != iProver_top
% 7.79/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3680,plain,
% 7.79/1.48      ( k2_funct_1(sK2) = X0
% 7.79/1.48      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 7.79/1.48      | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(sK2,X0)
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.79/1.48      | v1_funct_1(sK2) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_2864,c_1243]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1245,plain,
% 7.79/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.79/1.48      | v1_relat_1(X1) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2259,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK2) = iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1227,c_1245]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2580,plain,
% 7.79/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_2259,c_38,c_1771,c_1806]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3,plain,
% 7.79/1.48      ( ~ v2_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_492,plain,
% 7.79/1.48      ( ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_relat_1(X0)
% 7.79/1.48      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.79/1.48      | sK2 != X0 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_3,c_27]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_493,plain,
% 7.79/1.48      ( ~ v1_funct_1(sK2)
% 7.79/1.48      | ~ v1_relat_1(sK2)
% 7.79/1.48      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_492]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_495,plain,
% 7.79/1.48      ( ~ v1_relat_1(sK2)
% 7.79/1.48      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_493,c_35]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1217,plain,
% 7.79/1.48      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.79/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2585,plain,
% 7.79/1.48      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_2580,c_1217]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3682,plain,
% 7.79/1.48      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 7.79/1.48      | k2_funct_1(sK2) = X0
% 7.79/1.48      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.79/1.48      | v1_funct_1(sK2) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.79/1.48      inference(light_normalisation,[status(thm)],[c_3680,c_2585]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_36,plain,
% 7.79/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_34,negated_conjecture,
% 7.79/1.48      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.79/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_37,plain,
% 7.79/1.48      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_23,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | ~ v2_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | v1_funct_1(k2_funct_1(X0))
% 7.79/1.48      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_378,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | v1_funct_1(k2_funct_1(X0))
% 7.79/1.48      | k2_relset_1(X1,X2,X0) != X2
% 7.79/1.48      | sK2 != X0 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_379,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK2,X0,X1)
% 7.79/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK2))
% 7.79/1.48      | ~ v1_funct_1(sK2)
% 7.79/1.48      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_378]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_383,plain,
% 7.79/1.48      ( v1_funct_1(k2_funct_1(sK2))
% 7.79/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | ~ v1_funct_2(sK2,X0,X1)
% 7.79/1.48      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_379,c_35]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_384,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK2,X0,X1)
% 7.79/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK2))
% 7.79/1.48      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.79/1.48      inference(renaming,[status(thm)],[c_383]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1358,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.79/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK2))
% 7.79/1.48      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_384]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1359,plain,
% 7.79/1.48      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 7.79/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.79/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.79/1.48      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1358]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_21,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.79/1.48      | ~ v2_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.79/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_426,plain,
% 7.79/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.79/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | k2_relset_1(X1,X2,X0) != X2
% 7.79/1.48      | sK2 != X0 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_427,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK2,X0,X1)
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.79/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | ~ v1_funct_1(sK2)
% 7.79/1.48      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_426]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_431,plain,
% 7.79/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.79/1.48      | ~ v1_funct_2(sK2,X0,X1)
% 7.79/1.48      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_427,c_35]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_432,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK2,X0,X1)
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.79/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | k2_relset_1(X0,X1,sK2) != X1 ),
% 7.79/1.48      inference(renaming,[status(thm)],[c_431]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1221,plain,
% 7.79/1.48      ( k2_relset_1(X0,X1,sK2) != X1
% 7.79/1.48      | v1_funct_2(sK2,X0,X1) != iProver_top
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 7.79/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1971,plain,
% 7.79/1.48      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 7.79/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_29,c_1221]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1512,plain,
% 7.79/1.48      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.79/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.79/1.48      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_432]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1513,plain,
% 7.79/1.48      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 7.79/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.79/1.48      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 7.79/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1512]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2089,plain,
% 7.79/1.48      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_1971,c_37,c_38,c_29,c_1513]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2260,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.79/1.48      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_2089,c_1245]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2810,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2811,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_2810]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25453,plain,
% 7.79/1.48      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 7.79/1.48      | k2_funct_1(sK2) = X0
% 7.79/1.48      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3682,c_36,c_37,c_38,c_29,c_1359,c_1771,c_1806,c_2260,
% 7.79/1.48                 c_2811]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3375,plain,
% 7.79/1.48      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 7.79/1.48      | sK1 = k1_xboole_0
% 7.79/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1227,c_1233]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2253,plain,
% 7.79/1.48      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1227,c_1241]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3377,plain,
% 7.79/1.48      ( k1_relat_1(sK2) = sK0
% 7.79/1.48      | sK1 = k1_xboole_0
% 7.79/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 7.79/1.48      inference(demodulation,[status(thm)],[c_3375,c_2253]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25,negated_conjecture,
% 7.79/1.48      ( k1_xboole_0 != sK1 ),
% 7.79/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1301,plain,
% 7.79/1.48      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_733]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1302,plain,
% 7.79/1.48      ( sK1 != k1_xboole_0
% 7.79/1.48      | k1_xboole_0 = sK1
% 7.79/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.79/1.48      inference(instantiation,[status(thm)],[c_1301]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_10219,plain,
% 7.79/1.48      ( k1_relat_1(sK2) = sK0 ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3377,c_37,c_25,c_763,c_1302]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25459,plain,
% 7.79/1.48      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 7.79/1.48      | k2_funct_1(sK2) = X0
% 7.79/1.48      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 7.79/1.48      | v1_funct_1(X0) != iProver_top
% 7.79/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.48      inference(light_normalisation,[status(thm)],[c_25453,c_10219]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25465,plain,
% 7.79/1.48      ( k5_relat_1(sK2,sK3) != k6_partfun1(sK0)
% 7.79/1.48      | k2_funct_1(sK2) = sK3
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_11099,c_25459]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_20,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.79/1.48      | ~ v1_funct_1(X0)
% 7.79/1.48      | ~ v1_funct_1(X3)
% 7.79/1.48      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1231,plain,
% 7.79/1.48      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.79/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.79/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.79/1.48      | v1_funct_1(X5) != iProver_top
% 7.79/1.48      | v1_funct_1(X4) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2688,plain,
% 7.79/1.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.79/1.48      | v1_funct_1(X2) != iProver_top
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1230,c_1231]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_32,negated_conjecture,
% 7.79/1.48      ( v1_funct_1(sK3) ),
% 7.79/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_39,plain,
% 7.79/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3049,plain,
% 7.79/1.48      ( v1_funct_1(X2) != iProver_top
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.79/1.48      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_2688,c_39]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3050,plain,
% 7.79/1.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.79/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.79/1.48      inference(renaming,[status(thm)],[c_3049]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3057,plain,
% 7.79/1.48      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.79/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1227,c_3050]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3151,plain,
% 7.79/1.48      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3057,c_36]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_12,plain,
% 7.79/1.48      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.79/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.79/1.48      | X2 = X3 ),
% 7.79/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_28,negated_conjecture,
% 7.79/1.48      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.79/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_362,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | X3 = X0
% 7.79/1.48      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.79/1.48      | k6_partfun1(sK0) != X3
% 7.79/1.48      | sK0 != X2
% 7.79/1.48      | sK0 != X1 ),
% 7.79/1.48      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_363,plain,
% 7.79/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.79/1.48      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.79/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.79/1.48      inference(unflattening,[status(thm)],[c_362]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_19,plain,
% 7.79/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.79/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_371,plain,
% 7.79/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.79/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.79/1.48      inference(forward_subsumption_resolution,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_363,c_19]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1224,plain,
% 7.79/1.48      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.79/1.48      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3153,plain,
% 7.79/1.48      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.79/1.48      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.79/1.48      inference(demodulation,[status(thm)],[c_3151,c_1224]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_41,plain,
% 7.79/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_10,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.79/1.48      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.79/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1239,plain,
% 7.79/1.48      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.79/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.79/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3506,plain,
% 7.79/1.48      ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.79/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1230,c_1239]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3769,plain,
% 7.79/1.48      ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1227,c_3506]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_7,plain,
% 7.79/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.79/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.79/1.48      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 7.79/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1242,plain,
% 7.79/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.79/1.48      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.79/1.48      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_3919,plain,
% 7.79/1.48      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.79/1.48      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.79/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_3769,c_1242]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_6135,plain,
% 7.79/1.48      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.79/1.48      inference(global_propositional_subsumption,
% 7.79/1.48                [status(thm)],
% 7.79/1.48                [c_3153,c_38,c_41,c_3919]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25466,plain,
% 7.79/1.48      ( k2_funct_1(sK2) = sK3
% 7.79/1.48      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.48      inference(light_normalisation,[status(thm)],[c_25465,c_6135]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_25467,plain,
% 7.79/1.48      ( k2_funct_1(sK2) = sK3
% 7.79/1.48      | v1_funct_1(sK3) != iProver_top
% 7.79/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.79/1.48      inference(equality_resolution_simp,[status(thm)],[c_25466]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_1244,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.79/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2258,plain,
% 7.79/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.79/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1230,c_1245]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_2577,plain,
% 7.79/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.79/1.48      inference(superposition,[status(thm)],[c_1244,c_2258]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(c_24,negated_conjecture,
% 7.79/1.48      ( k2_funct_1(sK2) != sK3 ),
% 7.79/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.79/1.48  
% 7.79/1.48  cnf(contradiction,plain,
% 7.79/1.48      ( $false ),
% 7.79/1.48      inference(minisat,[status(thm)],[c_25467,c_2577,c_24,c_39]) ).
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.48  
% 7.79/1.48  ------                               Statistics
% 7.79/1.48  
% 7.79/1.48  ------ General
% 7.79/1.48  
% 7.79/1.48  abstr_ref_over_cycles:                  0
% 7.79/1.48  abstr_ref_under_cycles:                 0
% 7.79/1.48  gc_basic_clause_elim:                   0
% 7.79/1.48  forced_gc_time:                         0
% 7.79/1.48  parsing_time:                           0.012
% 7.79/1.48  unif_index_cands_time:                  0.
% 7.79/1.48  unif_index_add_time:                    0.
% 7.79/1.48  orderings_time:                         0.
% 7.79/1.48  out_proof_time:                         0.017
% 7.79/1.48  total_time:                             0.841
% 7.79/1.48  num_of_symbols:                         53
% 7.79/1.48  num_of_terms:                           37931
% 7.79/1.48  
% 7.79/1.48  ------ Preprocessing
% 7.79/1.48  
% 7.79/1.48  num_of_splits:                          0
% 7.79/1.48  num_of_split_atoms:                     0
% 7.79/1.48  num_of_reused_defs:                     0
% 7.79/1.48  num_eq_ax_congr_red:                    24
% 7.79/1.48  num_of_sem_filtered_clauses:            1
% 7.79/1.48  num_of_subtypes:                        0
% 7.79/1.48  monotx_restored_types:                  0
% 7.79/1.48  sat_num_of_epr_types:                   0
% 7.79/1.48  sat_num_of_non_cyclic_types:            0
% 7.79/1.48  sat_guarded_non_collapsed_types:        0
% 7.79/1.48  num_pure_diseq_elim:                    0
% 7.79/1.48  simp_replaced_by:                       0
% 7.79/1.48  res_preprocessed:                       168
% 7.79/1.48  prep_upred:                             0
% 7.79/1.48  prep_unflattend:                        15
% 7.79/1.48  smt_new_axioms:                         0
% 7.79/1.48  pred_elim_cands:                        4
% 7.79/1.48  pred_elim:                              2
% 7.79/1.48  pred_elim_cl:                           3
% 7.79/1.48  pred_elim_cycles:                       4
% 7.79/1.48  merged_defs:                            0
% 7.79/1.48  merged_defs_ncl:                        0
% 7.79/1.48  bin_hyper_res:                          0
% 7.79/1.48  prep_cycles:                            4
% 7.79/1.48  pred_elim_time:                         0.005
% 7.79/1.48  splitting_time:                         0.
% 7.79/1.48  sem_filter_time:                        0.
% 7.79/1.48  monotx_time:                            0.001
% 7.79/1.48  subtype_inf_time:                       0.
% 7.79/1.48  
% 7.79/1.48  ------ Problem properties
% 7.79/1.48  
% 7.79/1.48  clauses:                                33
% 7.79/1.48  conjectures:                            10
% 7.79/1.48  epr:                                    6
% 7.79/1.48  horn:                                   29
% 7.79/1.48  ground:                                 15
% 7.79/1.48  unary:                                  12
% 7.79/1.48  binary:                                 7
% 7.79/1.48  lits:                                   82
% 7.79/1.48  lits_eq:                                28
% 7.79/1.48  fd_pure:                                0
% 7.79/1.48  fd_pseudo:                              0
% 7.79/1.48  fd_cond:                                3
% 7.79/1.48  fd_pseudo_cond:                         1
% 7.79/1.48  ac_symbols:                             0
% 7.79/1.48  
% 7.79/1.48  ------ Propositional Solver
% 7.79/1.48  
% 7.79/1.48  prop_solver_calls:                      34
% 7.79/1.48  prop_fast_solver_calls:                 1609
% 7.79/1.48  smt_solver_calls:                       0
% 7.79/1.48  smt_fast_solver_calls:                  0
% 7.79/1.48  prop_num_of_clauses:                    10270
% 7.79/1.48  prop_preprocess_simplified:             19081
% 7.79/1.48  prop_fo_subsumed:                       91
% 7.79/1.48  prop_solver_time:                       0.
% 7.79/1.48  smt_solver_time:                        0.
% 7.79/1.48  smt_fast_solver_time:                   0.
% 7.79/1.48  prop_fast_solver_time:                  0.
% 7.79/1.48  prop_unsat_core_time:                   0.001
% 7.79/1.48  
% 7.79/1.48  ------ QBF
% 7.79/1.48  
% 7.79/1.48  qbf_q_res:                              0
% 7.79/1.48  qbf_num_tautologies:                    0
% 7.79/1.48  qbf_prep_cycles:                        0
% 7.79/1.48  
% 7.79/1.48  ------ BMC1
% 7.79/1.48  
% 7.79/1.48  bmc1_current_bound:                     -1
% 7.79/1.48  bmc1_last_solved_bound:                 -1
% 7.79/1.48  bmc1_unsat_core_size:                   -1
% 7.79/1.48  bmc1_unsat_core_parents_size:           -1
% 7.79/1.48  bmc1_merge_next_fun:                    0
% 7.79/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.79/1.48  
% 7.79/1.48  ------ Instantiation
% 7.79/1.48  
% 7.79/1.48  inst_num_of_clauses:                    2785
% 7.79/1.48  inst_num_in_passive:                    1268
% 7.79/1.48  inst_num_in_active:                     1401
% 7.79/1.48  inst_num_in_unprocessed:                118
% 7.79/1.48  inst_num_of_loops:                      1460
% 7.79/1.48  inst_num_of_learning_restarts:          0
% 7.79/1.48  inst_num_moves_active_passive:          56
% 7.79/1.48  inst_lit_activity:                      0
% 7.79/1.48  inst_lit_activity_moves:                2
% 7.79/1.48  inst_num_tautologies:                   0
% 7.79/1.48  inst_num_prop_implied:                  0
% 7.79/1.48  inst_num_existing_simplified:           0
% 7.79/1.48  inst_num_eq_res_simplified:             0
% 7.79/1.48  inst_num_child_elim:                    0
% 7.79/1.48  inst_num_of_dismatching_blockings:      5340
% 7.79/1.48  inst_num_of_non_proper_insts:           4639
% 7.79/1.48  inst_num_of_duplicates:                 0
% 7.79/1.48  inst_inst_num_from_inst_to_res:         0
% 7.79/1.48  inst_dismatching_checking_time:         0.
% 7.79/1.48  
% 7.79/1.48  ------ Resolution
% 7.79/1.48  
% 7.79/1.48  res_num_of_clauses:                     0
% 7.79/1.48  res_num_in_passive:                     0
% 7.79/1.48  res_num_in_active:                      0
% 7.79/1.48  res_num_of_loops:                       172
% 7.79/1.48  res_forward_subset_subsumed:            180
% 7.79/1.48  res_backward_subset_subsumed:           4
% 7.79/1.48  res_forward_subsumed:                   0
% 7.79/1.48  res_backward_subsumed:                  0
% 7.79/1.48  res_forward_subsumption_resolution:     1
% 7.79/1.48  res_backward_subsumption_resolution:    0
% 7.79/1.48  res_clause_to_clause_subsumption:       2373
% 7.79/1.48  res_orphan_elimination:                 0
% 7.79/1.48  res_tautology_del:                      128
% 7.79/1.48  res_num_eq_res_simplified:              0
% 7.79/1.48  res_num_sel_changes:                    0
% 7.79/1.48  res_moves_from_active_to_pass:          0
% 7.79/1.48  
% 7.79/1.48  ------ Superposition
% 7.79/1.48  
% 7.79/1.48  sup_time_total:                         0.
% 7.79/1.48  sup_time_generating:                    0.
% 7.79/1.48  sup_time_sim_full:                      0.
% 7.79/1.48  sup_time_sim_immed:                     0.
% 7.79/1.48  
% 7.79/1.48  sup_num_of_clauses:                     1203
% 7.79/1.48  sup_num_in_active:                      273
% 7.79/1.48  sup_num_in_passive:                     930
% 7.79/1.48  sup_num_of_loops:                       291
% 7.79/1.48  sup_fw_superposition:                   687
% 7.79/1.48  sup_bw_superposition:                   575
% 7.79/1.48  sup_immediate_simplified:               630
% 7.79/1.48  sup_given_eliminated:                   0
% 7.79/1.48  comparisons_done:                       0
% 7.79/1.48  comparisons_avoided:                    1
% 7.79/1.48  
% 7.79/1.48  ------ Simplifications
% 7.79/1.48  
% 7.79/1.48  
% 7.79/1.48  sim_fw_subset_subsumed:                 17
% 7.79/1.48  sim_bw_subset_subsumed:                 2
% 7.79/1.48  sim_fw_subsumed:                        42
% 7.79/1.48  sim_bw_subsumed:                        2
% 7.79/1.48  sim_fw_subsumption_res:                 0
% 7.79/1.48  sim_bw_subsumption_res:                 0
% 7.79/1.48  sim_tautology_del:                      0
% 7.79/1.48  sim_eq_tautology_del:                   25
% 7.79/1.48  sim_eq_res_simp:                        1
% 7.79/1.48  sim_fw_demodulated:                     109
% 7.79/1.48  sim_bw_demodulated:                     15
% 7.79/1.48  sim_light_normalised:                   504
% 7.79/1.48  sim_joinable_taut:                      0
% 7.79/1.48  sim_joinable_simp:                      0
% 7.79/1.48  sim_ac_normalised:                      0
% 7.79/1.48  sim_smt_subsumption:                    0
% 7.79/1.48  
%------------------------------------------------------------------------------
