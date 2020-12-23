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
% DateTime   : Thu Dec  3 12:02:59 EST 2020

% Result     : Theorem 15.55s
% Output     : CNFRefutation 15.55s
% Verified   : 
% Statistics : Number of formulae       :  233 (3029 expanded)
%              Number of clauses        :  138 ( 852 expanded)
%              Number of leaves         :   22 ( 778 expanded)
%              Depth                    :   27
%              Number of atoms          :  901 (25823 expanded)
%              Number of equality atoms :  453 (9621 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f47])).

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f55,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f54,f53])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f94,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
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

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

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
    inference(flattening,[],[f45])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f55])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f72,f78])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f43])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f99,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f78])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f97,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f61,f78])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f78])).

fof(f98,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1704,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1707,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1718,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5139,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1707,c_1718])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_45,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_5188,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5139,c_45])).

cnf(c_5189,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5188])).

cnf(c_5196,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1704,c_5189])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5235,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5196,c_42])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | v2_funct_2(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1717,plain,
    ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v2_funct_2(X3,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7352,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v2_funct_2(sK3,sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5235,c_1717])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_43,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_44,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_46,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1708,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5237,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5235,c_1708])).

cnf(c_8498,plain,
    ( v2_funct_2(sK3,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7352,c_42,c_43,c_44,c_45,c_46,c_47,c_5237])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_400,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_18])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_412,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_400,c_11])).

cnf(c_1701,plain,
    ( k2_relat_1(X0) = X1
    | v2_funct_2(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_2711,plain,
    ( k2_relat_1(sK3) = sK0
    | v2_funct_2(sK3,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1707,c_1701])).

cnf(c_8502,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(superposition,[status(thm)],[c_8498,c_2711])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1724,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2788,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1707,c_1724])).

cnf(c_8505,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_8502,c_2788])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1710,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8575,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8505,c_1710])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_49,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3227,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | k2_relat_1(sK3) != sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2788,c_1710])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_122,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_126,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1123,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1843,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_1844,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_3413,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | k2_relat_1(sK3) != sK0
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3227,c_45,c_46,c_47,c_32,c_122,c_126,c_1844])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1721,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1720,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5674,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5235,c_1720])).

cnf(c_6966,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5674,c_42,c_44,c_45,c_47])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1722,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6977,plain,
    ( k5_relat_1(sK2,sK3) = X0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6966,c_1722])).

cnf(c_9539,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5237,c_6977])).

cnf(c_9543,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(superposition,[status(thm)],[c_1721,c_9539])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1719,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5239,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK2,sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5235,c_1719])).

cnf(c_6828,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5239,c_42,c_44,c_45,c_47])).

cnf(c_9571,plain,
    ( v1_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9543,c_6828])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1714,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6023,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1714])).

cnf(c_6250,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6023,c_42,c_43,c_44])).

cnf(c_6251,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6250])).

cnf(c_6254,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5235,c_6251])).

cnf(c_6319,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6254,c_45,c_46,c_47,c_32,c_122,c_126,c_1844])).

cnf(c_9572,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9543,c_6319])).

cnf(c_3,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1702,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1727,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4300,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1702,c_1727])).

cnf(c_3226,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_1710])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1800,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1968,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1800])).

cnf(c_2107,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1968])).

cnf(c_3410,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3226,c_41,c_40,c_39,c_35,c_33,c_31,c_2107])).

cnf(c_4301,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4300,c_3410])).

cnf(c_1725,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2557,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1704,c_1725])).

cnf(c_4878,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4301,c_49,c_2557])).

cnf(c_4890,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4878,c_3])).

cnf(c_4891,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_4890,c_3])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1729,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5152,plain,
    ( k2_relat_1(X0) != sK0
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4891,c_1729])).

cnf(c_11268,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | k2_relat_1(X0) != sK0
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5152,c_42,c_2557])).

cnf(c_11269,plain,
    ( k2_relat_1(X0) != sK0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11268])).

cnf(c_11274,plain,
    ( sK0 != X0
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
    | v2_funct_1(k6_partfun1(X0)) = iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_11269])).

cnf(c_2555,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_1725])).

cnf(c_11317,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top
    | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | sK0 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11274,c_2555])).

cnf(c_11318,plain,
    ( sK0 != X0
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
    | v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_11317])).

cnf(c_11323,plain,
    ( v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2)) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_11318])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1732,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1731,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3351,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1731])).

cnf(c_3478,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2557,c_3351])).

cnf(c_4880,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_4878,c_3478])).

cnf(c_11324,plain,
    ( v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11323,c_4880])).

cnf(c_33850,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8575,c_42,c_43,c_44,c_45,c_46,c_47,c_49,c_32,c_122,c_126,c_1844,c_2711,c_3227,c_5237,c_7352,c_9571,c_9572,c_11324])).

cnf(c_11461,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11324,c_49,c_9571])).

cnf(c_11467,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11461,c_9572])).

cnf(c_1705,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4299,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1727])).

cnf(c_1865,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2183,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1865])).

cnf(c_2184,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2183])).

cnf(c_4894,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4299,c_47,c_2184])).

cnf(c_4895,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4894])).

cnf(c_11471,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(superposition,[status(thm)],[c_11467,c_4895])).

cnf(c_33852,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_33850,c_11471])).

cnf(c_52956,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_33852,c_3])).

cnf(c_52965,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_52956,c_3])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1726,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9580,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9543,c_1726])).

cnf(c_2789,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1704,c_1724])).

cnf(c_2790,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2789,c_35])).

cnf(c_9581,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9580,c_2790,c_4891])).

cnf(c_9582,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9581])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f98])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52965,c_9582,c_2557,c_2184,c_30,c_49,c_47,c_45,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.55/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.55/2.49  
% 15.55/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.55/2.49  
% 15.55/2.49  ------  iProver source info
% 15.55/2.49  
% 15.55/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.55/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.55/2.49  git: non_committed_changes: false
% 15.55/2.49  git: last_make_outside_of_git: false
% 15.55/2.49  
% 15.55/2.49  ------ 
% 15.55/2.49  
% 15.55/2.49  ------ Input Options
% 15.55/2.49  
% 15.55/2.49  --out_options                           all
% 15.55/2.49  --tptp_safe_out                         true
% 15.55/2.49  --problem_path                          ""
% 15.55/2.49  --include_path                          ""
% 15.55/2.49  --clausifier                            res/vclausify_rel
% 15.55/2.49  --clausifier_options                    ""
% 15.55/2.49  --stdin                                 false
% 15.55/2.49  --stats_out                             all
% 15.55/2.49  
% 15.55/2.49  ------ General Options
% 15.55/2.49  
% 15.55/2.49  --fof                                   false
% 15.55/2.49  --time_out_real                         305.
% 15.55/2.49  --time_out_virtual                      -1.
% 15.55/2.49  --symbol_type_check                     false
% 15.55/2.49  --clausify_out                          false
% 15.55/2.49  --sig_cnt_out                           false
% 15.55/2.49  --trig_cnt_out                          false
% 15.55/2.49  --trig_cnt_out_tolerance                1.
% 15.55/2.49  --trig_cnt_out_sk_spl                   false
% 15.55/2.49  --abstr_cl_out                          false
% 15.55/2.49  
% 15.55/2.49  ------ Global Options
% 15.55/2.49  
% 15.55/2.49  --schedule                              default
% 15.55/2.49  --add_important_lit                     false
% 15.55/2.49  --prop_solver_per_cl                    1000
% 15.55/2.49  --min_unsat_core                        false
% 15.55/2.49  --soft_assumptions                      false
% 15.55/2.49  --soft_lemma_size                       3
% 15.55/2.49  --prop_impl_unit_size                   0
% 15.55/2.49  --prop_impl_unit                        []
% 15.55/2.49  --share_sel_clauses                     true
% 15.55/2.49  --reset_solvers                         false
% 15.55/2.49  --bc_imp_inh                            [conj_cone]
% 15.55/2.49  --conj_cone_tolerance                   3.
% 15.55/2.49  --extra_neg_conj                        none
% 15.55/2.49  --large_theory_mode                     true
% 15.55/2.49  --prolific_symb_bound                   200
% 15.55/2.49  --lt_threshold                          2000
% 15.55/2.49  --clause_weak_htbl                      true
% 15.55/2.49  --gc_record_bc_elim                     false
% 15.55/2.49  
% 15.55/2.49  ------ Preprocessing Options
% 15.55/2.49  
% 15.55/2.49  --preprocessing_flag                    true
% 15.55/2.49  --time_out_prep_mult                    0.1
% 15.55/2.49  --splitting_mode                        input
% 15.55/2.49  --splitting_grd                         true
% 15.55/2.49  --splitting_cvd                         false
% 15.55/2.49  --splitting_cvd_svl                     false
% 15.55/2.49  --splitting_nvd                         32
% 15.55/2.49  --sub_typing                            true
% 15.55/2.49  --prep_gs_sim                           true
% 15.55/2.49  --prep_unflatten                        true
% 15.55/2.49  --prep_res_sim                          true
% 15.55/2.49  --prep_upred                            true
% 15.55/2.49  --prep_sem_filter                       exhaustive
% 15.55/2.49  --prep_sem_filter_out                   false
% 15.55/2.49  --pred_elim                             true
% 15.55/2.49  --res_sim_input                         true
% 15.55/2.49  --eq_ax_congr_red                       true
% 15.55/2.49  --pure_diseq_elim                       true
% 15.55/2.49  --brand_transform                       false
% 15.55/2.49  --non_eq_to_eq                          false
% 15.55/2.49  --prep_def_merge                        true
% 15.55/2.49  --prep_def_merge_prop_impl              false
% 15.55/2.49  --prep_def_merge_mbd                    true
% 15.55/2.49  --prep_def_merge_tr_red                 false
% 15.55/2.49  --prep_def_merge_tr_cl                  false
% 15.55/2.49  --smt_preprocessing                     true
% 15.55/2.49  --smt_ac_axioms                         fast
% 15.55/2.49  --preprocessed_out                      false
% 15.55/2.49  --preprocessed_stats                    false
% 15.55/2.49  
% 15.55/2.49  ------ Abstraction refinement Options
% 15.55/2.49  
% 15.55/2.49  --abstr_ref                             []
% 15.55/2.49  --abstr_ref_prep                        false
% 15.55/2.49  --abstr_ref_until_sat                   false
% 15.55/2.49  --abstr_ref_sig_restrict                funpre
% 15.55/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.55/2.49  --abstr_ref_under                       []
% 15.55/2.49  
% 15.55/2.49  ------ SAT Options
% 15.55/2.49  
% 15.55/2.49  --sat_mode                              false
% 15.55/2.49  --sat_fm_restart_options                ""
% 15.55/2.49  --sat_gr_def                            false
% 15.55/2.49  --sat_epr_types                         true
% 15.55/2.49  --sat_non_cyclic_types                  false
% 15.55/2.49  --sat_finite_models                     false
% 15.55/2.49  --sat_fm_lemmas                         false
% 15.55/2.49  --sat_fm_prep                           false
% 15.55/2.49  --sat_fm_uc_incr                        true
% 15.55/2.49  --sat_out_model                         small
% 15.55/2.49  --sat_out_clauses                       false
% 15.55/2.49  
% 15.55/2.49  ------ QBF Options
% 15.55/2.49  
% 15.55/2.49  --qbf_mode                              false
% 15.55/2.49  --qbf_elim_univ                         false
% 15.55/2.49  --qbf_dom_inst                          none
% 15.55/2.49  --qbf_dom_pre_inst                      false
% 15.55/2.49  --qbf_sk_in                             false
% 15.55/2.49  --qbf_pred_elim                         true
% 15.55/2.49  --qbf_split                             512
% 15.55/2.49  
% 15.55/2.49  ------ BMC1 Options
% 15.55/2.49  
% 15.55/2.49  --bmc1_incremental                      false
% 15.55/2.49  --bmc1_axioms                           reachable_all
% 15.55/2.49  --bmc1_min_bound                        0
% 15.55/2.49  --bmc1_max_bound                        -1
% 15.55/2.49  --bmc1_max_bound_default                -1
% 15.55/2.49  --bmc1_symbol_reachability              true
% 15.55/2.49  --bmc1_property_lemmas                  false
% 15.55/2.49  --bmc1_k_induction                      false
% 15.55/2.49  --bmc1_non_equiv_states                 false
% 15.55/2.49  --bmc1_deadlock                         false
% 15.55/2.49  --bmc1_ucm                              false
% 15.55/2.49  --bmc1_add_unsat_core                   none
% 15.55/2.49  --bmc1_unsat_core_children              false
% 15.55/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.55/2.49  --bmc1_out_stat                         full
% 15.55/2.49  --bmc1_ground_init                      false
% 15.55/2.49  --bmc1_pre_inst_next_state              false
% 15.55/2.49  --bmc1_pre_inst_state                   false
% 15.55/2.49  --bmc1_pre_inst_reach_state             false
% 15.55/2.49  --bmc1_out_unsat_core                   false
% 15.55/2.49  --bmc1_aig_witness_out                  false
% 15.55/2.49  --bmc1_verbose                          false
% 15.55/2.49  --bmc1_dump_clauses_tptp                false
% 15.55/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.55/2.49  --bmc1_dump_file                        -
% 15.55/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.55/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.55/2.49  --bmc1_ucm_extend_mode                  1
% 15.55/2.49  --bmc1_ucm_init_mode                    2
% 15.55/2.49  --bmc1_ucm_cone_mode                    none
% 15.55/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.55/2.49  --bmc1_ucm_relax_model                  4
% 15.55/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.55/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.55/2.49  --bmc1_ucm_layered_model                none
% 15.55/2.49  --bmc1_ucm_max_lemma_size               10
% 15.55/2.49  
% 15.55/2.49  ------ AIG Options
% 15.55/2.49  
% 15.55/2.49  --aig_mode                              false
% 15.55/2.49  
% 15.55/2.49  ------ Instantiation Options
% 15.55/2.49  
% 15.55/2.49  --instantiation_flag                    true
% 15.55/2.49  --inst_sos_flag                         true
% 15.55/2.49  --inst_sos_phase                        true
% 15.55/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.55/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.55/2.49  --inst_lit_sel_side                     num_symb
% 15.55/2.49  --inst_solver_per_active                1400
% 15.55/2.49  --inst_solver_calls_frac                1.
% 15.55/2.49  --inst_passive_queue_type               priority_queues
% 15.55/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.55/2.49  --inst_passive_queues_freq              [25;2]
% 15.55/2.49  --inst_dismatching                      true
% 15.55/2.49  --inst_eager_unprocessed_to_passive     true
% 15.55/2.49  --inst_prop_sim_given                   true
% 15.55/2.49  --inst_prop_sim_new                     false
% 15.55/2.49  --inst_subs_new                         false
% 15.55/2.49  --inst_eq_res_simp                      false
% 15.55/2.49  --inst_subs_given                       false
% 15.55/2.49  --inst_orphan_elimination               true
% 15.55/2.49  --inst_learning_loop_flag               true
% 15.55/2.49  --inst_learning_start                   3000
% 15.55/2.49  --inst_learning_factor                  2
% 15.55/2.49  --inst_start_prop_sim_after_learn       3
% 15.55/2.49  --inst_sel_renew                        solver
% 15.55/2.49  --inst_lit_activity_flag                true
% 15.55/2.49  --inst_restr_to_given                   false
% 15.55/2.49  --inst_activity_threshold               500
% 15.55/2.49  --inst_out_proof                        true
% 15.55/2.49  
% 15.55/2.49  ------ Resolution Options
% 15.55/2.49  
% 15.55/2.49  --resolution_flag                       true
% 15.55/2.49  --res_lit_sel                           adaptive
% 15.55/2.49  --res_lit_sel_side                      none
% 15.55/2.49  --res_ordering                          kbo
% 15.55/2.49  --res_to_prop_solver                    active
% 15.55/2.49  --res_prop_simpl_new                    false
% 15.55/2.49  --res_prop_simpl_given                  true
% 15.55/2.49  --res_passive_queue_type                priority_queues
% 15.55/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.55/2.49  --res_passive_queues_freq               [15;5]
% 15.55/2.49  --res_forward_subs                      full
% 15.55/2.49  --res_backward_subs                     full
% 15.55/2.49  --res_forward_subs_resolution           true
% 15.55/2.49  --res_backward_subs_resolution          true
% 15.55/2.49  --res_orphan_elimination                true
% 15.55/2.49  --res_time_limit                        2.
% 15.55/2.49  --res_out_proof                         true
% 15.55/2.49  
% 15.55/2.49  ------ Superposition Options
% 15.55/2.49  
% 15.55/2.49  --superposition_flag                    true
% 15.55/2.49  --sup_passive_queue_type                priority_queues
% 15.55/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.55/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.55/2.49  --demod_completeness_check              fast
% 15.55/2.49  --demod_use_ground                      true
% 15.55/2.49  --sup_to_prop_solver                    passive
% 15.55/2.49  --sup_prop_simpl_new                    true
% 15.55/2.49  --sup_prop_simpl_given                  true
% 15.55/2.49  --sup_fun_splitting                     true
% 15.55/2.49  --sup_smt_interval                      50000
% 15.55/2.49  
% 15.55/2.49  ------ Superposition Simplification Setup
% 15.55/2.49  
% 15.55/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.55/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.55/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.55/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.55/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.55/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.55/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.55/2.49  --sup_immed_triv                        [TrivRules]
% 15.55/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.55/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.55/2.49  --sup_immed_bw_main                     []
% 15.55/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.55/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.55/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.55/2.49  --sup_input_bw                          []
% 15.55/2.49  
% 15.55/2.49  ------ Combination Options
% 15.55/2.49  
% 15.55/2.49  --comb_res_mult                         3
% 15.55/2.49  --comb_sup_mult                         2
% 15.55/2.49  --comb_inst_mult                        10
% 15.55/2.49  
% 15.55/2.49  ------ Debug Options
% 15.55/2.49  
% 15.55/2.49  --dbg_backtrace                         false
% 15.55/2.49  --dbg_dump_prop_clauses                 false
% 15.55/2.49  --dbg_dump_prop_clauses_file            -
% 15.55/2.49  --dbg_out_stat                          false
% 15.55/2.49  ------ Parsing...
% 15.55/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.55/2.49  
% 15.55/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.55/2.49  
% 15.55/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.55/2.49  
% 15.55/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.55/2.49  ------ Proving...
% 15.55/2.49  ------ Problem Properties 
% 15.55/2.49  
% 15.55/2.49  
% 15.55/2.49  clauses                                 40
% 15.55/2.49  conjectures                             12
% 15.55/2.49  EPR                                     9
% 15.55/2.49  Horn                                    36
% 15.55/2.49  unary                                   16
% 15.55/2.49  binary                                  4
% 15.55/2.49  lits                                    150
% 15.55/2.49  lits eq                                 31
% 15.55/2.49  fd_pure                                 0
% 15.55/2.49  fd_pseudo                               0
% 15.55/2.49  fd_cond                                 4
% 15.55/2.49  fd_pseudo_cond                          4
% 15.55/2.49  AC symbols                              0
% 15.55/2.49  
% 15.55/2.49  ------ Schedule dynamic 5 is on 
% 15.55/2.49  
% 15.55/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.55/2.49  
% 15.55/2.49  
% 15.55/2.49  ------ 
% 15.55/2.49  Current options:
% 15.55/2.49  ------ 
% 15.55/2.49  
% 15.55/2.49  ------ Input Options
% 15.55/2.49  
% 15.55/2.49  --out_options                           all
% 15.55/2.49  --tptp_safe_out                         true
% 15.55/2.49  --problem_path                          ""
% 15.55/2.49  --include_path                          ""
% 15.55/2.49  --clausifier                            res/vclausify_rel
% 15.55/2.49  --clausifier_options                    ""
% 15.55/2.49  --stdin                                 false
% 15.55/2.49  --stats_out                             all
% 15.55/2.49  
% 15.55/2.49  ------ General Options
% 15.55/2.49  
% 15.55/2.49  --fof                                   false
% 15.55/2.49  --time_out_real                         305.
% 15.55/2.49  --time_out_virtual                      -1.
% 15.55/2.49  --symbol_type_check                     false
% 15.55/2.49  --clausify_out                          false
% 15.55/2.49  --sig_cnt_out                           false
% 15.55/2.49  --trig_cnt_out                          false
% 15.55/2.49  --trig_cnt_out_tolerance                1.
% 15.55/2.49  --trig_cnt_out_sk_spl                   false
% 15.55/2.49  --abstr_cl_out                          false
% 15.55/2.49  
% 15.55/2.49  ------ Global Options
% 15.55/2.49  
% 15.55/2.49  --schedule                              default
% 15.55/2.49  --add_important_lit                     false
% 15.55/2.49  --prop_solver_per_cl                    1000
% 15.55/2.49  --min_unsat_core                        false
% 15.55/2.49  --soft_assumptions                      false
% 15.55/2.49  --soft_lemma_size                       3
% 15.55/2.49  --prop_impl_unit_size                   0
% 15.55/2.49  --prop_impl_unit                        []
% 15.55/2.49  --share_sel_clauses                     true
% 15.55/2.49  --reset_solvers                         false
% 15.55/2.49  --bc_imp_inh                            [conj_cone]
% 15.55/2.49  --conj_cone_tolerance                   3.
% 15.55/2.49  --extra_neg_conj                        none
% 15.55/2.49  --large_theory_mode                     true
% 15.55/2.49  --prolific_symb_bound                   200
% 15.55/2.49  --lt_threshold                          2000
% 15.55/2.49  --clause_weak_htbl                      true
% 15.55/2.49  --gc_record_bc_elim                     false
% 15.55/2.49  
% 15.55/2.49  ------ Preprocessing Options
% 15.55/2.49  
% 15.55/2.49  --preprocessing_flag                    true
% 15.55/2.49  --time_out_prep_mult                    0.1
% 15.55/2.49  --splitting_mode                        input
% 15.55/2.49  --splitting_grd                         true
% 15.55/2.49  --splitting_cvd                         false
% 15.55/2.49  --splitting_cvd_svl                     false
% 15.55/2.49  --splitting_nvd                         32
% 15.55/2.49  --sub_typing                            true
% 15.55/2.49  --prep_gs_sim                           true
% 15.55/2.49  --prep_unflatten                        true
% 15.55/2.49  --prep_res_sim                          true
% 15.55/2.49  --prep_upred                            true
% 15.55/2.49  --prep_sem_filter                       exhaustive
% 15.55/2.49  --prep_sem_filter_out                   false
% 15.55/2.49  --pred_elim                             true
% 15.55/2.49  --res_sim_input                         true
% 15.55/2.49  --eq_ax_congr_red                       true
% 15.55/2.49  --pure_diseq_elim                       true
% 15.55/2.49  --brand_transform                       false
% 15.55/2.49  --non_eq_to_eq                          false
% 15.55/2.49  --prep_def_merge                        true
% 15.55/2.49  --prep_def_merge_prop_impl              false
% 15.55/2.49  --prep_def_merge_mbd                    true
% 15.55/2.49  --prep_def_merge_tr_red                 false
% 15.55/2.49  --prep_def_merge_tr_cl                  false
% 15.55/2.49  --smt_preprocessing                     true
% 15.55/2.49  --smt_ac_axioms                         fast
% 15.55/2.49  --preprocessed_out                      false
% 15.55/2.49  --preprocessed_stats                    false
% 15.55/2.49  
% 15.55/2.49  ------ Abstraction refinement Options
% 15.55/2.49  
% 15.55/2.49  --abstr_ref                             []
% 15.55/2.49  --abstr_ref_prep                        false
% 15.55/2.49  --abstr_ref_until_sat                   false
% 15.55/2.49  --abstr_ref_sig_restrict                funpre
% 15.55/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.55/2.49  --abstr_ref_under                       []
% 15.55/2.49  
% 15.55/2.49  ------ SAT Options
% 15.55/2.49  
% 15.55/2.49  --sat_mode                              false
% 15.55/2.49  --sat_fm_restart_options                ""
% 15.55/2.49  --sat_gr_def                            false
% 15.55/2.49  --sat_epr_types                         true
% 15.55/2.49  --sat_non_cyclic_types                  false
% 15.55/2.49  --sat_finite_models                     false
% 15.55/2.49  --sat_fm_lemmas                         false
% 15.55/2.49  --sat_fm_prep                           false
% 15.55/2.49  --sat_fm_uc_incr                        true
% 15.55/2.49  --sat_out_model                         small
% 15.55/2.49  --sat_out_clauses                       false
% 15.55/2.49  
% 15.55/2.49  ------ QBF Options
% 15.55/2.49  
% 15.55/2.49  --qbf_mode                              false
% 15.55/2.49  --qbf_elim_univ                         false
% 15.55/2.49  --qbf_dom_inst                          none
% 15.55/2.49  --qbf_dom_pre_inst                      false
% 15.55/2.49  --qbf_sk_in                             false
% 15.55/2.49  --qbf_pred_elim                         true
% 15.55/2.49  --qbf_split                             512
% 15.55/2.49  
% 15.55/2.49  ------ BMC1 Options
% 15.55/2.49  
% 15.55/2.49  --bmc1_incremental                      false
% 15.55/2.49  --bmc1_axioms                           reachable_all
% 15.55/2.49  --bmc1_min_bound                        0
% 15.55/2.49  --bmc1_max_bound                        -1
% 15.55/2.49  --bmc1_max_bound_default                -1
% 15.55/2.49  --bmc1_symbol_reachability              true
% 15.55/2.49  --bmc1_property_lemmas                  false
% 15.55/2.49  --bmc1_k_induction                      false
% 15.55/2.49  --bmc1_non_equiv_states                 false
% 15.55/2.49  --bmc1_deadlock                         false
% 15.55/2.49  --bmc1_ucm                              false
% 15.55/2.49  --bmc1_add_unsat_core                   none
% 15.55/2.49  --bmc1_unsat_core_children              false
% 15.55/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.55/2.49  --bmc1_out_stat                         full
% 15.55/2.49  --bmc1_ground_init                      false
% 15.55/2.49  --bmc1_pre_inst_next_state              false
% 15.55/2.49  --bmc1_pre_inst_state                   false
% 15.55/2.49  --bmc1_pre_inst_reach_state             false
% 15.55/2.49  --bmc1_out_unsat_core                   false
% 15.55/2.49  --bmc1_aig_witness_out                  false
% 15.55/2.49  --bmc1_verbose                          false
% 15.55/2.49  --bmc1_dump_clauses_tptp                false
% 15.55/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.55/2.49  --bmc1_dump_file                        -
% 15.55/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.55/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.55/2.49  --bmc1_ucm_extend_mode                  1
% 15.55/2.49  --bmc1_ucm_init_mode                    2
% 15.55/2.49  --bmc1_ucm_cone_mode                    none
% 15.55/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.55/2.49  --bmc1_ucm_relax_model                  4
% 15.55/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.55/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.55/2.49  --bmc1_ucm_layered_model                none
% 15.55/2.49  --bmc1_ucm_max_lemma_size               10
% 15.55/2.49  
% 15.55/2.49  ------ AIG Options
% 15.55/2.49  
% 15.55/2.49  --aig_mode                              false
% 15.55/2.49  
% 15.55/2.49  ------ Instantiation Options
% 15.55/2.49  
% 15.55/2.49  --instantiation_flag                    true
% 15.55/2.49  --inst_sos_flag                         true
% 15.55/2.49  --inst_sos_phase                        true
% 15.55/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.55/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.55/2.49  --inst_lit_sel_side                     none
% 15.55/2.49  --inst_solver_per_active                1400
% 15.55/2.49  --inst_solver_calls_frac                1.
% 15.55/2.49  --inst_passive_queue_type               priority_queues
% 15.55/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.55/2.49  --inst_passive_queues_freq              [25;2]
% 15.55/2.49  --inst_dismatching                      true
% 15.55/2.49  --inst_eager_unprocessed_to_passive     true
% 15.55/2.49  --inst_prop_sim_given                   true
% 15.55/2.49  --inst_prop_sim_new                     false
% 15.55/2.49  --inst_subs_new                         false
% 15.55/2.49  --inst_eq_res_simp                      false
% 15.55/2.49  --inst_subs_given                       false
% 15.55/2.49  --inst_orphan_elimination               true
% 15.55/2.49  --inst_learning_loop_flag               true
% 15.55/2.49  --inst_learning_start                   3000
% 15.55/2.49  --inst_learning_factor                  2
% 15.55/2.49  --inst_start_prop_sim_after_learn       3
% 15.55/2.49  --inst_sel_renew                        solver
% 15.55/2.49  --inst_lit_activity_flag                true
% 15.55/2.49  --inst_restr_to_given                   false
% 15.55/2.49  --inst_activity_threshold               500
% 15.55/2.49  --inst_out_proof                        true
% 15.55/2.49  
% 15.55/2.49  ------ Resolution Options
% 15.55/2.49  
% 15.55/2.49  --resolution_flag                       false
% 15.55/2.49  --res_lit_sel                           adaptive
% 15.55/2.49  --res_lit_sel_side                      none
% 15.55/2.49  --res_ordering                          kbo
% 15.55/2.49  --res_to_prop_solver                    active
% 15.55/2.49  --res_prop_simpl_new                    false
% 15.55/2.49  --res_prop_simpl_given                  true
% 15.55/2.49  --res_passive_queue_type                priority_queues
% 15.55/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.55/2.49  --res_passive_queues_freq               [15;5]
% 15.55/2.49  --res_forward_subs                      full
% 15.55/2.49  --res_backward_subs                     full
% 15.55/2.49  --res_forward_subs_resolution           true
% 15.55/2.49  --res_backward_subs_resolution          true
% 15.55/2.49  --res_orphan_elimination                true
% 15.55/2.49  --res_time_limit                        2.
% 15.55/2.49  --res_out_proof                         true
% 15.55/2.49  
% 15.55/2.49  ------ Superposition Options
% 15.55/2.49  
% 15.55/2.49  --superposition_flag                    true
% 15.55/2.49  --sup_passive_queue_type                priority_queues
% 15.55/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.55/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.55/2.49  --demod_completeness_check              fast
% 15.55/2.49  --demod_use_ground                      true
% 15.55/2.49  --sup_to_prop_solver                    passive
% 15.55/2.49  --sup_prop_simpl_new                    true
% 15.55/2.49  --sup_prop_simpl_given                  true
% 15.55/2.49  --sup_fun_splitting                     true
% 15.55/2.49  --sup_smt_interval                      50000
% 15.55/2.49  
% 15.55/2.49  ------ Superposition Simplification Setup
% 15.55/2.49  
% 15.55/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.55/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.55/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.55/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.55/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.55/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.55/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.55/2.49  --sup_immed_triv                        [TrivRules]
% 15.55/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.55/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.55/2.49  --sup_immed_bw_main                     []
% 15.55/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.55/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.55/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.55/2.49  --sup_input_bw                          []
% 15.55/2.49  
% 15.55/2.49  ------ Combination Options
% 15.55/2.49  
% 15.55/2.49  --comb_res_mult                         3
% 15.55/2.49  --comb_sup_mult                         2
% 15.55/2.49  --comb_inst_mult                        10
% 15.55/2.49  
% 15.55/2.49  ------ Debug Options
% 15.55/2.49  
% 15.55/2.49  --dbg_backtrace                         false
% 15.55/2.49  --dbg_dump_prop_clauses                 false
% 15.55/2.49  --dbg_dump_prop_clauses_file            -
% 15.55/2.49  --dbg_out_stat                          false
% 15.55/2.49  
% 15.55/2.49  
% 15.55/2.49  
% 15.55/2.49  
% 15.55/2.49  ------ Proving...
% 15.55/2.49  
% 15.55/2.49  
% 15.55/2.49  % SZS status Theorem for theBenchmark.p
% 15.55/2.49  
% 15.55/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.55/2.49  
% 15.55/2.49  fof(f19,conjecture,(
% 15.55/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f20,negated_conjecture,(
% 15.55/2.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.55/2.49    inference(negated_conjecture,[],[f19])).
% 15.55/2.49  
% 15.55/2.49  fof(f47,plain,(
% 15.55/2.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.55/2.49    inference(ennf_transformation,[],[f20])).
% 15.55/2.49  
% 15.55/2.49  fof(f48,plain,(
% 15.55/2.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.55/2.49    inference(flattening,[],[f47])).
% 15.55/2.49  
% 15.55/2.49  fof(f54,plain,(
% 15.55/2.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 15.55/2.49    introduced(choice_axiom,[])).
% 15.55/2.49  
% 15.55/2.49  fof(f53,plain,(
% 15.55/2.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 15.55/2.49    introduced(choice_axiom,[])).
% 15.55/2.49  
% 15.55/2.49  fof(f55,plain,(
% 15.55/2.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 15.55/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f54,f53])).
% 15.55/2.49  
% 15.55/2.49  fof(f89,plain,(
% 15.55/2.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f92,plain,(
% 15.55/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f14,axiom,(
% 15.55/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f39,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.55/2.49    inference(ennf_transformation,[],[f14])).
% 15.55/2.49  
% 15.55/2.49  fof(f40,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.55/2.49    inference(flattening,[],[f39])).
% 15.55/2.49  
% 15.55/2.49  fof(f77,plain,(
% 15.55/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f40])).
% 15.55/2.49  
% 15.55/2.49  fof(f90,plain,(
% 15.55/2.49    v1_funct_1(sK3)),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f87,plain,(
% 15.55/2.49    v1_funct_1(sK2)),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f16,axiom,(
% 15.55/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f41,plain,(
% 15.55/2.49    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.55/2.49    inference(ennf_transformation,[],[f16])).
% 15.55/2.49  
% 15.55/2.49  fof(f42,plain,(
% 15.55/2.49    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.55/2.49    inference(flattening,[],[f41])).
% 15.55/2.49  
% 15.55/2.49  fof(f80,plain,(
% 15.55/2.49    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f42])).
% 15.55/2.49  
% 15.55/2.49  fof(f88,plain,(
% 15.55/2.49    v1_funct_2(sK2,sK0,sK1)),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f91,plain,(
% 15.55/2.49    v1_funct_2(sK3,sK1,sK0)),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f94,plain,(
% 15.55/2.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f8,axiom,(
% 15.55/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f21,plain,(
% 15.55/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 15.55/2.49    inference(pure_predicate_removal,[],[f8])).
% 15.55/2.49  
% 15.55/2.49  fof(f31,plain,(
% 15.55/2.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.55/2.49    inference(ennf_transformation,[],[f21])).
% 15.55/2.49  
% 15.55/2.49  fof(f68,plain,(
% 15.55/2.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.55/2.49    inference(cnf_transformation,[],[f31])).
% 15.55/2.49  
% 15.55/2.49  fof(f12,axiom,(
% 15.55/2.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f35,plain,(
% 15.55/2.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.55/2.49    inference(ennf_transformation,[],[f12])).
% 15.55/2.49  
% 15.55/2.49  fof(f36,plain,(
% 15.55/2.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.55/2.49    inference(flattening,[],[f35])).
% 15.55/2.49  
% 15.55/2.49  fof(f52,plain,(
% 15.55/2.49    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.55/2.49    inference(nnf_transformation,[],[f36])).
% 15.55/2.49  
% 15.55/2.49  fof(f73,plain,(
% 15.55/2.49    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f52])).
% 15.55/2.49  
% 15.55/2.49  fof(f7,axiom,(
% 15.55/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f30,plain,(
% 15.55/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.55/2.49    inference(ennf_transformation,[],[f7])).
% 15.55/2.49  
% 15.55/2.49  fof(f67,plain,(
% 15.55/2.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.55/2.49    inference(cnf_transformation,[],[f30])).
% 15.55/2.49  
% 15.55/2.49  fof(f9,axiom,(
% 15.55/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f32,plain,(
% 15.55/2.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.55/2.49    inference(ennf_transformation,[],[f9])).
% 15.55/2.49  
% 15.55/2.49  fof(f69,plain,(
% 15.55/2.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.55/2.49    inference(cnf_transformation,[],[f32])).
% 15.55/2.49  
% 15.55/2.49  fof(f18,axiom,(
% 15.55/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f45,plain,(
% 15.55/2.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.55/2.49    inference(ennf_transformation,[],[f18])).
% 15.55/2.49  
% 15.55/2.49  fof(f46,plain,(
% 15.55/2.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.55/2.49    inference(flattening,[],[f45])).
% 15.55/2.49  
% 15.55/2.49  fof(f85,plain,(
% 15.55/2.49    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f46])).
% 15.55/2.49  
% 15.55/2.49  fof(f95,plain,(
% 15.55/2.49    v2_funct_1(sK2)),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f96,plain,(
% 15.55/2.49    k1_xboole_0 != sK0),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f1,axiom,(
% 15.55/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f49,plain,(
% 15.55/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.55/2.49    inference(nnf_transformation,[],[f1])).
% 15.55/2.49  
% 15.55/2.49  fof(f50,plain,(
% 15.55/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.55/2.49    inference(flattening,[],[f49])).
% 15.55/2.49  
% 15.55/2.49  fof(f56,plain,(
% 15.55/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.55/2.49    inference(cnf_transformation,[],[f50])).
% 15.55/2.49  
% 15.55/2.49  fof(f107,plain,(
% 15.55/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.55/2.49    inference(equality_resolution,[],[f56])).
% 15.55/2.49  
% 15.55/2.49  fof(f58,plain,(
% 15.55/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f50])).
% 15.55/2.49  
% 15.55/2.49  fof(f11,axiom,(
% 15.55/2.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f72,plain,(
% 15.55/2.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.55/2.49    inference(cnf_transformation,[],[f11])).
% 15.55/2.49  
% 15.55/2.49  fof(f15,axiom,(
% 15.55/2.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f78,plain,(
% 15.55/2.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f15])).
% 15.55/2.49  
% 15.55/2.49  fof(f105,plain,(
% 15.55/2.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.55/2.49    inference(definition_unfolding,[],[f72,f78])).
% 15.55/2.49  
% 15.55/2.49  fof(f13,axiom,(
% 15.55/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f37,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.55/2.49    inference(ennf_transformation,[],[f13])).
% 15.55/2.49  
% 15.55/2.49  fof(f38,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.55/2.49    inference(flattening,[],[f37])).
% 15.55/2.49  
% 15.55/2.49  fof(f76,plain,(
% 15.55/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f38])).
% 15.55/2.49  
% 15.55/2.49  fof(f10,axiom,(
% 15.55/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f33,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.55/2.49    inference(ennf_transformation,[],[f10])).
% 15.55/2.49  
% 15.55/2.49  fof(f34,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.55/2.49    inference(flattening,[],[f33])).
% 15.55/2.49  
% 15.55/2.49  fof(f51,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.55/2.49    inference(nnf_transformation,[],[f34])).
% 15.55/2.49  
% 15.55/2.49  fof(f70,plain,(
% 15.55/2.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.55/2.49    inference(cnf_transformation,[],[f51])).
% 15.55/2.49  
% 15.55/2.49  fof(f75,plain,(
% 15.55/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f38])).
% 15.55/2.49  
% 15.55/2.49  fof(f93,plain,(
% 15.55/2.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f17,axiom,(
% 15.55/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f43,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 15.55/2.49    inference(ennf_transformation,[],[f17])).
% 15.55/2.49  
% 15.55/2.49  fof(f44,plain,(
% 15.55/2.49    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 15.55/2.49    inference(flattening,[],[f43])).
% 15.55/2.49  
% 15.55/2.49  fof(f83,plain,(
% 15.55/2.49    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f44])).
% 15.55/2.49  
% 15.55/2.49  fof(f2,axiom,(
% 15.55/2.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f60,plain,(
% 15.55/2.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 15.55/2.49    inference(cnf_transformation,[],[f2])).
% 15.55/2.49  
% 15.55/2.49  fof(f99,plain,(
% 15.55/2.49    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 15.55/2.49    inference(definition_unfolding,[],[f60,f78])).
% 15.55/2.49  
% 15.55/2.49  fof(f5,axiom,(
% 15.55/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f26,plain,(
% 15.55/2.49    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.55/2.49    inference(ennf_transformation,[],[f5])).
% 15.55/2.49  
% 15.55/2.49  fof(f27,plain,(
% 15.55/2.49    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.55/2.49    inference(flattening,[],[f26])).
% 15.55/2.49  
% 15.55/2.49  fof(f64,plain,(
% 15.55/2.49    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f27])).
% 15.55/2.49  
% 15.55/2.49  fof(f103,plain,(
% 15.55/2.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.55/2.49    inference(definition_unfolding,[],[f64,f78])).
% 15.55/2.49  
% 15.55/2.49  fof(f97,plain,(
% 15.55/2.49    k1_xboole_0 != sK1),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  fof(f4,axiom,(
% 15.55/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f24,plain,(
% 15.55/2.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.55/2.49    inference(ennf_transformation,[],[f4])).
% 15.55/2.49  
% 15.55/2.49  fof(f25,plain,(
% 15.55/2.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.55/2.49    inference(flattening,[],[f24])).
% 15.55/2.49  
% 15.55/2.49  fof(f62,plain,(
% 15.55/2.49    ( ! [X0,X1] : (v2_funct_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f25])).
% 15.55/2.49  
% 15.55/2.49  fof(f57,plain,(
% 15.55/2.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.55/2.49    inference(cnf_transformation,[],[f50])).
% 15.55/2.49  
% 15.55/2.49  fof(f106,plain,(
% 15.55/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.55/2.49    inference(equality_resolution,[],[f57])).
% 15.55/2.49  
% 15.55/2.49  fof(f3,axiom,(
% 15.55/2.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f22,plain,(
% 15.55/2.49    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.55/2.49    inference(ennf_transformation,[],[f3])).
% 15.55/2.49  
% 15.55/2.49  fof(f23,plain,(
% 15.55/2.49    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 15.55/2.49    inference(flattening,[],[f22])).
% 15.55/2.49  
% 15.55/2.49  fof(f61,plain,(
% 15.55/2.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f23])).
% 15.55/2.49  
% 15.55/2.49  fof(f101,plain,(
% 15.55/2.49    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 15.55/2.49    inference(definition_unfolding,[],[f61,f78])).
% 15.55/2.49  
% 15.55/2.49  fof(f6,axiom,(
% 15.55/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 15.55/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.55/2.49  
% 15.55/2.49  fof(f28,plain,(
% 15.55/2.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.55/2.49    inference(ennf_transformation,[],[f6])).
% 15.55/2.49  
% 15.55/2.49  fof(f29,plain,(
% 15.55/2.49    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.55/2.49    inference(flattening,[],[f28])).
% 15.55/2.49  
% 15.55/2.49  fof(f66,plain,(
% 15.55/2.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.55/2.49    inference(cnf_transformation,[],[f29])).
% 15.55/2.49  
% 15.55/2.49  fof(f104,plain,(
% 15.55/2.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.55/2.49    inference(definition_unfolding,[],[f66,f78])).
% 15.55/2.49  
% 15.55/2.49  fof(f98,plain,(
% 15.55/2.49    k2_funct_1(sK2) != sK3),
% 15.55/2.49    inference(cnf_transformation,[],[f55])).
% 15.55/2.49  
% 15.55/2.49  cnf(c_39,negated_conjecture,
% 15.55/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.55/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1704,plain,
% 15.55/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_36,negated_conjecture,
% 15.55/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 15.55/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1707,plain,
% 15.55/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_21,plain,
% 15.55/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.55/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.55/2.49      | ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v1_funct_1(X3)
% 15.55/2.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.55/2.49      inference(cnf_transformation,[],[f77]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1718,plain,
% 15.55/2.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.55/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.55/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.55/2.49      | v1_funct_1(X5) != iProver_top
% 15.55/2.49      | v1_funct_1(X4) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5139,plain,
% 15.55/2.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.55/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.55/2.49      | v1_funct_1(X2) != iProver_top
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1707,c_1718]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_38,negated_conjecture,
% 15.55/2.49      ( v1_funct_1(sK3) ),
% 15.55/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_45,plain,
% 15.55/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5188,plain,
% 15.55/2.49      ( v1_funct_1(X2) != iProver_top
% 15.55/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.55/2.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_5139,c_45]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5189,plain,
% 15.55/2.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.55/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.55/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.55/2.49      inference(renaming,[status(thm)],[c_5188]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5196,plain,
% 15.55/2.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1704,c_5189]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_41,negated_conjecture,
% 15.55/2.49      ( v1_funct_1(sK2) ),
% 15.55/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_42,plain,
% 15.55/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5235,plain,
% 15.55/2.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_5196,c_42]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_22,plain,
% 15.55/2.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 15.55/2.49      | ~ v1_funct_2(X3,X1,X0)
% 15.55/2.49      | ~ v1_funct_2(X2,X0,X1)
% 15.55/2.49      | v2_funct_2(X3,X0)
% 15.55/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.55/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 15.55/2.49      | ~ v1_funct_1(X3)
% 15.55/2.49      | ~ v1_funct_1(X2) ),
% 15.55/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1717,plain,
% 15.55/2.49      ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) != iProver_top
% 15.55/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.55/2.49      | v1_funct_2(X3,X1,X0) != iProver_top
% 15.55/2.49      | v2_funct_2(X3,X0) = iProver_top
% 15.55/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.55/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 15.55/2.49      | v1_funct_1(X2) != iProver_top
% 15.55/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_7352,plain,
% 15.55/2.49      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) != iProver_top
% 15.55/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.55/2.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.55/2.49      | v2_funct_2(sK3,sK0) = iProver_top
% 15.55/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.55/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_5235,c_1717]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_40,negated_conjecture,
% 15.55/2.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 15.55/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_43,plain,
% 15.55/2.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_44,plain,
% 15.55/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_37,negated_conjecture,
% 15.55/2.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 15.55/2.49      inference(cnf_transformation,[],[f91]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_46,plain,
% 15.55/2.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_47,plain,
% 15.55/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_34,negated_conjecture,
% 15.55/2.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 15.55/2.49      inference(cnf_transformation,[],[f94]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1708,plain,
% 15.55/2.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5237,plain,
% 15.55/2.49      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 15.55/2.49      inference(demodulation,[status(thm)],[c_5235,c_1708]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_8498,plain,
% 15.55/2.49      ( v2_funct_2(sK3,sK0) = iProver_top ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_7352,c_42,c_43,c_44,c_45,c_46,c_47,c_5237]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_12,plain,
% 15.55/2.49      ( v5_relat_1(X0,X1)
% 15.55/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 15.55/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_18,plain,
% 15.55/2.49      ( ~ v2_funct_2(X0,X1)
% 15.55/2.49      | ~ v5_relat_1(X0,X1)
% 15.55/2.49      | ~ v1_relat_1(X0)
% 15.55/2.49      | k2_relat_1(X0) = X1 ),
% 15.55/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_400,plain,
% 15.55/2.49      ( ~ v2_funct_2(X0,X1)
% 15.55/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.55/2.49      | ~ v1_relat_1(X0)
% 15.55/2.49      | k2_relat_1(X0) = X1 ),
% 15.55/2.49      inference(resolution,[status(thm)],[c_12,c_18]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11,plain,
% 15.55/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.55/2.49      | v1_relat_1(X0) ),
% 15.55/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_412,plain,
% 15.55/2.49      ( ~ v2_funct_2(X0,X1)
% 15.55/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.55/2.49      | k2_relat_1(X0) = X1 ),
% 15.55/2.49      inference(forward_subsumption_resolution,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_400,c_11]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1701,plain,
% 15.55/2.49      ( k2_relat_1(X0) = X1
% 15.55/2.49      | v2_funct_2(X0,X1) != iProver_top
% 15.55/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2711,plain,
% 15.55/2.49      ( k2_relat_1(sK3) = sK0 | v2_funct_2(sK3,sK0) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1707,c_1701]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_8502,plain,
% 15.55/2.49      ( k2_relat_1(sK3) = sK0 ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_8498,c_2711]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_13,plain,
% 15.55/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.55/2.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.55/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1724,plain,
% 15.55/2.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.55/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2788,plain,
% 15.55/2.49      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1707,c_1724]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_8505,plain,
% 15.55/2.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 15.55/2.49      inference(demodulation,[status(thm)],[c_8502,c_2788]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_29,plain,
% 15.55/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.55/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.55/2.49      | ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v2_funct_1(X0)
% 15.55/2.49      | k2_relset_1(X1,X2,X0) != X2
% 15.55/2.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 15.55/2.49      | k1_xboole_0 = X2 ),
% 15.55/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1710,plain,
% 15.55/2.49      ( k2_relset_1(X0,X1,X2) != X1
% 15.55/2.49      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 15.55/2.49      | k1_xboole_0 = X1
% 15.55/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.55/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.55/2.49      | v1_funct_1(X2) != iProver_top
% 15.55/2.49      | v2_funct_1(X2) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_8575,plain,
% 15.55/2.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 15.55/2.49      | sK0 = k1_xboole_0
% 15.55/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.55/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v2_funct_1(sK3) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_8505,c_1710]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_33,negated_conjecture,
% 15.55/2.49      ( v2_funct_1(sK2) ),
% 15.55/2.49      inference(cnf_transformation,[],[f95]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_49,plain,
% 15.55/2.49      ( v2_funct_1(sK2) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_3227,plain,
% 15.55/2.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 15.55/2.49      | k2_relat_1(sK3) != sK0
% 15.55/2.49      | sK0 = k1_xboole_0
% 15.55/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.55/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v2_funct_1(sK3) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_2788,c_1710]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_32,negated_conjecture,
% 15.55/2.49      ( k1_xboole_0 != sK0 ),
% 15.55/2.49      inference(cnf_transformation,[],[f96]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2,plain,
% 15.55/2.49      ( r1_tarski(X0,X0) ),
% 15.55/2.49      inference(cnf_transformation,[],[f107]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_122,plain,
% 15.55/2.49      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_0,plain,
% 15.55/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.55/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_126,plain,
% 15.55/2.49      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.55/2.49      | k1_xboole_0 = k1_xboole_0 ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1123,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1843,plain,
% 15.55/2.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_1123]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1844,plain,
% 15.55/2.49      ( sK0 != k1_xboole_0
% 15.55/2.49      | k1_xboole_0 = sK0
% 15.55/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_1843]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_3413,plain,
% 15.55/2.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 15.55/2.49      | k2_relat_1(sK3) != sK0
% 15.55/2.49      | v2_funct_1(sK3) != iProver_top ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_3227,c_45,c_46,c_47,c_32,c_122,c_126,c_1844]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_16,plain,
% 15.55/2.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.55/2.49      inference(cnf_transformation,[],[f105]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1721,plain,
% 15.55/2.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_19,plain,
% 15.55/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.55/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.55/2.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.55/2.49      | ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v1_funct_1(X3) ),
% 15.55/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1720,plain,
% 15.55/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.55/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 15.55/2.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 15.55/2.49      | v1_funct_1(X0) != iProver_top
% 15.55/2.49      | v1_funct_1(X3) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5674,plain,
% 15.55/2.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 15.55/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.55/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_5235,c_1720]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_6966,plain,
% 15.55/2.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_5674,c_42,c_44,c_45,c_47]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_15,plain,
% 15.55/2.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.55/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.55/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.55/2.49      | X3 = X2 ),
% 15.55/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1722,plain,
% 15.55/2.49      ( X0 = X1
% 15.55/2.49      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 15.55/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.55/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_6977,plain,
% 15.55/2.49      ( k5_relat_1(sK2,sK3) = X0
% 15.55/2.49      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
% 15.55/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_6966,c_1722]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_9539,plain,
% 15.55/2.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 15.55/2.49      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_5237,c_6977]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_9543,plain,
% 15.55/2.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1721,c_9539]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_20,plain,
% 15.55/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.55/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.55/2.49      | ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v1_funct_1(X3)
% 15.55/2.49      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
% 15.55/2.49      inference(cnf_transformation,[],[f75]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1719,plain,
% 15.55/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.55/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 15.55/2.49      | v1_funct_1(X0) != iProver_top
% 15.55/2.49      | v1_funct_1(X3) != iProver_top
% 15.55/2.49      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5239,plain,
% 15.55/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.55/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.55/2.49      | v1_funct_1(k5_relat_1(sK2,sK3)) = iProver_top
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_5235,c_1719]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_6828,plain,
% 15.55/2.49      ( v1_funct_1(k5_relat_1(sK2,sK3)) = iProver_top ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_5239,c_42,c_44,c_45,c_47]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_9571,plain,
% 15.55/2.49      ( v1_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 15.55/2.49      inference(demodulation,[status(thm)],[c_9543,c_6828]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_35,negated_conjecture,
% 15.55/2.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 15.55/2.49      inference(cnf_transformation,[],[f93]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_25,plain,
% 15.55/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.55/2.49      | ~ v1_funct_2(X3,X4,X1)
% 15.55/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 15.55/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.55/2.49      | ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v1_funct_1(X3)
% 15.55/2.49      | v2_funct_1(X0)
% 15.55/2.49      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 15.55/2.49      | k2_relset_1(X4,X1,X3) != X1
% 15.55/2.49      | k1_xboole_0 = X2 ),
% 15.55/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1714,plain,
% 15.55/2.49      ( k2_relset_1(X0,X1,X2) != X1
% 15.55/2.49      | k1_xboole_0 = X3
% 15.55/2.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 15.55/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.55/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 15.55/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.55/2.49      | v1_funct_1(X4) != iProver_top
% 15.55/2.49      | v1_funct_1(X2) != iProver_top
% 15.55/2.49      | v2_funct_1(X4) = iProver_top
% 15.55/2.49      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_6023,plain,
% 15.55/2.49      ( k1_xboole_0 = X0
% 15.55/2.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.55/2.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.55/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 15.55/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.55/2.49      | v1_funct_1(X1) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top
% 15.55/2.49      | v2_funct_1(X1) = iProver_top
% 15.55/2.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_35,c_1714]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_6250,plain,
% 15.55/2.49      ( v1_funct_1(X1) != iProver_top
% 15.55/2.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.55/2.49      | k1_xboole_0 = X0
% 15.55/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 15.55/2.49      | v2_funct_1(X1) = iProver_top
% 15.55/2.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_6023,c_42,c_43,c_44]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_6251,plain,
% 15.55/2.49      ( k1_xboole_0 = X0
% 15.55/2.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 15.55/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 15.55/2.49      | v1_funct_1(X1) != iProver_top
% 15.55/2.49      | v2_funct_1(X1) = iProver_top
% 15.55/2.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 15.55/2.49      inference(renaming,[status(thm)],[c_6250]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_6254,plain,
% 15.55/2.49      ( sK0 = k1_xboole_0
% 15.55/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 15.55/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 15.55/2.49      | v2_funct_1(sK3) = iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_5235,c_6251]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_6319,plain,
% 15.55/2.49      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 15.55/2.49      | v2_funct_1(sK3) = iProver_top ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_6254,c_45,c_46,c_47,c_32,c_122,c_126,c_1844]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_9572,plain,
% 15.55/2.49      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 15.55/2.49      | v2_funct_1(sK3) = iProver_top ),
% 15.55/2.49      inference(demodulation,[status(thm)],[c_9543,c_6319]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_3,plain,
% 15.55/2.49      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 15.55/2.49      inference(cnf_transformation,[],[f99]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1702,plain,
% 15.55/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_9,plain,
% 15.55/2.49      ( ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v2_funct_1(X0)
% 15.55/2.49      | ~ v1_relat_1(X0)
% 15.55/2.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 15.55/2.49      inference(cnf_transformation,[],[f103]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1727,plain,
% 15.55/2.49      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 15.55/2.49      | v1_funct_1(X0) != iProver_top
% 15.55/2.49      | v2_funct_1(X0) != iProver_top
% 15.55/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4300,plain,
% 15.55/2.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 15.55/2.49      | v2_funct_1(sK2) != iProver_top
% 15.55/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1702,c_1727]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_3226,plain,
% 15.55/2.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 15.55/2.49      | sK1 = k1_xboole_0
% 15.55/2.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.55/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top
% 15.55/2.49      | v2_funct_1(sK2) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_35,c_1710]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_31,negated_conjecture,
% 15.55/2.49      ( k1_xboole_0 != sK1 ),
% 15.55/2.49      inference(cnf_transformation,[],[f97]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1800,plain,
% 15.55/2.49      ( ~ v1_funct_2(X0,X1,sK1)
% 15.55/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 15.55/2.49      | ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v2_funct_1(X0)
% 15.55/2.49      | k2_relset_1(X1,sK1,X0) != sK1
% 15.55/2.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 15.55/2.49      | k1_xboole_0 = sK1 ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_29]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1968,plain,
% 15.55/2.49      ( ~ v1_funct_2(sK2,X0,sK1)
% 15.55/2.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 15.55/2.49      | ~ v1_funct_1(sK2)
% 15.55/2.49      | ~ v2_funct_1(sK2)
% 15.55/2.49      | k2_relset_1(X0,sK1,sK2) != sK1
% 15.55/2.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 15.55/2.49      | k1_xboole_0 = sK1 ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_1800]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2107,plain,
% 15.55/2.49      ( ~ v1_funct_2(sK2,sK0,sK1)
% 15.55/2.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.55/2.49      | ~ v1_funct_1(sK2)
% 15.55/2.49      | ~ v2_funct_1(sK2)
% 15.55/2.49      | k2_relset_1(sK0,sK1,sK2) != sK1
% 15.55/2.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 15.55/2.49      | k1_xboole_0 = sK1 ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_1968]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_3410,plain,
% 15.55/2.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_3226,c_41,c_40,c_39,c_35,c_33,c_31,c_2107]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4301,plain,
% 15.55/2.49      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 15.55/2.49      | v2_funct_1(sK2) != iProver_top
% 15.55/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.55/2.49      inference(light_normalisation,[status(thm)],[c_4300,c_3410]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1725,plain,
% 15.55/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.55/2.49      | v1_relat_1(X0) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2557,plain,
% 15.55/2.49      ( v1_relat_1(sK2) = iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1704,c_1725]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4878,plain,
% 15.55/2.49      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_4301,c_49,c_2557]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4890,plain,
% 15.55/2.49      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_4878,c_3]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4891,plain,
% 15.55/2.49      ( k1_relat_1(sK2) = sK0 ),
% 15.55/2.49      inference(demodulation,[status(thm)],[c_4890,c_3]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_7,plain,
% 15.55/2.49      ( ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v1_funct_1(X1)
% 15.55/2.49      | v2_funct_1(X0)
% 15.55/2.49      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 15.55/2.49      | ~ v1_relat_1(X0)
% 15.55/2.49      | ~ v1_relat_1(X1)
% 15.55/2.49      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 15.55/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1729,plain,
% 15.55/2.49      ( k1_relat_1(X0) != k2_relat_1(X1)
% 15.55/2.49      | v1_funct_1(X1) != iProver_top
% 15.55/2.49      | v1_funct_1(X0) != iProver_top
% 15.55/2.49      | v2_funct_1(X1) = iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 15.55/2.49      | v1_relat_1(X1) != iProver_top
% 15.55/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5152,plain,
% 15.55/2.49      ( k2_relat_1(X0) != sK0
% 15.55/2.49      | v1_funct_1(X0) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top
% 15.55/2.49      | v2_funct_1(X0) = iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
% 15.55/2.49      | v1_relat_1(X0) != iProver_top
% 15.55/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_4891,c_1729]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11268,plain,
% 15.55/2.49      ( v1_relat_1(X0) != iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
% 15.55/2.49      | v2_funct_1(X0) = iProver_top
% 15.55/2.49      | k2_relat_1(X0) != sK0
% 15.55/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_5152,c_42,c_2557]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11269,plain,
% 15.55/2.49      ( k2_relat_1(X0) != sK0
% 15.55/2.49      | v1_funct_1(X0) != iProver_top
% 15.55/2.49      | v2_funct_1(X0) = iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
% 15.55/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.55/2.49      inference(renaming,[status(thm)],[c_11268]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11274,plain,
% 15.55/2.49      ( sK0 != X0
% 15.55/2.49      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
% 15.55/2.49      | v2_funct_1(k6_partfun1(X0)) = iProver_top
% 15.55/2.49      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_3,c_11269]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2555,plain,
% 15.55/2.49      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1721,c_1725]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11317,plain,
% 15.55/2.49      ( v2_funct_1(k6_partfun1(X0)) = iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
% 15.55/2.49      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 15.55/2.49      | sK0 != X0 ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_11274,c_2555]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11318,plain,
% 15.55/2.49      ( sK0 != X0
% 15.55/2.49      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
% 15.55/2.49      | v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 15.55/2.49      inference(renaming,[status(thm)],[c_11317]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11323,plain,
% 15.55/2.49      ( v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 15.55/2.49      | v2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2)) != iProver_top
% 15.55/2.49      | v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 15.55/2.49      inference(equality_resolution,[status(thm)],[c_11318]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1,plain,
% 15.55/2.49      ( r1_tarski(X0,X0) ),
% 15.55/2.49      inference(cnf_transformation,[],[f106]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1732,plain,
% 15.55/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_5,plain,
% 15.55/2.49      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 15.55/2.49      | ~ v1_relat_1(X0)
% 15.55/2.49      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 15.55/2.49      inference(cnf_transformation,[],[f101]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1731,plain,
% 15.55/2.49      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 15.55/2.49      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 15.55/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_3351,plain,
% 15.55/2.49      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 15.55/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1732,c_1731]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_3478,plain,
% 15.55/2.49      ( k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) = sK2 ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_2557,c_3351]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4880,plain,
% 15.55/2.49      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 15.55/2.49      inference(demodulation,[status(thm)],[c_4878,c_3478]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11324,plain,
% 15.55/2.49      ( v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 15.55/2.49      | v2_funct_1(k6_partfun1(sK0)) = iProver_top
% 15.55/2.49      | v2_funct_1(sK2) != iProver_top ),
% 15.55/2.49      inference(light_normalisation,[status(thm)],[c_11323,c_4880]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_33850,plain,
% 15.55/2.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_8575,c_42,c_43,c_44,c_45,c_46,c_47,c_49,c_32,c_122,
% 15.55/2.49                 c_126,c_1844,c_2711,c_3227,c_5237,c_7352,c_9571,c_9572,
% 15.55/2.49                 c_11324]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11461,plain,
% 15.55/2.49      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_11324,c_49,c_9571]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11467,plain,
% 15.55/2.49      ( v2_funct_1(sK3) = iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_11461,c_9572]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1705,plain,
% 15.55/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4299,plain,
% 15.55/2.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 15.55/2.49      | v2_funct_1(sK3) != iProver_top
% 15.55/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1705,c_1727]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1865,plain,
% 15.55/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.55/2.49      | v1_relat_1(sK3) ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_11]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2183,plain,
% 15.55/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.55/2.49      | v1_relat_1(sK3) ),
% 15.55/2.49      inference(instantiation,[status(thm)],[c_1865]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2184,plain,
% 15.55/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.55/2.49      | v1_relat_1(sK3) = iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_2183]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4894,plain,
% 15.55/2.49      ( v2_funct_1(sK3) != iProver_top
% 15.55/2.49      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 15.55/2.49      inference(global_propositional_subsumption,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_4299,c_47,c_2184]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_4895,plain,
% 15.55/2.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 15.55/2.49      | v2_funct_1(sK3) != iProver_top ),
% 15.55/2.49      inference(renaming,[status(thm)],[c_4894]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_11471,plain,
% 15.55/2.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_11467,c_4895]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_33852,plain,
% 15.55/2.49      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 15.55/2.49      inference(demodulation,[status(thm)],[c_33850,c_11471]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_52956,plain,
% 15.55/2.49      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_33852,c_3]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_52965,plain,
% 15.55/2.49      ( k1_relat_1(sK3) = sK1 ),
% 15.55/2.49      inference(demodulation,[status(thm)],[c_52956,c_3]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_10,plain,
% 15.55/2.49      ( ~ v1_funct_1(X0)
% 15.55/2.49      | ~ v1_funct_1(X1)
% 15.55/2.49      | ~ v2_funct_1(X1)
% 15.55/2.49      | ~ v1_relat_1(X0)
% 15.55/2.49      | ~ v1_relat_1(X1)
% 15.55/2.49      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 15.55/2.49      | k2_funct_1(X1) = X0
% 15.55/2.49      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 15.55/2.49      inference(cnf_transformation,[],[f104]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_1726,plain,
% 15.55/2.49      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 15.55/2.49      | k2_funct_1(X0) = X1
% 15.55/2.49      | k1_relat_1(X1) != k2_relat_1(X0)
% 15.55/2.49      | v1_funct_1(X1) != iProver_top
% 15.55/2.49      | v1_funct_1(X0) != iProver_top
% 15.55/2.49      | v2_funct_1(X0) != iProver_top
% 15.55/2.49      | v1_relat_1(X1) != iProver_top
% 15.55/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.55/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_9580,plain,
% 15.55/2.49      ( k2_funct_1(sK2) = sK3
% 15.55/2.49      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 15.55/2.49      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(sK0)
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top
% 15.55/2.49      | v2_funct_1(sK2) != iProver_top
% 15.55/2.49      | v1_relat_1(sK3) != iProver_top
% 15.55/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_9543,c_1726]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2789,plain,
% 15.55/2.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 15.55/2.49      inference(superposition,[status(thm)],[c_1704,c_1724]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_2790,plain,
% 15.55/2.49      ( k2_relat_1(sK2) = sK1 ),
% 15.55/2.49      inference(light_normalisation,[status(thm)],[c_2789,c_35]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_9581,plain,
% 15.55/2.49      ( k2_funct_1(sK2) = sK3
% 15.55/2.49      | k1_relat_1(sK3) != sK1
% 15.55/2.49      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top
% 15.55/2.49      | v2_funct_1(sK2) != iProver_top
% 15.55/2.49      | v1_relat_1(sK3) != iProver_top
% 15.55/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.55/2.49      inference(light_normalisation,[status(thm)],[c_9580,c_2790,c_4891]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_9582,plain,
% 15.55/2.49      ( k2_funct_1(sK2) = sK3
% 15.55/2.49      | k1_relat_1(sK3) != sK1
% 15.55/2.49      | v1_funct_1(sK3) != iProver_top
% 15.55/2.49      | v1_funct_1(sK2) != iProver_top
% 15.55/2.49      | v2_funct_1(sK2) != iProver_top
% 15.55/2.49      | v1_relat_1(sK3) != iProver_top
% 15.55/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.55/2.49      inference(equality_resolution_simp,[status(thm)],[c_9581]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(c_30,negated_conjecture,
% 15.55/2.49      ( k2_funct_1(sK2) != sK3 ),
% 15.55/2.49      inference(cnf_transformation,[],[f98]) ).
% 15.55/2.49  
% 15.55/2.49  cnf(contradiction,plain,
% 15.55/2.49      ( $false ),
% 15.55/2.49      inference(minisat,
% 15.55/2.49                [status(thm)],
% 15.55/2.49                [c_52965,c_9582,c_2557,c_2184,c_30,c_49,c_47,c_45,c_42]) ).
% 15.55/2.49  
% 15.55/2.49  
% 15.55/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.55/2.49  
% 15.55/2.49  ------                               Statistics
% 15.55/2.49  
% 15.55/2.49  ------ General
% 15.55/2.49  
% 15.55/2.49  abstr_ref_over_cycles:                  0
% 15.55/2.49  abstr_ref_under_cycles:                 0
% 15.55/2.49  gc_basic_clause_elim:                   0
% 15.55/2.49  forced_gc_time:                         0
% 15.55/2.49  parsing_time:                           0.018
% 15.55/2.49  unif_index_cands_time:                  0.
% 15.55/2.49  unif_index_add_time:                    0.
% 15.55/2.49  orderings_time:                         0.
% 15.55/2.49  out_proof_time:                         0.022
% 15.55/2.49  total_time:                             1.942
% 15.55/2.49  num_of_symbols:                         54
% 15.55/2.49  num_of_terms:                           61239
% 15.55/2.49  
% 15.55/2.49  ------ Preprocessing
% 15.55/2.49  
% 15.55/2.49  num_of_splits:                          0
% 15.55/2.49  num_of_split_atoms:                     0
% 15.55/2.49  num_of_reused_defs:                     0
% 15.55/2.49  num_eq_ax_congr_red:                    10
% 15.55/2.49  num_of_sem_filtered_clauses:            1
% 15.55/2.49  num_of_subtypes:                        0
% 15.55/2.49  monotx_restored_types:                  0
% 15.55/2.49  sat_num_of_epr_types:                   0
% 15.55/2.49  sat_num_of_non_cyclic_types:            0
% 15.55/2.49  sat_guarded_non_collapsed_types:        0
% 15.55/2.49  num_pure_diseq_elim:                    0
% 15.55/2.49  simp_replaced_by:                       0
% 15.55/2.49  res_preprocessed:                       198
% 15.55/2.49  prep_upred:                             0
% 15.55/2.49  prep_unflattend:                        42
% 15.55/2.49  smt_new_axioms:                         0
% 15.55/2.49  pred_elim_cands:                        8
% 15.55/2.49  pred_elim:                              1
% 15.55/2.49  pred_elim_cl:                           1
% 15.55/2.49  pred_elim_cycles:                       5
% 15.55/2.49  merged_defs:                            0
% 15.55/2.49  merged_defs_ncl:                        0
% 15.55/2.49  bin_hyper_res:                          0
% 15.55/2.49  prep_cycles:                            4
% 15.55/2.49  pred_elim_time:                         0.02
% 15.55/2.49  splitting_time:                         0.
% 15.55/2.49  sem_filter_time:                        0.
% 15.55/2.49  monotx_time:                            0.001
% 15.55/2.49  subtype_inf_time:                       0.
% 15.55/2.49  
% 15.55/2.49  ------ Problem properties
% 15.55/2.49  
% 15.55/2.49  clauses:                                40
% 15.55/2.49  conjectures:                            12
% 15.55/2.49  epr:                                    9
% 15.55/2.49  horn:                                   36
% 15.55/2.49  ground:                                 12
% 15.55/2.49  unary:                                  16
% 15.55/2.49  binary:                                 4
% 15.55/2.49  lits:                                   150
% 15.55/2.49  lits_eq:                                31
% 15.55/2.49  fd_pure:                                0
% 15.55/2.49  fd_pseudo:                              0
% 15.55/2.49  fd_cond:                                4
% 15.55/2.49  fd_pseudo_cond:                         4
% 15.55/2.49  ac_symbols:                             0
% 15.55/2.49  
% 15.55/2.49  ------ Propositional Solver
% 15.55/2.49  
% 15.55/2.49  prop_solver_calls:                      42
% 15.55/2.49  prop_fast_solver_calls:                 4502
% 15.55/2.49  smt_solver_calls:                       0
% 15.55/2.49  smt_fast_solver_calls:                  0
% 15.55/2.49  prop_num_of_clauses:                    26983
% 15.55/2.49  prop_preprocess_simplified:             41393
% 15.55/2.49  prop_fo_subsumed:                       983
% 15.55/2.49  prop_solver_time:                       0.
% 15.55/2.49  smt_solver_time:                        0.
% 15.55/2.49  smt_fast_solver_time:                   0.
% 15.55/2.49  prop_fast_solver_time:                  0.
% 15.55/2.49  prop_unsat_core_time:                   0.004
% 15.55/2.49  
% 15.55/2.49  ------ QBF
% 15.55/2.49  
% 15.55/2.49  qbf_q_res:                              0
% 15.55/2.49  qbf_num_tautologies:                    0
% 15.55/2.49  qbf_prep_cycles:                        0
% 15.55/2.49  
% 15.55/2.49  ------ BMC1
% 15.55/2.49  
% 15.55/2.49  bmc1_current_bound:                     -1
% 15.55/2.49  bmc1_last_solved_bound:                 -1
% 15.55/2.49  bmc1_unsat_core_size:                   -1
% 15.55/2.49  bmc1_unsat_core_parents_size:           -1
% 15.55/2.49  bmc1_merge_next_fun:                    0
% 15.55/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.55/2.49  
% 15.55/2.49  ------ Instantiation
% 15.55/2.49  
% 15.55/2.49  inst_num_of_clauses:                    624
% 15.55/2.49  inst_num_in_passive:                    289
% 15.55/2.49  inst_num_in_active:                     3066
% 15.55/2.49  inst_num_in_unprocessed:                98
% 15.55/2.49  inst_num_of_loops:                      3239
% 15.55/2.49  inst_num_of_learning_restarts:          1
% 15.55/2.49  inst_num_moves_active_passive:          166
% 15.55/2.49  inst_lit_activity:                      0
% 15.55/2.49  inst_lit_activity_moves:                1
% 15.55/2.49  inst_num_tautologies:                   0
% 15.55/2.49  inst_num_prop_implied:                  0
% 15.55/2.49  inst_num_existing_simplified:           0
% 15.55/2.49  inst_num_eq_res_simplified:             0
% 15.55/2.49  inst_num_child_elim:                    0
% 15.55/2.49  inst_num_of_dismatching_blockings:      2175
% 15.55/2.49  inst_num_of_non_proper_insts:           8377
% 15.55/2.49  inst_num_of_duplicates:                 0
% 15.55/2.49  inst_inst_num_from_inst_to_res:         0
% 15.55/2.49  inst_dismatching_checking_time:         0.
% 15.55/2.49  
% 15.55/2.49  ------ Resolution
% 15.55/2.49  
% 15.55/2.49  res_num_of_clauses:                     58
% 15.55/2.49  res_num_in_passive:                     58
% 15.55/2.49  res_num_in_active:                      0
% 15.55/2.49  res_num_of_loops:                       202
% 15.55/2.49  res_forward_subset_subsumed:            772
% 15.55/2.49  res_backward_subset_subsumed:           4
% 15.55/2.49  res_forward_subsumed:                   0
% 15.55/2.49  res_backward_subsumed:                  0
% 15.55/2.49  res_forward_subsumption_resolution:     5
% 15.55/2.49  res_backward_subsumption_resolution:    0
% 15.55/2.49  res_clause_to_clause_subsumption:       4516
% 15.55/2.49  res_orphan_elimination:                 0
% 15.55/2.49  res_tautology_del:                      418
% 15.55/2.49  res_num_eq_res_simplified:              0
% 15.55/2.49  res_num_sel_changes:                    0
% 15.55/2.49  res_moves_from_active_to_pass:          0
% 15.55/2.49  
% 15.55/2.49  ------ Superposition
% 15.55/2.49  
% 15.55/2.49  sup_time_total:                         0.
% 15.55/2.49  sup_time_generating:                    0.
% 15.55/2.49  sup_time_sim_full:                      0.
% 15.55/2.49  sup_time_sim_immed:                     0.
% 15.55/2.49  
% 15.55/2.49  sup_num_of_clauses:                     2151
% 15.55/2.49  sup_num_in_active:                      601
% 15.55/2.49  sup_num_in_passive:                     1550
% 15.55/2.49  sup_num_of_loops:                       647
% 15.55/2.49  sup_fw_superposition:                   765
% 15.55/2.49  sup_bw_superposition:                   1846
% 15.55/2.49  sup_immediate_simplified:               626
% 15.55/2.49  sup_given_eliminated:                   2
% 15.55/2.49  comparisons_done:                       0
% 15.55/2.49  comparisons_avoided:                    4
% 15.55/2.49  
% 15.55/2.49  ------ Simplifications
% 15.55/2.49  
% 15.55/2.49  
% 15.55/2.49  sim_fw_subset_subsumed:                 69
% 15.55/2.49  sim_bw_subset_subsumed:                 170
% 15.55/2.49  sim_fw_subsumed:                        49
% 15.55/2.49  sim_bw_subsumed:                        7
% 15.55/2.49  sim_fw_subsumption_res:                 0
% 15.55/2.49  sim_bw_subsumption_res:                 0
% 15.55/2.49  sim_tautology_del:                      16
% 15.55/2.49  sim_eq_tautology_del:                   36
% 15.55/2.49  sim_eq_res_simp:                        8
% 15.55/2.49  sim_fw_demodulated:                     173
% 15.55/2.49  sim_bw_demodulated:                     24
% 15.55/2.49  sim_light_normalised:                   435
% 15.55/2.49  sim_joinable_taut:                      0
% 15.55/2.49  sim_joinable_simp:                      0
% 15.55/2.49  sim_ac_normalised:                      0
% 15.55/2.49  sim_smt_subsumption:                    0
% 15.55/2.49  
%------------------------------------------------------------------------------
