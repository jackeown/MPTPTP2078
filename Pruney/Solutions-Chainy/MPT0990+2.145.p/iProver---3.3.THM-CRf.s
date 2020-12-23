%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:28 EST 2020

% Result     : Theorem 15.49s
% Output     : CNFRefutation 15.49s
% Verified   : 
% Statistics : Number of formulae       :  232 (1829 expanded)
%              Number of clauses        :  143 ( 582 expanded)
%              Number of leaves         :   22 ( 454 expanded)
%              Depth                    :   24
%              Number of atoms          :  825 (14352 expanded)
%              Number of equality atoms :  438 (5260 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f50,f49])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
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

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f62,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
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
    inference(definition_unfolding,[],[f61,f77,f77])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f93])).

fof(f56,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1213,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1216,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1221,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4881,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1221])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5901,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4881,c_43])).

cnf(c_5902,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5901])).

cnf(c_5910,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_5902])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6294,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5910,c_40])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_410,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_418,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_410,c_23])).

cnf(c_1210,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_6296,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6294,c_1210])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1229,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5017,plain,
    ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1229])).

cnf(c_5466,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1213,c_5017])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1231,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5619,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5466,c_1231])).

cnf(c_7187,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6296,c_42,c_45,c_5619])).

cnf(c_1211,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1233,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4206,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_1233])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1238,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2993,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_1238])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_47,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1242,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2356,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1243])).

cnf(c_2777,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_2356])).

cnf(c_3276,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2993,c_47,c_2777])).

cnf(c_4209,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4206,c_3276])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1237,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3283,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_1237])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1235,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3285,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_1235])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1218,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(X2)) = iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2234,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1218])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_41,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2582,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2234,c_40,c_41,c_42,c_47])).

cnf(c_3279,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3276,c_2582])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1232,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4018,plain,
    ( k5_relat_1(k4_relat_1(sK2),k2_funct_1(k4_relat_1(sK2))) = k6_partfun1(k1_relat_1(k4_relat_1(sK2)))
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_1232])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1239,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2781,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2777,c_1239])).

cnf(c_2994,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2582,c_1238])).

cnf(c_2538,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2539,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2538])).

cnf(c_3503,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2994,c_40,c_47,c_2539,c_2777])).

cnf(c_3504,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3503])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1241,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2782,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_2777,c_1241])).

cnf(c_3507,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3504,c_2782,c_3276])).

cnf(c_3463,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(k4_relat_1(sK2))
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3279,c_1238])).

cnf(c_3464,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3463,c_2782])).

cnf(c_3509,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3507,c_40,c_47,c_2777,c_3283,c_3285,c_3464])).

cnf(c_4019,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4018,c_2781,c_3509])).

cnf(c_4748,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4209,c_40,c_47,c_2777,c_3283,c_3285,c_4019])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | X1 = X0
    | k5_relat_1(X0,X2) != k6_partfun1(k1_relat_1(X1))
    | k5_relat_1(X2,X1) != k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1234,plain,
    ( X0 = X1
    | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
    | k5_relat_1(X2,X0) != k6_partfun1(k2_relat_1(X1))
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5278,plain,
    ( k6_partfun1(k1_relat_1(X0)) != k6_partfun1(k2_relat_1(sK2))
    | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(sK2,X0)
    | k4_relat_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4748,c_1234])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1240,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2780,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2777,c_1240])).

cnf(c_5282,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(k2_relat_1(sK2))
    | k4_relat_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5278,c_2780])).

cnf(c_53976,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(k2_relat_1(sK2))
    | k4_relat_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5282,c_40,c_47,c_2777,c_3279,c_3285])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1223,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4219,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1223])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1230,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2231,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1213,c_1230])).

cnf(c_4220,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4219,c_2231])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_654,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_689,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_655,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1293,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_1294,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_23951,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4220,c_41,c_29,c_689,c_1294])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1220,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3563,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1220])).

cnf(c_3564,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3563,c_3276])).

cnf(c_4510,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3564,c_40,c_41,c_42,c_47])).

cnf(c_4515,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4510,c_1223])).

cnf(c_4516,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4510,c_1230])).

cnf(c_4517,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4516,c_2781])).

cnf(c_4518,plain,
    ( k2_relat_1(sK2) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4515,c_4517])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1316,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_655])).

cnf(c_1317,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1219,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2904,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1219])).

cnf(c_3154,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2904,c_40,c_41,c_42,c_47])).

cnf(c_3278,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3276,c_3154])).

cnf(c_33701,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4518,c_30,c_689,c_1317,c_3278])).

cnf(c_53982,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | k4_relat_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_53976,c_23951,c_33701])).

cnf(c_53986,plain,
    ( k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | k4_relat_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7187,c_53982])).

cnf(c_4218,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1223])).

cnf(c_2230,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1216,c_1230])).

cnf(c_4221,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4218,c_2230])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_25301,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4221,c_44,c_30,c_689,c_1317])).

cnf(c_53987,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | k4_relat_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_53986,c_25301])).

cnf(c_53988,plain,
    ( k4_relat_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_53987])).

cnf(c_28,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3280,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_3276,c_28])).

cnf(c_2336,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2337,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2336])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1562,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_2014,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_2015,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2014])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_53988,c_3280,c_2337,c_2015,c_45,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.49/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.49/2.49  
% 15.49/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.49/2.49  
% 15.49/2.49  ------  iProver source info
% 15.49/2.49  
% 15.49/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.49/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.49/2.49  git: non_committed_changes: false
% 15.49/2.49  git: last_make_outside_of_git: false
% 15.49/2.49  
% 15.49/2.49  ------ 
% 15.49/2.49  
% 15.49/2.49  ------ Input Options
% 15.49/2.49  
% 15.49/2.49  --out_options                           all
% 15.49/2.49  --tptp_safe_out                         true
% 15.49/2.49  --problem_path                          ""
% 15.49/2.49  --include_path                          ""
% 15.49/2.49  --clausifier                            res/vclausify_rel
% 15.49/2.49  --clausifier_options                    ""
% 15.49/2.49  --stdin                                 false
% 15.49/2.49  --stats_out                             all
% 15.49/2.49  
% 15.49/2.49  ------ General Options
% 15.49/2.49  
% 15.49/2.49  --fof                                   false
% 15.49/2.49  --time_out_real                         305.
% 15.49/2.49  --time_out_virtual                      -1.
% 15.49/2.49  --symbol_type_check                     false
% 15.49/2.49  --clausify_out                          false
% 15.49/2.49  --sig_cnt_out                           false
% 15.49/2.49  --trig_cnt_out                          false
% 15.49/2.49  --trig_cnt_out_tolerance                1.
% 15.49/2.49  --trig_cnt_out_sk_spl                   false
% 15.49/2.49  --abstr_cl_out                          false
% 15.49/2.49  
% 15.49/2.49  ------ Global Options
% 15.49/2.49  
% 15.49/2.49  --schedule                              default
% 15.49/2.49  --add_important_lit                     false
% 15.49/2.49  --prop_solver_per_cl                    1000
% 15.49/2.49  --min_unsat_core                        false
% 15.49/2.49  --soft_assumptions                      false
% 15.49/2.49  --soft_lemma_size                       3
% 15.49/2.49  --prop_impl_unit_size                   0
% 15.49/2.49  --prop_impl_unit                        []
% 15.49/2.49  --share_sel_clauses                     true
% 15.49/2.49  --reset_solvers                         false
% 15.49/2.49  --bc_imp_inh                            [conj_cone]
% 15.49/2.49  --conj_cone_tolerance                   3.
% 15.49/2.49  --extra_neg_conj                        none
% 15.49/2.49  --large_theory_mode                     true
% 15.49/2.49  --prolific_symb_bound                   200
% 15.49/2.49  --lt_threshold                          2000
% 15.49/2.49  --clause_weak_htbl                      true
% 15.49/2.49  --gc_record_bc_elim                     false
% 15.49/2.49  
% 15.49/2.49  ------ Preprocessing Options
% 15.49/2.49  
% 15.49/2.49  --preprocessing_flag                    true
% 15.49/2.49  --time_out_prep_mult                    0.1
% 15.49/2.49  --splitting_mode                        input
% 15.49/2.49  --splitting_grd                         true
% 15.49/2.49  --splitting_cvd                         false
% 15.49/2.49  --splitting_cvd_svl                     false
% 15.49/2.49  --splitting_nvd                         32
% 15.49/2.49  --sub_typing                            true
% 15.49/2.49  --prep_gs_sim                           true
% 15.49/2.49  --prep_unflatten                        true
% 15.49/2.49  --prep_res_sim                          true
% 15.49/2.49  --prep_upred                            true
% 15.49/2.49  --prep_sem_filter                       exhaustive
% 15.49/2.49  --prep_sem_filter_out                   false
% 15.49/2.49  --pred_elim                             true
% 15.49/2.49  --res_sim_input                         true
% 15.49/2.49  --eq_ax_congr_red                       true
% 15.49/2.49  --pure_diseq_elim                       true
% 15.49/2.49  --brand_transform                       false
% 15.49/2.49  --non_eq_to_eq                          false
% 15.49/2.49  --prep_def_merge                        true
% 15.49/2.49  --prep_def_merge_prop_impl              false
% 15.49/2.49  --prep_def_merge_mbd                    true
% 15.49/2.49  --prep_def_merge_tr_red                 false
% 15.49/2.49  --prep_def_merge_tr_cl                  false
% 15.49/2.49  --smt_preprocessing                     true
% 15.49/2.49  --smt_ac_axioms                         fast
% 15.49/2.49  --preprocessed_out                      false
% 15.49/2.49  --preprocessed_stats                    false
% 15.49/2.49  
% 15.49/2.49  ------ Abstraction refinement Options
% 15.49/2.49  
% 15.49/2.49  --abstr_ref                             []
% 15.49/2.49  --abstr_ref_prep                        false
% 15.49/2.49  --abstr_ref_until_sat                   false
% 15.49/2.49  --abstr_ref_sig_restrict                funpre
% 15.49/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.49/2.49  --abstr_ref_under                       []
% 15.49/2.49  
% 15.49/2.49  ------ SAT Options
% 15.49/2.49  
% 15.49/2.49  --sat_mode                              false
% 15.49/2.49  --sat_fm_restart_options                ""
% 15.49/2.49  --sat_gr_def                            false
% 15.49/2.49  --sat_epr_types                         true
% 15.49/2.49  --sat_non_cyclic_types                  false
% 15.49/2.49  --sat_finite_models                     false
% 15.49/2.49  --sat_fm_lemmas                         false
% 15.49/2.49  --sat_fm_prep                           false
% 15.49/2.49  --sat_fm_uc_incr                        true
% 15.49/2.49  --sat_out_model                         small
% 15.49/2.49  --sat_out_clauses                       false
% 15.49/2.49  
% 15.49/2.49  ------ QBF Options
% 15.49/2.49  
% 15.49/2.49  --qbf_mode                              false
% 15.49/2.49  --qbf_elim_univ                         false
% 15.49/2.49  --qbf_dom_inst                          none
% 15.49/2.49  --qbf_dom_pre_inst                      false
% 15.49/2.49  --qbf_sk_in                             false
% 15.49/2.49  --qbf_pred_elim                         true
% 15.49/2.49  --qbf_split                             512
% 15.49/2.49  
% 15.49/2.49  ------ BMC1 Options
% 15.49/2.49  
% 15.49/2.49  --bmc1_incremental                      false
% 15.49/2.49  --bmc1_axioms                           reachable_all
% 15.49/2.49  --bmc1_min_bound                        0
% 15.49/2.49  --bmc1_max_bound                        -1
% 15.49/2.49  --bmc1_max_bound_default                -1
% 15.49/2.49  --bmc1_symbol_reachability              true
% 15.49/2.49  --bmc1_property_lemmas                  false
% 15.49/2.49  --bmc1_k_induction                      false
% 15.49/2.49  --bmc1_non_equiv_states                 false
% 15.49/2.49  --bmc1_deadlock                         false
% 15.49/2.49  --bmc1_ucm                              false
% 15.49/2.49  --bmc1_add_unsat_core                   none
% 15.49/2.49  --bmc1_unsat_core_children              false
% 15.49/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.49/2.49  --bmc1_out_stat                         full
% 15.49/2.49  --bmc1_ground_init                      false
% 15.49/2.49  --bmc1_pre_inst_next_state              false
% 15.49/2.49  --bmc1_pre_inst_state                   false
% 15.49/2.49  --bmc1_pre_inst_reach_state             false
% 15.49/2.49  --bmc1_out_unsat_core                   false
% 15.49/2.49  --bmc1_aig_witness_out                  false
% 15.49/2.49  --bmc1_verbose                          false
% 15.49/2.49  --bmc1_dump_clauses_tptp                false
% 15.49/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.49/2.49  --bmc1_dump_file                        -
% 15.49/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.49/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.49/2.49  --bmc1_ucm_extend_mode                  1
% 15.49/2.49  --bmc1_ucm_init_mode                    2
% 15.49/2.49  --bmc1_ucm_cone_mode                    none
% 15.49/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.49/2.49  --bmc1_ucm_relax_model                  4
% 15.49/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.49/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.49/2.49  --bmc1_ucm_layered_model                none
% 15.49/2.49  --bmc1_ucm_max_lemma_size               10
% 15.49/2.49  
% 15.49/2.49  ------ AIG Options
% 15.49/2.49  
% 15.49/2.49  --aig_mode                              false
% 15.49/2.49  
% 15.49/2.49  ------ Instantiation Options
% 15.49/2.49  
% 15.49/2.49  --instantiation_flag                    true
% 15.49/2.49  --inst_sos_flag                         true
% 15.49/2.49  --inst_sos_phase                        true
% 15.49/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.49/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.49/2.49  --inst_lit_sel_side                     num_symb
% 15.49/2.49  --inst_solver_per_active                1400
% 15.49/2.49  --inst_solver_calls_frac                1.
% 15.49/2.49  --inst_passive_queue_type               priority_queues
% 15.49/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.49/2.49  --inst_passive_queues_freq              [25;2]
% 15.49/2.49  --inst_dismatching                      true
% 15.49/2.49  --inst_eager_unprocessed_to_passive     true
% 15.49/2.49  --inst_prop_sim_given                   true
% 15.49/2.49  --inst_prop_sim_new                     false
% 15.49/2.49  --inst_subs_new                         false
% 15.49/2.49  --inst_eq_res_simp                      false
% 15.49/2.49  --inst_subs_given                       false
% 15.49/2.49  --inst_orphan_elimination               true
% 15.49/2.49  --inst_learning_loop_flag               true
% 15.49/2.49  --inst_learning_start                   3000
% 15.49/2.49  --inst_learning_factor                  2
% 15.49/2.49  --inst_start_prop_sim_after_learn       3
% 15.49/2.49  --inst_sel_renew                        solver
% 15.49/2.49  --inst_lit_activity_flag                true
% 15.49/2.49  --inst_restr_to_given                   false
% 15.49/2.49  --inst_activity_threshold               500
% 15.49/2.49  --inst_out_proof                        true
% 15.49/2.49  
% 15.49/2.49  ------ Resolution Options
% 15.49/2.49  
% 15.49/2.49  --resolution_flag                       true
% 15.49/2.49  --res_lit_sel                           adaptive
% 15.49/2.49  --res_lit_sel_side                      none
% 15.49/2.49  --res_ordering                          kbo
% 15.49/2.49  --res_to_prop_solver                    active
% 15.49/2.49  --res_prop_simpl_new                    false
% 15.49/2.49  --res_prop_simpl_given                  true
% 15.49/2.49  --res_passive_queue_type                priority_queues
% 15.49/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.49/2.49  --res_passive_queues_freq               [15;5]
% 15.49/2.49  --res_forward_subs                      full
% 15.49/2.49  --res_backward_subs                     full
% 15.49/2.49  --res_forward_subs_resolution           true
% 15.49/2.49  --res_backward_subs_resolution          true
% 15.49/2.49  --res_orphan_elimination                true
% 15.49/2.49  --res_time_limit                        2.
% 15.49/2.49  --res_out_proof                         true
% 15.49/2.49  
% 15.49/2.49  ------ Superposition Options
% 15.49/2.49  
% 15.49/2.49  --superposition_flag                    true
% 15.49/2.49  --sup_passive_queue_type                priority_queues
% 15.49/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.49/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.49/2.49  --demod_completeness_check              fast
% 15.49/2.49  --demod_use_ground                      true
% 15.49/2.49  --sup_to_prop_solver                    passive
% 15.49/2.49  --sup_prop_simpl_new                    true
% 15.49/2.49  --sup_prop_simpl_given                  true
% 15.49/2.49  --sup_fun_splitting                     true
% 15.49/2.49  --sup_smt_interval                      50000
% 15.49/2.49  
% 15.49/2.49  ------ Superposition Simplification Setup
% 15.49/2.49  
% 15.49/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.49/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.49/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.49/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.49/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.49/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.49/2.49  --sup_immed_triv                        [TrivRules]
% 15.49/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_immed_bw_main                     []
% 15.49/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.49/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.49/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_input_bw                          []
% 15.49/2.49  
% 15.49/2.49  ------ Combination Options
% 15.49/2.49  
% 15.49/2.49  --comb_res_mult                         3
% 15.49/2.49  --comb_sup_mult                         2
% 15.49/2.49  --comb_inst_mult                        10
% 15.49/2.49  
% 15.49/2.49  ------ Debug Options
% 15.49/2.49  
% 15.49/2.49  --dbg_backtrace                         false
% 15.49/2.49  --dbg_dump_prop_clauses                 false
% 15.49/2.49  --dbg_dump_prop_clauses_file            -
% 15.49/2.49  --dbg_out_stat                          false
% 15.49/2.49  ------ Parsing...
% 15.49/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.49/2.49  
% 15.49/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.49/2.49  
% 15.49/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.49/2.49  
% 15.49/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.49/2.49  ------ Proving...
% 15.49/2.49  ------ Problem Properties 
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  clauses                                 38
% 15.49/2.49  conjectures                             11
% 15.49/2.49  EPR                                     7
% 15.49/2.49  Horn                                    34
% 15.49/2.49  unary                                   13
% 15.49/2.49  binary                                  5
% 15.49/2.49  lits                                    109
% 15.49/2.49  lits eq                                 29
% 15.49/2.49  fd_pure                                 0
% 15.49/2.49  fd_pseudo                               0
% 15.49/2.49  fd_cond                                 3
% 15.49/2.49  fd_pseudo_cond                          1
% 15.49/2.49  AC symbols                              0
% 15.49/2.49  
% 15.49/2.49  ------ Schedule dynamic 5 is on 
% 15.49/2.49  
% 15.49/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  ------ 
% 15.49/2.49  Current options:
% 15.49/2.49  ------ 
% 15.49/2.49  
% 15.49/2.49  ------ Input Options
% 15.49/2.49  
% 15.49/2.49  --out_options                           all
% 15.49/2.49  --tptp_safe_out                         true
% 15.49/2.49  --problem_path                          ""
% 15.49/2.49  --include_path                          ""
% 15.49/2.49  --clausifier                            res/vclausify_rel
% 15.49/2.49  --clausifier_options                    ""
% 15.49/2.49  --stdin                                 false
% 15.49/2.49  --stats_out                             all
% 15.49/2.49  
% 15.49/2.49  ------ General Options
% 15.49/2.49  
% 15.49/2.49  --fof                                   false
% 15.49/2.49  --time_out_real                         305.
% 15.49/2.49  --time_out_virtual                      -1.
% 15.49/2.49  --symbol_type_check                     false
% 15.49/2.49  --clausify_out                          false
% 15.49/2.49  --sig_cnt_out                           false
% 15.49/2.49  --trig_cnt_out                          false
% 15.49/2.49  --trig_cnt_out_tolerance                1.
% 15.49/2.49  --trig_cnt_out_sk_spl                   false
% 15.49/2.49  --abstr_cl_out                          false
% 15.49/2.49  
% 15.49/2.49  ------ Global Options
% 15.49/2.49  
% 15.49/2.49  --schedule                              default
% 15.49/2.49  --add_important_lit                     false
% 15.49/2.49  --prop_solver_per_cl                    1000
% 15.49/2.49  --min_unsat_core                        false
% 15.49/2.49  --soft_assumptions                      false
% 15.49/2.49  --soft_lemma_size                       3
% 15.49/2.49  --prop_impl_unit_size                   0
% 15.49/2.49  --prop_impl_unit                        []
% 15.49/2.49  --share_sel_clauses                     true
% 15.49/2.49  --reset_solvers                         false
% 15.49/2.49  --bc_imp_inh                            [conj_cone]
% 15.49/2.49  --conj_cone_tolerance                   3.
% 15.49/2.49  --extra_neg_conj                        none
% 15.49/2.49  --large_theory_mode                     true
% 15.49/2.49  --prolific_symb_bound                   200
% 15.49/2.49  --lt_threshold                          2000
% 15.49/2.49  --clause_weak_htbl                      true
% 15.49/2.49  --gc_record_bc_elim                     false
% 15.49/2.49  
% 15.49/2.49  ------ Preprocessing Options
% 15.49/2.49  
% 15.49/2.49  --preprocessing_flag                    true
% 15.49/2.49  --time_out_prep_mult                    0.1
% 15.49/2.49  --splitting_mode                        input
% 15.49/2.49  --splitting_grd                         true
% 15.49/2.49  --splitting_cvd                         false
% 15.49/2.49  --splitting_cvd_svl                     false
% 15.49/2.49  --splitting_nvd                         32
% 15.49/2.49  --sub_typing                            true
% 15.49/2.49  --prep_gs_sim                           true
% 15.49/2.49  --prep_unflatten                        true
% 15.49/2.49  --prep_res_sim                          true
% 15.49/2.49  --prep_upred                            true
% 15.49/2.49  --prep_sem_filter                       exhaustive
% 15.49/2.49  --prep_sem_filter_out                   false
% 15.49/2.49  --pred_elim                             true
% 15.49/2.49  --res_sim_input                         true
% 15.49/2.49  --eq_ax_congr_red                       true
% 15.49/2.49  --pure_diseq_elim                       true
% 15.49/2.49  --brand_transform                       false
% 15.49/2.49  --non_eq_to_eq                          false
% 15.49/2.49  --prep_def_merge                        true
% 15.49/2.49  --prep_def_merge_prop_impl              false
% 15.49/2.49  --prep_def_merge_mbd                    true
% 15.49/2.49  --prep_def_merge_tr_red                 false
% 15.49/2.49  --prep_def_merge_tr_cl                  false
% 15.49/2.49  --smt_preprocessing                     true
% 15.49/2.49  --smt_ac_axioms                         fast
% 15.49/2.49  --preprocessed_out                      false
% 15.49/2.49  --preprocessed_stats                    false
% 15.49/2.49  
% 15.49/2.49  ------ Abstraction refinement Options
% 15.49/2.49  
% 15.49/2.49  --abstr_ref                             []
% 15.49/2.49  --abstr_ref_prep                        false
% 15.49/2.49  --abstr_ref_until_sat                   false
% 15.49/2.49  --abstr_ref_sig_restrict                funpre
% 15.49/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.49/2.49  --abstr_ref_under                       []
% 15.49/2.49  
% 15.49/2.49  ------ SAT Options
% 15.49/2.49  
% 15.49/2.49  --sat_mode                              false
% 15.49/2.49  --sat_fm_restart_options                ""
% 15.49/2.49  --sat_gr_def                            false
% 15.49/2.49  --sat_epr_types                         true
% 15.49/2.49  --sat_non_cyclic_types                  false
% 15.49/2.49  --sat_finite_models                     false
% 15.49/2.49  --sat_fm_lemmas                         false
% 15.49/2.49  --sat_fm_prep                           false
% 15.49/2.49  --sat_fm_uc_incr                        true
% 15.49/2.49  --sat_out_model                         small
% 15.49/2.49  --sat_out_clauses                       false
% 15.49/2.49  
% 15.49/2.49  ------ QBF Options
% 15.49/2.49  
% 15.49/2.49  --qbf_mode                              false
% 15.49/2.49  --qbf_elim_univ                         false
% 15.49/2.49  --qbf_dom_inst                          none
% 15.49/2.49  --qbf_dom_pre_inst                      false
% 15.49/2.49  --qbf_sk_in                             false
% 15.49/2.49  --qbf_pred_elim                         true
% 15.49/2.49  --qbf_split                             512
% 15.49/2.49  
% 15.49/2.49  ------ BMC1 Options
% 15.49/2.49  
% 15.49/2.49  --bmc1_incremental                      false
% 15.49/2.49  --bmc1_axioms                           reachable_all
% 15.49/2.49  --bmc1_min_bound                        0
% 15.49/2.49  --bmc1_max_bound                        -1
% 15.49/2.49  --bmc1_max_bound_default                -1
% 15.49/2.49  --bmc1_symbol_reachability              true
% 15.49/2.49  --bmc1_property_lemmas                  false
% 15.49/2.49  --bmc1_k_induction                      false
% 15.49/2.49  --bmc1_non_equiv_states                 false
% 15.49/2.49  --bmc1_deadlock                         false
% 15.49/2.49  --bmc1_ucm                              false
% 15.49/2.49  --bmc1_add_unsat_core                   none
% 15.49/2.49  --bmc1_unsat_core_children              false
% 15.49/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.49/2.49  --bmc1_out_stat                         full
% 15.49/2.49  --bmc1_ground_init                      false
% 15.49/2.49  --bmc1_pre_inst_next_state              false
% 15.49/2.49  --bmc1_pre_inst_state                   false
% 15.49/2.49  --bmc1_pre_inst_reach_state             false
% 15.49/2.49  --bmc1_out_unsat_core                   false
% 15.49/2.49  --bmc1_aig_witness_out                  false
% 15.49/2.49  --bmc1_verbose                          false
% 15.49/2.49  --bmc1_dump_clauses_tptp                false
% 15.49/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.49/2.49  --bmc1_dump_file                        -
% 15.49/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.49/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.49/2.49  --bmc1_ucm_extend_mode                  1
% 15.49/2.49  --bmc1_ucm_init_mode                    2
% 15.49/2.49  --bmc1_ucm_cone_mode                    none
% 15.49/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.49/2.49  --bmc1_ucm_relax_model                  4
% 15.49/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.49/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.49/2.49  --bmc1_ucm_layered_model                none
% 15.49/2.49  --bmc1_ucm_max_lemma_size               10
% 15.49/2.49  
% 15.49/2.49  ------ AIG Options
% 15.49/2.49  
% 15.49/2.49  --aig_mode                              false
% 15.49/2.49  
% 15.49/2.49  ------ Instantiation Options
% 15.49/2.49  
% 15.49/2.49  --instantiation_flag                    true
% 15.49/2.49  --inst_sos_flag                         true
% 15.49/2.49  --inst_sos_phase                        true
% 15.49/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.49/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.49/2.49  --inst_lit_sel_side                     none
% 15.49/2.49  --inst_solver_per_active                1400
% 15.49/2.49  --inst_solver_calls_frac                1.
% 15.49/2.49  --inst_passive_queue_type               priority_queues
% 15.49/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.49/2.49  --inst_passive_queues_freq              [25;2]
% 15.49/2.49  --inst_dismatching                      true
% 15.49/2.49  --inst_eager_unprocessed_to_passive     true
% 15.49/2.49  --inst_prop_sim_given                   true
% 15.49/2.49  --inst_prop_sim_new                     false
% 15.49/2.49  --inst_subs_new                         false
% 15.49/2.49  --inst_eq_res_simp                      false
% 15.49/2.49  --inst_subs_given                       false
% 15.49/2.49  --inst_orphan_elimination               true
% 15.49/2.49  --inst_learning_loop_flag               true
% 15.49/2.49  --inst_learning_start                   3000
% 15.49/2.49  --inst_learning_factor                  2
% 15.49/2.49  --inst_start_prop_sim_after_learn       3
% 15.49/2.49  --inst_sel_renew                        solver
% 15.49/2.49  --inst_lit_activity_flag                true
% 15.49/2.49  --inst_restr_to_given                   false
% 15.49/2.49  --inst_activity_threshold               500
% 15.49/2.49  --inst_out_proof                        true
% 15.49/2.49  
% 15.49/2.49  ------ Resolution Options
% 15.49/2.49  
% 15.49/2.49  --resolution_flag                       false
% 15.49/2.49  --res_lit_sel                           adaptive
% 15.49/2.49  --res_lit_sel_side                      none
% 15.49/2.49  --res_ordering                          kbo
% 15.49/2.49  --res_to_prop_solver                    active
% 15.49/2.49  --res_prop_simpl_new                    false
% 15.49/2.49  --res_prop_simpl_given                  true
% 15.49/2.49  --res_passive_queue_type                priority_queues
% 15.49/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.49/2.49  --res_passive_queues_freq               [15;5]
% 15.49/2.49  --res_forward_subs                      full
% 15.49/2.49  --res_backward_subs                     full
% 15.49/2.49  --res_forward_subs_resolution           true
% 15.49/2.49  --res_backward_subs_resolution          true
% 15.49/2.49  --res_orphan_elimination                true
% 15.49/2.49  --res_time_limit                        2.
% 15.49/2.49  --res_out_proof                         true
% 15.49/2.49  
% 15.49/2.49  ------ Superposition Options
% 15.49/2.49  
% 15.49/2.49  --superposition_flag                    true
% 15.49/2.49  --sup_passive_queue_type                priority_queues
% 15.49/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.49/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.49/2.49  --demod_completeness_check              fast
% 15.49/2.49  --demod_use_ground                      true
% 15.49/2.49  --sup_to_prop_solver                    passive
% 15.49/2.49  --sup_prop_simpl_new                    true
% 15.49/2.49  --sup_prop_simpl_given                  true
% 15.49/2.49  --sup_fun_splitting                     true
% 15.49/2.49  --sup_smt_interval                      50000
% 15.49/2.49  
% 15.49/2.49  ------ Superposition Simplification Setup
% 15.49/2.49  
% 15.49/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.49/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.49/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.49/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.49/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.49/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.49/2.49  --sup_immed_triv                        [TrivRules]
% 15.49/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_immed_bw_main                     []
% 15.49/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.49/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.49/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.49  --sup_input_bw                          []
% 15.49/2.49  
% 15.49/2.49  ------ Combination Options
% 15.49/2.49  
% 15.49/2.49  --comb_res_mult                         3
% 15.49/2.49  --comb_sup_mult                         2
% 15.49/2.49  --comb_inst_mult                        10
% 15.49/2.49  
% 15.49/2.49  ------ Debug Options
% 15.49/2.49  
% 15.49/2.49  --dbg_backtrace                         false
% 15.49/2.49  --dbg_dump_prop_clauses                 false
% 15.49/2.49  --dbg_dump_prop_clauses_file            -
% 15.49/2.49  --dbg_out_stat                          false
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  ------ Proving...
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  % SZS status Theorem for theBenchmark.p
% 15.49/2.49  
% 15.49/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.49/2.49  
% 15.49/2.49  fof(f18,conjecture,(
% 15.49/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f19,negated_conjecture,(
% 15.49/2.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.49/2.49    inference(negated_conjecture,[],[f18])).
% 15.49/2.49  
% 15.49/2.49  fof(f45,plain,(
% 15.49/2.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.49/2.49    inference(ennf_transformation,[],[f19])).
% 15.49/2.49  
% 15.49/2.49  fof(f46,plain,(
% 15.49/2.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.49/2.49    inference(flattening,[],[f45])).
% 15.49/2.49  
% 15.49/2.49  fof(f50,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 15.49/2.49    introduced(choice_axiom,[])).
% 15.49/2.49  
% 15.49/2.49  fof(f49,plain,(
% 15.49/2.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 15.49/2.49    introduced(choice_axiom,[])).
% 15.49/2.49  
% 15.49/2.49  fof(f51,plain,(
% 15.49/2.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 15.49/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f50,f49])).
% 15.49/2.49  
% 15.49/2.49  fof(f83,plain,(
% 15.49/2.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f86,plain,(
% 15.49/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f15,axiom,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f41,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.49/2.49    inference(ennf_transformation,[],[f15])).
% 15.49/2.49  
% 15.49/2.49  fof(f42,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.49/2.49    inference(flattening,[],[f41])).
% 15.49/2.49  
% 15.49/2.49  fof(f76,plain,(
% 15.49/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f42])).
% 15.49/2.49  
% 15.49/2.49  fof(f84,plain,(
% 15.49/2.49    v1_funct_1(sK3)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f81,plain,(
% 15.49/2.49    v1_funct_1(sK2)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f12,axiom,(
% 15.49/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f37,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.49/2.49    inference(ennf_transformation,[],[f12])).
% 15.49/2.49  
% 15.49/2.49  fof(f38,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(flattening,[],[f37])).
% 15.49/2.49  
% 15.49/2.49  fof(f47,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(nnf_transformation,[],[f38])).
% 15.49/2.49  
% 15.49/2.49  fof(f67,plain,(
% 15.49/2.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f47])).
% 15.49/2.49  
% 15.49/2.49  fof(f88,plain,(
% 15.49/2.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f14,axiom,(
% 15.49/2.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f20,plain,(
% 15.49/2.49    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 15.49/2.49    inference(pure_predicate_removal,[],[f14])).
% 15.49/2.49  
% 15.49/2.49  fof(f75,plain,(
% 15.49/2.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f20])).
% 15.49/2.49  
% 15.49/2.49  fof(f11,axiom,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f35,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.49/2.49    inference(ennf_transformation,[],[f11])).
% 15.49/2.49  
% 15.49/2.49  fof(f36,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(flattening,[],[f35])).
% 15.49/2.49  
% 15.49/2.49  fof(f66,plain,(
% 15.49/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f36])).
% 15.49/2.49  
% 15.49/2.49  fof(f9,axiom,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f32,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.49/2.49    inference(ennf_transformation,[],[f9])).
% 15.49/2.49  
% 15.49/2.49  fof(f33,plain,(
% 15.49/2.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(flattening,[],[f32])).
% 15.49/2.49  
% 15.49/2.49  fof(f64,plain,(
% 15.49/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f33])).
% 15.49/2.49  
% 15.49/2.49  fof(f8,axiom,(
% 15.49/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f30,plain,(
% 15.49/2.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.49/2.49    inference(ennf_transformation,[],[f8])).
% 15.49/2.49  
% 15.49/2.49  fof(f31,plain,(
% 15.49/2.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(flattening,[],[f30])).
% 15.49/2.49  
% 15.49/2.49  fof(f63,plain,(
% 15.49/2.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f31])).
% 15.49/2.49  
% 15.49/2.49  fof(f16,axiom,(
% 15.49/2.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f77,plain,(
% 15.49/2.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f16])).
% 15.49/2.49  
% 15.49/2.49  fof(f94,plain,(
% 15.49/2.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(definition_unfolding,[],[f63,f77])).
% 15.49/2.49  
% 15.49/2.49  fof(f5,axiom,(
% 15.49/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f24,plain,(
% 15.49/2.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.49/2.49    inference(ennf_transformation,[],[f5])).
% 15.49/2.49  
% 15.49/2.49  fof(f25,plain,(
% 15.49/2.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(flattening,[],[f24])).
% 15.49/2.49  
% 15.49/2.49  fof(f57,plain,(
% 15.49/2.49    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f25])).
% 15.49/2.49  
% 15.49/2.49  fof(f89,plain,(
% 15.49/2.49    v2_funct_1(sK2)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f2,axiom,(
% 15.49/2.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f53,plain,(
% 15.49/2.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f2])).
% 15.49/2.49  
% 15.49/2.49  fof(f1,axiom,(
% 15.49/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f21,plain,(
% 15.49/2.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(ennf_transformation,[],[f1])).
% 15.49/2.49  
% 15.49/2.49  fof(f52,plain,(
% 15.49/2.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f21])).
% 15.49/2.49  
% 15.49/2.49  fof(f6,axiom,(
% 15.49/2.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f26,plain,(
% 15.49/2.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.49/2.49    inference(ennf_transformation,[],[f6])).
% 15.49/2.49  
% 15.49/2.49  fof(f27,plain,(
% 15.49/2.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(flattening,[],[f26])).
% 15.49/2.49  
% 15.49/2.49  fof(f60,plain,(
% 15.49/2.49    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f27])).
% 15.49/2.49  
% 15.49/2.49  fof(f58,plain,(
% 15.49/2.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f27])).
% 15.49/2.49  
% 15.49/2.49  fof(f87,plain,(
% 15.49/2.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f17,axiom,(
% 15.49/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f43,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.49/2.49    inference(ennf_transformation,[],[f17])).
% 15.49/2.49  
% 15.49/2.49  fof(f44,plain,(
% 15.49/2.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.49/2.49    inference(flattening,[],[f43])).
% 15.49/2.49  
% 15.49/2.49  fof(f78,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f44])).
% 15.49/2.49  
% 15.49/2.49  fof(f82,plain,(
% 15.49/2.49    v1_funct_2(sK2,sK0,sK1)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f62,plain,(
% 15.49/2.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f31])).
% 15.49/2.49  
% 15.49/2.49  fof(f95,plain,(
% 15.49/2.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(definition_unfolding,[],[f62,f77])).
% 15.49/2.49  
% 15.49/2.49  fof(f4,axiom,(
% 15.49/2.49    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f23,plain,(
% 15.49/2.49    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 15.49/2.49    inference(ennf_transformation,[],[f4])).
% 15.49/2.49  
% 15.49/2.49  fof(f55,plain,(
% 15.49/2.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f23])).
% 15.49/2.49  
% 15.49/2.49  fof(f3,axiom,(
% 15.49/2.49    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f22,plain,(
% 15.49/2.49    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 15.49/2.49    inference(ennf_transformation,[],[f3])).
% 15.49/2.49  
% 15.49/2.49  fof(f54,plain,(
% 15.49/2.49    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f22])).
% 15.49/2.49  
% 15.49/2.49  fof(f7,axiom,(
% 15.49/2.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f28,plain,(
% 15.49/2.49    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.49/2.49    inference(ennf_transformation,[],[f7])).
% 15.49/2.49  
% 15.49/2.49  fof(f29,plain,(
% 15.49/2.49    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.49/2.49    inference(flattening,[],[f28])).
% 15.49/2.49  
% 15.49/2.49  fof(f61,plain,(
% 15.49/2.49    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f29])).
% 15.49/2.49  
% 15.49/2.49  fof(f93,plain,(
% 15.49/2.49    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(X0) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.49/2.49    inference(definition_unfolding,[],[f61,f77,f77])).
% 15.49/2.49  
% 15.49/2.49  fof(f96,plain,(
% 15.49/2.49    ( ! [X2,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1)) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.49/2.49    inference(equality_resolution,[],[f93])).
% 15.49/2.49  
% 15.49/2.49  fof(f56,plain,(
% 15.49/2.49    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f23])).
% 15.49/2.49  
% 15.49/2.49  fof(f13,axiom,(
% 15.49/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f39,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(ennf_transformation,[],[f13])).
% 15.49/2.49  
% 15.49/2.49  fof(f40,plain,(
% 15.49/2.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(flattening,[],[f39])).
% 15.49/2.49  
% 15.49/2.49  fof(f48,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(nnf_transformation,[],[f40])).
% 15.49/2.49  
% 15.49/2.49  fof(f69,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f48])).
% 15.49/2.49  
% 15.49/2.49  fof(f10,axiom,(
% 15.49/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.49/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.49  
% 15.49/2.49  fof(f34,plain,(
% 15.49/2.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.49    inference(ennf_transformation,[],[f10])).
% 15.49/2.49  
% 15.49/2.49  fof(f65,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.49    inference(cnf_transformation,[],[f34])).
% 15.49/2.49  
% 15.49/2.49  fof(f91,plain,(
% 15.49/2.49    k1_xboole_0 != sK1),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f80,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f44])).
% 15.49/2.49  
% 15.49/2.49  fof(f90,plain,(
% 15.49/2.49    k1_xboole_0 != sK0),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f79,plain,(
% 15.49/2.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.49/2.49    inference(cnf_transformation,[],[f44])).
% 15.49/2.49  
% 15.49/2.49  fof(f85,plain,(
% 15.49/2.49    v1_funct_2(sK3,sK1,sK0)),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  fof(f92,plain,(
% 15.49/2.49    k2_funct_1(sK2) != sK3),
% 15.49/2.49    inference(cnf_transformation,[],[f51])).
% 15.49/2.49  
% 15.49/2.49  cnf(c_37,negated_conjecture,
% 15.49/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.49/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1213,plain,
% 15.49/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_34,negated_conjecture,
% 15.49/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 15.49/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1216,plain,
% 15.49/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_24,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.49/2.49      | ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v1_funct_1(X3)
% 15.49/2.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1221,plain,
% 15.49/2.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.49/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.49/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | v1_funct_1(X5) != iProver_top
% 15.49/2.49      | v1_funct_1(X4) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4881,plain,
% 15.49/2.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | v1_funct_1(X2) != iProver_top
% 15.49/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1216,c_1221]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_36,negated_conjecture,
% 15.49/2.49      ( v1_funct_1(sK3) ),
% 15.49/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_43,plain,
% 15.49/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5901,plain,
% 15.49/2.49      ( v1_funct_1(X2) != iProver_top
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_4881,c_43]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5902,plain,
% 15.49/2.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.49/2.49      inference(renaming,[status(thm)],[c_5901]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5910,plain,
% 15.49/2.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 15.49/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1213,c_5902]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_39,negated_conjecture,
% 15.49/2.49      ( v1_funct_1(sK2) ),
% 15.49/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_40,plain,
% 15.49/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6294,plain,
% 15.49/2.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_5910,c_40]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_16,plain,
% 15.49/2.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.49/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.49/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.49/2.49      | X2 = X3 ),
% 15.49/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_32,negated_conjecture,
% 15.49/2.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 15.49/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_409,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | X3 = X0
% 15.49/2.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 15.49/2.49      | k6_partfun1(sK0) != X3
% 15.49/2.49      | sK0 != X2
% 15.49/2.49      | sK0 != X1 ),
% 15.49/2.49      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_410,plain,
% 15.49/2.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.49/2.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.49/2.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.49/2.49      inference(unflattening,[status(thm)],[c_409]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_23,plain,
% 15.49/2.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.49/2.49      inference(cnf_transformation,[],[f75]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_418,plain,
% 15.49/2.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.49/2.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.49/2.49      inference(forward_subsumption_resolution,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_410,c_23]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1210,plain,
% 15.49/2.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.49/2.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6296,plain,
% 15.49/2.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 15.49/2.49      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_6294,c_1210]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_42,plain,
% 15.49/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_45,plain,
% 15.49/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_14,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.49/2.49      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1229,plain,
% 15.49/2.49      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.49/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.49/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5017,plain,
% 15.49/2.49      ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1216,c_1229]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5466,plain,
% 15.49/2.49      ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1213,c_5017]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_12,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.49/2.49      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 15.49/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1231,plain,
% 15.49/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.49/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 15.49/2.49      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5619,plain,
% 15.49/2.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 15.49/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.49/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_5466,c_1231]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_7187,plain,
% 15.49/2.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_6296,c_42,c_45,c_5619]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1211,plain,
% 15.49/2.49      ( v1_funct_1(sK2) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_10,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 15.49/2.49      inference(cnf_transformation,[],[f94]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1233,plain,
% 15.49/2.49      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4206,plain,
% 15.49/2.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top
% 15.49/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1211,c_1233]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1238,plain,
% 15.49/2.49      ( k2_funct_1(X0) = k4_relat_1(X0)
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2993,plain,
% 15.49/2.49      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top
% 15.49/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1211,c_1238]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_31,negated_conjecture,
% 15.49/2.49      ( v2_funct_1(sK2) ),
% 15.49/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_47,plain,
% 15.49/2.49      ( v2_funct_1(sK2) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1,plain,
% 15.49/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.49/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1242,plain,
% 15.49/2.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_0,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.49/2.49      | ~ v1_relat_1(X1)
% 15.49/2.49      | v1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1243,plain,
% 15.49/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.49/2.49      | v1_relat_1(X1) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2356,plain,
% 15.49/2.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.49/2.49      | v1_relat_1(sK2) = iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1213,c_1243]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2777,plain,
% 15.49/2.49      ( v1_relat_1(sK2) = iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1242,c_2356]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3276,plain,
% 15.49/2.49      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_2993,c_47,c_2777]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4209,plain,
% 15.49/2.49      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top
% 15.49/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_4206,c_3276]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_6,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | v2_funct_1(k2_funct_1(X0))
% 15.49/2.49      | ~ v1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1237,plain,
% 15.49/2.49      ( v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(k2_funct_1(X0)) = iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3283,plain,
% 15.49/2.49      ( v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top
% 15.49/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_3276,c_1237]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_8,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | v1_relat_1(k2_funct_1(X0)) ),
% 15.49/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1235,plain,
% 15.49/2.49      ( v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3285,plain,
% 15.49/2.49      ( v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top
% 15.49/2.49      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 15.49/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_3276,c_1235]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_33,negated_conjecture,
% 15.49/2.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 15.49/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_27,plain,
% 15.49/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.49/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | ~ v1_funct_1(X0)
% 15.49/2.49      | v1_funct_1(k2_funct_1(X0))
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 15.49/2.49      inference(cnf_transformation,[],[f78]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1218,plain,
% 15.49/2.49      ( k2_relset_1(X0,X1,X2) != X1
% 15.49/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | v1_funct_1(X2) != iProver_top
% 15.49/2.49      | v1_funct_1(k2_funct_1(X2)) = iProver_top
% 15.49/2.49      | v2_funct_1(X2) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2234,plain,
% 15.49/2.49      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.49/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.49/2.49      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 15.49/2.49      | v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_33,c_1218]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_38,negated_conjecture,
% 15.49/2.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 15.49/2.49      inference(cnf_transformation,[],[f82]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_41,plain,
% 15.49/2.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2582,plain,
% 15.49/2.49      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_2234,c_40,c_41,c_42,c_47]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3279,plain,
% 15.49/2.49      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_3276,c_2582]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_11,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 15.49/2.49      inference(cnf_transformation,[],[f95]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1232,plain,
% 15.49/2.49      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v2_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4018,plain,
% 15.49/2.49      ( k5_relat_1(k4_relat_1(sK2),k2_funct_1(k4_relat_1(sK2))) = k6_partfun1(k1_relat_1(k4_relat_1(sK2)))
% 15.49/2.49      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 15.49/2.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_3279,c_1232]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4,plain,
% 15.49/2.49      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1239,plain,
% 15.49/2.49      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2781,plain,
% 15.49/2.49      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_2777,c_1239]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2994,plain,
% 15.49/2.49      ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
% 15.49/2.49      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_2582,c_1238]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2538,plain,
% 15.49/2.49      ( ~ v1_funct_1(sK2)
% 15.49/2.49      | ~ v2_funct_1(sK2)
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK2))
% 15.49/2.49      | ~ v1_relat_1(sK2) ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2539,plain,
% 15.49/2.49      ( v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top
% 15.49/2.49      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 15.49/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_2538]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3503,plain,
% 15.49/2.49      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 15.49/2.49      | k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2)) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_2994,c_40,c_47,c_2539,c_2777]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3504,plain,
% 15.49/2.49      ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
% 15.49/2.49      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 15.49/2.49      inference(renaming,[status(thm)],[c_3503]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2,plain,
% 15.49/2.49      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 15.49/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1241,plain,
% 15.49/2.49      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2782,plain,
% 15.49/2.49      ( k4_relat_1(k4_relat_1(sK2)) = sK2 ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_2777,c_1241]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3507,plain,
% 15.49/2.49      ( k2_funct_1(k4_relat_1(sK2)) = sK2
% 15.49/2.49      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_3504,c_2782,c_3276]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3463,plain,
% 15.49/2.49      ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(k4_relat_1(sK2))
% 15.49/2.49      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 15.49/2.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_3279,c_1238]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3464,plain,
% 15.49/2.49      ( k2_funct_1(k4_relat_1(sK2)) = sK2
% 15.49/2.49      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 15.49/2.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_3463,c_2782]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3509,plain,
% 15.49/2.49      ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_3507,c_40,c_47,c_2777,c_3283,c_3285,c_3464]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4019,plain,
% 15.49/2.49      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 15.49/2.49      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 15.49/2.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_4018,c_2781,c_3509]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4748,plain,
% 15.49/2.49      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_4209,c_40,c_47,c_2777,c_3283,c_3285,c_4019]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_9,plain,
% 15.49/2.49      ( ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v1_funct_1(X1)
% 15.49/2.49      | ~ v1_funct_1(X2)
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | ~ v1_relat_1(X1)
% 15.49/2.49      | ~ v1_relat_1(X2)
% 15.49/2.49      | X1 = X0
% 15.49/2.49      | k5_relat_1(X0,X2) != k6_partfun1(k1_relat_1(X1))
% 15.49/2.49      | k5_relat_1(X2,X1) != k6_partfun1(k2_relat_1(X0)) ),
% 15.49/2.49      inference(cnf_transformation,[],[f96]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1234,plain,
% 15.49/2.49      ( X0 = X1
% 15.49/2.49      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
% 15.49/2.49      | k5_relat_1(X2,X0) != k6_partfun1(k2_relat_1(X1))
% 15.49/2.49      | v1_funct_1(X1) != iProver_top
% 15.49/2.49      | v1_funct_1(X2) != iProver_top
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X1) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X2) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5278,plain,
% 15.49/2.49      ( k6_partfun1(k1_relat_1(X0)) != k6_partfun1(k2_relat_1(sK2))
% 15.49/2.49      | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k5_relat_1(sK2,X0)
% 15.49/2.49      | k4_relat_1(sK2) = X0
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 15.49/2.49      | v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top
% 15.49/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_4748,c_1234]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3,plain,
% 15.49/2.49      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1240,plain,
% 15.49/2.49      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2780,plain,
% 15.49/2.49      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_2777,c_1240]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_5282,plain,
% 15.49/2.49      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 15.49/2.49      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(k2_relat_1(sK2))
% 15.49/2.49      | k4_relat_1(sK2) = X0
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 15.49/2.49      | v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top
% 15.49/2.49      | v1_relat_1(sK2) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_5278,c_2780]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_53976,plain,
% 15.49/2.49      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 15.49/2.49      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(k2_relat_1(sK2))
% 15.49/2.49      | k4_relat_1(sK2) = X0
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_5282,c_40,c_47,c_2777,c_3279,c_3285]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_22,plain,
% 15.49/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.49/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.49/2.49      | k1_xboole_0 = X2 ),
% 15.49/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1223,plain,
% 15.49/2.49      ( k1_relset_1(X0,X1,X2) = X0
% 15.49/2.49      | k1_xboole_0 = X1
% 15.49/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4219,plain,
% 15.49/2.49      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 15.49/2.49      | sK1 = k1_xboole_0
% 15.49/2.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1213,c_1223]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_13,plain,
% 15.49/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1230,plain,
% 15.49/2.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2231,plain,
% 15.49/2.49      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1213,c_1230]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4220,plain,
% 15.49/2.49      ( k1_relat_1(sK2) = sK0
% 15.49/2.49      | sK1 = k1_xboole_0
% 15.49/2.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_4219,c_2231]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_29,negated_conjecture,
% 15.49/2.49      ( k1_xboole_0 != sK1 ),
% 15.49/2.49      inference(cnf_transformation,[],[f91]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_654,plain,( X0 = X0 ),theory(equality) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_689,plain,
% 15.49/2.49      ( k1_xboole_0 = k1_xboole_0 ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_654]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_655,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1293,plain,
% 15.49/2.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_655]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1294,plain,
% 15.49/2.49      ( sK1 != k1_xboole_0
% 15.49/2.49      | k1_xboole_0 = sK1
% 15.49/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_1293]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_23951,plain,
% 15.49/2.49      ( k1_relat_1(sK2) = sK0 ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_4220,c_41,c_29,c_689,c_1294]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_25,plain,
% 15.49/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.49/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.49/2.49      | ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 15.49/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1220,plain,
% 15.49/2.49      ( k2_relset_1(X0,X1,X2) != X1
% 15.49/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 15.49/2.49      | v1_funct_1(X2) != iProver_top
% 15.49/2.49      | v2_funct_1(X2) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3563,plain,
% 15.49/2.49      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.49/2.49      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 15.49/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.49/2.49      | v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_33,c_1220]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3564,plain,
% 15.49/2.49      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.49/2.49      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 15.49/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.49/2.49      | v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_3563,c_3276]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4510,plain,
% 15.49/2.49      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_3564,c_40,c_41,c_42,c_47]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4515,plain,
% 15.49/2.49      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1
% 15.49/2.49      | sK0 = k1_xboole_0
% 15.49/2.49      | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_4510,c_1223]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4516,plain,
% 15.49/2.49      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_4510,c_1230]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4517,plain,
% 15.49/2.49      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_4516,c_2781]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4518,plain,
% 15.49/2.49      ( k2_relat_1(sK2) = sK1
% 15.49/2.49      | sK0 = k1_xboole_0
% 15.49/2.49      | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_4515,c_4517]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_30,negated_conjecture,
% 15.49/2.49      ( k1_xboole_0 != sK0 ),
% 15.49/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1316,plain,
% 15.49/2.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_655]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1317,plain,
% 15.49/2.49      ( sK0 != k1_xboole_0
% 15.49/2.49      | k1_xboole_0 = sK0
% 15.49/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_1316]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_26,plain,
% 15.49/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.49/2.49      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 15.49/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.49      | ~ v1_funct_1(X0)
% 15.49/2.49      | ~ v2_funct_1(X0)
% 15.49/2.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 15.49/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1219,plain,
% 15.49/2.49      ( k2_relset_1(X0,X1,X2) != X1
% 15.49/2.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.49/2.49      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 15.49/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.49      | v1_funct_1(X2) != iProver_top
% 15.49/2.49      | v2_funct_1(X2) != iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2904,plain,
% 15.49/2.49      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
% 15.49/2.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.49/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.49/2.49      | v1_funct_1(sK2) != iProver_top
% 15.49/2.49      | v2_funct_1(sK2) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_33,c_1219]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3154,plain,
% 15.49/2.49      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_2904,c_40,c_41,c_42,c_47]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3278,plain,
% 15.49/2.49      ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) = iProver_top ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_3276,c_3154]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_33701,plain,
% 15.49/2.49      ( k2_relat_1(sK2) = sK1 ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_4518,c_30,c_689,c_1317,c_3278]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_53982,plain,
% 15.49/2.49      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 15.49/2.49      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 15.49/2.49      | k4_relat_1(sK2) = X0
% 15.49/2.49      | v1_funct_1(X0) != iProver_top
% 15.49/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_53976,c_23951,c_33701]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_53986,plain,
% 15.49/2.49      ( k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 15.49/2.49      | k4_relat_1(sK2) = sK3
% 15.49/2.49      | v1_funct_1(sK3) != iProver_top
% 15.49/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_7187,c_53982]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4218,plain,
% 15.49/2.49      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 15.49/2.49      | sK0 = k1_xboole_0
% 15.49/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1216,c_1223]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2230,plain,
% 15.49/2.49      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 15.49/2.49      inference(superposition,[status(thm)],[c_1216,c_1230]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_4221,plain,
% 15.49/2.49      ( k1_relat_1(sK3) = sK1
% 15.49/2.49      | sK0 = k1_xboole_0
% 15.49/2.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_4218,c_2230]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_35,negated_conjecture,
% 15.49/2.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 15.49/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_44,plain,
% 15.49/2.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_25301,plain,
% 15.49/2.49      ( k1_relat_1(sK3) = sK1 ),
% 15.49/2.49      inference(global_propositional_subsumption,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_4221,c_44,c_30,c_689,c_1317]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_53987,plain,
% 15.49/2.49      ( k6_partfun1(sK1) != k6_partfun1(sK1)
% 15.49/2.49      | k4_relat_1(sK2) = sK3
% 15.49/2.49      | v1_funct_1(sK3) != iProver_top
% 15.49/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.49/2.49      inference(light_normalisation,[status(thm)],[c_53986,c_25301]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_53988,plain,
% 15.49/2.49      ( k4_relat_1(sK2) = sK3
% 15.49/2.49      | v1_funct_1(sK3) != iProver_top
% 15.49/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.49/2.49      inference(equality_resolution_simp,[status(thm)],[c_53987]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_28,negated_conjecture,
% 15.49/2.49      ( k2_funct_1(sK2) != sK3 ),
% 15.49/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_3280,plain,
% 15.49/2.49      ( k4_relat_1(sK2) != sK3 ),
% 15.49/2.49      inference(demodulation,[status(thm)],[c_3276,c_28]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2336,plain,
% 15.49/2.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2337,plain,
% 15.49/2.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_2336]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1398,plain,
% 15.49/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 15.49/2.49      | ~ v1_relat_1(X0)
% 15.49/2.49      | v1_relat_1(sK3) ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_1562,plain,
% 15.49/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.49/2.49      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 15.49/2.49      | v1_relat_1(sK3) ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_1398]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2014,plain,
% 15.49/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.49/2.49      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 15.49/2.49      | v1_relat_1(sK3) ),
% 15.49/2.49      inference(instantiation,[status(thm)],[c_1562]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(c_2015,plain,
% 15.49/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.49/2.49      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 15.49/2.49      | v1_relat_1(sK3) = iProver_top ),
% 15.49/2.49      inference(predicate_to_equality,[status(thm)],[c_2014]) ).
% 15.49/2.49  
% 15.49/2.49  cnf(contradiction,plain,
% 15.49/2.49      ( $false ),
% 15.49/2.49      inference(minisat,
% 15.49/2.49                [status(thm)],
% 15.49/2.49                [c_53988,c_3280,c_2337,c_2015,c_45,c_43]) ).
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.49/2.49  
% 15.49/2.49  ------                               Statistics
% 15.49/2.49  
% 15.49/2.49  ------ General
% 15.49/2.49  
% 15.49/2.49  abstr_ref_over_cycles:                  0
% 15.49/2.49  abstr_ref_under_cycles:                 0
% 15.49/2.49  gc_basic_clause_elim:                   0
% 15.49/2.49  forced_gc_time:                         0
% 15.49/2.49  parsing_time:                           0.01
% 15.49/2.49  unif_index_cands_time:                  0.
% 15.49/2.49  unif_index_add_time:                    0.
% 15.49/2.49  orderings_time:                         0.
% 15.49/2.49  out_proof_time:                         0.021
% 15.49/2.49  total_time:                             1.838
% 15.49/2.49  num_of_symbols:                         54
% 15.49/2.49  num_of_terms:                           84809
% 15.49/2.49  
% 15.49/2.49  ------ Preprocessing
% 15.49/2.49  
% 15.49/2.49  num_of_splits:                          0
% 15.49/2.49  num_of_split_atoms:                     0
% 15.49/2.49  num_of_reused_defs:                     0
% 15.49/2.49  num_eq_ax_congr_red:                    24
% 15.49/2.49  num_of_sem_filtered_clauses:            1
% 15.49/2.49  num_of_subtypes:                        0
% 15.49/2.49  monotx_restored_types:                  0
% 15.49/2.49  sat_num_of_epr_types:                   0
% 15.49/2.49  sat_num_of_non_cyclic_types:            0
% 15.49/2.49  sat_guarded_non_collapsed_types:        0
% 15.49/2.49  num_pure_diseq_elim:                    0
% 15.49/2.49  simp_replaced_by:                       0
% 15.49/2.49  res_preprocessed:                       191
% 15.49/2.49  prep_upred:                             0
% 15.49/2.49  prep_unflattend:                        8
% 15.49/2.49  smt_new_axioms:                         0
% 15.49/2.49  pred_elim_cands:                        5
% 15.49/2.49  pred_elim:                              1
% 15.49/2.49  pred_elim_cl:                           2
% 15.49/2.49  pred_elim_cycles:                       3
% 15.49/2.49  merged_defs:                            0
% 15.49/2.49  merged_defs_ncl:                        0
% 15.49/2.49  bin_hyper_res:                          0
% 15.49/2.49  prep_cycles:                            4
% 15.49/2.49  pred_elim_time:                         0.002
% 15.49/2.49  splitting_time:                         0.
% 15.49/2.49  sem_filter_time:                        0.
% 15.49/2.49  monotx_time:                            0.
% 15.49/2.49  subtype_inf_time:                       0.
% 15.49/2.49  
% 15.49/2.49  ------ Problem properties
% 15.49/2.49  
% 15.49/2.49  clauses:                                38
% 15.49/2.49  conjectures:                            11
% 15.49/2.49  epr:                                    7
% 15.49/2.49  horn:                                   34
% 15.49/2.49  ground:                                 12
% 15.49/2.49  unary:                                  13
% 15.49/2.49  binary:                                 5
% 15.49/2.49  lits:                                   109
% 15.49/2.49  lits_eq:                                29
% 15.49/2.49  fd_pure:                                0
% 15.49/2.49  fd_pseudo:                              0
% 15.49/2.49  fd_cond:                                3
% 15.49/2.49  fd_pseudo_cond:                         1
% 15.49/2.49  ac_symbols:                             0
% 15.49/2.49  
% 15.49/2.49  ------ Propositional Solver
% 15.49/2.49  
% 15.49/2.49  prop_solver_calls:                      37
% 15.49/2.49  prop_fast_solver_calls:                 2138
% 15.49/2.49  smt_solver_calls:                       0
% 15.49/2.49  smt_fast_solver_calls:                  0
% 15.49/2.49  prop_num_of_clauses:                    20135
% 15.49/2.49  prop_preprocess_simplified:             30649
% 15.49/2.49  prop_fo_subsumed:                       136
% 15.49/2.49  prop_solver_time:                       0.
% 15.49/2.49  smt_solver_time:                        0.
% 15.49/2.49  smt_fast_solver_time:                   0.
% 15.49/2.49  prop_fast_solver_time:                  0.
% 15.49/2.49  prop_unsat_core_time:                   0.003
% 15.49/2.49  
% 15.49/2.49  ------ QBF
% 15.49/2.49  
% 15.49/2.49  qbf_q_res:                              0
% 15.49/2.49  qbf_num_tautologies:                    0
% 15.49/2.49  qbf_prep_cycles:                        0
% 15.49/2.49  
% 15.49/2.49  ------ BMC1
% 15.49/2.49  
% 15.49/2.49  bmc1_current_bound:                     -1
% 15.49/2.49  bmc1_last_solved_bound:                 -1
% 15.49/2.49  bmc1_unsat_core_size:                   -1
% 15.49/2.49  bmc1_unsat_core_parents_size:           -1
% 15.49/2.49  bmc1_merge_next_fun:                    0
% 15.49/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.49/2.49  
% 15.49/2.49  ------ Instantiation
% 15.49/2.49  
% 15.49/2.49  inst_num_of_clauses:                    6153
% 15.49/2.49  inst_num_in_passive:                    1979
% 15.49/2.49  inst_num_in_active:                     1999
% 15.49/2.49  inst_num_in_unprocessed:                2175
% 15.49/2.49  inst_num_of_loops:                      2110
% 15.49/2.49  inst_num_of_learning_restarts:          0
% 15.49/2.49  inst_num_moves_active_passive:          109
% 15.49/2.49  inst_lit_activity:                      0
% 15.49/2.49  inst_lit_activity_moves:                5
% 15.49/2.49  inst_num_tautologies:                   0
% 15.49/2.49  inst_num_prop_implied:                  0
% 15.49/2.49  inst_num_existing_simplified:           0
% 15.49/2.49  inst_num_eq_res_simplified:             0
% 15.49/2.49  inst_num_child_elim:                    0
% 15.49/2.49  inst_num_of_dismatching_blockings:      18004
% 15.49/2.49  inst_num_of_non_proper_insts:           9257
% 15.49/2.49  inst_num_of_duplicates:                 0
% 15.49/2.49  inst_inst_num_from_inst_to_res:         0
% 15.49/2.49  inst_dismatching_checking_time:         0.
% 15.49/2.49  
% 15.49/2.49  ------ Resolution
% 15.49/2.49  
% 15.49/2.49  res_num_of_clauses:                     0
% 15.49/2.49  res_num_in_passive:                     0
% 15.49/2.49  res_num_in_active:                      0
% 15.49/2.49  res_num_of_loops:                       195
% 15.49/2.49  res_forward_subset_subsumed:            129
% 15.49/2.49  res_backward_subset_subsumed:           2
% 15.49/2.49  res_forward_subsumed:                   0
% 15.49/2.49  res_backward_subsumed:                  0
% 15.49/2.49  res_forward_subsumption_resolution:     1
% 15.49/2.49  res_backward_subsumption_resolution:    0
% 15.49/2.49  res_clause_to_clause_subsumption:       5090
% 15.49/2.49  res_orphan_elimination:                 0
% 15.49/2.49  res_tautology_del:                      62
% 15.49/2.49  res_num_eq_res_simplified:              0
% 15.49/2.49  res_num_sel_changes:                    0
% 15.49/2.49  res_moves_from_active_to_pass:          0
% 15.49/2.49  
% 15.49/2.49  ------ Superposition
% 15.49/2.49  
% 15.49/2.49  sup_time_total:                         0.
% 15.49/2.49  sup_time_generating:                    0.
% 15.49/2.49  sup_time_sim_full:                      0.
% 15.49/2.49  sup_time_sim_immed:                     0.
% 15.49/2.49  
% 15.49/2.49  sup_num_of_clauses:                     2354
% 15.49/2.49  sup_num_in_active:                      387
% 15.49/2.49  sup_num_in_passive:                     1967
% 15.49/2.49  sup_num_of_loops:                       421
% 15.49/2.49  sup_fw_superposition:                   1436
% 15.49/2.49  sup_bw_superposition:                   1085
% 15.49/2.49  sup_immediate_simplified:               1496
% 15.49/2.49  sup_given_eliminated:                   0
% 15.49/2.49  comparisons_done:                       0
% 15.49/2.49  comparisons_avoided:                    1
% 15.49/2.49  
% 15.49/2.49  ------ Simplifications
% 15.49/2.49  
% 15.49/2.49  
% 15.49/2.49  sim_fw_subset_subsumed:                 30
% 15.49/2.49  sim_bw_subset_subsumed:                 23
% 15.49/2.49  sim_fw_subsumed:                        30
% 15.49/2.49  sim_bw_subsumed:                        2
% 15.49/2.49  sim_fw_subsumption_res:                 0
% 15.49/2.49  sim_bw_subsumption_res:                 0
% 15.49/2.49  sim_tautology_del:                      0
% 15.49/2.49  sim_eq_tautology_del:                   118
% 15.49/2.49  sim_eq_res_simp:                        1
% 15.49/2.49  sim_fw_demodulated:                     421
% 15.49/2.49  sim_bw_demodulated:                     27
% 15.49/2.49  sim_light_normalised:                   1057
% 15.49/2.49  sim_joinable_taut:                      0
% 15.49/2.49  sim_joinable_simp:                      0
% 15.49/2.49  sim_ac_normalised:                      0
% 15.49/2.49  sim_smt_subsumption:                    0
% 15.49/2.49  
%------------------------------------------------------------------------------
