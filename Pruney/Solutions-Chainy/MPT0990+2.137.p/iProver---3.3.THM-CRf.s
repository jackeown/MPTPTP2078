%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:26 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :  224 (2568 expanded)
%              Number of clauses        :  131 ( 734 expanded)
%              Number of leaves         :   24 ( 653 expanded)
%              Depth                    :   22
%              Number of atoms          :  835 (21517 expanded)
%              Number of equality atoms :  395 (7708 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f61,plain,(
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

fof(f60,plain,
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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f61,f60])).

fof(f100,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f103,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f105,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f98,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f82,f90])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f62])).

fof(f21,axiom,(
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

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f22,axiom,(
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

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f80,f90])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f23,axiom,(
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

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f111,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f90])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f109,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1448,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1451,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1459,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5955,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_1459])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_6298,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5955,c_49])).

cnf(c_6299,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6298])).

cnf(c_6307,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_6299])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_38])).

cnf(c_487,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_25,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_495,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_487,c_25])).

cnf(c_1444,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1809,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2287,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1444,c_45,c_43,c_42,c_40,c_495,c_1809])).

cnf(c_6308,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6307,c_2287])).

cnf(c_46,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_7213,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6308,c_46])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1464,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7215,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7213,c_1464])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1463,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3025,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1448,c_1463])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3026,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3025,c_39])).

cnf(c_3024,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1451,c_1463])).

cnf(c_27,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_499,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_38])).

cnf(c_500,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_592,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_500])).

cnf(c_1443,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_2004,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1443])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_47,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_50,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2294,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2004,c_46,c_47,c_48,c_49,c_50,c_51])).

cnf(c_3027,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3024,c_2294])).

cnf(c_7216,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7215,c_3026,c_3027])).

cnf(c_7217,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7216])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f94])).

cnf(c_1457,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5947,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_1457])).

cnf(c_6291,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5947,c_46,c_47,c_48])).

cnf(c_6292,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6291])).

cnf(c_6295,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2287,c_6292])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_138,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_142,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_815,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1580,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_1581,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_16,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_5204,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_5205,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5204])).

cnf(c_7143,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6295,c_49,c_50,c_51,c_36,c_138,c_142,c_1581,c_5205])).

cnf(c_1449,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1470,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3729,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1449,c_1470])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1599,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1918,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_2422,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_2423,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2422])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2825,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2826,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_4082,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3729,c_51,c_2423,c_2826])).

cnf(c_4083,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4082])).

cnf(c_7148,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_7143,c_4083])).

cnf(c_7218,plain,
    ( k1_relat_1(sK3) != sK1
    | k4_relat_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7217,c_7148])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2368,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2369,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2368])).

cnf(c_1478,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3655,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1478])).

cnf(c_3657,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3655])).

cnf(c_3826,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6296,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6295])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1468,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7156,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7148,c_1468])).

cnf(c_7219,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK3) != sK1
    | k4_relat_1(sK3) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7218])).

cnf(c_3654,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_1478])).

cnf(c_3808,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3654,c_51,c_2423,c_2826])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1472,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3815,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3808,c_1472])).

cnf(c_3817,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3815,c_3027])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1471,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4631,plain,
    ( k1_relat_1(k5_relat_1(sK3,X0)) = k1_relat_1(sK3)
    | r1_tarski(sK0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3027,c_1471])).

cnf(c_13198,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(sK0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(sK3,X0)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4631,c_51,c_2423,c_2826])).

cnf(c_13199,plain,
    ( k1_relat_1(k5_relat_1(sK3,X0)) = k1_relat_1(sK3)
    | r1_tarski(sK0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_13198])).

cnf(c_13208,plain,
    ( k1_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))) = k1_relat_1(sK3)
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3817,c_13199])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1453,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3006,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2294,c_1453])).

cnf(c_3049,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3006,c_49,c_50,c_51,c_36,c_138,c_142,c_1581])).

cnf(c_7149,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_7143,c_3049])).

cnf(c_7150,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_7148,c_7149])).

cnf(c_13233,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13208,c_7150])).

cnf(c_12,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_13234,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(sK0,sK0) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13233,c_12])).

cnf(c_32361,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7218,c_45,c_42,c_49,c_41,c_40,c_51,c_36,c_138,c_142,c_1581,c_2369,c_2422,c_2423,c_2825,c_2826,c_3657,c_3826,c_5204,c_6296,c_7156,c_7219,c_13234])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1476,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3816,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_3808,c_1476])).

cnf(c_32418,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_32361,c_3816])).

cnf(c_1446,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3730,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_1470])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3735,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3730])).

cnf(c_4087,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3730,c_37,c_3657,c_3735,c_3826])).

cnf(c_34,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_4091,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_4087,c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32418,c_4091])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:04:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.82/1.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.82/1.93  
% 11.82/1.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.82/1.93  
% 11.82/1.93  ------  iProver source info
% 11.82/1.93  
% 11.82/1.93  git: date: 2020-06-30 10:37:57 +0100
% 11.82/1.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.82/1.93  git: non_committed_changes: false
% 11.82/1.93  git: last_make_outside_of_git: false
% 11.82/1.93  
% 11.82/1.93  ------ 
% 11.82/1.93  
% 11.82/1.93  ------ Input Options
% 11.82/1.93  
% 11.82/1.93  --out_options                           all
% 11.82/1.93  --tptp_safe_out                         true
% 11.82/1.93  --problem_path                          ""
% 11.82/1.93  --include_path                          ""
% 11.82/1.93  --clausifier                            res/vclausify_rel
% 11.82/1.93  --clausifier_options                    ""
% 11.82/1.93  --stdin                                 false
% 11.82/1.93  --stats_out                             all
% 11.82/1.93  
% 11.82/1.93  ------ General Options
% 11.82/1.93  
% 11.82/1.93  --fof                                   false
% 11.82/1.93  --time_out_real                         305.
% 11.82/1.93  --time_out_virtual                      -1.
% 11.82/1.93  --symbol_type_check                     false
% 11.82/1.93  --clausify_out                          false
% 11.82/1.93  --sig_cnt_out                           false
% 11.82/1.93  --trig_cnt_out                          false
% 11.82/1.93  --trig_cnt_out_tolerance                1.
% 11.82/1.93  --trig_cnt_out_sk_spl                   false
% 11.82/1.93  --abstr_cl_out                          false
% 11.82/1.93  
% 11.82/1.93  ------ Global Options
% 11.82/1.93  
% 11.82/1.93  --schedule                              default
% 11.82/1.93  --add_important_lit                     false
% 11.82/1.93  --prop_solver_per_cl                    1000
% 11.82/1.93  --min_unsat_core                        false
% 11.82/1.93  --soft_assumptions                      false
% 11.82/1.93  --soft_lemma_size                       3
% 11.82/1.93  --prop_impl_unit_size                   0
% 11.82/1.93  --prop_impl_unit                        []
% 11.82/1.93  --share_sel_clauses                     true
% 11.82/1.93  --reset_solvers                         false
% 11.82/1.93  --bc_imp_inh                            [conj_cone]
% 11.82/1.93  --conj_cone_tolerance                   3.
% 11.82/1.93  --extra_neg_conj                        none
% 11.82/1.93  --large_theory_mode                     true
% 11.82/1.93  --prolific_symb_bound                   200
% 11.82/1.93  --lt_threshold                          2000
% 11.82/1.93  --clause_weak_htbl                      true
% 11.82/1.93  --gc_record_bc_elim                     false
% 11.82/1.93  
% 11.82/1.93  ------ Preprocessing Options
% 11.82/1.93  
% 11.82/1.93  --preprocessing_flag                    true
% 11.82/1.93  --time_out_prep_mult                    0.1
% 11.82/1.93  --splitting_mode                        input
% 11.82/1.93  --splitting_grd                         true
% 11.82/1.93  --splitting_cvd                         false
% 11.82/1.93  --splitting_cvd_svl                     false
% 11.82/1.93  --splitting_nvd                         32
% 11.82/1.93  --sub_typing                            true
% 11.82/1.93  --prep_gs_sim                           true
% 11.82/1.93  --prep_unflatten                        true
% 11.82/1.93  --prep_res_sim                          true
% 11.82/1.93  --prep_upred                            true
% 11.82/1.93  --prep_sem_filter                       exhaustive
% 11.82/1.93  --prep_sem_filter_out                   false
% 11.82/1.93  --pred_elim                             true
% 11.82/1.93  --res_sim_input                         true
% 11.82/1.93  --eq_ax_congr_red                       true
% 11.82/1.93  --pure_diseq_elim                       true
% 11.82/1.93  --brand_transform                       false
% 11.82/1.93  --non_eq_to_eq                          false
% 11.82/1.93  --prep_def_merge                        true
% 11.82/1.93  --prep_def_merge_prop_impl              false
% 11.82/1.93  --prep_def_merge_mbd                    true
% 11.82/1.93  --prep_def_merge_tr_red                 false
% 11.82/1.93  --prep_def_merge_tr_cl                  false
% 11.82/1.93  --smt_preprocessing                     true
% 11.82/1.93  --smt_ac_axioms                         fast
% 11.82/1.93  --preprocessed_out                      false
% 11.82/1.93  --preprocessed_stats                    false
% 11.82/1.93  
% 11.82/1.93  ------ Abstraction refinement Options
% 11.82/1.93  
% 11.82/1.93  --abstr_ref                             []
% 11.82/1.93  --abstr_ref_prep                        false
% 11.82/1.93  --abstr_ref_until_sat                   false
% 11.82/1.93  --abstr_ref_sig_restrict                funpre
% 11.82/1.93  --abstr_ref_af_restrict_to_split_sk     false
% 11.82/1.93  --abstr_ref_under                       []
% 11.82/1.93  
% 11.82/1.93  ------ SAT Options
% 11.82/1.93  
% 11.82/1.93  --sat_mode                              false
% 11.82/1.93  --sat_fm_restart_options                ""
% 11.82/1.93  --sat_gr_def                            false
% 11.82/1.93  --sat_epr_types                         true
% 11.82/1.93  --sat_non_cyclic_types                  false
% 11.82/1.93  --sat_finite_models                     false
% 11.82/1.93  --sat_fm_lemmas                         false
% 11.82/1.93  --sat_fm_prep                           false
% 11.82/1.93  --sat_fm_uc_incr                        true
% 11.82/1.93  --sat_out_model                         small
% 11.82/1.93  --sat_out_clauses                       false
% 11.82/1.93  
% 11.82/1.93  ------ QBF Options
% 11.82/1.93  
% 11.82/1.93  --qbf_mode                              false
% 11.82/1.93  --qbf_elim_univ                         false
% 11.82/1.93  --qbf_dom_inst                          none
% 11.82/1.93  --qbf_dom_pre_inst                      false
% 11.82/1.93  --qbf_sk_in                             false
% 11.82/1.93  --qbf_pred_elim                         true
% 11.82/1.93  --qbf_split                             512
% 11.82/1.93  
% 11.82/1.93  ------ BMC1 Options
% 11.82/1.93  
% 11.82/1.93  --bmc1_incremental                      false
% 11.82/1.93  --bmc1_axioms                           reachable_all
% 11.82/1.93  --bmc1_min_bound                        0
% 11.82/1.93  --bmc1_max_bound                        -1
% 11.82/1.93  --bmc1_max_bound_default                -1
% 11.82/1.93  --bmc1_symbol_reachability              true
% 11.82/1.93  --bmc1_property_lemmas                  false
% 11.82/1.93  --bmc1_k_induction                      false
% 11.82/1.93  --bmc1_non_equiv_states                 false
% 11.82/1.93  --bmc1_deadlock                         false
% 11.82/1.93  --bmc1_ucm                              false
% 11.82/1.93  --bmc1_add_unsat_core                   none
% 11.82/1.93  --bmc1_unsat_core_children              false
% 11.82/1.93  --bmc1_unsat_core_extrapolate_axioms    false
% 11.82/1.93  --bmc1_out_stat                         full
% 11.82/1.93  --bmc1_ground_init                      false
% 11.82/1.93  --bmc1_pre_inst_next_state              false
% 11.82/1.93  --bmc1_pre_inst_state                   false
% 11.82/1.93  --bmc1_pre_inst_reach_state             false
% 11.82/1.93  --bmc1_out_unsat_core                   false
% 11.82/1.93  --bmc1_aig_witness_out                  false
% 11.82/1.93  --bmc1_verbose                          false
% 11.82/1.93  --bmc1_dump_clauses_tptp                false
% 11.82/1.93  --bmc1_dump_unsat_core_tptp             false
% 11.82/1.93  --bmc1_dump_file                        -
% 11.82/1.93  --bmc1_ucm_expand_uc_limit              128
% 11.82/1.93  --bmc1_ucm_n_expand_iterations          6
% 11.82/1.93  --bmc1_ucm_extend_mode                  1
% 11.82/1.93  --bmc1_ucm_init_mode                    2
% 11.82/1.93  --bmc1_ucm_cone_mode                    none
% 11.82/1.93  --bmc1_ucm_reduced_relation_type        0
% 11.82/1.93  --bmc1_ucm_relax_model                  4
% 11.82/1.93  --bmc1_ucm_full_tr_after_sat            true
% 11.82/1.93  --bmc1_ucm_expand_neg_assumptions       false
% 11.82/1.93  --bmc1_ucm_layered_model                none
% 11.82/1.93  --bmc1_ucm_max_lemma_size               10
% 11.82/1.93  
% 11.82/1.93  ------ AIG Options
% 11.82/1.93  
% 11.82/1.93  --aig_mode                              false
% 11.82/1.93  
% 11.82/1.93  ------ Instantiation Options
% 11.82/1.93  
% 11.82/1.93  --instantiation_flag                    true
% 11.82/1.93  --inst_sos_flag                         true
% 11.82/1.93  --inst_sos_phase                        true
% 11.82/1.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.82/1.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.82/1.93  --inst_lit_sel_side                     num_symb
% 11.82/1.93  --inst_solver_per_active                1400
% 11.82/1.93  --inst_solver_calls_frac                1.
% 11.82/1.93  --inst_passive_queue_type               priority_queues
% 11.82/1.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.82/1.93  --inst_passive_queues_freq              [25;2]
% 11.82/1.93  --inst_dismatching                      true
% 11.82/1.93  --inst_eager_unprocessed_to_passive     true
% 11.82/1.93  --inst_prop_sim_given                   true
% 11.82/1.93  --inst_prop_sim_new                     false
% 11.82/1.93  --inst_subs_new                         false
% 11.82/1.93  --inst_eq_res_simp                      false
% 11.82/1.93  --inst_subs_given                       false
% 11.82/1.93  --inst_orphan_elimination               true
% 11.82/1.93  --inst_learning_loop_flag               true
% 11.82/1.93  --inst_learning_start                   3000
% 11.82/1.93  --inst_learning_factor                  2
% 11.82/1.93  --inst_start_prop_sim_after_learn       3
% 11.82/1.93  --inst_sel_renew                        solver
% 11.82/1.93  --inst_lit_activity_flag                true
% 11.82/1.93  --inst_restr_to_given                   false
% 11.82/1.93  --inst_activity_threshold               500
% 11.82/1.93  --inst_out_proof                        true
% 11.82/1.93  
% 11.82/1.93  ------ Resolution Options
% 11.82/1.93  
% 11.82/1.93  --resolution_flag                       true
% 11.82/1.93  --res_lit_sel                           adaptive
% 11.82/1.93  --res_lit_sel_side                      none
% 11.82/1.93  --res_ordering                          kbo
% 11.82/1.93  --res_to_prop_solver                    active
% 11.82/1.93  --res_prop_simpl_new                    false
% 11.82/1.93  --res_prop_simpl_given                  true
% 11.82/1.93  --res_passive_queue_type                priority_queues
% 11.82/1.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.82/1.93  --res_passive_queues_freq               [15;5]
% 11.82/1.93  --res_forward_subs                      full
% 11.82/1.93  --res_backward_subs                     full
% 11.82/1.93  --res_forward_subs_resolution           true
% 11.82/1.93  --res_backward_subs_resolution          true
% 11.82/1.93  --res_orphan_elimination                true
% 11.82/1.93  --res_time_limit                        2.
% 11.82/1.93  --res_out_proof                         true
% 11.82/1.93  
% 11.82/1.93  ------ Superposition Options
% 11.82/1.93  
% 11.82/1.93  --superposition_flag                    true
% 11.82/1.93  --sup_passive_queue_type                priority_queues
% 11.82/1.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.82/1.93  --sup_passive_queues_freq               [8;1;4]
% 11.82/1.93  --demod_completeness_check              fast
% 11.82/1.93  --demod_use_ground                      true
% 11.82/1.93  --sup_to_prop_solver                    passive
% 11.82/1.93  --sup_prop_simpl_new                    true
% 11.82/1.93  --sup_prop_simpl_given                  true
% 11.82/1.93  --sup_fun_splitting                     true
% 11.82/1.93  --sup_smt_interval                      50000
% 11.82/1.93  
% 11.82/1.93  ------ Superposition Simplification Setup
% 11.82/1.93  
% 11.82/1.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.82/1.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.82/1.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.82/1.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.82/1.93  --sup_full_triv                         [TrivRules;PropSubs]
% 11.82/1.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.82/1.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.82/1.93  --sup_immed_triv                        [TrivRules]
% 11.82/1.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/1.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/1.93  --sup_immed_bw_main                     []
% 11.82/1.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.82/1.93  --sup_input_triv                        [Unflattening;TrivRules]
% 11.82/1.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/1.93  --sup_input_bw                          []
% 11.82/1.93  
% 11.82/1.93  ------ Combination Options
% 11.82/1.93  
% 11.82/1.93  --comb_res_mult                         3
% 11.82/1.93  --comb_sup_mult                         2
% 11.82/1.93  --comb_inst_mult                        10
% 11.82/1.93  
% 11.82/1.93  ------ Debug Options
% 11.82/1.93  
% 11.82/1.93  --dbg_backtrace                         false
% 11.82/1.93  --dbg_dump_prop_clauses                 false
% 11.82/1.93  --dbg_dump_prop_clauses_file            -
% 11.82/1.93  --dbg_out_stat                          false
% 11.82/1.93  ------ Parsing...
% 11.82/1.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.82/1.93  
% 11.82/1.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.82/1.93  
% 11.82/1.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.82/1.93  
% 11.82/1.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.82/1.93  ------ Proving...
% 11.82/1.93  ------ Problem Properties 
% 11.82/1.93  
% 11.82/1.93  
% 11.82/1.93  clauses                                 44
% 11.82/1.93  conjectures                             11
% 11.82/1.93  EPR                                     9
% 11.82/1.93  Horn                                    40
% 11.82/1.93  unary                                   18
% 11.82/1.93  binary                                  7
% 11.82/1.93  lits                                    147
% 11.82/1.93  lits eq                                 37
% 11.82/1.93  fd_pure                                 0
% 11.82/1.93  fd_pseudo                               0
% 11.82/1.93  fd_cond                                 4
% 11.82/1.93  fd_pseudo_cond                          2
% 11.82/1.93  AC symbols                              0
% 11.82/1.93  
% 11.82/1.93  ------ Schedule dynamic 5 is on 
% 11.82/1.93  
% 11.82/1.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.82/1.93  
% 11.82/1.93  
% 11.82/1.93  ------ 
% 11.82/1.93  Current options:
% 11.82/1.93  ------ 
% 11.82/1.93  
% 11.82/1.93  ------ Input Options
% 11.82/1.93  
% 11.82/1.93  --out_options                           all
% 11.82/1.93  --tptp_safe_out                         true
% 11.82/1.93  --problem_path                          ""
% 11.82/1.93  --include_path                          ""
% 11.82/1.93  --clausifier                            res/vclausify_rel
% 11.82/1.93  --clausifier_options                    ""
% 11.82/1.93  --stdin                                 false
% 11.82/1.93  --stats_out                             all
% 11.82/1.93  
% 11.82/1.93  ------ General Options
% 11.82/1.93  
% 11.82/1.93  --fof                                   false
% 11.82/1.93  --time_out_real                         305.
% 11.82/1.93  --time_out_virtual                      -1.
% 11.82/1.93  --symbol_type_check                     false
% 11.82/1.93  --clausify_out                          false
% 11.82/1.93  --sig_cnt_out                           false
% 11.82/1.93  --trig_cnt_out                          false
% 11.82/1.93  --trig_cnt_out_tolerance                1.
% 11.82/1.93  --trig_cnt_out_sk_spl                   false
% 11.82/1.93  --abstr_cl_out                          false
% 11.82/1.93  
% 11.82/1.93  ------ Global Options
% 11.82/1.93  
% 11.82/1.93  --schedule                              default
% 11.82/1.93  --add_important_lit                     false
% 11.82/1.93  --prop_solver_per_cl                    1000
% 11.82/1.93  --min_unsat_core                        false
% 11.82/1.93  --soft_assumptions                      false
% 11.82/1.93  --soft_lemma_size                       3
% 11.82/1.93  --prop_impl_unit_size                   0
% 11.82/1.93  --prop_impl_unit                        []
% 11.82/1.93  --share_sel_clauses                     true
% 11.82/1.93  --reset_solvers                         false
% 11.82/1.93  --bc_imp_inh                            [conj_cone]
% 11.82/1.93  --conj_cone_tolerance                   3.
% 11.82/1.93  --extra_neg_conj                        none
% 11.82/1.93  --large_theory_mode                     true
% 11.82/1.93  --prolific_symb_bound                   200
% 11.82/1.93  --lt_threshold                          2000
% 11.82/1.93  --clause_weak_htbl                      true
% 11.82/1.93  --gc_record_bc_elim                     false
% 11.82/1.93  
% 11.82/1.93  ------ Preprocessing Options
% 11.82/1.93  
% 11.82/1.93  --preprocessing_flag                    true
% 11.82/1.93  --time_out_prep_mult                    0.1
% 11.82/1.93  --splitting_mode                        input
% 11.82/1.93  --splitting_grd                         true
% 11.82/1.93  --splitting_cvd                         false
% 11.82/1.93  --splitting_cvd_svl                     false
% 11.82/1.93  --splitting_nvd                         32
% 11.82/1.93  --sub_typing                            true
% 11.82/1.93  --prep_gs_sim                           true
% 11.82/1.93  --prep_unflatten                        true
% 11.82/1.93  --prep_res_sim                          true
% 11.82/1.93  --prep_upred                            true
% 11.82/1.93  --prep_sem_filter                       exhaustive
% 11.82/1.93  --prep_sem_filter_out                   false
% 11.82/1.93  --pred_elim                             true
% 11.82/1.93  --res_sim_input                         true
% 11.82/1.93  --eq_ax_congr_red                       true
% 11.82/1.93  --pure_diseq_elim                       true
% 11.82/1.93  --brand_transform                       false
% 11.82/1.93  --non_eq_to_eq                          false
% 11.82/1.93  --prep_def_merge                        true
% 11.82/1.93  --prep_def_merge_prop_impl              false
% 11.82/1.93  --prep_def_merge_mbd                    true
% 11.82/1.93  --prep_def_merge_tr_red                 false
% 11.82/1.93  --prep_def_merge_tr_cl                  false
% 11.82/1.93  --smt_preprocessing                     true
% 11.82/1.93  --smt_ac_axioms                         fast
% 11.82/1.93  --preprocessed_out                      false
% 11.82/1.93  --preprocessed_stats                    false
% 11.82/1.93  
% 11.82/1.93  ------ Abstraction refinement Options
% 11.82/1.93  
% 11.82/1.93  --abstr_ref                             []
% 11.82/1.93  --abstr_ref_prep                        false
% 11.82/1.93  --abstr_ref_until_sat                   false
% 11.82/1.93  --abstr_ref_sig_restrict                funpre
% 11.82/1.93  --abstr_ref_af_restrict_to_split_sk     false
% 11.82/1.93  --abstr_ref_under                       []
% 11.82/1.93  
% 11.82/1.93  ------ SAT Options
% 11.82/1.93  
% 11.82/1.93  --sat_mode                              false
% 11.82/1.93  --sat_fm_restart_options                ""
% 11.82/1.93  --sat_gr_def                            false
% 11.82/1.93  --sat_epr_types                         true
% 11.82/1.93  --sat_non_cyclic_types                  false
% 11.82/1.93  --sat_finite_models                     false
% 11.82/1.93  --sat_fm_lemmas                         false
% 11.82/1.93  --sat_fm_prep                           false
% 11.82/1.93  --sat_fm_uc_incr                        true
% 11.82/1.93  --sat_out_model                         small
% 11.82/1.93  --sat_out_clauses                       false
% 11.82/1.93  
% 11.82/1.93  ------ QBF Options
% 11.82/1.93  
% 11.82/1.93  --qbf_mode                              false
% 11.82/1.93  --qbf_elim_univ                         false
% 11.82/1.93  --qbf_dom_inst                          none
% 11.82/1.93  --qbf_dom_pre_inst                      false
% 11.82/1.93  --qbf_sk_in                             false
% 11.82/1.93  --qbf_pred_elim                         true
% 11.82/1.93  --qbf_split                             512
% 11.82/1.93  
% 11.82/1.93  ------ BMC1 Options
% 11.82/1.93  
% 11.82/1.93  --bmc1_incremental                      false
% 11.82/1.93  --bmc1_axioms                           reachable_all
% 11.82/1.93  --bmc1_min_bound                        0
% 11.82/1.93  --bmc1_max_bound                        -1
% 11.82/1.93  --bmc1_max_bound_default                -1
% 11.82/1.93  --bmc1_symbol_reachability              true
% 11.82/1.93  --bmc1_property_lemmas                  false
% 11.82/1.93  --bmc1_k_induction                      false
% 11.82/1.93  --bmc1_non_equiv_states                 false
% 11.82/1.93  --bmc1_deadlock                         false
% 11.82/1.93  --bmc1_ucm                              false
% 11.82/1.93  --bmc1_add_unsat_core                   none
% 11.82/1.93  --bmc1_unsat_core_children              false
% 11.82/1.93  --bmc1_unsat_core_extrapolate_axioms    false
% 11.82/1.93  --bmc1_out_stat                         full
% 11.82/1.93  --bmc1_ground_init                      false
% 11.82/1.93  --bmc1_pre_inst_next_state              false
% 11.82/1.93  --bmc1_pre_inst_state                   false
% 11.82/1.93  --bmc1_pre_inst_reach_state             false
% 11.82/1.93  --bmc1_out_unsat_core                   false
% 11.82/1.93  --bmc1_aig_witness_out                  false
% 11.82/1.93  --bmc1_verbose                          false
% 11.82/1.93  --bmc1_dump_clauses_tptp                false
% 11.82/1.93  --bmc1_dump_unsat_core_tptp             false
% 11.82/1.93  --bmc1_dump_file                        -
% 11.82/1.93  --bmc1_ucm_expand_uc_limit              128
% 11.82/1.93  --bmc1_ucm_n_expand_iterations          6
% 11.82/1.93  --bmc1_ucm_extend_mode                  1
% 11.82/1.93  --bmc1_ucm_init_mode                    2
% 11.82/1.93  --bmc1_ucm_cone_mode                    none
% 11.82/1.93  --bmc1_ucm_reduced_relation_type        0
% 11.82/1.93  --bmc1_ucm_relax_model                  4
% 11.82/1.93  --bmc1_ucm_full_tr_after_sat            true
% 11.82/1.93  --bmc1_ucm_expand_neg_assumptions       false
% 11.82/1.93  --bmc1_ucm_layered_model                none
% 11.82/1.93  --bmc1_ucm_max_lemma_size               10
% 11.82/1.93  
% 11.82/1.93  ------ AIG Options
% 11.82/1.93  
% 11.82/1.93  --aig_mode                              false
% 11.82/1.93  
% 11.82/1.93  ------ Instantiation Options
% 11.82/1.93  
% 11.82/1.93  --instantiation_flag                    true
% 11.82/1.93  --inst_sos_flag                         true
% 11.82/1.93  --inst_sos_phase                        true
% 11.82/1.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.82/1.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.82/1.93  --inst_lit_sel_side                     none
% 11.82/1.93  --inst_solver_per_active                1400
% 11.82/1.93  --inst_solver_calls_frac                1.
% 11.82/1.93  --inst_passive_queue_type               priority_queues
% 11.82/1.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.82/1.93  --inst_passive_queues_freq              [25;2]
% 11.82/1.93  --inst_dismatching                      true
% 11.82/1.93  --inst_eager_unprocessed_to_passive     true
% 11.82/1.93  --inst_prop_sim_given                   true
% 11.82/1.93  --inst_prop_sim_new                     false
% 11.82/1.93  --inst_subs_new                         false
% 11.82/1.93  --inst_eq_res_simp                      false
% 11.82/1.93  --inst_subs_given                       false
% 11.82/1.93  --inst_orphan_elimination               true
% 11.82/1.93  --inst_learning_loop_flag               true
% 11.82/1.93  --inst_learning_start                   3000
% 11.82/1.93  --inst_learning_factor                  2
% 11.82/1.93  --inst_start_prop_sim_after_learn       3
% 11.82/1.93  --inst_sel_renew                        solver
% 11.82/1.93  --inst_lit_activity_flag                true
% 11.82/1.93  --inst_restr_to_given                   false
% 11.82/1.93  --inst_activity_threshold               500
% 11.82/1.93  --inst_out_proof                        true
% 11.82/1.93  
% 11.82/1.93  ------ Resolution Options
% 11.82/1.93  
% 11.82/1.93  --resolution_flag                       false
% 11.82/1.93  --res_lit_sel                           adaptive
% 11.82/1.93  --res_lit_sel_side                      none
% 11.82/1.93  --res_ordering                          kbo
% 11.82/1.93  --res_to_prop_solver                    active
% 11.82/1.93  --res_prop_simpl_new                    false
% 11.82/1.93  --res_prop_simpl_given                  true
% 11.82/1.93  --res_passive_queue_type                priority_queues
% 11.82/1.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.82/1.93  --res_passive_queues_freq               [15;5]
% 11.82/1.93  --res_forward_subs                      full
% 11.82/1.93  --res_backward_subs                     full
% 11.82/1.93  --res_forward_subs_resolution           true
% 11.82/1.93  --res_backward_subs_resolution          true
% 11.82/1.93  --res_orphan_elimination                true
% 11.82/1.93  --res_time_limit                        2.
% 11.82/1.93  --res_out_proof                         true
% 11.82/1.93  
% 11.82/1.93  ------ Superposition Options
% 11.82/1.93  
% 11.82/1.93  --superposition_flag                    true
% 11.82/1.93  --sup_passive_queue_type                priority_queues
% 11.82/1.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.82/1.93  --sup_passive_queues_freq               [8;1;4]
% 11.82/1.93  --demod_completeness_check              fast
% 11.82/1.93  --demod_use_ground                      true
% 11.82/1.93  --sup_to_prop_solver                    passive
% 11.82/1.93  --sup_prop_simpl_new                    true
% 11.82/1.93  --sup_prop_simpl_given                  true
% 11.82/1.93  --sup_fun_splitting                     true
% 11.82/1.93  --sup_smt_interval                      50000
% 11.82/1.93  
% 11.82/1.93  ------ Superposition Simplification Setup
% 11.82/1.93  
% 11.82/1.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.82/1.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.82/1.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.82/1.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.82/1.93  --sup_full_triv                         [TrivRules;PropSubs]
% 11.82/1.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.82/1.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.82/1.93  --sup_immed_triv                        [TrivRules]
% 11.82/1.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/1.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/1.93  --sup_immed_bw_main                     []
% 11.82/1.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.82/1.93  --sup_input_triv                        [Unflattening;TrivRules]
% 11.82/1.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.82/1.93  --sup_input_bw                          []
% 11.82/1.93  
% 11.82/1.93  ------ Combination Options
% 11.82/1.93  
% 11.82/1.93  --comb_res_mult                         3
% 11.82/1.93  --comb_sup_mult                         2
% 11.82/1.93  --comb_inst_mult                        10
% 11.82/1.93  
% 11.82/1.93  ------ Debug Options
% 11.82/1.93  
% 11.82/1.93  --dbg_backtrace                         false
% 11.82/1.93  --dbg_dump_prop_clauses                 false
% 11.82/1.93  --dbg_dump_prop_clauses_file            -
% 11.82/1.93  --dbg_out_stat                          false
% 11.82/1.93  
% 11.82/1.93  
% 11.82/1.93  
% 11.82/1.93  
% 11.82/1.93  ------ Proving...
% 11.82/1.93  
% 11.82/1.93  
% 11.82/1.93  % SZS status Theorem for theBenchmark.p
% 11.82/1.93  
% 11.82/1.93  % SZS output start CNFRefutation for theBenchmark.p
% 11.82/1.93  
% 11.82/1.93  fof(f24,conjecture,(
% 11.82/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f25,negated_conjecture,(
% 11.82/1.93    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.82/1.93    inference(negated_conjecture,[],[f24])).
% 11.82/1.93  
% 11.82/1.93  fof(f55,plain,(
% 11.82/1.93    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.82/1.93    inference(ennf_transformation,[],[f25])).
% 11.82/1.93  
% 11.82/1.93  fof(f56,plain,(
% 11.82/1.93    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.82/1.93    inference(flattening,[],[f55])).
% 11.82/1.93  
% 11.82/1.93  fof(f61,plain,(
% 11.82/1.93    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 11.82/1.93    introduced(choice_axiom,[])).
% 11.82/1.93  
% 11.82/1.93  fof(f60,plain,(
% 11.82/1.93    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 11.82/1.93    introduced(choice_axiom,[])).
% 11.82/1.93  
% 11.82/1.93  fof(f62,plain,(
% 11.82/1.93    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 11.82/1.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f61,f60])).
% 11.82/1.93  
% 11.82/1.93  fof(f100,plain,(
% 11.82/1.93    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f103,plain,(
% 11.82/1.93    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f19,axiom,(
% 11.82/1.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f47,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.82/1.93    inference(ennf_transformation,[],[f19])).
% 11.82/1.93  
% 11.82/1.93  fof(f48,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.82/1.93    inference(flattening,[],[f47])).
% 11.82/1.93  
% 11.82/1.93  fof(f89,plain,(
% 11.82/1.93    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f48])).
% 11.82/1.93  
% 11.82/1.93  fof(f101,plain,(
% 11.82/1.93    v1_funct_1(sK3)),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f16,axiom,(
% 11.82/1.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f43,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.82/1.93    inference(ennf_transformation,[],[f16])).
% 11.82/1.93  
% 11.82/1.93  fof(f44,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.82/1.93    inference(flattening,[],[f43])).
% 11.82/1.93  
% 11.82/1.93  fof(f59,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.82/1.93    inference(nnf_transformation,[],[f44])).
% 11.82/1.93  
% 11.82/1.93  fof(f84,plain,(
% 11.82/1.93    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.82/1.93    inference(cnf_transformation,[],[f59])).
% 11.82/1.93  
% 11.82/1.93  fof(f105,plain,(
% 11.82/1.93    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f18,axiom,(
% 11.82/1.93    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f26,plain,(
% 11.82/1.93    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.82/1.93    inference(pure_predicate_removal,[],[f18])).
% 11.82/1.93  
% 11.82/1.93  fof(f88,plain,(
% 11.82/1.93    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.82/1.93    inference(cnf_transformation,[],[f26])).
% 11.82/1.93  
% 11.82/1.93  fof(f98,plain,(
% 11.82/1.93    v1_funct_1(sK2)),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f17,axiom,(
% 11.82/1.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f45,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.82/1.93    inference(ennf_transformation,[],[f17])).
% 11.82/1.93  
% 11.82/1.93  fof(f46,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.82/1.93    inference(flattening,[],[f45])).
% 11.82/1.93  
% 11.82/1.93  fof(f87,plain,(
% 11.82/1.93    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f46])).
% 11.82/1.93  
% 11.82/1.93  fof(f14,axiom,(
% 11.82/1.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f40,plain,(
% 11.82/1.93    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.82/1.93    inference(ennf_transformation,[],[f14])).
% 11.82/1.93  
% 11.82/1.93  fof(f41,plain,(
% 11.82/1.93    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.82/1.93    inference(flattening,[],[f40])).
% 11.82/1.93  
% 11.82/1.93  fof(f82,plain,(
% 11.82/1.93    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f41])).
% 11.82/1.93  
% 11.82/1.93  fof(f20,axiom,(
% 11.82/1.93    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f90,plain,(
% 11.82/1.93    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f20])).
% 11.82/1.93  
% 11.82/1.93  fof(f114,plain,(
% 11.82/1.93    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.82/1.93    inference(definition_unfolding,[],[f82,f90])).
% 11.82/1.93  
% 11.82/1.93  fof(f15,axiom,(
% 11.82/1.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f42,plain,(
% 11.82/1.93    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.82/1.93    inference(ennf_transformation,[],[f15])).
% 11.82/1.93  
% 11.82/1.93  fof(f83,plain,(
% 11.82/1.93    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.82/1.93    inference(cnf_transformation,[],[f42])).
% 11.82/1.93  
% 11.82/1.93  fof(f104,plain,(
% 11.82/1.93    k2_relset_1(sK0,sK1,sK2) = sK1),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f21,axiom,(
% 11.82/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f49,plain,(
% 11.82/1.93    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.82/1.93    inference(ennf_transformation,[],[f21])).
% 11.82/1.93  
% 11.82/1.93  fof(f50,plain,(
% 11.82/1.93    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.82/1.93    inference(flattening,[],[f49])).
% 11.82/1.93  
% 11.82/1.93  fof(f91,plain,(
% 11.82/1.93    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f50])).
% 11.82/1.93  
% 11.82/1.93  fof(f99,plain,(
% 11.82/1.93    v1_funct_2(sK2,sK0,sK1)),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f102,plain,(
% 11.82/1.93    v1_funct_2(sK3,sK1,sK0)),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f22,axiom,(
% 11.82/1.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f51,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.82/1.93    inference(ennf_transformation,[],[f22])).
% 11.82/1.93  
% 11.82/1.93  fof(f52,plain,(
% 11.82/1.93    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.82/1.93    inference(flattening,[],[f51])).
% 11.82/1.93  
% 11.82/1.93  fof(f94,plain,(
% 11.82/1.93    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f52])).
% 11.82/1.93  
% 11.82/1.93  fof(f107,plain,(
% 11.82/1.93    k1_xboole_0 != sK0),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f1,axiom,(
% 11.82/1.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f57,plain,(
% 11.82/1.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.82/1.93    inference(nnf_transformation,[],[f1])).
% 11.82/1.93  
% 11.82/1.93  fof(f58,plain,(
% 11.82/1.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.82/1.93    inference(flattening,[],[f57])).
% 11.82/1.93  
% 11.82/1.93  fof(f63,plain,(
% 11.82/1.93    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.82/1.93    inference(cnf_transformation,[],[f58])).
% 11.82/1.93  
% 11.82/1.93  fof(f116,plain,(
% 11.82/1.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.82/1.93    inference(equality_resolution,[],[f63])).
% 11.82/1.93  
% 11.82/1.93  fof(f65,plain,(
% 11.82/1.93    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f58])).
% 11.82/1.93  
% 11.82/1.93  fof(f12,axiom,(
% 11.82/1.93    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f80,plain,(
% 11.82/1.93    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.82/1.93    inference(cnf_transformation,[],[f12])).
% 11.82/1.93  
% 11.82/1.93  fof(f112,plain,(
% 11.82/1.93    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 11.82/1.93    inference(definition_unfolding,[],[f80,f90])).
% 11.82/1.93  
% 11.82/1.93  fof(f10,axiom,(
% 11.82/1.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f34,plain,(
% 11.82/1.93    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.82/1.93    inference(ennf_transformation,[],[f10])).
% 11.82/1.93  
% 11.82/1.93  fof(f35,plain,(
% 11.82/1.93    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.82/1.93    inference(flattening,[],[f34])).
% 11.82/1.93  
% 11.82/1.93  fof(f76,plain,(
% 11.82/1.93    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f35])).
% 11.82/1.93  
% 11.82/1.93  fof(f2,axiom,(
% 11.82/1.93    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f27,plain,(
% 11.82/1.93    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.82/1.93    inference(ennf_transformation,[],[f2])).
% 11.82/1.93  
% 11.82/1.93  fof(f66,plain,(
% 11.82/1.93    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f27])).
% 11.82/1.93  
% 11.82/1.93  fof(f3,axiom,(
% 11.82/1.93    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f67,plain,(
% 11.82/1.93    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.82/1.93    inference(cnf_transformation,[],[f3])).
% 11.82/1.93  
% 11.82/1.93  fof(f64,plain,(
% 11.82/1.93    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.82/1.93    inference(cnf_transformation,[],[f58])).
% 11.82/1.93  
% 11.82/1.93  fof(f115,plain,(
% 11.82/1.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.82/1.93    inference(equality_resolution,[],[f64])).
% 11.82/1.93  
% 11.82/1.93  fof(f11,axiom,(
% 11.82/1.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f36,plain,(
% 11.82/1.93    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.82/1.93    inference(ennf_transformation,[],[f11])).
% 11.82/1.93  
% 11.82/1.93  fof(f37,plain,(
% 11.82/1.93    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.82/1.93    inference(flattening,[],[f36])).
% 11.82/1.93  
% 11.82/1.93  fof(f77,plain,(
% 11.82/1.93    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f37])).
% 11.82/1.93  
% 11.82/1.93  fof(f7,axiom,(
% 11.82/1.93    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f31,plain,(
% 11.82/1.93    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 11.82/1.93    inference(ennf_transformation,[],[f7])).
% 11.82/1.93  
% 11.82/1.93  fof(f71,plain,(
% 11.82/1.93    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f31])).
% 11.82/1.93  
% 11.82/1.93  fof(f8,axiom,(
% 11.82/1.93    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f32,plain,(
% 11.82/1.93    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.82/1.93    inference(ennf_transformation,[],[f8])).
% 11.82/1.93  
% 11.82/1.93  fof(f33,plain,(
% 11.82/1.93    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.82/1.93    inference(flattening,[],[f32])).
% 11.82/1.93  
% 11.82/1.93  fof(f73,plain,(
% 11.82/1.93    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f33])).
% 11.82/1.93  
% 11.82/1.93  fof(f23,axiom,(
% 11.82/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f53,plain,(
% 11.82/1.93    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.82/1.93    inference(ennf_transformation,[],[f23])).
% 11.82/1.93  
% 11.82/1.93  fof(f54,plain,(
% 11.82/1.93    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.82/1.93    inference(flattening,[],[f53])).
% 11.82/1.93  
% 11.82/1.93  fof(f96,plain,(
% 11.82/1.93    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f54])).
% 11.82/1.93  
% 11.82/1.93  fof(f9,axiom,(
% 11.82/1.93    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f74,plain,(
% 11.82/1.93    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.82/1.93    inference(cnf_transformation,[],[f9])).
% 11.82/1.93  
% 11.82/1.93  fof(f111,plain,(
% 11.82/1.93    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 11.82/1.93    inference(definition_unfolding,[],[f74,f90])).
% 11.82/1.93  
% 11.82/1.93  fof(f4,axiom,(
% 11.82/1.93    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 11.82/1.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.82/1.93  
% 11.82/1.93  fof(f28,plain,(
% 11.82/1.93    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 11.82/1.93    inference(ennf_transformation,[],[f4])).
% 11.82/1.93  
% 11.82/1.93  fof(f68,plain,(
% 11.82/1.93    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 11.82/1.93    inference(cnf_transformation,[],[f28])).
% 11.82/1.93  
% 11.82/1.93  fof(f106,plain,(
% 11.82/1.93    v2_funct_1(sK2)),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  fof(f109,plain,(
% 11.82/1.93    k2_funct_1(sK2) != sK3),
% 11.82/1.93    inference(cnf_transformation,[],[f62])).
% 11.82/1.93  
% 11.82/1.93  cnf(c_43,negated_conjecture,
% 11.82/1.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.82/1.93      inference(cnf_transformation,[],[f100]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1448,plain,
% 11.82/1.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_40,negated_conjecture,
% 11.82/1.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 11.82/1.93      inference(cnf_transformation,[],[f103]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1451,plain,
% 11.82/1.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_26,plain,
% 11.82/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.82/1.93      | ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v1_funct_1(X3)
% 11.82/1.93      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f89]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1459,plain,
% 11.82/1.93      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.82/1.93      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.82/1.93      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.82/1.93      | v1_funct_1(X5) != iProver_top
% 11.82/1.93      | v1_funct_1(X4) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_5955,plain,
% 11.82/1.93      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.82/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.82/1.93      | v1_funct_1(X2) != iProver_top
% 11.82/1.93      | v1_funct_1(sK3) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_1451,c_1459]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_42,negated_conjecture,
% 11.82/1.93      ( v1_funct_1(sK3) ),
% 11.82/1.93      inference(cnf_transformation,[],[f101]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_49,plain,
% 11.82/1.93      ( v1_funct_1(sK3) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_6298,plain,
% 11.82/1.93      ( v1_funct_1(X2) != iProver_top
% 11.82/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.82/1.93      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_5955,c_49]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_6299,plain,
% 11.82/1.93      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 11.82/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.82/1.93      | v1_funct_1(X2) != iProver_top ),
% 11.82/1.93      inference(renaming,[status(thm)],[c_6298]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_6307,plain,
% 11.82/1.93      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 11.82/1.93      | v1_funct_1(sK2) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_1448,c_6299]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_22,plain,
% 11.82/1.93      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.82/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.82/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.82/1.93      | X3 = X2 ),
% 11.82/1.93      inference(cnf_transformation,[],[f84]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_38,negated_conjecture,
% 11.82/1.93      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 11.82/1.93      inference(cnf_transformation,[],[f105]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_486,plain,
% 11.82/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.93      | X3 = X0
% 11.82/1.93      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 11.82/1.93      | k6_partfun1(sK0) != X3
% 11.82/1.93      | sK0 != X2
% 11.82/1.93      | sK0 != X1 ),
% 11.82/1.93      inference(resolution_lifted,[status(thm)],[c_22,c_38]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_487,plain,
% 11.82/1.93      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.82/1.93      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.82/1.93      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.82/1.93      inference(unflattening,[status(thm)],[c_486]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_25,plain,
% 11.82/1.93      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.82/1.93      inference(cnf_transformation,[],[f88]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_495,plain,
% 11.82/1.93      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.82/1.93      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.82/1.93      inference(forward_subsumption_resolution,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_487,c_25]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1444,plain,
% 11.82/1.93      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.82/1.93      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_45,negated_conjecture,
% 11.82/1.93      ( v1_funct_1(sK2) ),
% 11.82/1.93      inference(cnf_transformation,[],[f98]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_23,plain,
% 11.82/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.82/1.93      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.82/1.93      | ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v1_funct_1(X3) ),
% 11.82/1.93      inference(cnf_transformation,[],[f87]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1809,plain,
% 11.82/1.93      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.82/1.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.82/1.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.82/1.93      | ~ v1_funct_1(sK3)
% 11.82/1.93      | ~ v1_funct_1(sK2) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_23]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2287,plain,
% 11.82/1.93      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_1444,c_45,c_43,c_42,c_40,c_495,c_1809]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_6308,plain,
% 11.82/1.93      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 11.82/1.93      | v1_funct_1(sK2) != iProver_top ),
% 11.82/1.93      inference(light_normalisation,[status(thm)],[c_6307,c_2287]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_46,plain,
% 11.82/1.93      ( v1_funct_1(sK2) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7213,plain,
% 11.82/1.93      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_6308,c_46]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_19,plain,
% 11.82/1.93      ( ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v1_funct_1(X1)
% 11.82/1.93      | ~ v2_funct_1(X0)
% 11.82/1.93      | ~ v1_relat_1(X0)
% 11.82/1.93      | ~ v1_relat_1(X1)
% 11.82/1.93      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 11.82/1.93      | k2_funct_1(X0) = X1
% 11.82/1.93      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f114]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1464,plain,
% 11.82/1.93      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 11.82/1.93      | k2_funct_1(X1) = X0
% 11.82/1.93      | k2_relat_1(X0) != k1_relat_1(X1)
% 11.82/1.93      | v1_funct_1(X1) != iProver_top
% 11.82/1.93      | v1_funct_1(X0) != iProver_top
% 11.82/1.93      | v2_funct_1(X1) != iProver_top
% 11.82/1.93      | v1_relat_1(X1) != iProver_top
% 11.82/1.93      | v1_relat_1(X0) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7215,plain,
% 11.82/1.93      ( k2_funct_1(sK3) = sK2
% 11.82/1.93      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 11.82/1.93      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 11.82/1.93      | v1_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_funct_1(sK2) != iProver_top
% 11.82/1.93      | v2_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK2) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_7213,c_1464]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_20,plain,
% 11.82/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.93      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f83]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1463,plain,
% 11.82/1.93      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.82/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3025,plain,
% 11.82/1.93      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_1448,c_1463]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_39,negated_conjecture,
% 11.82/1.93      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 11.82/1.93      inference(cnf_transformation,[],[f104]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3026,plain,
% 11.82/1.93      ( k2_relat_1(sK2) = sK1 ),
% 11.82/1.93      inference(light_normalisation,[status(thm)],[c_3025,c_39]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3024,plain,
% 11.82/1.93      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_1451,c_1463]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_27,plain,
% 11.82/1.93      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 11.82/1.93      | ~ v1_funct_2(X2,X0,X1)
% 11.82/1.93      | ~ v1_funct_2(X3,X1,X0)
% 11.82/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.82/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.82/1.93      | ~ v1_funct_1(X2)
% 11.82/1.93      | ~ v1_funct_1(X3)
% 11.82/1.93      | k2_relset_1(X1,X0,X3) = X0 ),
% 11.82/1.93      inference(cnf_transformation,[],[f91]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_499,plain,
% 11.82/1.93      ( ~ v1_funct_2(X0,X1,X2)
% 11.82/1.93      | ~ v1_funct_2(X3,X2,X1)
% 11.82/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.82/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.93      | ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v1_funct_1(X3)
% 11.82/1.93      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.82/1.93      | k2_relset_1(X1,X2,X0) = X2
% 11.82/1.93      | k6_partfun1(X2) != k6_partfun1(sK0)
% 11.82/1.93      | sK0 != X2 ),
% 11.82/1.93      inference(resolution_lifted,[status(thm)],[c_27,c_38]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_500,plain,
% 11.82/1.93      ( ~ v1_funct_2(X0,X1,sK0)
% 11.82/1.93      | ~ v1_funct_2(X2,sK0,X1)
% 11.82/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.82/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.82/1.93      | ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v1_funct_1(X2)
% 11.82/1.93      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.82/1.93      | k2_relset_1(X1,sK0,X0) = sK0
% 11.82/1.93      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 11.82/1.93      inference(unflattening,[status(thm)],[c_499]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_592,plain,
% 11.82/1.93      ( ~ v1_funct_2(X0,X1,sK0)
% 11.82/1.93      | ~ v1_funct_2(X2,sK0,X1)
% 11.82/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 11.82/1.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 11.82/1.93      | ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v1_funct_1(X2)
% 11.82/1.93      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.82/1.93      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 11.82/1.93      inference(equality_resolution_simp,[status(thm)],[c_500]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1443,plain,
% 11.82/1.93      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 11.82/1.93      | k2_relset_1(X0,sK0,X2) = sK0
% 11.82/1.93      | v1_funct_2(X2,X0,sK0) != iProver_top
% 11.82/1.93      | v1_funct_2(X1,sK0,X0) != iProver_top
% 11.82/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 11.82/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 11.82/1.93      | v1_funct_1(X2) != iProver_top
% 11.82/1.93      | v1_funct_1(X1) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2004,plain,
% 11.82/1.93      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 11.82/1.93      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.82/1.93      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.82/1.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.82/1.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.82/1.93      | v1_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_funct_1(sK2) != iProver_top ),
% 11.82/1.93      inference(equality_resolution,[status(thm)],[c_1443]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_44,negated_conjecture,
% 11.82/1.93      ( v1_funct_2(sK2,sK0,sK1) ),
% 11.82/1.93      inference(cnf_transformation,[],[f99]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_47,plain,
% 11.82/1.93      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_48,plain,
% 11.82/1.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_41,negated_conjecture,
% 11.82/1.93      ( v1_funct_2(sK3,sK1,sK0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f102]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_50,plain,
% 11.82/1.93      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_51,plain,
% 11.82/1.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2294,plain,
% 11.82/1.93      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_2004,c_46,c_47,c_48,c_49,c_50,c_51]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3027,plain,
% 11.82/1.93      ( k2_relat_1(sK3) = sK0 ),
% 11.82/1.93      inference(light_normalisation,[status(thm)],[c_3024,c_2294]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7216,plain,
% 11.82/1.93      ( k2_funct_1(sK3) = sK2
% 11.82/1.93      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 11.82/1.93      | k1_relat_1(sK3) != sK1
% 11.82/1.93      | v1_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_funct_1(sK2) != iProver_top
% 11.82/1.93      | v2_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK2) != iProver_top ),
% 11.82/1.93      inference(light_normalisation,[status(thm)],[c_7215,c_3026,c_3027]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7217,plain,
% 11.82/1.93      ( k2_funct_1(sK3) = sK2
% 11.82/1.93      | k1_relat_1(sK3) != sK1
% 11.82/1.93      | v1_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_funct_1(sK2) != iProver_top
% 11.82/1.93      | v2_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK2) != iProver_top ),
% 11.82/1.93      inference(equality_resolution_simp,[status(thm)],[c_7216]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_29,plain,
% 11.82/1.93      ( ~ v1_funct_2(X0,X1,X2)
% 11.82/1.93      | ~ v1_funct_2(X3,X4,X1)
% 11.82/1.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.82/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.93      | ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v1_funct_1(X3)
% 11.82/1.93      | v2_funct_1(X0)
% 11.82/1.93      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.82/1.93      | k2_relset_1(X4,X1,X3) != X1
% 11.82/1.93      | k1_xboole_0 = X2 ),
% 11.82/1.93      inference(cnf_transformation,[],[f94]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1457,plain,
% 11.82/1.93      ( k2_relset_1(X0,X1,X2) != X1
% 11.82/1.93      | k1_xboole_0 = X3
% 11.82/1.93      | v1_funct_2(X4,X1,X3) != iProver_top
% 11.82/1.93      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.82/1.93      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 11.82/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.82/1.93      | v1_funct_1(X4) != iProver_top
% 11.82/1.93      | v1_funct_1(X2) != iProver_top
% 11.82/1.93      | v2_funct_1(X4) = iProver_top
% 11.82/1.93      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_5947,plain,
% 11.82/1.93      ( k1_xboole_0 = X0
% 11.82/1.93      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.82/1.93      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 11.82/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.82/1.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.82/1.93      | v1_funct_1(X1) != iProver_top
% 11.82/1.93      | v1_funct_1(sK2) != iProver_top
% 11.82/1.93      | v2_funct_1(X1) = iProver_top
% 11.82/1.93      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_39,c_1457]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_6291,plain,
% 11.82/1.93      ( v1_funct_1(X1) != iProver_top
% 11.82/1.93      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.82/1.93      | k1_xboole_0 = X0
% 11.82/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.82/1.93      | v2_funct_1(X1) = iProver_top
% 11.82/1.93      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_5947,c_46,c_47,c_48]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_6292,plain,
% 11.82/1.93      ( k1_xboole_0 = X0
% 11.82/1.93      | v1_funct_2(X1,sK1,X0) != iProver_top
% 11.82/1.93      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 11.82/1.93      | v1_funct_1(X1) != iProver_top
% 11.82/1.93      | v2_funct_1(X1) = iProver_top
% 11.82/1.93      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 11.82/1.93      inference(renaming,[status(thm)],[c_6291]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_6295,plain,
% 11.82/1.93      ( sK0 = k1_xboole_0
% 11.82/1.93      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.82/1.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.82/1.93      | v1_funct_1(sK3) != iProver_top
% 11.82/1.93      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 11.82/1.93      | v2_funct_1(sK3) = iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_2287,c_6292]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_36,negated_conjecture,
% 11.82/1.93      ( k1_xboole_0 != sK0 ),
% 11.82/1.93      inference(cnf_transformation,[],[f107]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2,plain,
% 11.82/1.93      ( r1_tarski(X0,X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f116]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_138,plain,
% 11.82/1.93      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_2]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_0,plain,
% 11.82/1.93      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.82/1.93      inference(cnf_transformation,[],[f65]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_142,plain,
% 11.82/1.93      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.82/1.93      | k1_xboole_0 = k1_xboole_0 ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_0]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_815,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1580,plain,
% 11.82/1.93      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_815]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1581,plain,
% 11.82/1.93      ( sK0 != k1_xboole_0
% 11.82/1.93      | k1_xboole_0 = sK0
% 11.82/1.93      | k1_xboole_0 != k1_xboole_0 ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_1580]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_16,plain,
% 11.82/1.93      ( v2_funct_1(k6_partfun1(X0)) ),
% 11.82/1.93      inference(cnf_transformation,[],[f112]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_5204,plain,
% 11.82/1.93      ( v2_funct_1(k6_partfun1(sK0)) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_16]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_5205,plain,
% 11.82/1.93      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_5204]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7143,plain,
% 11.82/1.93      ( v2_funct_1(sK3) = iProver_top ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_6295,c_49,c_50,c_51,c_36,c_138,c_142,c_1581,c_5205]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1449,plain,
% 11.82/1.93      ( v1_funct_1(sK3) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_13,plain,
% 11.82/1.93      ( ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v2_funct_1(X0)
% 11.82/1.93      | ~ v1_relat_1(X0)
% 11.82/1.93      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f76]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1470,plain,
% 11.82/1.93      ( k2_funct_1(X0) = k4_relat_1(X0)
% 11.82/1.93      | v1_funct_1(X0) != iProver_top
% 11.82/1.93      | v2_funct_1(X0) != iProver_top
% 11.82/1.93      | v1_relat_1(X0) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3729,plain,
% 11.82/1.93      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 11.82/1.93      | v2_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK3) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_1449,c_1470]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3,plain,
% 11.82/1.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.82/1.93      | ~ v1_relat_1(X1)
% 11.82/1.93      | v1_relat_1(X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f66]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1599,plain,
% 11.82/1.93      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 11.82/1.93      | ~ v1_relat_1(X0)
% 11.82/1.93      | v1_relat_1(sK3) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_3]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1918,plain,
% 11.82/1.93      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.82/1.93      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 11.82/1.93      | v1_relat_1(sK3) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_1599]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2422,plain,
% 11.82/1.93      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.82/1.93      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 11.82/1.93      | v1_relat_1(sK3) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_1918]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2423,plain,
% 11.82/1.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.82/1.93      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 11.82/1.93      | v1_relat_1(sK3) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_2422]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_4,plain,
% 11.82/1.93      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.82/1.93      inference(cnf_transformation,[],[f67]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2825,plain,
% 11.82/1.93      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_4]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2826,plain,
% 11.82/1.93      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_4082,plain,
% 11.82/1.93      ( v2_funct_1(sK3) != iProver_top
% 11.82/1.93      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_3729,c_51,c_2423,c_2826]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_4083,plain,
% 11.82/1.93      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 11.82/1.93      | v2_funct_1(sK3) != iProver_top ),
% 11.82/1.93      inference(renaming,[status(thm)],[c_4082]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7148,plain,
% 11.82/1.93      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_7143,c_4083]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7218,plain,
% 11.82/1.93      ( k1_relat_1(sK3) != sK1
% 11.82/1.93      | k4_relat_1(sK3) = sK2
% 11.82/1.93      | v1_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_funct_1(sK2) != iProver_top
% 11.82/1.93      | v2_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(sK2) != iProver_top ),
% 11.82/1.93      inference(demodulation,[status(thm)],[c_7217,c_7148]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1,plain,
% 11.82/1.93      ( r1_tarski(X0,X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f115]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2368,plain,
% 11.82/1.93      ( r1_tarski(sK0,sK0) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_1]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_2369,plain,
% 11.82/1.93      ( r1_tarski(sK0,sK0) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_2368]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1478,plain,
% 11.82/1.93      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.82/1.93      | v1_relat_1(X1) != iProver_top
% 11.82/1.93      | v1_relat_1(X0) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3655,plain,
% 11.82/1.93      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.82/1.93      | v1_relat_1(sK2) = iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_1448,c_1478]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3657,plain,
% 11.82/1.93      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 11.82/1.93      inference(predicate_to_equality_rev,[status(thm)],[c_3655]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3826,plain,
% 11.82/1.93      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 11.82/1.93      inference(instantiation,[status(thm)],[c_4]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_6296,plain,
% 11.82/1.93      ( ~ v1_funct_2(sK3,sK1,sK0)
% 11.82/1.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 11.82/1.93      | ~ v1_funct_1(sK3)
% 11.82/1.93      | ~ v2_funct_1(k6_partfun1(sK0))
% 11.82/1.93      | v2_funct_1(sK3)
% 11.82/1.93      | sK0 = k1_xboole_0 ),
% 11.82/1.93      inference(predicate_to_equality_rev,[status(thm)],[c_6295]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_15,plain,
% 11.82/1.93      ( ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v1_relat_1(X0)
% 11.82/1.93      | v1_relat_1(k2_funct_1(X0)) ),
% 11.82/1.93      inference(cnf_transformation,[],[f77]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1468,plain,
% 11.82/1.93      ( v1_funct_1(X0) != iProver_top
% 11.82/1.93      | v1_relat_1(X0) != iProver_top
% 11.82/1.93      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7156,plain,
% 11.82/1.93      ( v1_funct_1(sK3) != iProver_top
% 11.82/1.93      | v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 11.82/1.93      | v1_relat_1(sK3) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_7148,c_1468]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7219,plain,
% 11.82/1.93      ( ~ v1_funct_1(sK3)
% 11.82/1.93      | ~ v1_funct_1(sK2)
% 11.82/1.93      | ~ v2_funct_1(sK3)
% 11.82/1.93      | ~ v1_relat_1(sK3)
% 11.82/1.93      | ~ v1_relat_1(sK2)
% 11.82/1.93      | k1_relat_1(sK3) != sK1
% 11.82/1.93      | k4_relat_1(sK3) = sK2 ),
% 11.82/1.93      inference(predicate_to_equality_rev,[status(thm)],[c_7218]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3654,plain,
% 11.82/1.93      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 11.82/1.93      | v1_relat_1(sK3) = iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_1451,c_1478]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3808,plain,
% 11.82/1.93      ( v1_relat_1(sK3) = iProver_top ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_3654,c_51,c_2423,c_2826]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_9,plain,
% 11.82/1.93      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f71]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1472,plain,
% 11.82/1.93      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 11.82/1.93      | v1_relat_1(X0) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3815,plain,
% 11.82/1.93      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_3808,c_1472]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3817,plain,
% 11.82/1.93      ( k1_relat_1(k4_relat_1(sK3)) = sK0 ),
% 11.82/1.93      inference(light_normalisation,[status(thm)],[c_3815,c_3027]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_10,plain,
% 11.82/1.93      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 11.82/1.93      | ~ v1_relat_1(X0)
% 11.82/1.93      | ~ v1_relat_1(X1)
% 11.82/1.93      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 11.82/1.93      inference(cnf_transformation,[],[f73]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1471,plain,
% 11.82/1.93      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 11.82/1.93      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 11.82/1.93      | v1_relat_1(X0) != iProver_top
% 11.82/1.93      | v1_relat_1(X1) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_4631,plain,
% 11.82/1.93      ( k1_relat_1(k5_relat_1(sK3,X0)) = k1_relat_1(sK3)
% 11.82/1.93      | r1_tarski(sK0,k1_relat_1(X0)) != iProver_top
% 11.82/1.93      | v1_relat_1(X0) != iProver_top
% 11.82/1.93      | v1_relat_1(sK3) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_3027,c_1471]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_13198,plain,
% 11.82/1.93      ( v1_relat_1(X0) != iProver_top
% 11.82/1.93      | r1_tarski(sK0,k1_relat_1(X0)) != iProver_top
% 11.82/1.93      | k1_relat_1(k5_relat_1(sK3,X0)) = k1_relat_1(sK3) ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_4631,c_51,c_2423,c_2826]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_13199,plain,
% 11.82/1.93      ( k1_relat_1(k5_relat_1(sK3,X0)) = k1_relat_1(sK3)
% 11.82/1.93      | r1_tarski(sK0,k1_relat_1(X0)) != iProver_top
% 11.82/1.93      | v1_relat_1(X0) != iProver_top ),
% 11.82/1.93      inference(renaming,[status(thm)],[c_13198]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_13208,plain,
% 11.82/1.93      ( k1_relat_1(k5_relat_1(sK3,k4_relat_1(sK3))) = k1_relat_1(sK3)
% 11.82/1.93      | r1_tarski(sK0,sK0) != iProver_top
% 11.82/1.93      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_3817,c_13199]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_33,plain,
% 11.82/1.93      ( ~ v1_funct_2(X0,X1,X2)
% 11.82/1.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.82/1.93      | ~ v1_funct_1(X0)
% 11.82/1.93      | ~ v2_funct_1(X0)
% 11.82/1.93      | k2_relset_1(X1,X2,X0) != X2
% 11.82/1.93      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 11.82/1.93      | k1_xboole_0 = X2 ),
% 11.82/1.93      inference(cnf_transformation,[],[f96]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1453,plain,
% 11.82/1.93      ( k2_relset_1(X0,X1,X2) != X1
% 11.82/1.93      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 11.82/1.93      | k1_xboole_0 = X1
% 11.82/1.93      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.82/1.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.82/1.93      | v1_funct_1(X2) != iProver_top
% 11.82/1.93      | v2_funct_1(X2) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3006,plain,
% 11.82/1.93      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.82/1.93      | sK0 = k1_xboole_0
% 11.82/1.93      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 11.82/1.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 11.82/1.93      | v1_funct_1(sK3) != iProver_top
% 11.82/1.93      | v2_funct_1(sK3) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_2294,c_1453]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3049,plain,
% 11.82/1.93      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 11.82/1.93      | v2_funct_1(sK3) != iProver_top ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_3006,c_49,c_50,c_51,c_36,c_138,c_142,c_1581]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7149,plain,
% 11.82/1.93      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_7143,c_3049]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_7150,plain,
% 11.82/1.93      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
% 11.82/1.93      inference(demodulation,[status(thm)],[c_7148,c_7149]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_13233,plain,
% 11.82/1.93      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 11.82/1.93      | r1_tarski(sK0,sK0) != iProver_top
% 11.82/1.93      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 11.82/1.93      inference(light_normalisation,[status(thm)],[c_13208,c_7150]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_12,plain,
% 11.82/1.93      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 11.82/1.93      inference(cnf_transformation,[],[f111]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_13234,plain,
% 11.82/1.93      ( k1_relat_1(sK3) = sK1
% 11.82/1.93      | r1_tarski(sK0,sK0) != iProver_top
% 11.82/1.93      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 11.82/1.93      inference(demodulation,[status(thm)],[c_13233,c_12]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_32361,plain,
% 11.82/1.93      ( k4_relat_1(sK3) = sK2 ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_7218,c_45,c_42,c_49,c_41,c_40,c_51,c_36,c_138,c_142,
% 11.82/1.93                 c_1581,c_2369,c_2422,c_2423,c_2825,c_2826,c_3657,c_3826,
% 11.82/1.93                 c_5204,c_6296,c_7156,c_7219,c_13234]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_5,plain,
% 11.82/1.93      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 11.82/1.93      inference(cnf_transformation,[],[f68]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1476,plain,
% 11.82/1.93      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3816,plain,
% 11.82/1.93      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_3808,c_1476]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_32418,plain,
% 11.82/1.93      ( k4_relat_1(sK2) = sK3 ),
% 11.82/1.93      inference(demodulation,[status(thm)],[c_32361,c_3816]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_1446,plain,
% 11.82/1.93      ( v1_funct_1(sK2) = iProver_top ),
% 11.82/1.93      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3730,plain,
% 11.82/1.93      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 11.82/1.93      | v2_funct_1(sK2) != iProver_top
% 11.82/1.93      | v1_relat_1(sK2) != iProver_top ),
% 11.82/1.93      inference(superposition,[status(thm)],[c_1446,c_1470]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_37,negated_conjecture,
% 11.82/1.93      ( v2_funct_1(sK2) ),
% 11.82/1.93      inference(cnf_transformation,[],[f106]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_3735,plain,
% 11.82/1.93      ( ~ v2_funct_1(sK2)
% 11.82/1.93      | ~ v1_relat_1(sK2)
% 11.82/1.93      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 11.82/1.93      inference(predicate_to_equality_rev,[status(thm)],[c_3730]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_4087,plain,
% 11.82/1.93      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 11.82/1.93      inference(global_propositional_subsumption,
% 11.82/1.93                [status(thm)],
% 11.82/1.93                [c_3730,c_37,c_3657,c_3735,c_3826]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_34,negated_conjecture,
% 11.82/1.93      ( k2_funct_1(sK2) != sK3 ),
% 11.82/1.93      inference(cnf_transformation,[],[f109]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(c_4091,plain,
% 11.82/1.93      ( k4_relat_1(sK2) != sK3 ),
% 11.82/1.93      inference(demodulation,[status(thm)],[c_4087,c_34]) ).
% 11.82/1.93  
% 11.82/1.93  cnf(contradiction,plain,
% 11.82/1.93      ( $false ),
% 11.82/1.93      inference(minisat,[status(thm)],[c_32418,c_4091]) ).
% 11.82/1.93  
% 11.82/1.93  
% 11.82/1.93  % SZS output end CNFRefutation for theBenchmark.p
% 11.82/1.93  
% 11.82/1.93  ------                               Statistics
% 11.82/1.93  
% 11.82/1.93  ------ General
% 11.82/1.93  
% 11.82/1.93  abstr_ref_over_cycles:                  0
% 11.82/1.93  abstr_ref_under_cycles:                 0
% 11.82/1.93  gc_basic_clause_elim:                   0
% 11.82/1.93  forced_gc_time:                         0
% 11.82/1.93  parsing_time:                           0.011
% 11.82/1.93  unif_index_cands_time:                  0.
% 11.82/1.93  unif_index_add_time:                    0.
% 11.82/1.93  orderings_time:                         0.
% 11.82/1.93  out_proof_time:                         0.018
% 11.82/1.93  total_time:                             1.254
% 11.82/1.93  num_of_symbols:                         55
% 11.82/1.93  num_of_terms:                           50535
% 11.82/1.93  
% 11.82/1.93  ------ Preprocessing
% 11.82/1.93  
% 11.82/1.93  num_of_splits:                          0
% 11.82/1.93  num_of_split_atoms:                     0
% 11.82/1.93  num_of_reused_defs:                     0
% 11.82/1.93  num_eq_ax_congr_red:                    3
% 11.82/1.93  num_of_sem_filtered_clauses:            1
% 11.82/1.93  num_of_subtypes:                        0
% 11.82/1.93  monotx_restored_types:                  0
% 11.82/1.93  sat_num_of_epr_types:                   0
% 11.82/1.93  sat_num_of_non_cyclic_types:            0
% 11.82/1.93  sat_guarded_non_collapsed_types:        0
% 11.82/1.93  num_pure_diseq_elim:                    0
% 11.82/1.93  simp_replaced_by:                       0
% 11.82/1.93  res_preprocessed:                       218
% 11.82/1.93  prep_upred:                             0
% 11.82/1.93  prep_unflattend:                        12
% 11.82/1.93  smt_new_axioms:                         0
% 11.82/1.93  pred_elim_cands:                        6
% 11.82/1.93  pred_elim:                              1
% 11.82/1.93  pred_elim_cl:                           1
% 11.82/1.93  pred_elim_cycles:                       3
% 11.82/1.93  merged_defs:                            0
% 11.82/1.94  merged_defs_ncl:                        0
% 11.82/1.94  bin_hyper_res:                          0
% 11.82/1.94  prep_cycles:                            4
% 11.82/1.94  pred_elim_time:                         0.005
% 11.82/1.94  splitting_time:                         0.
% 11.82/1.94  sem_filter_time:                        0.
% 11.82/1.94  monotx_time:                            0.001
% 11.82/1.94  subtype_inf_time:                       0.
% 11.82/1.94  
% 11.82/1.94  ------ Problem properties
% 11.82/1.94  
% 11.82/1.94  clauses:                                44
% 11.82/1.94  conjectures:                            11
% 11.82/1.94  epr:                                    9
% 11.82/1.94  horn:                                   40
% 11.82/1.94  ground:                                 12
% 11.82/1.94  unary:                                  18
% 11.82/1.94  binary:                                 7
% 11.82/1.94  lits:                                   147
% 11.82/1.94  lits_eq:                                37
% 11.82/1.94  fd_pure:                                0
% 11.82/1.94  fd_pseudo:                              0
% 11.82/1.94  fd_cond:                                4
% 11.82/1.94  fd_pseudo_cond:                         2
% 11.82/1.94  ac_symbols:                             0
% 11.82/1.94  
% 11.82/1.94  ------ Propositional Solver
% 11.82/1.94  
% 11.82/1.94  prop_solver_calls:                      35
% 11.82/1.94  prop_fast_solver_calls:                 3224
% 11.82/1.94  smt_solver_calls:                       0
% 11.82/1.94  smt_fast_solver_calls:                  0
% 11.82/1.94  prop_num_of_clauses:                    17416
% 11.82/1.94  prop_preprocess_simplified:             23701
% 11.82/1.94  prop_fo_subsumed:                       352
% 11.82/1.94  prop_solver_time:                       0.
% 11.82/1.94  smt_solver_time:                        0.
% 11.82/1.94  smt_fast_solver_time:                   0.
% 11.82/1.94  prop_fast_solver_time:                  0.
% 11.82/1.94  prop_unsat_core_time:                   0.002
% 11.82/1.94  
% 11.82/1.94  ------ QBF
% 11.82/1.94  
% 11.82/1.94  qbf_q_res:                              0
% 11.82/1.94  qbf_num_tautologies:                    0
% 11.82/1.94  qbf_prep_cycles:                        0
% 11.82/1.94  
% 11.82/1.94  ------ BMC1
% 11.82/1.94  
% 11.82/1.94  bmc1_current_bound:                     -1
% 11.82/1.94  bmc1_last_solved_bound:                 -1
% 11.82/1.94  bmc1_unsat_core_size:                   -1
% 11.82/1.94  bmc1_unsat_core_parents_size:           -1
% 11.82/1.94  bmc1_merge_next_fun:                    0
% 11.82/1.94  bmc1_unsat_core_clauses_time:           0.
% 11.82/1.94  
% 11.82/1.94  ------ Instantiation
% 11.82/1.94  
% 11.82/1.94  inst_num_of_clauses:                    4086
% 11.82/1.94  inst_num_in_passive:                    1637
% 11.82/1.94  inst_num_in_active:                     2106
% 11.82/1.94  inst_num_in_unprocessed:                343
% 11.82/1.94  inst_num_of_loops:                      2360
% 11.82/1.94  inst_num_of_learning_restarts:          0
% 11.82/1.94  inst_num_moves_active_passive:          249
% 11.82/1.94  inst_lit_activity:                      0
% 11.82/1.94  inst_lit_activity_moves:                2
% 11.82/1.94  inst_num_tautologies:                   0
% 11.82/1.94  inst_num_prop_implied:                  0
% 11.82/1.94  inst_num_existing_simplified:           0
% 11.82/1.94  inst_num_eq_res_simplified:             0
% 11.82/1.94  inst_num_child_elim:                    0
% 11.82/1.94  inst_num_of_dismatching_blockings:      1162
% 11.82/1.94  inst_num_of_non_proper_insts:           3593
% 11.82/1.94  inst_num_of_duplicates:                 0
% 11.82/1.94  inst_inst_num_from_inst_to_res:         0
% 11.82/1.94  inst_dismatching_checking_time:         0.
% 11.82/1.94  
% 11.82/1.94  ------ Resolution
% 11.82/1.94  
% 11.82/1.94  res_num_of_clauses:                     0
% 11.82/1.94  res_num_in_passive:                     0
% 11.82/1.94  res_num_in_active:                      0
% 11.82/1.94  res_num_of_loops:                       222
% 11.82/1.94  res_forward_subset_subsumed:            195
% 11.82/1.94  res_backward_subset_subsumed:           0
% 11.82/1.94  res_forward_subsumed:                   0
% 11.82/1.94  res_backward_subsumed:                  0
% 11.82/1.94  res_forward_subsumption_resolution:     2
% 11.82/1.94  res_backward_subsumption_resolution:    0
% 11.82/1.94  res_clause_to_clause_subsumption:       3668
% 11.82/1.94  res_orphan_elimination:                 0
% 11.82/1.94  res_tautology_del:                      289
% 11.82/1.94  res_num_eq_res_simplified:              1
% 11.82/1.94  res_num_sel_changes:                    0
% 11.82/1.94  res_moves_from_active_to_pass:          0
% 11.82/1.94  
% 11.82/1.94  ------ Superposition
% 11.82/1.94  
% 11.82/1.94  sup_time_total:                         0.
% 11.82/1.94  sup_time_generating:                    0.
% 11.82/1.94  sup_time_sim_full:                      0.
% 11.82/1.94  sup_time_sim_immed:                     0.
% 11.82/1.94  
% 11.82/1.94  sup_num_of_clauses:                     1551
% 11.82/1.94  sup_num_in_active:                      385
% 11.82/1.94  sup_num_in_passive:                     1166
% 11.82/1.94  sup_num_of_loops:                       470
% 11.82/1.94  sup_fw_superposition:                   910
% 11.82/1.94  sup_bw_superposition:                   879
% 11.82/1.94  sup_immediate_simplified:               632
% 11.82/1.94  sup_given_eliminated:                   0
% 11.82/1.94  comparisons_done:                       0
% 11.82/1.94  comparisons_avoided:                    4
% 11.82/1.94  
% 11.82/1.94  ------ Simplifications
% 11.82/1.94  
% 11.82/1.94  
% 11.82/1.94  sim_fw_subset_subsumed:                 37
% 11.82/1.94  sim_bw_subset_subsumed:                 54
% 11.82/1.94  sim_fw_subsumed:                        42
% 11.82/1.94  sim_bw_subsumed:                        0
% 11.82/1.94  sim_fw_subsumption_res:                 0
% 11.82/1.94  sim_bw_subsumption_res:                 0
% 11.82/1.94  sim_tautology_del:                      0
% 11.82/1.94  sim_eq_tautology_del:                   94
% 11.82/1.94  sim_eq_res_simp:                        3
% 11.82/1.94  sim_fw_demodulated:                     37
% 11.82/1.94  sim_bw_demodulated:                     77
% 11.82/1.94  sim_light_normalised:                   589
% 11.82/1.94  sim_joinable_taut:                      0
% 11.82/1.94  sim_joinable_simp:                      0
% 11.82/1.94  sim_ac_normalised:                      0
% 11.82/1.94  sim_smt_subsumption:                    0
% 11.82/1.94  
%------------------------------------------------------------------------------
