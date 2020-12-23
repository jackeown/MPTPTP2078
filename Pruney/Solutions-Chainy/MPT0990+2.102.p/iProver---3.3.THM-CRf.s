%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:18 EST 2020

% Result     : Theorem 15.43s
% Output     : CNFRefutation 15.43s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 686 expanded)
%              Number of clauses        :  122 ( 193 expanded)
%              Number of leaves         :   20 ( 176 expanded)
%              Depth                    :   20
%              Number of atoms          :  857 (5910 expanded)
%              Number of equality atoms :  423 (2181 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f24])).

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
    inference(flattening,[],[f54])).

fof(f62,plain,(
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

fof(f61,plain,
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

fof(f63,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f62,f61])).

fof(f103,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f106,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f108,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f87,f95])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f63])).

fof(f22,axiom,(
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

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

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
    inference(flattening,[],[f52])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f109,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f111,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f63])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

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
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f115,plain,(
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
    inference(definition_unfolding,[],[f74,f95,f95])).

fof(f122,plain,(
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
    inference(equality_resolution,[],[f115])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f118,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f95])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
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

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f110,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f121,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f112,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2436,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2439,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2446,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10126,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2439,c_2446])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_51,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_10568,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10126,c_51])).

cnf(c_10569,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_10568])).

cnf(c_10580,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2436,c_10569])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3030,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3529,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3030])).

cnf(c_4177,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3529])).

cnf(c_5625,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_4177])).

cnf(c_10736,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10580,c_47,c_45,c_44,c_42,c_5625])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X2 = X3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X0 = X3
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X3
    | k6_partfun1(sK0) != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_40])).

cnf(c_492,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_500,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_492,c_23])).

cnf(c_2432,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_10739,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10736,c_2432])).

cnf(c_50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_53,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2454,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8114,plain,
    ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2439,c_2454])).

cnf(c_9242,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_2436,c_8114])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2457,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9549,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9242,c_2457])).

cnf(c_12411,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10739,c_50,c_53,c_9549])).

cnf(c_41,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2442,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5575,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_2442])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3040,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_3428,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3040])).

cnf(c_4006,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3428])).

cnf(c_5891,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5575,c_47,c_46,c_45,c_41,c_39,c_37,c_4006])).

cnf(c_2440,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2461,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5777,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2440,c_2461])).

cnf(c_931,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_39])).

cnf(c_932,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_931])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2815,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3210,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3674,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_6022,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5777,c_47,c_45,c_932,c_3210,c_3674])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | X0 = X2
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X2))
    | k5_relat_1(X2,X1) != k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2463,plain,
    ( X0 = X1
    | k5_relat_1(X2,X0) != k6_partfun1(k2_relat_1(X1))
    | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_10213,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(sK2))
    | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(sK2) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6022,c_2463])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2458,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6620,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2440,c_2458])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2441,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4427,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_2441])).

cnf(c_3050,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3493,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3050])).

cnf(c_4025,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3493])).

cnf(c_4732,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_47,c_46,c_45,c_41,c_39,c_37,c_4025])).

cnf(c_6621,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6620,c_4732])).

cnf(c_48,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3211,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3210])).

cnf(c_3675,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3674])).

cnf(c_6935,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6621,c_48,c_50,c_3211,c_3675])).

cnf(c_10223,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(sK0)
    | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(sK2) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10213,c_6935])).

cnf(c_49,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_55,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2971,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3369,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_2971])).

cnf(c_3370,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3369])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3024,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_3422,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_3024])).

cnf(c_3423,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3422])).

cnf(c_3671,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3672,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3671])).

cnf(c_3957,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_3974,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3957])).

cnf(c_58205,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(X0,X1) != k6_partfun1(sK0)
    | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(sK2) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10223,c_48,c_49,c_50,c_41,c_55,c_3370,c_3423,c_3672,c_3974])).

cnf(c_58206,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(sK0)
    | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
    | k2_funct_1(sK2) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_58205])).

cnf(c_58218,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5891,c_58206])).

cnf(c_59432,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_58218,c_48,c_50,c_3211,c_3675])).

cnf(c_59433,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_59432])).

cnf(c_59444,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12411,c_59433])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2447,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6730,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2439,c_2447])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2456,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3565,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2439,c_2456])).

cnf(c_6739,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_3565])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_52,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_150,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_154,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1795,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2888,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_2889,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2888])).

cnf(c_7661,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6739,c_52,c_38,c_150,c_154,c_2889])).

cnf(c_59449,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_59444,c_7661])).

cnf(c_59450,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_59449])).

cnf(c_3207,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2815])).

cnf(c_3208,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3207])).

cnf(c_36,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f112])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_59450,c_3672,c_3208,c_36,c_53,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.43/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.43/2.50  
% 15.43/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.43/2.50  
% 15.43/2.50  ------  iProver source info
% 15.43/2.50  
% 15.43/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.43/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.43/2.50  git: non_committed_changes: false
% 15.43/2.50  git: last_make_outside_of_git: false
% 15.43/2.50  
% 15.43/2.50  ------ 
% 15.43/2.50  
% 15.43/2.50  ------ Input Options
% 15.43/2.50  
% 15.43/2.50  --out_options                           all
% 15.43/2.50  --tptp_safe_out                         true
% 15.43/2.50  --problem_path                          ""
% 15.43/2.50  --include_path                          ""
% 15.43/2.50  --clausifier                            res/vclausify_rel
% 15.43/2.50  --clausifier_options                    --mode clausify
% 15.43/2.50  --stdin                                 false
% 15.43/2.50  --stats_out                             all
% 15.43/2.50  
% 15.43/2.50  ------ General Options
% 15.43/2.50  
% 15.43/2.50  --fof                                   false
% 15.43/2.50  --time_out_real                         305.
% 15.43/2.50  --time_out_virtual                      -1.
% 15.43/2.50  --symbol_type_check                     false
% 15.43/2.50  --clausify_out                          false
% 15.43/2.50  --sig_cnt_out                           false
% 15.43/2.50  --trig_cnt_out                          false
% 15.43/2.50  --trig_cnt_out_tolerance                1.
% 15.43/2.50  --trig_cnt_out_sk_spl                   false
% 15.43/2.50  --abstr_cl_out                          false
% 15.43/2.50  
% 15.43/2.50  ------ Global Options
% 15.43/2.50  
% 15.43/2.50  --schedule                              default
% 15.43/2.50  --add_important_lit                     false
% 15.43/2.50  --prop_solver_per_cl                    1000
% 15.43/2.50  --min_unsat_core                        false
% 15.43/2.50  --soft_assumptions                      false
% 15.43/2.50  --soft_lemma_size                       3
% 15.43/2.50  --prop_impl_unit_size                   0
% 15.43/2.50  --prop_impl_unit                        []
% 15.43/2.50  --share_sel_clauses                     true
% 15.43/2.50  --reset_solvers                         false
% 15.43/2.50  --bc_imp_inh                            [conj_cone]
% 15.43/2.50  --conj_cone_tolerance                   3.
% 15.43/2.50  --extra_neg_conj                        none
% 15.43/2.50  --large_theory_mode                     true
% 15.43/2.50  --prolific_symb_bound                   200
% 15.43/2.50  --lt_threshold                          2000
% 15.43/2.50  --clause_weak_htbl                      true
% 15.43/2.50  --gc_record_bc_elim                     false
% 15.43/2.50  
% 15.43/2.50  ------ Preprocessing Options
% 15.43/2.50  
% 15.43/2.50  --preprocessing_flag                    true
% 15.43/2.50  --time_out_prep_mult                    0.1
% 15.43/2.50  --splitting_mode                        input
% 15.43/2.50  --splitting_grd                         true
% 15.43/2.50  --splitting_cvd                         false
% 15.43/2.50  --splitting_cvd_svl                     false
% 15.43/2.50  --splitting_nvd                         32
% 15.43/2.50  --sub_typing                            true
% 15.43/2.50  --prep_gs_sim                           true
% 15.43/2.50  --prep_unflatten                        true
% 15.43/2.50  --prep_res_sim                          true
% 15.43/2.50  --prep_upred                            true
% 15.43/2.50  --prep_sem_filter                       exhaustive
% 15.43/2.50  --prep_sem_filter_out                   false
% 15.43/2.50  --pred_elim                             true
% 15.43/2.50  --res_sim_input                         true
% 15.43/2.50  --eq_ax_congr_red                       true
% 15.43/2.50  --pure_diseq_elim                       true
% 15.43/2.50  --brand_transform                       false
% 15.43/2.50  --non_eq_to_eq                          false
% 15.43/2.50  --prep_def_merge                        true
% 15.43/2.50  --prep_def_merge_prop_impl              false
% 15.43/2.50  --prep_def_merge_mbd                    true
% 15.43/2.50  --prep_def_merge_tr_red                 false
% 15.43/2.50  --prep_def_merge_tr_cl                  false
% 15.43/2.50  --smt_preprocessing                     true
% 15.43/2.50  --smt_ac_axioms                         fast
% 15.43/2.50  --preprocessed_out                      false
% 15.43/2.50  --preprocessed_stats                    false
% 15.43/2.50  
% 15.43/2.50  ------ Abstraction refinement Options
% 15.43/2.50  
% 15.43/2.50  --abstr_ref                             []
% 15.43/2.50  --abstr_ref_prep                        false
% 15.43/2.50  --abstr_ref_until_sat                   false
% 15.43/2.50  --abstr_ref_sig_restrict                funpre
% 15.43/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.43/2.50  --abstr_ref_under                       []
% 15.43/2.50  
% 15.43/2.50  ------ SAT Options
% 15.43/2.50  
% 15.43/2.50  --sat_mode                              false
% 15.43/2.50  --sat_fm_restart_options                ""
% 15.43/2.50  --sat_gr_def                            false
% 15.43/2.50  --sat_epr_types                         true
% 15.43/2.50  --sat_non_cyclic_types                  false
% 15.43/2.50  --sat_finite_models                     false
% 15.43/2.50  --sat_fm_lemmas                         false
% 15.43/2.50  --sat_fm_prep                           false
% 15.43/2.50  --sat_fm_uc_incr                        true
% 15.43/2.50  --sat_out_model                         small
% 15.43/2.50  --sat_out_clauses                       false
% 15.43/2.50  
% 15.43/2.50  ------ QBF Options
% 15.43/2.50  
% 15.43/2.50  --qbf_mode                              false
% 15.43/2.50  --qbf_elim_univ                         false
% 15.43/2.50  --qbf_dom_inst                          none
% 15.43/2.50  --qbf_dom_pre_inst                      false
% 15.43/2.50  --qbf_sk_in                             false
% 15.43/2.50  --qbf_pred_elim                         true
% 15.43/2.50  --qbf_split                             512
% 15.43/2.50  
% 15.43/2.50  ------ BMC1 Options
% 15.43/2.50  
% 15.43/2.50  --bmc1_incremental                      false
% 15.43/2.50  --bmc1_axioms                           reachable_all
% 15.43/2.50  --bmc1_min_bound                        0
% 15.43/2.50  --bmc1_max_bound                        -1
% 15.43/2.50  --bmc1_max_bound_default                -1
% 15.43/2.50  --bmc1_symbol_reachability              true
% 15.43/2.50  --bmc1_property_lemmas                  false
% 15.43/2.50  --bmc1_k_induction                      false
% 15.43/2.50  --bmc1_non_equiv_states                 false
% 15.43/2.50  --bmc1_deadlock                         false
% 15.43/2.50  --bmc1_ucm                              false
% 15.43/2.50  --bmc1_add_unsat_core                   none
% 15.43/2.50  --bmc1_unsat_core_children              false
% 15.43/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.43/2.50  --bmc1_out_stat                         full
% 15.43/2.50  --bmc1_ground_init                      false
% 15.43/2.50  --bmc1_pre_inst_next_state              false
% 15.43/2.50  --bmc1_pre_inst_state                   false
% 15.43/2.50  --bmc1_pre_inst_reach_state             false
% 15.43/2.50  --bmc1_out_unsat_core                   false
% 15.43/2.50  --bmc1_aig_witness_out                  false
% 15.43/2.50  --bmc1_verbose                          false
% 15.43/2.50  --bmc1_dump_clauses_tptp                false
% 15.43/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.43/2.50  --bmc1_dump_file                        -
% 15.43/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.43/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.43/2.50  --bmc1_ucm_extend_mode                  1
% 15.43/2.50  --bmc1_ucm_init_mode                    2
% 15.43/2.50  --bmc1_ucm_cone_mode                    none
% 15.43/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.43/2.50  --bmc1_ucm_relax_model                  4
% 15.43/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.43/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.43/2.50  --bmc1_ucm_layered_model                none
% 15.43/2.50  --bmc1_ucm_max_lemma_size               10
% 15.43/2.50  
% 15.43/2.50  ------ AIG Options
% 15.43/2.50  
% 15.43/2.50  --aig_mode                              false
% 15.43/2.50  
% 15.43/2.50  ------ Instantiation Options
% 15.43/2.50  
% 15.43/2.50  --instantiation_flag                    true
% 15.43/2.50  --inst_sos_flag                         false
% 15.43/2.50  --inst_sos_phase                        true
% 15.43/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.43/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.43/2.50  --inst_lit_sel_side                     num_symb
% 15.43/2.50  --inst_solver_per_active                1400
% 15.43/2.50  --inst_solver_calls_frac                1.
% 15.43/2.50  --inst_passive_queue_type               priority_queues
% 15.43/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.43/2.50  --inst_passive_queues_freq              [25;2]
% 15.43/2.50  --inst_dismatching                      true
% 15.43/2.50  --inst_eager_unprocessed_to_passive     true
% 15.43/2.50  --inst_prop_sim_given                   true
% 15.43/2.50  --inst_prop_sim_new                     false
% 15.43/2.50  --inst_subs_new                         false
% 15.43/2.50  --inst_eq_res_simp                      false
% 15.43/2.50  --inst_subs_given                       false
% 15.43/2.50  --inst_orphan_elimination               true
% 15.43/2.50  --inst_learning_loop_flag               true
% 15.43/2.50  --inst_learning_start                   3000
% 15.43/2.50  --inst_learning_factor                  2
% 15.43/2.50  --inst_start_prop_sim_after_learn       3
% 15.43/2.50  --inst_sel_renew                        solver
% 15.43/2.50  --inst_lit_activity_flag                true
% 15.43/2.50  --inst_restr_to_given                   false
% 15.43/2.50  --inst_activity_threshold               500
% 15.43/2.50  --inst_out_proof                        true
% 15.43/2.50  
% 15.43/2.50  ------ Resolution Options
% 15.43/2.50  
% 15.43/2.50  --resolution_flag                       true
% 15.43/2.50  --res_lit_sel                           adaptive
% 15.43/2.50  --res_lit_sel_side                      none
% 15.43/2.50  --res_ordering                          kbo
% 15.43/2.50  --res_to_prop_solver                    active
% 15.43/2.50  --res_prop_simpl_new                    false
% 15.43/2.50  --res_prop_simpl_given                  true
% 15.43/2.50  --res_passive_queue_type                priority_queues
% 15.43/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.43/2.50  --res_passive_queues_freq               [15;5]
% 15.43/2.50  --res_forward_subs                      full
% 15.43/2.50  --res_backward_subs                     full
% 15.43/2.50  --res_forward_subs_resolution           true
% 15.43/2.50  --res_backward_subs_resolution          true
% 15.43/2.50  --res_orphan_elimination                true
% 15.43/2.50  --res_time_limit                        2.
% 15.43/2.50  --res_out_proof                         true
% 15.43/2.50  
% 15.43/2.50  ------ Superposition Options
% 15.43/2.50  
% 15.43/2.50  --superposition_flag                    true
% 15.43/2.50  --sup_passive_queue_type                priority_queues
% 15.43/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.43/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.43/2.50  --demod_completeness_check              fast
% 15.43/2.50  --demod_use_ground                      true
% 15.43/2.50  --sup_to_prop_solver                    passive
% 15.43/2.50  --sup_prop_simpl_new                    true
% 15.43/2.50  --sup_prop_simpl_given                  true
% 15.43/2.50  --sup_fun_splitting                     false
% 15.43/2.50  --sup_smt_interval                      50000
% 15.43/2.50  
% 15.43/2.50  ------ Superposition Simplification Setup
% 15.43/2.50  
% 15.43/2.50  --sup_indices_passive                   []
% 15.43/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.43/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.43/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.43/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.43/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.43/2.50  --sup_full_bw                           [BwDemod]
% 15.43/2.50  --sup_immed_triv                        [TrivRules]
% 15.43/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.43/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.43/2.50  --sup_immed_bw_main                     []
% 15.43/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.43/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.43/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.43/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.43/2.50  
% 15.43/2.50  ------ Combination Options
% 15.43/2.50  
% 15.43/2.50  --comb_res_mult                         3
% 15.43/2.50  --comb_sup_mult                         2
% 15.43/2.50  --comb_inst_mult                        10
% 15.43/2.50  
% 15.43/2.50  ------ Debug Options
% 15.43/2.50  
% 15.43/2.50  --dbg_backtrace                         false
% 15.43/2.50  --dbg_dump_prop_clauses                 false
% 15.43/2.50  --dbg_dump_prop_clauses_file            -
% 15.43/2.50  --dbg_out_stat                          false
% 15.43/2.50  ------ Parsing...
% 15.43/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.43/2.50  
% 15.43/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.43/2.50  
% 15.43/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.43/2.50  
% 15.43/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.43/2.50  ------ Proving...
% 15.43/2.50  ------ Problem Properties 
% 15.43/2.50  
% 15.43/2.50  
% 15.43/2.50  clauses                                 43
% 15.43/2.50  conjectures                             11
% 15.43/2.50  EPR                                     9
% 15.43/2.50  Horn                                    37
% 15.43/2.50  unary                                   16
% 15.43/2.50  binary                                  3
% 15.43/2.50  lits                                    129
% 15.43/2.50  lits eq                                 38
% 15.43/2.50  fd_pure                                 0
% 15.43/2.50  fd_pseudo                               0
% 15.43/2.50  fd_cond                                 5
% 15.43/2.50  fd_pseudo_cond                          2
% 15.43/2.50  AC symbols                              0
% 15.43/2.50  
% 15.43/2.50  ------ Schedule dynamic 5 is on 
% 15.43/2.50  
% 15.43/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.43/2.50  
% 15.43/2.50  
% 15.43/2.50  ------ 
% 15.43/2.50  Current options:
% 15.43/2.50  ------ 
% 15.43/2.50  
% 15.43/2.50  ------ Input Options
% 15.43/2.50  
% 15.43/2.50  --out_options                           all
% 15.43/2.50  --tptp_safe_out                         true
% 15.43/2.50  --problem_path                          ""
% 15.43/2.50  --include_path                          ""
% 15.43/2.50  --clausifier                            res/vclausify_rel
% 15.43/2.50  --clausifier_options                    --mode clausify
% 15.43/2.50  --stdin                                 false
% 15.43/2.50  --stats_out                             all
% 15.43/2.50  
% 15.43/2.50  ------ General Options
% 15.43/2.50  
% 15.43/2.50  --fof                                   false
% 15.43/2.50  --time_out_real                         305.
% 15.43/2.50  --time_out_virtual                      -1.
% 15.43/2.50  --symbol_type_check                     false
% 15.43/2.50  --clausify_out                          false
% 15.43/2.50  --sig_cnt_out                           false
% 15.43/2.50  --trig_cnt_out                          false
% 15.43/2.50  --trig_cnt_out_tolerance                1.
% 15.43/2.50  --trig_cnt_out_sk_spl                   false
% 15.43/2.50  --abstr_cl_out                          false
% 15.43/2.50  
% 15.43/2.50  ------ Global Options
% 15.43/2.50  
% 15.43/2.50  --schedule                              default
% 15.43/2.50  --add_important_lit                     false
% 15.43/2.50  --prop_solver_per_cl                    1000
% 15.43/2.50  --min_unsat_core                        false
% 15.43/2.50  --soft_assumptions                      false
% 15.43/2.50  --soft_lemma_size                       3
% 15.43/2.50  --prop_impl_unit_size                   0
% 15.43/2.50  --prop_impl_unit                        []
% 15.43/2.50  --share_sel_clauses                     true
% 15.43/2.50  --reset_solvers                         false
% 15.43/2.50  --bc_imp_inh                            [conj_cone]
% 15.43/2.50  --conj_cone_tolerance                   3.
% 15.43/2.50  --extra_neg_conj                        none
% 15.43/2.50  --large_theory_mode                     true
% 15.43/2.50  --prolific_symb_bound                   200
% 15.43/2.50  --lt_threshold                          2000
% 15.43/2.50  --clause_weak_htbl                      true
% 15.43/2.50  --gc_record_bc_elim                     false
% 15.43/2.50  
% 15.43/2.50  ------ Preprocessing Options
% 15.43/2.50  
% 15.43/2.50  --preprocessing_flag                    true
% 15.43/2.50  --time_out_prep_mult                    0.1
% 15.43/2.50  --splitting_mode                        input
% 15.43/2.50  --splitting_grd                         true
% 15.43/2.50  --splitting_cvd                         false
% 15.43/2.50  --splitting_cvd_svl                     false
% 15.43/2.50  --splitting_nvd                         32
% 15.43/2.50  --sub_typing                            true
% 15.43/2.50  --prep_gs_sim                           true
% 15.43/2.50  --prep_unflatten                        true
% 15.43/2.50  --prep_res_sim                          true
% 15.43/2.50  --prep_upred                            true
% 15.43/2.50  --prep_sem_filter                       exhaustive
% 15.43/2.50  --prep_sem_filter_out                   false
% 15.43/2.50  --pred_elim                             true
% 15.43/2.50  --res_sim_input                         true
% 15.43/2.50  --eq_ax_congr_red                       true
% 15.43/2.50  --pure_diseq_elim                       true
% 15.43/2.50  --brand_transform                       false
% 15.43/2.50  --non_eq_to_eq                          false
% 15.43/2.50  --prep_def_merge                        true
% 15.43/2.50  --prep_def_merge_prop_impl              false
% 15.43/2.50  --prep_def_merge_mbd                    true
% 15.43/2.50  --prep_def_merge_tr_red                 false
% 15.43/2.50  --prep_def_merge_tr_cl                  false
% 15.43/2.50  --smt_preprocessing                     true
% 15.43/2.50  --smt_ac_axioms                         fast
% 15.43/2.50  --preprocessed_out                      false
% 15.43/2.50  --preprocessed_stats                    false
% 15.43/2.50  
% 15.43/2.50  ------ Abstraction refinement Options
% 15.43/2.50  
% 15.43/2.50  --abstr_ref                             []
% 15.43/2.50  --abstr_ref_prep                        false
% 15.43/2.50  --abstr_ref_until_sat                   false
% 15.43/2.50  --abstr_ref_sig_restrict                funpre
% 15.43/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.43/2.50  --abstr_ref_under                       []
% 15.43/2.50  
% 15.43/2.50  ------ SAT Options
% 15.43/2.50  
% 15.43/2.50  --sat_mode                              false
% 15.43/2.50  --sat_fm_restart_options                ""
% 15.43/2.50  --sat_gr_def                            false
% 15.43/2.50  --sat_epr_types                         true
% 15.43/2.50  --sat_non_cyclic_types                  false
% 15.43/2.50  --sat_finite_models                     false
% 15.43/2.50  --sat_fm_lemmas                         false
% 15.43/2.50  --sat_fm_prep                           false
% 15.43/2.50  --sat_fm_uc_incr                        true
% 15.43/2.50  --sat_out_model                         small
% 15.43/2.50  --sat_out_clauses                       false
% 15.43/2.50  
% 15.43/2.50  ------ QBF Options
% 15.43/2.50  
% 15.43/2.50  --qbf_mode                              false
% 15.43/2.50  --qbf_elim_univ                         false
% 15.43/2.50  --qbf_dom_inst                          none
% 15.43/2.50  --qbf_dom_pre_inst                      false
% 15.43/2.50  --qbf_sk_in                             false
% 15.43/2.50  --qbf_pred_elim                         true
% 15.43/2.50  --qbf_split                             512
% 15.43/2.50  
% 15.43/2.50  ------ BMC1 Options
% 15.43/2.50  
% 15.43/2.50  --bmc1_incremental                      false
% 15.43/2.50  --bmc1_axioms                           reachable_all
% 15.43/2.50  --bmc1_min_bound                        0
% 15.43/2.50  --bmc1_max_bound                        -1
% 15.43/2.50  --bmc1_max_bound_default                -1
% 15.43/2.50  --bmc1_symbol_reachability              true
% 15.43/2.50  --bmc1_property_lemmas                  false
% 15.43/2.50  --bmc1_k_induction                      false
% 15.43/2.50  --bmc1_non_equiv_states                 false
% 15.43/2.50  --bmc1_deadlock                         false
% 15.43/2.50  --bmc1_ucm                              false
% 15.43/2.50  --bmc1_add_unsat_core                   none
% 15.43/2.50  --bmc1_unsat_core_children              false
% 15.43/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.43/2.50  --bmc1_out_stat                         full
% 15.43/2.50  --bmc1_ground_init                      false
% 15.43/2.50  --bmc1_pre_inst_next_state              false
% 15.43/2.50  --bmc1_pre_inst_state                   false
% 15.43/2.50  --bmc1_pre_inst_reach_state             false
% 15.43/2.50  --bmc1_out_unsat_core                   false
% 15.43/2.50  --bmc1_aig_witness_out                  false
% 15.43/2.50  --bmc1_verbose                          false
% 15.43/2.50  --bmc1_dump_clauses_tptp                false
% 15.43/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.43/2.50  --bmc1_dump_file                        -
% 15.43/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.43/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.43/2.50  --bmc1_ucm_extend_mode                  1
% 15.43/2.50  --bmc1_ucm_init_mode                    2
% 15.43/2.50  --bmc1_ucm_cone_mode                    none
% 15.43/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.43/2.50  --bmc1_ucm_relax_model                  4
% 15.43/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.43/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.43/2.50  --bmc1_ucm_layered_model                none
% 15.43/2.50  --bmc1_ucm_max_lemma_size               10
% 15.43/2.50  
% 15.43/2.50  ------ AIG Options
% 15.43/2.50  
% 15.43/2.50  --aig_mode                              false
% 15.43/2.50  
% 15.43/2.50  ------ Instantiation Options
% 15.43/2.50  
% 15.43/2.50  --instantiation_flag                    true
% 15.43/2.50  --inst_sos_flag                         false
% 15.43/2.50  --inst_sos_phase                        true
% 15.43/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.43/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.43/2.50  --inst_lit_sel_side                     none
% 15.43/2.50  --inst_solver_per_active                1400
% 15.43/2.50  --inst_solver_calls_frac                1.
% 15.43/2.50  --inst_passive_queue_type               priority_queues
% 15.43/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.43/2.50  --inst_passive_queues_freq              [25;2]
% 15.43/2.50  --inst_dismatching                      true
% 15.43/2.50  --inst_eager_unprocessed_to_passive     true
% 15.43/2.50  --inst_prop_sim_given                   true
% 15.43/2.50  --inst_prop_sim_new                     false
% 15.43/2.50  --inst_subs_new                         false
% 15.43/2.50  --inst_eq_res_simp                      false
% 15.43/2.50  --inst_subs_given                       false
% 15.43/2.50  --inst_orphan_elimination               true
% 15.43/2.50  --inst_learning_loop_flag               true
% 15.43/2.50  --inst_learning_start                   3000
% 15.43/2.50  --inst_learning_factor                  2
% 15.43/2.50  --inst_start_prop_sim_after_learn       3
% 15.43/2.50  --inst_sel_renew                        solver
% 15.43/2.50  --inst_lit_activity_flag                true
% 15.43/2.50  --inst_restr_to_given                   false
% 15.43/2.50  --inst_activity_threshold               500
% 15.43/2.50  --inst_out_proof                        true
% 15.43/2.50  
% 15.43/2.50  ------ Resolution Options
% 15.43/2.50  
% 15.43/2.50  --resolution_flag                       false
% 15.43/2.50  --res_lit_sel                           adaptive
% 15.43/2.50  --res_lit_sel_side                      none
% 15.43/2.50  --res_ordering                          kbo
% 15.43/2.50  --res_to_prop_solver                    active
% 15.43/2.50  --res_prop_simpl_new                    false
% 15.43/2.50  --res_prop_simpl_given                  true
% 15.43/2.50  --res_passive_queue_type                priority_queues
% 15.43/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.43/2.50  --res_passive_queues_freq               [15;5]
% 15.43/2.50  --res_forward_subs                      full
% 15.43/2.50  --res_backward_subs                     full
% 15.43/2.50  --res_forward_subs_resolution           true
% 15.43/2.50  --res_backward_subs_resolution          true
% 15.43/2.50  --res_orphan_elimination                true
% 15.43/2.50  --res_time_limit                        2.
% 15.43/2.50  --res_out_proof                         true
% 15.43/2.50  
% 15.43/2.50  ------ Superposition Options
% 15.43/2.50  
% 15.43/2.50  --superposition_flag                    true
% 15.43/2.50  --sup_passive_queue_type                priority_queues
% 15.43/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.43/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.43/2.50  --demod_completeness_check              fast
% 15.43/2.50  --demod_use_ground                      true
% 15.43/2.50  --sup_to_prop_solver                    passive
% 15.43/2.50  --sup_prop_simpl_new                    true
% 15.43/2.50  --sup_prop_simpl_given                  true
% 15.43/2.50  --sup_fun_splitting                     false
% 15.43/2.50  --sup_smt_interval                      50000
% 15.43/2.50  
% 15.43/2.50  ------ Superposition Simplification Setup
% 15.43/2.50  
% 15.43/2.50  --sup_indices_passive                   []
% 15.43/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.43/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.43/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.43/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.43/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.43/2.50  --sup_full_bw                           [BwDemod]
% 15.43/2.50  --sup_immed_triv                        [TrivRules]
% 15.43/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.43/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.43/2.50  --sup_immed_bw_main                     []
% 15.43/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.43/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.43/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.43/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.43/2.50  
% 15.43/2.50  ------ Combination Options
% 15.43/2.50  
% 15.43/2.50  --comb_res_mult                         3
% 15.43/2.50  --comb_sup_mult                         2
% 15.43/2.50  --comb_inst_mult                        10
% 15.43/2.50  
% 15.43/2.50  ------ Debug Options
% 15.43/2.50  
% 15.43/2.50  --dbg_backtrace                         false
% 15.43/2.50  --dbg_dump_prop_clauses                 false
% 15.43/2.50  --dbg_dump_prop_clauses_file            -
% 15.43/2.50  --dbg_out_stat                          false
% 15.43/2.50  
% 15.43/2.50  
% 15.43/2.50  
% 15.43/2.50  
% 15.43/2.50  ------ Proving...
% 15.43/2.50  
% 15.43/2.50  
% 15.43/2.50  % SZS status Theorem for theBenchmark.p
% 15.43/2.50  
% 15.43/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.43/2.50  
% 15.43/2.50  fof(f23,conjecture,(
% 15.43/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f24,negated_conjecture,(
% 15.43/2.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 15.43/2.50    inference(negated_conjecture,[],[f23])).
% 15.43/2.50  
% 15.43/2.50  fof(f54,plain,(
% 15.43/2.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.43/2.50    inference(ennf_transformation,[],[f24])).
% 15.43/2.50  
% 15.43/2.50  fof(f55,plain,(
% 15.43/2.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.43/2.50    inference(flattening,[],[f54])).
% 15.43/2.50  
% 15.43/2.50  fof(f62,plain,(
% 15.43/2.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 15.43/2.50    introduced(choice_axiom,[])).
% 15.43/2.50  
% 15.43/2.50  fof(f61,plain,(
% 15.43/2.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 15.43/2.50    introduced(choice_axiom,[])).
% 15.43/2.50  
% 15.43/2.50  fof(f63,plain,(
% 15.43/2.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 15.43/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f62,f61])).
% 15.43/2.50  
% 15.43/2.50  fof(f103,plain,(
% 15.43/2.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f106,plain,(
% 15.43/2.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f19,axiom,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f48,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.43/2.50    inference(ennf_transformation,[],[f19])).
% 15.43/2.50  
% 15.43/2.50  fof(f49,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.43/2.50    inference(flattening,[],[f48])).
% 15.43/2.50  
% 15.43/2.50  fof(f94,plain,(
% 15.43/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f49])).
% 15.43/2.50  
% 15.43/2.50  fof(f104,plain,(
% 15.43/2.50    v1_funct_1(sK3)),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f101,plain,(
% 15.43/2.50    v1_funct_1(sK2)),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f16,axiom,(
% 15.43/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f44,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.43/2.50    inference(ennf_transformation,[],[f16])).
% 15.43/2.50  
% 15.43/2.50  fof(f45,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.43/2.50    inference(flattening,[],[f44])).
% 15.43/2.50  
% 15.43/2.50  fof(f59,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.43/2.50    inference(nnf_transformation,[],[f45])).
% 15.43/2.50  
% 15.43/2.50  fof(f85,plain,(
% 15.43/2.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.43/2.50    inference(cnf_transformation,[],[f59])).
% 15.43/2.50  
% 15.43/2.50  fof(f108,plain,(
% 15.43/2.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f17,axiom,(
% 15.43/2.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f87,plain,(
% 15.43/2.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.43/2.50    inference(cnf_transformation,[],[f17])).
% 15.43/2.50  
% 15.43/2.50  fof(f20,axiom,(
% 15.43/2.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f95,plain,(
% 15.43/2.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f20])).
% 15.43/2.50  
% 15.43/2.50  fof(f119,plain,(
% 15.43/2.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.43/2.50    inference(definition_unfolding,[],[f87,f95])).
% 15.43/2.50  
% 15.43/2.50  fof(f15,axiom,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f42,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.43/2.50    inference(ennf_transformation,[],[f15])).
% 15.43/2.50  
% 15.43/2.50  fof(f43,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.43/2.50    inference(flattening,[],[f42])).
% 15.43/2.50  
% 15.43/2.50  fof(f84,plain,(
% 15.43/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.43/2.50    inference(cnf_transformation,[],[f43])).
% 15.43/2.50  
% 15.43/2.50  fof(f12,axiom,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f38,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.43/2.50    inference(ennf_transformation,[],[f12])).
% 15.43/2.50  
% 15.43/2.50  fof(f39,plain,(
% 15.43/2.50    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.43/2.50    inference(flattening,[],[f38])).
% 15.43/2.50  
% 15.43/2.50  fof(f81,plain,(
% 15.43/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.43/2.50    inference(cnf_transformation,[],[f39])).
% 15.43/2.50  
% 15.43/2.50  fof(f107,plain,(
% 15.43/2.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f22,axiom,(
% 15.43/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f52,plain,(
% 15.43/2.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.43/2.50    inference(ennf_transformation,[],[f22])).
% 15.43/2.50  
% 15.43/2.50  fof(f53,plain,(
% 15.43/2.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.43/2.50    inference(flattening,[],[f52])).
% 15.43/2.50  
% 15.43/2.50  fof(f100,plain,(
% 15.43/2.50    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f53])).
% 15.43/2.50  
% 15.43/2.50  fof(f102,plain,(
% 15.43/2.50    v1_funct_2(sK2,sK0,sK1)),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f109,plain,(
% 15.43/2.50    v2_funct_1(sK2)),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f111,plain,(
% 15.43/2.50    k1_xboole_0 != sK1),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f9,axiom,(
% 15.43/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f33,plain,(
% 15.43/2.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.43/2.50    inference(ennf_transformation,[],[f9])).
% 15.43/2.50  
% 15.43/2.50  fof(f34,plain,(
% 15.43/2.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.43/2.50    inference(flattening,[],[f33])).
% 15.43/2.50  
% 15.43/2.50  fof(f77,plain,(
% 15.43/2.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f34])).
% 15.43/2.50  
% 15.43/2.50  fof(f2,axiom,(
% 15.43/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f26,plain,(
% 15.43/2.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.43/2.50    inference(ennf_transformation,[],[f2])).
% 15.43/2.50  
% 15.43/2.50  fof(f67,plain,(
% 15.43/2.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f26])).
% 15.43/2.50  
% 15.43/2.50  fof(f4,axiom,(
% 15.43/2.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f70,plain,(
% 15.43/2.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.43/2.50    inference(cnf_transformation,[],[f4])).
% 15.43/2.50  
% 15.43/2.50  fof(f7,axiom,(
% 15.43/2.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ((k5_relat_1(X2,X3) = k6_relat_1(X0) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & k2_relat_1(X1) = X0) => X1 = X3))))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f29,plain,(
% 15.43/2.50    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0)) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.43/2.50    inference(ennf_transformation,[],[f7])).
% 15.43/2.50  
% 15.43/2.50  fof(f30,plain,(
% 15.43/2.50    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.43/2.50    inference(flattening,[],[f29])).
% 15.43/2.50  
% 15.43/2.50  fof(f74,plain,(
% 15.43/2.50    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_relat_1(X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f30])).
% 15.43/2.50  
% 15.43/2.50  fof(f115,plain,(
% 15.43/2.50    ( ! [X2,X0,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(X0) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | k2_relat_1(X1) != X0 | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.43/2.50    inference(definition_unfolding,[],[f74,f95,f95])).
% 15.43/2.50  
% 15.43/2.50  fof(f122,plain,(
% 15.43/2.50    ( ! [X2,X3,X1] : (X1 = X3 | k5_relat_1(X2,X3) != k6_partfun1(k2_relat_1(X1)) | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.43/2.50    inference(equality_resolution,[],[f115])).
% 15.43/2.50  
% 15.43/2.50  fof(f10,axiom,(
% 15.43/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f35,plain,(
% 15.43/2.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.43/2.50    inference(ennf_transformation,[],[f10])).
% 15.43/2.50  
% 15.43/2.50  fof(f36,plain,(
% 15.43/2.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.43/2.50    inference(flattening,[],[f35])).
% 15.43/2.50  
% 15.43/2.50  fof(f78,plain,(
% 15.43/2.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f36])).
% 15.43/2.50  
% 15.43/2.50  fof(f118,plain,(
% 15.43/2.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.43/2.50    inference(definition_unfolding,[],[f78,f95])).
% 15.43/2.50  
% 15.43/2.50  fof(f99,plain,(
% 15.43/2.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f53])).
% 15.43/2.50  
% 15.43/2.50  fof(f21,axiom,(
% 15.43/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f50,plain,(
% 15.43/2.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 15.43/2.50    inference(ennf_transformation,[],[f21])).
% 15.43/2.50  
% 15.43/2.50  fof(f51,plain,(
% 15.43/2.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 15.43/2.50    inference(flattening,[],[f50])).
% 15.43/2.50  
% 15.43/2.50  fof(f96,plain,(
% 15.43/2.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f51])).
% 15.43/2.50  
% 15.43/2.50  fof(f98,plain,(
% 15.43/2.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f51])).
% 15.43/2.50  
% 15.43/2.50  fof(f18,axiom,(
% 15.43/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f46,plain,(
% 15.43/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.43/2.50    inference(ennf_transformation,[],[f18])).
% 15.43/2.50  
% 15.43/2.50  fof(f47,plain,(
% 15.43/2.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.43/2.50    inference(flattening,[],[f46])).
% 15.43/2.50  
% 15.43/2.50  fof(f60,plain,(
% 15.43/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.43/2.50    inference(nnf_transformation,[],[f47])).
% 15.43/2.50  
% 15.43/2.50  fof(f88,plain,(
% 15.43/2.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.43/2.50    inference(cnf_transformation,[],[f60])).
% 15.43/2.50  
% 15.43/2.50  fof(f13,axiom,(
% 15.43/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f40,plain,(
% 15.43/2.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.43/2.50    inference(ennf_transformation,[],[f13])).
% 15.43/2.50  
% 15.43/2.50  fof(f82,plain,(
% 15.43/2.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.43/2.50    inference(cnf_transformation,[],[f40])).
% 15.43/2.50  
% 15.43/2.50  fof(f105,plain,(
% 15.43/2.50    v1_funct_2(sK3,sK1,sK0)),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f110,plain,(
% 15.43/2.50    k1_xboole_0 != sK0),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  fof(f1,axiom,(
% 15.43/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.43/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.43/2.50  
% 15.43/2.50  fof(f56,plain,(
% 15.43/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.43/2.50    inference(nnf_transformation,[],[f1])).
% 15.43/2.50  
% 15.43/2.50  fof(f57,plain,(
% 15.43/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.43/2.50    inference(flattening,[],[f56])).
% 15.43/2.50  
% 15.43/2.50  fof(f64,plain,(
% 15.43/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.43/2.50    inference(cnf_transformation,[],[f57])).
% 15.43/2.50  
% 15.43/2.50  fof(f121,plain,(
% 15.43/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.43/2.50    inference(equality_resolution,[],[f64])).
% 15.43/2.50  
% 15.43/2.50  fof(f66,plain,(
% 15.43/2.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.43/2.50    inference(cnf_transformation,[],[f57])).
% 15.43/2.50  
% 15.43/2.50  fof(f112,plain,(
% 15.43/2.50    k2_funct_1(sK2) != sK3),
% 15.43/2.50    inference(cnf_transformation,[],[f63])).
% 15.43/2.50  
% 15.43/2.50  cnf(c_45,negated_conjecture,
% 15.43/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.43/2.50      inference(cnf_transformation,[],[f103]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2436,plain,
% 15.43/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_42,negated_conjecture,
% 15.43/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 15.43/2.50      inference(cnf_transformation,[],[f106]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2439,plain,
% 15.43/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_30,plain,
% 15.43/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X3)
% 15.43/2.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.43/2.50      inference(cnf_transformation,[],[f94]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2446,plain,
% 15.43/2.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.43/2.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.43/2.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.43/2.50      | v1_funct_1(X5) != iProver_top
% 15.43/2.50      | v1_funct_1(X4) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10126,plain,
% 15.43/2.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.43/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.43/2.50      | v1_funct_1(X2) != iProver_top
% 15.43/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_2439,c_2446]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_44,negated_conjecture,
% 15.43/2.50      ( v1_funct_1(sK3) ),
% 15.43/2.50      inference(cnf_transformation,[],[f104]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_51,plain,
% 15.43/2.50      ( v1_funct_1(sK3) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10568,plain,
% 15.43/2.50      ( v1_funct_1(X2) != iProver_top
% 15.43/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.43/2.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_10126,c_51]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10569,plain,
% 15.43/2.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.43/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.43/2.50      | v1_funct_1(X2) != iProver_top ),
% 15.43/2.50      inference(renaming,[status(thm)],[c_10568]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10580,plain,
% 15.43/2.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_2436,c_10569]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_47,negated_conjecture,
% 15.43/2.50      ( v1_funct_1(sK2) ),
% 15.43/2.50      inference(cnf_transformation,[],[f101]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3030,plain,
% 15.43/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(sK3)
% 15.43/2.50      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_30]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3529,plain,
% 15.43/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 15.43/2.50      | ~ v1_funct_1(sK3)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_3030]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_4177,plain,
% 15.43/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.43/2.50      | ~ v1_funct_1(sK3)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_3529]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_5625,plain,
% 15.43/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.43/2.50      | ~ v1_funct_1(sK3)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_4177]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10736,plain,
% 15.43/2.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_10580,c_47,c_45,c_44,c_42,c_5625]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_22,plain,
% 15.43/2.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.43/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.43/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.43/2.50      | X2 = X3 ),
% 15.43/2.50      inference(cnf_transformation,[],[f85]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_40,negated_conjecture,
% 15.43/2.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 15.43/2.50      inference(cnf_transformation,[],[f108]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_491,plain,
% 15.43/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | X0 = X3
% 15.43/2.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X3
% 15.43/2.50      | k6_partfun1(sK0) != X0
% 15.43/2.50      | sK0 != X2
% 15.43/2.50      | sK0 != X1 ),
% 15.43/2.50      inference(resolution_lifted,[status(thm)],[c_22,c_40]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_492,plain,
% 15.43/2.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.43/2.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.43/2.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.43/2.50      inference(unflattening,[status(thm)],[c_491]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_23,plain,
% 15.43/2.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.43/2.50      inference(cnf_transformation,[],[f119]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_500,plain,
% 15.43/2.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 15.43/2.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 15.43/2.50      inference(forward_subsumption_resolution,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_492,c_23]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2432,plain,
% 15.43/2.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 15.43/2.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10739,plain,
% 15.43/2.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 15.43/2.50      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 15.43/2.50      inference(demodulation,[status(thm)],[c_10736,c_2432]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_50,plain,
% 15.43/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_53,plain,
% 15.43/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_20,plain,
% 15.43/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.43/2.50      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.43/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2454,plain,
% 15.43/2.50      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.43/2.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.43/2.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_8114,plain,
% 15.43/2.50      ( k4_relset_1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 15.43/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_2439,c_2454]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_9242,plain,
% 15.43/2.50      ( k4_relset_1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_2436,c_8114]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_17,plain,
% 15.43/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.43/2.50      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 15.43/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2457,plain,
% 15.43/2.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.43/2.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 15.43/2.50      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_9549,plain,
% 15.43/2.50      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 15.43/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.43/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_9242,c_2457]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_12411,plain,
% 15.43/2.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_10739,c_50,c_53,c_9549]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_41,negated_conjecture,
% 15.43/2.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 15.43/2.50      inference(cnf_transformation,[],[f107]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_34,plain,
% 15.43/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.43/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | ~ v2_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | k2_relset_1(X1,X2,X0) != X2
% 15.43/2.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 15.43/2.50      | k1_xboole_0 = X2 ),
% 15.43/2.50      inference(cnf_transformation,[],[f100]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2442,plain,
% 15.43/2.50      ( k2_relset_1(X0,X1,X2) != X1
% 15.43/2.50      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 15.43/2.50      | k1_xboole_0 = X1
% 15.43/2.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.43/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.43/2.50      | v2_funct_1(X2) != iProver_top
% 15.43/2.50      | v1_funct_1(X2) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_5575,plain,
% 15.43/2.50      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 15.43/2.50      | sK1 = k1_xboole_0
% 15.43/2.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.43/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.43/2.50      | v2_funct_1(sK2) != iProver_top
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_41,c_2442]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_46,negated_conjecture,
% 15.43/2.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 15.43/2.50      inference(cnf_transformation,[],[f102]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_39,negated_conjecture,
% 15.43/2.50      ( v2_funct_1(sK2) ),
% 15.43/2.50      inference(cnf_transformation,[],[f109]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_37,negated_conjecture,
% 15.43/2.50      ( k1_xboole_0 != sK1 ),
% 15.43/2.50      inference(cnf_transformation,[],[f111]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3040,plain,
% 15.43/2.50      ( ~ v1_funct_2(X0,X1,sK1)
% 15.43/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 15.43/2.50      | ~ v2_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | k2_relset_1(X1,sK1,X0) != sK1
% 15.43/2.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 15.43/2.50      | k1_xboole_0 = sK1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_34]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3428,plain,
% 15.43/2.50      ( ~ v1_funct_2(sK2,X0,sK1)
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 15.43/2.50      | ~ v2_funct_1(sK2)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k2_relset_1(X0,sK1,sK2) != sK1
% 15.43/2.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 15.43/2.50      | k1_xboole_0 = sK1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_3040]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_4006,plain,
% 15.43/2.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.43/2.50      | ~ v2_funct_1(sK2)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 15.43/2.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 15.43/2.50      | k1_xboole_0 = sK1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_3428]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_5891,plain,
% 15.43/2.50      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_5575,c_47,c_46,c_45,c_41,c_39,c_37,c_4006]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2440,plain,
% 15.43/2.50      ( v2_funct_1(sK2) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_12,plain,
% 15.43/2.50      ( ~ v2_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | ~ v1_relat_1(X0)
% 15.43/2.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 15.43/2.50      inference(cnf_transformation,[],[f77]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2461,plain,
% 15.43/2.50      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 15.43/2.50      | v2_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_5777,plain,
% 15.43/2.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top
% 15.43/2.50      | v1_relat_1(sK2) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_2440,c_2461]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_931,plain,
% 15.43/2.50      ( ~ v1_funct_1(X0)
% 15.43/2.50      | ~ v1_relat_1(X0)
% 15.43/2.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 15.43/2.50      | sK2 != X0 ),
% 15.43/2.50      inference(resolution_lifted,[status(thm)],[c_12,c_39]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_932,plain,
% 15.43/2.50      ( ~ v1_funct_1(sK2)
% 15.43/2.50      | ~ v1_relat_1(sK2)
% 15.43/2.50      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 15.43/2.50      inference(unflattening,[status(thm)],[c_931]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3,plain,
% 15.43/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.43/2.50      | ~ v1_relat_1(X1)
% 15.43/2.50      | v1_relat_1(X0) ),
% 15.43/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2815,plain,
% 15.43/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | v1_relat_1(X0)
% 15.43/2.50      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3210,plain,
% 15.43/2.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.43/2.50      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 15.43/2.50      | v1_relat_1(sK2) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_2815]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_6,plain,
% 15.43/2.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.43/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3674,plain,
% 15.43/2.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_6022,plain,
% 15.43/2.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_5777,c_47,c_45,c_932,c_3210,c_3674]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10,plain,
% 15.43/2.50      ( ~ v1_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X1)
% 15.43/2.50      | ~ v1_funct_1(X2)
% 15.43/2.50      | ~ v1_relat_1(X2)
% 15.43/2.50      | ~ v1_relat_1(X0)
% 15.43/2.50      | ~ v1_relat_1(X1)
% 15.43/2.50      | X0 = X2
% 15.43/2.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X2))
% 15.43/2.50      | k5_relat_1(X2,X1) != k6_partfun1(k1_relat_1(X0)) ),
% 15.43/2.50      inference(cnf_transformation,[],[f122]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2463,plain,
% 15.43/2.50      ( X0 = X1
% 15.43/2.50      | k5_relat_1(X2,X0) != k6_partfun1(k2_relat_1(X1))
% 15.43/2.50      | k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X0))
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_funct_1(X1) != iProver_top
% 15.43/2.50      | v1_funct_1(X2) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top
% 15.43/2.50      | v1_relat_1(X2) != iProver_top
% 15.43/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10213,plain,
% 15.43/2.50      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(sK2))
% 15.43/2.50      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
% 15.43/2.50      | k2_funct_1(sK2) = X1
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_funct_1(X1) != iProver_top
% 15.43/2.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top
% 15.43/2.50      | v1_relat_1(X1) != iProver_top
% 15.43/2.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_6022,c_2463]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_15,plain,
% 15.43/2.50      ( ~ v2_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | ~ v1_relat_1(X0)
% 15.43/2.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 15.43/2.50      inference(cnf_transformation,[],[f118]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2458,plain,
% 15.43/2.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 15.43/2.50      | v2_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_6620,plain,
% 15.43/2.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top
% 15.43/2.50      | v1_relat_1(sK2) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_2440,c_2458]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_35,plain,
% 15.43/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.43/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | ~ v2_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | k2_relset_1(X1,X2,X0) != X2
% 15.43/2.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 15.43/2.50      | k1_xboole_0 = X2 ),
% 15.43/2.50      inference(cnf_transformation,[],[f99]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2441,plain,
% 15.43/2.50      ( k2_relset_1(X0,X1,X2) != X1
% 15.43/2.50      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 15.43/2.50      | k1_xboole_0 = X1
% 15.43/2.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.43/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.43/2.50      | v2_funct_1(X2) != iProver_top
% 15.43/2.50      | v1_funct_1(X2) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_4427,plain,
% 15.43/2.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 15.43/2.50      | sK1 = k1_xboole_0
% 15.43/2.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.43/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.43/2.50      | v2_funct_1(sK2) != iProver_top
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_41,c_2441]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3050,plain,
% 15.43/2.50      ( ~ v1_funct_2(X0,X1,sK1)
% 15.43/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 15.43/2.50      | ~ v2_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | k2_relset_1(X1,sK1,X0) != sK1
% 15.43/2.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 15.43/2.50      | k1_xboole_0 = sK1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_35]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3493,plain,
% 15.43/2.50      ( ~ v1_funct_2(sK2,X0,sK1)
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 15.43/2.50      | ~ v2_funct_1(sK2)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k2_relset_1(X0,sK1,sK2) != sK1
% 15.43/2.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 15.43/2.50      | k1_xboole_0 = sK1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_3050]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_4025,plain,
% 15.43/2.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.43/2.50      | ~ v2_funct_1(sK2)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 15.43/2.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 15.43/2.50      | k1_xboole_0 = sK1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_3493]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_4732,plain,
% 15.43/2.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_4427,c_47,c_46,c_45,c_41,c_39,c_37,c_4025]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_6621,plain,
% 15.43/2.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top
% 15.43/2.50      | v1_relat_1(sK2) != iProver_top ),
% 15.43/2.50      inference(light_normalisation,[status(thm)],[c_6620,c_4732]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_48,plain,
% 15.43/2.50      ( v1_funct_1(sK2) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3211,plain,
% 15.43/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.43/2.50      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.43/2.50      | v1_relat_1(sK2) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_3210]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3675,plain,
% 15.43/2.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_3674]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_6935,plain,
% 15.43/2.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_6621,c_48,c_50,c_3211,c_3675]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_10223,plain,
% 15.43/2.50      ( k5_relat_1(X0,X1) != k6_partfun1(sK0)
% 15.43/2.50      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
% 15.43/2.50      | k2_funct_1(sK2) = X1
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_funct_1(X1) != iProver_top
% 15.43/2.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top
% 15.43/2.50      | v1_relat_1(X1) != iProver_top
% 15.43/2.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 15.43/2.50      inference(light_normalisation,[status(thm)],[c_10213,c_6935]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_49,plain,
% 15.43/2.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_55,plain,
% 15.43/2.50      ( v2_funct_1(sK2) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_33,plain,
% 15.43/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.43/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | ~ v2_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | v1_funct_1(k2_funct_1(X0))
% 15.43/2.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 15.43/2.50      inference(cnf_transformation,[],[f96]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2971,plain,
% 15.43/2.50      ( ~ v1_funct_2(sK2,X0,X1)
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.43/2.50      | ~ v2_funct_1(sK2)
% 15.43/2.50      | v1_funct_1(k2_funct_1(sK2))
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_33]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3369,plain,
% 15.43/2.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.43/2.50      | ~ v2_funct_1(sK2)
% 15.43/2.50      | v1_funct_1(k2_funct_1(sK2))
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_2971]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3370,plain,
% 15.43/2.50      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 15.43/2.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.43/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.43/2.50      | v2_funct_1(sK2) != iProver_top
% 15.43/2.50      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_3369]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_31,plain,
% 15.43/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.43/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 15.43/2.50      | ~ v2_funct_1(X0)
% 15.43/2.50      | ~ v1_funct_1(X0)
% 15.43/2.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 15.43/2.50      inference(cnf_transformation,[],[f98]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3024,plain,
% 15.43/2.50      ( ~ v1_funct_2(sK2,X0,X1)
% 15.43/2.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.43/2.50      | ~ v2_funct_1(sK2)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k2_relset_1(X0,X1,sK2) != X1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_31]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3422,plain,
% 15.43/2.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 15.43/2.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.43/2.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.43/2.50      | ~ v2_funct_1(sK2)
% 15.43/2.50      | ~ v1_funct_1(sK2)
% 15.43/2.50      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_3024]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3423,plain,
% 15.43/2.50      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 15.43/2.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 15.43/2.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 15.43/2.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.43/2.50      | v2_funct_1(sK2) != iProver_top
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_3422]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3671,plain,
% 15.43/2.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_6]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3672,plain,
% 15.43/2.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_3671]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3957,plain,
% 15.43/2.50      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.43/2.50      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 15.43/2.50      | v1_relat_1(k2_funct_1(sK2)) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_2815]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3974,plain,
% 15.43/2.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.43/2.50      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 15.43/2.50      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_3957]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_58205,plain,
% 15.43/2.50      ( v1_relat_1(X1) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top
% 15.43/2.50      | k5_relat_1(X0,X1) != k6_partfun1(sK0)
% 15.43/2.50      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
% 15.43/2.50      | k2_funct_1(sK2) = X1
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_funct_1(X1) != iProver_top ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_10223,c_48,c_49,c_50,c_41,c_55,c_3370,c_3423,c_3672,
% 15.43/2.50                 c_3974]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_58206,plain,
% 15.43/2.50      ( k5_relat_1(X0,X1) != k6_partfun1(sK0)
% 15.43/2.50      | k5_relat_1(k2_funct_1(sK2),X0) != k6_partfun1(k1_relat_1(X1))
% 15.43/2.50      | k2_funct_1(sK2) = X1
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_funct_1(X1) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top
% 15.43/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.43/2.50      inference(renaming,[status(thm)],[c_58205]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_58218,plain,
% 15.43/2.50      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 15.43/2.50      | k2_funct_1(sK2) = X0
% 15.43/2.50      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_funct_1(sK2) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top
% 15.43/2.50      | v1_relat_1(sK2) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_5891,c_58206]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_59432,plain,
% 15.43/2.50      ( v1_relat_1(X0) != iProver_top
% 15.43/2.50      | k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 15.43/2.50      | k2_funct_1(sK2) = X0
% 15.43/2.50      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 15.43/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_58218,c_48,c_50,c_3211,c_3675]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_59433,plain,
% 15.43/2.50      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 15.43/2.50      | k2_funct_1(sK2) = X0
% 15.43/2.50      | k6_partfun1(k1_relat_1(X0)) != k6_partfun1(sK1)
% 15.43/2.50      | v1_funct_1(X0) != iProver_top
% 15.43/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.43/2.50      inference(renaming,[status(thm)],[c_59432]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_59444,plain,
% 15.43/2.50      ( k2_funct_1(sK2) = sK3
% 15.43/2.50      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 15.43/2.50      | v1_funct_1(sK3) != iProver_top
% 15.43/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_12411,c_59433]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_29,plain,
% 15.43/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.43/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | k1_relset_1(X1,X2,X0) = X1
% 15.43/2.50      | k1_xboole_0 = X2 ),
% 15.43/2.50      inference(cnf_transformation,[],[f88]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2447,plain,
% 15.43/2.50      ( k1_relset_1(X0,X1,X2) = X0
% 15.43/2.50      | k1_xboole_0 = X1
% 15.43/2.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.43/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_6730,plain,
% 15.43/2.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 15.43/2.50      | sK0 = k1_xboole_0
% 15.43/2.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_2439,c_2447]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_18,plain,
% 15.43/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.43/2.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.43/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2456,plain,
% 15.43/2.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.43/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3565,plain,
% 15.43/2.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 15.43/2.50      inference(superposition,[status(thm)],[c_2439,c_2456]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_6739,plain,
% 15.43/2.50      ( k1_relat_1(sK3) = sK1
% 15.43/2.50      | sK0 = k1_xboole_0
% 15.43/2.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 15.43/2.50      inference(demodulation,[status(thm)],[c_6730,c_3565]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_43,negated_conjecture,
% 15.43/2.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 15.43/2.50      inference(cnf_transformation,[],[f105]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_52,plain,
% 15.43/2.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_38,negated_conjecture,
% 15.43/2.50      ( k1_xboole_0 != sK0 ),
% 15.43/2.50      inference(cnf_transformation,[],[f110]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2,plain,
% 15.43/2.50      ( r1_tarski(X0,X0) ),
% 15.43/2.50      inference(cnf_transformation,[],[f121]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_150,plain,
% 15.43/2.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_0,plain,
% 15.43/2.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.43/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_154,plain,
% 15.43/2.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.43/2.50      | k1_xboole_0 = k1_xboole_0 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_1795,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2888,plain,
% 15.43/2.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_1795]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_2889,plain,
% 15.43/2.50      ( sK0 != k1_xboole_0
% 15.43/2.50      | k1_xboole_0 = sK0
% 15.43/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_2888]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_7661,plain,
% 15.43/2.50      ( k1_relat_1(sK3) = sK1 ),
% 15.43/2.50      inference(global_propositional_subsumption,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_6739,c_52,c_38,c_150,c_154,c_2889]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_59449,plain,
% 15.43/2.50      ( k2_funct_1(sK2) = sK3
% 15.43/2.50      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 15.43/2.50      | v1_funct_1(sK3) != iProver_top
% 15.43/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.43/2.50      inference(light_normalisation,[status(thm)],[c_59444,c_7661]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_59450,plain,
% 15.43/2.50      ( k2_funct_1(sK2) = sK3
% 15.43/2.50      | v1_funct_1(sK3) != iProver_top
% 15.43/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.43/2.50      inference(equality_resolution_simp,[status(thm)],[c_59449]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3207,plain,
% 15.43/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 15.43/2.50      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 15.43/2.50      | v1_relat_1(sK3) ),
% 15.43/2.50      inference(instantiation,[status(thm)],[c_2815]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_3208,plain,
% 15.43/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 15.43/2.50      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 15.43/2.50      | v1_relat_1(sK3) = iProver_top ),
% 15.43/2.50      inference(predicate_to_equality,[status(thm)],[c_3207]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(c_36,negated_conjecture,
% 15.43/2.50      ( k2_funct_1(sK2) != sK3 ),
% 15.43/2.50      inference(cnf_transformation,[],[f112]) ).
% 15.43/2.50  
% 15.43/2.50  cnf(contradiction,plain,
% 15.43/2.50      ( $false ),
% 15.43/2.50      inference(minisat,
% 15.43/2.50                [status(thm)],
% 15.43/2.50                [c_59450,c_3672,c_3208,c_36,c_53,c_51]) ).
% 15.43/2.50  
% 15.43/2.50  
% 15.43/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.43/2.50  
% 15.43/2.50  ------                               Statistics
% 15.43/2.50  
% 15.43/2.50  ------ General
% 15.43/2.50  
% 15.43/2.50  abstr_ref_over_cycles:                  0
% 15.43/2.50  abstr_ref_under_cycles:                 0
% 15.43/2.50  gc_basic_clause_elim:                   0
% 15.43/2.50  forced_gc_time:                         0
% 15.43/2.50  parsing_time:                           0.011
% 15.43/2.50  unif_index_cands_time:                  0.
% 15.43/2.50  unif_index_add_time:                    0.
% 15.43/2.50  orderings_time:                         0.
% 15.43/2.50  out_proof_time:                         0.023
% 15.43/2.50  total_time:                             1.692
% 15.43/2.50  num_of_symbols:                         55
% 15.43/2.50  num_of_terms:                           74835
% 15.43/2.50  
% 15.43/2.50  ------ Preprocessing
% 15.43/2.50  
% 15.43/2.50  num_of_splits:                          0
% 15.43/2.50  num_of_split_atoms:                     0
% 15.43/2.50  num_of_reused_defs:                     0
% 15.43/2.50  num_eq_ax_congr_red:                    26
% 15.43/2.50  num_of_sem_filtered_clauses:            1
% 15.43/2.50  num_of_subtypes:                        0
% 15.43/2.50  monotx_restored_types:                  0
% 15.43/2.50  sat_num_of_epr_types:                   0
% 15.43/2.50  sat_num_of_non_cyclic_types:            0
% 15.43/2.50  sat_guarded_non_collapsed_types:        0
% 15.43/2.50  num_pure_diseq_elim:                    0
% 15.43/2.50  simp_replaced_by:                       0
% 15.43/2.50  res_preprocessed:                       213
% 15.43/2.50  prep_upred:                             0
% 15.43/2.50  prep_unflattend:                        26
% 15.43/2.50  smt_new_axioms:                         0
% 15.43/2.50  pred_elim_cands:                        6
% 15.43/2.50  pred_elim:                              2
% 15.43/2.50  pred_elim_cl:                           4
% 15.43/2.50  pred_elim_cycles:                       4
% 15.43/2.50  merged_defs:                            0
% 15.43/2.50  merged_defs_ncl:                        0
% 15.43/2.50  bin_hyper_res:                          0
% 15.43/2.50  prep_cycles:                            4
% 15.43/2.50  pred_elim_time:                         0.023
% 15.43/2.50  splitting_time:                         0.
% 15.43/2.50  sem_filter_time:                        0.
% 15.43/2.50  monotx_time:                            0.001
% 15.43/2.50  subtype_inf_time:                       0.
% 15.43/2.50  
% 15.43/2.50  ------ Problem properties
% 15.43/2.50  
% 15.43/2.50  clauses:                                43
% 15.43/2.50  conjectures:                            11
% 15.43/2.50  epr:                                    9
% 15.43/2.50  horn:                                   37
% 15.43/2.50  ground:                                 12
% 15.43/2.50  unary:                                  16
% 15.43/2.50  binary:                                 3
% 15.43/2.50  lits:                                   129
% 15.43/2.50  lits_eq:                                38
% 15.43/2.50  fd_pure:                                0
% 15.43/2.50  fd_pseudo:                              0
% 15.43/2.50  fd_cond:                                5
% 15.43/2.50  fd_pseudo_cond:                         2
% 15.43/2.50  ac_symbols:                             0
% 15.43/2.50  
% 15.43/2.50  ------ Propositional Solver
% 15.43/2.50  
% 15.43/2.50  prop_solver_calls:                      34
% 15.43/2.50  prop_fast_solver_calls:                 2921
% 15.43/2.50  smt_solver_calls:                       0
% 15.43/2.50  smt_fast_solver_calls:                  0
% 15.43/2.50  prop_num_of_clauses:                    21599
% 15.43/2.50  prop_preprocess_simplified:             36608
% 15.43/2.50  prop_fo_subsumed:                       261
% 15.43/2.50  prop_solver_time:                       0.
% 15.43/2.50  smt_solver_time:                        0.
% 15.43/2.50  smt_fast_solver_time:                   0.
% 15.43/2.50  prop_fast_solver_time:                  0.
% 15.43/2.50  prop_unsat_core_time:                   0.003
% 15.43/2.50  
% 15.43/2.50  ------ QBF
% 15.43/2.50  
% 15.43/2.50  qbf_q_res:                              0
% 15.43/2.50  qbf_num_tautologies:                    0
% 15.43/2.50  qbf_prep_cycles:                        0
% 15.43/2.50  
% 15.43/2.50  ------ BMC1
% 15.43/2.50  
% 15.43/2.50  bmc1_current_bound:                     -1
% 15.43/2.50  bmc1_last_solved_bound:                 -1
% 15.43/2.50  bmc1_unsat_core_size:                   -1
% 15.43/2.50  bmc1_unsat_core_parents_size:           -1
% 15.43/2.50  bmc1_merge_next_fun:                    0
% 15.43/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.43/2.50  
% 15.43/2.50  ------ Instantiation
% 15.43/2.50  
% 15.43/2.50  inst_num_of_clauses:                    5518
% 15.43/2.50  inst_num_in_passive:                    1790
% 15.43/2.50  inst_num_in_active:                     2302
% 15.43/2.50  inst_num_in_unprocessed:                1430
% 15.43/2.50  inst_num_of_loops:                      2470
% 15.43/2.50  inst_num_of_learning_restarts:          0
% 15.43/2.50  inst_num_moves_active_passive:          166
% 15.43/2.50  inst_lit_activity:                      0
% 15.43/2.50  inst_lit_activity_moves:                3
% 15.43/2.50  inst_num_tautologies:                   0
% 15.43/2.50  inst_num_prop_implied:                  0
% 15.43/2.50  inst_num_existing_simplified:           0
% 15.43/2.50  inst_num_eq_res_simplified:             0
% 15.43/2.50  inst_num_child_elim:                    0
% 15.43/2.50  inst_num_of_dismatching_blockings:      4887
% 15.43/2.50  inst_num_of_non_proper_insts:           6152
% 15.43/2.50  inst_num_of_duplicates:                 0
% 15.43/2.50  inst_inst_num_from_inst_to_res:         0
% 15.43/2.50  inst_dismatching_checking_time:         0.
% 15.43/2.50  
% 15.43/2.50  ------ Resolution
% 15.43/2.50  
% 15.43/2.50  res_num_of_clauses:                     0
% 15.43/2.50  res_num_in_passive:                     0
% 15.43/2.50  res_num_in_active:                      0
% 15.43/2.50  res_num_of_loops:                       217
% 15.43/2.50  res_forward_subset_subsumed:            331
% 15.43/2.50  res_backward_subset_subsumed:           8
% 15.43/2.50  res_forward_subsumed:                   0
% 15.43/2.50  res_backward_subsumed:                  0
% 15.43/2.50  res_forward_subsumption_resolution:     1
% 15.43/2.50  res_backward_subsumption_resolution:    0
% 15.43/2.50  res_clause_to_clause_subsumption:       3891
% 15.43/2.50  res_orphan_elimination:                 0
% 15.43/2.50  res_tautology_del:                      100
% 15.43/2.50  res_num_eq_res_simplified:              0
% 15.43/2.50  res_num_sel_changes:                    0
% 15.43/2.50  res_moves_from_active_to_pass:          0
% 15.43/2.50  
% 15.43/2.50  ------ Superposition
% 15.43/2.50  
% 15.43/2.50  sup_time_total:                         0.
% 15.43/2.50  sup_time_generating:                    0.
% 15.43/2.50  sup_time_sim_full:                      0.
% 15.43/2.50  sup_time_sim_immed:                     0.
% 15.43/2.50  
% 15.43/2.50  sup_num_of_clauses:                     2122
% 15.43/2.50  sup_num_in_active:                      470
% 15.43/2.50  sup_num_in_passive:                     1652
% 15.43/2.50  sup_num_of_loops:                       492
% 15.43/2.50  sup_fw_superposition:                   1291
% 15.43/2.50  sup_bw_superposition:                   976
% 15.43/2.50  sup_immediate_simplified:               830
% 15.43/2.50  sup_given_eliminated:                   1
% 15.43/2.50  comparisons_done:                       0
% 15.43/2.50  comparisons_avoided:                    5
% 15.43/2.50  
% 15.43/2.50  ------ Simplifications
% 15.43/2.50  
% 15.43/2.50  
% 15.43/2.50  sim_fw_subset_subsumed:                 44
% 15.43/2.50  sim_bw_subset_subsumed:                 16
% 15.43/2.50  sim_fw_subsumed:                        48
% 15.43/2.50  sim_bw_subsumed:                        0
% 15.43/2.50  sim_fw_subsumption_res:                 7
% 15.43/2.50  sim_bw_subsumption_res:                 0
% 15.43/2.50  sim_tautology_del:                      0
% 15.43/2.50  sim_eq_tautology_del:                   59
% 15.43/2.50  sim_eq_res_simp:                        2
% 15.43/2.50  sim_fw_demodulated:                     117
% 15.43/2.50  sim_bw_demodulated:                     23
% 15.43/2.50  sim_light_normalised:                   680
% 15.43/2.50  sim_joinable_taut:                      0
% 15.43/2.50  sim_joinable_simp:                      0
% 15.43/2.50  sim_ac_normalised:                      0
% 15.43/2.50  sim_smt_subsumption:                    0
% 15.43/2.50  
%------------------------------------------------------------------------------
